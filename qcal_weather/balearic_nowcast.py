from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, Optional

import numpy as np

from .assimilation.enkf import EnsembleKalmanFilter, build_ensemble
from .assimilation.observation_operator import ObservationOperator
from .certification import build_technical_certification
from .config import DEFAULT_BALEARIC_CONFIG, RegionalDomainConfig
from .data.quality_control import quality_control_filter
from .data.sensors import generate_synthetic_observations
from .hindcast.baselines import run_persistence_baseline
from .hindcast.evaluation import evaluate_nowcast
from .models.atmosphere_boussinesq import AtmosphericState
from .models.atmosphere_boussinesq import BoussinesqAtmosphereModel, create_balearic_initial_state
from .models.qcal_coupling import QCALAtmosphereCoupler
from .qcal_core.coherence_field import CoherenceField


@dataclass
class NowcastResult:
    config: Dict[str, object]
    certification: Dict[str, object]
    baseline: Dict[str, object]
    qcal: Dict[str, object]
    evaluation: Dict[str, Dict[str, float]]
    accepted_observations: int
    rejected_observations: int
    coherence_mean: float


class QCALBalearicNowcast:
    def __init__(self, config: RegionalDomainConfig | None = None):
        self.config = config or DEFAULT_BALEARIC_CONFIG
        self.operator = ObservationOperator(self.config)
        self.enkf = EnsembleKalmanFilter()

    def create_initial_state(self):
        return create_balearic_initial_state(self.config)

    def build_observed_proxy(self, initial_state, forecast_hours: float):
        observed = initial_state.copy()
        y = np.linspace(-1.0, 1.0, self.config.ny)
        x = np.linspace(-1.0, 1.0, self.config.nx)
        xx, yy = np.meshgrid(x, y)
        drift = forecast_hours / max(self.config.forecast_hours_min, 1)
        observed.wind_u = observed.wind_u + 0.4 * drift * np.sin(np.pi * xx)
        observed.wind_v = observed.wind_v + 0.3 * drift * np.cos(np.pi * yy)
        observed.temperature = observed.temperature - 0.25 * drift + 0.15 * np.sin(np.pi * xx * yy)
        observed.pressure = observed.pressure + 0.15 * drift + 0.2 * np.cos(np.pi * xx)
        observed.humidity = np.clip(observed.humidity + 0.03 * drift, 0.0, 1.0)
        observed.sea_level_anomaly = observed.sea_level_anomaly + 0.01 * drift * np.sin(np.pi * yy)
        return observed

    def assimilate(self, initial_state, observations: Iterable):
        qc = quality_control_filter(observations)
        ensemble = build_ensemble(initial_state, members=4, perturbation_scale=0.03)
        updated_ensemble = self.enkf.update(ensemble, qc.accepted, self.operator)
        wind_u_stack = np.stack([member.wind_u for member in updated_ensemble], axis=0)
        wind_v_stack = np.stack([member.wind_v for member in updated_ensemble], axis=0)
        temperature_stack = np.stack([member.temperature for member in updated_ensemble], axis=0)
        pressure_stack = np.stack([member.pressure for member in updated_ensemble], axis=0)
        humidity_stack = np.stack([member.humidity for member in updated_ensemble], axis=0)
        sea_level_stack = np.stack([member.sea_level_anomaly for member in updated_ensemble], axis=0)
        mean_state = AtmosphericState(
            wind_u=np.mean(wind_u_stack, axis=0),
            wind_v=np.mean(wind_v_stack, axis=0),
            temperature=np.mean(temperature_stack, axis=0),
            pressure=np.mean(pressure_stack, axis=0),
            humidity=np.mean(humidity_stack, axis=0),
            sea_level_anomaly=np.mean(sea_level_stack, axis=0),
        )
        return mean_state, qc

    def run_cycle(
        self,
        forecast_hours: float = 6.0,
        observations: Optional[Iterable] = None,
    ) -> NowcastResult:
        initial_state = self.create_initial_state()
        observations = list(observations or generate_synthetic_observations(self.config))
        assimilated_state, qc = self.assimilate(initial_state, observations)

        baseline = run_persistence_baseline(
            assimilated_state,
            forecast_hours=forecast_hours,
            output_interval_minutes=self.config.output_interval_minutes,
        )

        coherence = CoherenceField.from_shape(assimilated_state.shape, value=1.0)
        qcal_model = BoussinesqAtmosphereModel(
            config=self.config,
            qcal_coupler=QCALAtmosphereCoupler(coherence),
        )
        qcal = qcal_model.run_forecast(assimilated_state, forecast_hours=forecast_hours)

        observed_proxy = self.build_observed_proxy(assimilated_state, forecast_hours)

        evaluation = evaluate_nowcast(
            baseline["states"][-1],
            qcal["states"][-1],
            observed_proxy,
        )

        return NowcastResult(
            config=self.config.as_dict(),
            certification=build_technical_certification(self.config).as_dict(),
            baseline=baseline,
            qcal=qcal,
            evaluation=evaluation,
            accepted_observations=len(qc.accepted),
            rejected_observations=len(qc.rejected),
            coherence_mean=float(np.mean(coherence.psi)),
        )
