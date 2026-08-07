#!/usr/bin/env python3
"""
Tests for the QCAL Balearic Nowcast MVP package.
"""

from datetime import UTC, datetime
import unittest

import numpy as np

from qcal_weather import QCALBalearicNowcast, RegionalDomainConfig, build_technical_certification
from qcal_weather.assimilation import EnsembleKalmanFilter, ObservationOperator, build_ensemble
from qcal_weather.data import Observation, generate_synthetic_observations, quality_control_filter
from qcal_weather.hindcast import brier_score, evaluate_nowcast, mae, minimum_pressure_error, rmse
from qcal_weather.models import BoussinesqAtmosphereModel, QCALAtmosphereCoupler, create_balearic_initial_state
from qcal_weather.qcal_core import CoherenceField, compute_spectral_diagnostics


class TestRegionalDomainConfig(unittest.TestCase):
    def test_domain_metrics(self):
        config = RegionalDomainConfig()
        self.assertEqual(config.nx, 167)
        self.assertEqual(config.ny, 167)
        self.assertEqual(config.total_cells, 167 * 167 * 60)
        self.assertGreater(config.estimated_state_size_mb(), 100.0)
        report_1km = config.mesh_memory_report(1.0)
        self.assertEqual(report_1km["total_cells"], 500 * 500 * 60)
        self.assertGreater(report_1km["state_memory_mb"], 900.0)
        self.assertGreater(report_1km["peak_vram_gb"], 9.0)

    def test_technical_certification(self):
        certification = build_technical_certification(RegionalDomainConfig())
        self.assertTrue(certification.hardware_ok)
        self.assertEqual(certification.status, "certified")
        self.assertGreater(certification.gpu_margin_percent, 100.0)


class TestQCALWeatherCore(unittest.TestCase):
    def setUp(self):
        self.config = RegionalDomainConfig(domain_size_km=(60.0, 60.0), resolution_km=20.0, vertical_levels=4)
        self.state = create_balearic_initial_state(self.config)

    def test_initial_state_shape(self):
        self.assertEqual(self.state.wind_u.shape, (3, 3))
        self.assertEqual(self.state.pressure.shape, (3, 3))

    def test_spectral_diagnostics(self):
        diagnostics = compute_spectral_diagnostics(self.state, self.config.resolution_km)
        self.assertIn("kinetic_energy", diagnostics)
        self.assertIn("vorticity_rms", diagnostics)
        self.assertGreater(diagnostics["wind_speed_mean"], 0.0)

    def test_coherence_field_update(self):
        coherence = CoherenceField.from_shape(self.state.shape, value=1.0)
        updated = coherence.step(self.state, dt_hours=1.0 / 6.0, spacing_km=self.config.resolution_km)
        self.assertEqual(updated.shape, self.state.shape)
        self.assertTrue(np.all(updated <= 1.0))
        self.assertTrue(np.all(updated >= 0.0))

    def test_model_forecast_without_qcal(self):
        model = BoussinesqAtmosphereModel(self.config)
        forecast = model.run_forecast(self.state, forecast_hours=1.0)
        self.assertEqual(len(forecast["states"]), 7)
        self.assertEqual(len(forecast["diagnostics"]), 7)

    def test_model_forecast_with_qcal(self):
        coherence = CoherenceField.from_shape(self.state.shape, value=1.0)
        coupler = QCALAtmosphereCoupler(coherence)
        model = BoussinesqAtmosphereModel(self.config, qcal_coupler=coupler)
        forecast = model.run_forecast(self.state, forecast_hours=1.0)
        self.assertEqual(len(forecast["states"]), 7)
        self.assertGreaterEqual(float(np.mean(coherence.psi)), 0.0)


class TestObservationsAndAssimilation(unittest.TestCase):
    def setUp(self):
        self.config = RegionalDomainConfig(domain_size_km=(60.0, 60.0), resolution_km=20.0, vertical_levels=4)
        self.state = create_balearic_initial_state(self.config)

    def test_quality_control_rejects_invalid_values(self):
        observations = [
            Observation(datetime.now(UTC), self.config.center_lat, self.config.center_lon, "temperature", 295.0),
            Observation(datetime.now(UTC), self.config.center_lat, self.config.center_lon, "temperature", 600.0),
        ]
        qc = quality_control_filter(observations)
        self.assertEqual(len(qc.accepted), 1)
        self.assertEqual(len(qc.rejected), 1)

    def test_observation_operator_reads_model_state(self):
        operator = ObservationOperator(self.config)
        value = operator.read_variable(self.state, "pressure", self.config.center_lat, self.config.center_lon)
        self.assertIsInstance(value, float)

    def test_enkf_update_returns_ensemble(self):
        observations = generate_synthetic_observations(self.config)
        qc = quality_control_filter(observations)
        operator = ObservationOperator(self.config)
        ensemble = build_ensemble(self.state, members=4)
        updated = EnsembleKalmanFilter().update(ensemble, qc.accepted, operator)
        self.assertEqual(len(updated), 4)
        self.assertEqual(updated[0].wind_u.shape, self.state.wind_u.shape)


class TestHindcastMetrics(unittest.TestCase):
    def test_scalar_metrics(self):
        predicted = np.array([1.0, 2.0, 3.0])
        observed = np.array([1.0, 3.0, 2.0])
        self.assertAlmostEqual(rmse(predicted, observed), np.sqrt(2.0 / 3.0))
        self.assertAlmostEqual(mae(predicted, observed), 2.0 / 3.0)
        self.assertAlmostEqual(brier_score(np.array([0.1, 0.8]), np.array([0.0, 1.0])), 0.025)
        self.assertAlmostEqual(minimum_pressure_error(predicted, observed), 0.0)

    def test_evaluation_summary(self):
        config = RegionalDomainConfig(domain_size_km=(60.0, 60.0), resolution_km=20.0, vertical_levels=4)
        baseline = create_balearic_initial_state(config)
        qcal = create_balearic_initial_state(config)
        observed = create_balearic_initial_state(config)
        observed.temperature = observed.temperature - 0.5
        scores = evaluate_nowcast(baseline, qcal, observed)
        self.assertIn("baseline", scores)
        self.assertIn("qcal", scores)


class TestBalearicNowcastPipeline(unittest.TestCase):
    def test_run_cycle(self):
        config = RegionalDomainConfig(domain_size_km=(60.0, 60.0), resolution_km=20.0, vertical_levels=4)
        result = QCALBalearicNowcast(config).run_cycle(forecast_hours=1.0)
        self.assertGreater(result.accepted_observations, 0)
        self.assertIn("baseline", result.evaluation)
        self.assertIn("qcal", result.evaluation)
        self.assertGreaterEqual(result.coherence_mean, 0.0)
        self.assertEqual(result.certification["status"], "certified")


if __name__ == "__main__":
    unittest.main()
