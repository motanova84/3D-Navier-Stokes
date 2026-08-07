from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List

import numpy as np

from qcal_weather.qcal_core.spectral_diagnostics import compute_spectral_diagnostics, gradient_x, gradient_y, laplacian


@dataclass
class AtmosphericState:
    wind_u: np.ndarray
    wind_v: np.ndarray
    temperature: np.ndarray
    pressure: np.ndarray
    humidity: np.ndarray
    sea_level_anomaly: np.ndarray

    def copy(self) -> "AtmosphericState":
        return AtmosphericState(
            wind_u=self.wind_u.copy(),
            wind_v=self.wind_v.copy(),
            temperature=self.temperature.copy(),
            pressure=self.pressure.copy(),
            humidity=self.humidity.copy(),
            sea_level_anomaly=self.sea_level_anomaly.copy(),
        )

    @property
    def shape(self):
        return self.wind_u.shape


def create_balearic_initial_state(config) -> AtmosphericState:
    y = np.linspace(-1.0, 1.0, config.ny)
    x = np.linspace(-1.0, 1.0, config.nx)
    xx, yy = np.meshgrid(x, y)
    island_mask = np.exp(-((xx - 0.1) ** 2 + (yy + 0.1) ** 2) / 0.08)
    wind_u = 8.0 + 2.0 * np.sin(np.pi * yy)
    wind_v = 1.5 * np.cos(np.pi * xx)
    temperature = 296.0 - 4.0 * yy + 0.8 * island_mask
    pressure = 1012.0 - 5.0 * island_mask + 1.2 * xx
    humidity = np.clip(0.65 + 0.1 * island_mask - 0.05 * yy, 0.0, 1.0)
    sea_level_anomaly = 0.15 * island_mask - 0.02 * xx
    return AtmosphericState(wind_u, wind_v, temperature, pressure, humidity, sea_level_anomaly)


class BoussinesqAtmosphereModel:
    def __init__(
        self,
        config,
        viscosity: float = 0.025,
        thermal_diffusivity: float = 0.012,
        pressure_coupling: float = 0.06,
        humidity_relaxation: float = 0.03,
        advection_coupling: float = 0.02,
        temperature_advection_coupling: float = 0.04,
        divergence_pressure_feedback: float = 0.6,
        pressure_diffusivity: float = 0.01,
        sea_level_wind_u_coupling: float = 0.04,
        sea_level_wind_v_coupling: float = 0.02,
        sea_level_diffusivity: float = 0.01,
        humidity_reference: float = 0.7,
        qcal_coupler=None,
    ):
        self.config = config
        self.viscosity = viscosity
        self.thermal_diffusivity = thermal_diffusivity
        self.pressure_coupling = pressure_coupling
        self.humidity_relaxation = humidity_relaxation
        self.advection_coupling = advection_coupling
        self.temperature_advection_coupling = temperature_advection_coupling
        self.divergence_pressure_feedback = divergence_pressure_feedback
        self.pressure_diffusivity = pressure_diffusivity
        self.sea_level_wind_u_coupling = sea_level_wind_u_coupling
        self.sea_level_wind_v_coupling = sea_level_wind_v_coupling
        self.sea_level_diffusivity = sea_level_diffusivity
        self.humidity_reference = humidity_reference
        self.qcal_coupler = qcal_coupler

    def step(self, state: AtmosphericState, dt_hours: float) -> AtmosphericState:
        spacing = self.config.resolution_km
        updated = state.copy()

        pressure_dx = gradient_x(state.pressure, spacing)
        pressure_dy = gradient_y(state.pressure, spacing)
        temp_dx = gradient_x(state.temperature, spacing)
        temp_dy = gradient_y(state.temperature, spacing)

        updated.wind_u = state.wind_u + dt_hours * (
            -self.advection_coupling * state.wind_u * temp_dx
            - self.pressure_coupling * pressure_dx
            + self.viscosity * laplacian(state.wind_u, spacing)
        )
        updated.wind_v = state.wind_v + dt_hours * (
            -self.advection_coupling * state.wind_v * temp_dy
            - self.pressure_coupling * pressure_dy
            + self.viscosity * laplacian(state.wind_v, spacing)
        )
        updated.temperature = state.temperature + dt_hours * (
            -self.temperature_advection_coupling * (state.wind_u * temp_dx + state.wind_v * temp_dy)
            + self.thermal_diffusivity * laplacian(state.temperature, spacing)
        )
        divergence = gradient_x(updated.wind_u, spacing) + gradient_y(updated.wind_v, spacing)
        updated.pressure = state.pressure + dt_hours * (
            -self.divergence_pressure_feedback * divergence
            + self.pressure_diffusivity * laplacian(state.pressure, spacing)
        )
        updated.humidity = np.clip(
            state.humidity
            + dt_hours
            * (
                -self.advection_coupling * divergence
                - self.humidity_relaxation * (state.humidity - self.humidity_reference)
            ),
            0.0,
            1.0,
        )
        updated.sea_level_anomaly = state.sea_level_anomaly + dt_hours * (
            self.sea_level_wind_u_coupling * updated.wind_u
            - self.sea_level_wind_v_coupling * updated.wind_v
            + self.sea_level_diffusivity * laplacian(state.sea_level_anomaly, spacing)
        )

        diagnostics = compute_spectral_diagnostics(updated, spacing)
        if self.qcal_coupler is not None:
            updated = self.qcal_coupler.apply(updated, diagnostics, dt_hours, spacing)
        return updated

    def run_forecast(self, initial_state: AtmosphericState, forecast_hours: float) -> Dict[str, List]:
        dt_hours = self.config.output_interval_minutes / 60.0
        steps = max(1, int(round(forecast_hours / dt_hours)))
        state = initial_state.copy()
        history = [state.copy()]
        diagnostics = [compute_spectral_diagnostics(state, self.config.resolution_km)]

        for _ in range(steps):
            state = self.step(state, dt_hours)
            history.append(state.copy())
            diagnostics.append(compute_spectral_diagnostics(state, self.config.resolution_km))

        return {
            "states": history,
            "diagnostics": diagnostics,
            "times_hours": np.linspace(0.0, steps * dt_hours, steps + 1),
        }
