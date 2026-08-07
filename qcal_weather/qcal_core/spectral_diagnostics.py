from __future__ import annotations

from typing import Dict

import numpy as np


def gradient_x(field: np.ndarray, spacing_km: float) -> np.ndarray:
    gradient = np.empty_like(field, dtype=float)
    gradient[:, 1:-1] = (field[:, 2:] - field[:, :-2]) / (2.0 * spacing_km)
    gradient[:, 0] = (field[:, 1] - field[:, 0]) / spacing_km
    gradient[:, -1] = (field[:, -1] - field[:, -2]) / spacing_km
    return gradient


def gradient_y(field: np.ndarray, spacing_km: float) -> np.ndarray:
    gradient = np.empty_like(field, dtype=float)
    gradient[1:-1, :] = (field[2:, :] - field[:-2, :]) / (2.0 * spacing_km)
    gradient[0, :] = (field[1, :] - field[0, :]) / spacing_km
    gradient[-1, :] = (field[-1, :] - field[-2, :]) / spacing_km
    return gradient


def laplacian(field: np.ndarray, spacing_km: float) -> np.ndarray:
    padded = np.pad(field, pad_width=1, mode="edge")
    return (
        padded[2:, 1:-1]
        + padded[:-2, 1:-1]
        + padded[1:-1, 2:]
        + padded[1:-1, :-2]
        - 4.0 * padded[1:-1, 1:-1]
    ) / max(spacing_km**2, 1e-12)


def compute_spectral_diagnostics(state, spacing_km: float) -> Dict[str, float]:
    wind_u = state.wind_u
    wind_v = state.wind_v
    temperature = state.temperature
    pressure = state.pressure

    dudx = gradient_x(wind_u, spacing_km)
    dudy = gradient_y(wind_u, spacing_km)
    dvdx = gradient_x(wind_v, spacing_km)
    dvdy = gradient_y(wind_v, spacing_km)
    temp_dx = gradient_x(temperature, spacing_km)
    temp_dy = gradient_y(temperature, spacing_km)
    pressure_dx = gradient_x(pressure, spacing_km)
    pressure_dy = gradient_y(pressure, spacing_km)

    vorticity = dvdx - dudy
    divergence = dudx + dvdy

    wind_speed = np.sqrt(wind_u**2 + wind_v**2)
    kinetic_energy = 0.5 * np.mean(wind_speed**2)

    return {
        "kinetic_energy": float(kinetic_energy),
        "wind_speed_mean": float(np.mean(wind_speed)),
        "vorticity_rms": float(np.sqrt(np.mean(vorticity**2))),
        "vorticity_norm_sq": float(np.mean(vorticity**2)),
        "divergence_abs_mean": float(np.mean(np.abs(divergence))),
        "temperature_gradient_norm_sq": float(np.mean(temp_dx**2 + temp_dy**2)),
        "pressure_gradient_norm_sq": float(np.mean(pressure_dx**2 + pressure_dy**2)),
    }
