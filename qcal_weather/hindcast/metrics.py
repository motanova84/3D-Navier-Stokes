from __future__ import annotations

import numpy as np


def rmse(predicted, observed) -> float:
    predicted = np.asarray(predicted, dtype=float)
    observed = np.asarray(observed, dtype=float)
    return float(np.sqrt(np.mean((predicted - observed) ** 2)))


def mae(predicted, observed) -> float:
    predicted = np.asarray(predicted, dtype=float)
    observed = np.asarray(observed, dtype=float)
    return float(np.mean(np.abs(predicted - observed)))


def brier_score(predicted_probability, observed_event) -> float:
    predicted_probability = np.asarray(predicted_probability, dtype=float)
    observed_event = np.asarray(observed_event, dtype=float)
    return float(np.mean((predicted_probability - observed_event) ** 2))


def minimum_pressure_error(predicted_pressure, observed_pressure) -> float:
    return float(abs(np.min(predicted_pressure) - np.min(observed_pressure)))
