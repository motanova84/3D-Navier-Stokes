from __future__ import annotations


def run_persistence_baseline(initial_state, forecast_hours: float, output_interval_minutes: int):
    steps = max(1, int(round(forecast_hours / (output_interval_minutes / 60.0))))
    states = [initial_state.copy() for _ in range(steps + 1)]
    return {
        "states": states,
        "times_hours": [index * output_interval_minutes / 60.0 for index in range(steps + 1)],
        "diagnostics": [],
    }
