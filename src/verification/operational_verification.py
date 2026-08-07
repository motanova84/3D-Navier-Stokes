#!/usr/bin/env python3
"""
Operational verification and synthetic certification support for QCAL-Balearic.
"""

from __future__ import annotations

import argparse
from datetime import UTC, datetime
import json
import logging
from pathlib import Path
from typing import Dict

import numpy as np
import xarray as xr
import yaml


LOGGER = logging.getLogger("qcal-verification")


class OperationalVerification:
    def __init__(self, config_path: str = "configs/verification_config.yaml"):
        with open(config_path, "r", encoding="utf-8") as handle:
            self.config = yaml.safe_load(handle) or {}
        self.baseline_results: Dict[int, Dict[str, float]] = {}
        self.qcal_results: Dict[int, Dict[str, float]] = {}
        self.comparison_results: Dict[int, Dict[str, float]] = {}

    def run_benchmark(
        self,
        baseline_predictions: Dict[int, xr.Dataset],
        qcal_predictions: Dict[int, xr.Dataset],
        observations: Dict[int, xr.Dataset],
    ) -> Dict[int, Dict[str, Dict[str, float]]]:
        results: Dict[int, Dict[str, Dict[str, float]]] = {}
        common_hours = sorted(set(baseline_predictions) & set(qcal_predictions) & set(observations))
        for hour in common_hours:
            baseline_metrics = self._compute_metrics(baseline_predictions[hour], observations[hour])
            qcal_metrics = self._compute_metrics(qcal_predictions[hour], observations[hour])
            comparison = self._compare_metrics(baseline_metrics, qcal_metrics)
            results[hour] = {
                "baseline": baseline_metrics,
                "qcal": qcal_metrics,
                "comparison": comparison,
            }
        self.baseline_results = {hour: value["baseline"] for hour, value in results.items()}
        self.qcal_results = {hour: value["qcal"] for hour, value in results.items()}
        self.comparison_results = {hour: value["comparison"] for hour, value in results.items()}
        return results

    def _compute_metrics(self, predictions: xr.Dataset, observations: xr.Dataset) -> Dict[str, float]:
        metrics: Dict[str, float] = {}
        for var_name in predictions.data_vars:
            if var_name not in observations.data_vars:
                continue
            pred = predictions[var_name].values
            obs = observations[var_name].values
            metrics[f"{var_name}_rmse"] = float(np.sqrt(np.mean((pred - obs) ** 2)))
            metrics[f"{var_name}_mae"] = float(np.mean(np.abs(pred - obs)))
            metrics[f"{var_name}_bias"] = float(np.mean(pred - obs))
            pred_flat = pred.reshape(-1)
            obs_flat = obs.reshape(-1)
            if np.allclose(pred_flat, pred_flat[0]) or np.allclose(obs_flat, obs_flat[0]):
                corr = 1.0 if np.allclose(pred_flat, obs_flat) else 0.0
            else:
                corr = float(np.corrcoef(pred_flat, obs_flat)[0, 1])
            metrics[f"{var_name}_corr"] = corr
        return metrics

    def _compare_metrics(self, baseline: Dict[str, float], qcal: Dict[str, float]) -> Dict[str, float]:
        comparison: Dict[str, float] = {}
        for key, baseline_value in baseline.items():
            if key not in qcal:
                continue
            qcal_value = qcal[key]
            if key.endswith("_corr"):
                denom = abs(baseline_value) if baseline_value != 0 else 1.0
                improvement = (qcal_value - baseline_value) / denom
            else:
                denom = abs(baseline_value) if baseline_value != 0 else 1.0
                improvement = (baseline_value - qcal_value) / denom
            comparison[f"{key}_improvement"] = float(improvement * 100.0)
            comparison[f"{key}_ss"] = float(improvement)
        return comparison

    def compute_skill_score(self) -> Dict[str, float]:
        aggregate: Dict[str, list[float]] = {}
        for hour_values in self.comparison_results.values():
            for key, value in hour_values.items():
                if key.endswith("_ss"):
                    aggregate.setdefault(key.replace("_ss", ""), []).append(value)
        return {key: float(np.mean(values)) for key, values in aggregate.items()}

    def generate_verification_report(self, output_path: str = "verification_report.json") -> Dict[str, object]:
        report = {
            "timestamp": datetime.now(UTC).isoformat(),
            "system": "QCAL-Balearic Nowcast",
            "version": "1.0.0",
            "f0_hz": 141.7001,
            "metrics": {
                "baseline": self.baseline_results,
                "qcal": self.qcal_results,
                "comparison": self.comparison_results,
            },
            "skill_score": self.compute_skill_score(),
        }
        report["summary"] = self._generate_summary(report["skill_score"])
        with open(output_path, "w", encoding="utf-8") as handle:
            json.dump(report, handle, indent=2)
        return report

    def _generate_summary(self, skill_score: Dict[str, float]) -> Dict[str, object]:
        values = list(skill_score.values()) or [0.0]
        threshold = float(self.config.get("certification_threshold", 0.0))
        qcal_superior = any(value > threshold for value in values)
        return {
            "status": "CERTIFIED" if qcal_superior else "NEEDS_IMPROVEMENT",
            "skill_score_mean": float(np.mean(values)),
            "skill_score_max": float(np.max(values)),
            "qcal_superior": qcal_superior,
            "certification": "PASSED" if qcal_superior else "PENDING",
        }


def _load_hourly_zarr(prefix_path: str) -> Dict[int, xr.Dataset]:
    base = Path(prefix_path)
    datasets: Dict[int, xr.Dataset] = {}
    if base.is_dir() and base.suffix == ".zarr":
        datasets[0] = xr.open_zarr(base, consolidated=False)
        return datasets
    if base.is_dir():
        for path in sorted(base.glob("*.zarr")):
            try:
                hour = int(path.stem.split("_f")[-1])
            except ValueError:
                continue
            datasets[hour] = xr.open_zarr(path, consolidated=False)
    return datasets


def main() -> None:
    parser = argparse.ArgumentParser(description="Run operational verification for QCAL-Balearic.")
    parser.add_argument("--baseline", required=True)
    parser.add_argument("--qcal", required=True)
    parser.add_argument("--observations", required=True)
    parser.add_argument("--output", default="verification_report.json")
    args = parser.parse_args()

    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    verification = OperationalVerification()
    baseline = _load_hourly_zarr(args.baseline)
    qcal = _load_hourly_zarr(args.qcal)
    observations = _load_hourly_zarr(args.observations)
    verification.run_benchmark(baseline, qcal, observations)
    report = verification.generate_verification_report(args.output)
    print(json.dumps(report["summary"], indent=2))


if __name__ == "__main__":
    main()
