#!/usr/bin/env python3
"""
Frontier and observation ingestion for QCAL-Balearic Nowcast Phase 2.

Real remote connectors are intentionally not hard-wired in this environment.
The module supports deterministic simulated payloads and local cache creation,
which can later be replaced by authenticated operational fetchers.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import UTC, datetime
import hashlib
import json
import logging
from pathlib import Path
from typing import Any, Dict

import numpy as np
import pandas as pd
import requests
import xarray as xr
import yaml


LOGGER = logging.getLogger("qcal-frontier")


@dataclass
class SourceState:
    active: bool = False
    last_update: str | None = None
    cache_path: str | None = None
    mode: str = "simulate"
    data: Any = None


class FrontierIngestion:
    """
    Frontier and observation ingestion manager.
    """

    def __init__(self, config_path: str = "configs/frontier_config.yaml"):
        self.config_path = Path(config_path)
        self.config = self._load_config(self.config_path)
        self.cache_dir = Path(self.config.get("cache_dir", "data/cache"))
        self.cache_dir.mkdir(parents=True, exist_ok=True)
        self.simulate = bool(self.config.get("simulate", True))
        self.session = requests.Session()
        self.sources: Dict[str, SourceState] = {
            name: SourceState(active=False, mode="simulate" if self.simulate else "remote")
            for name in ("gfs", "ecmwf", "socib", "aemet", "puertos", "copernicus", "qcal")
        }
        LOGGER.info("Initialized frontier ingestion with cache %s", self.cache_dir)

    def _load_config(self, path: Path) -> Dict[str, Any]:
        with open(path, "r", encoding="utf-8") as handle:
            return yaml.safe_load(handle) or {}

    def _now(self) -> datetime:
        return datetime.now(UTC)

    def _time_index(self, freq: str) -> pd.DatetimeIndex:
        return pd.date_range(pd.Timestamp(self._now()).tz_localize(None), periods=1, freq=freq)

    def _rng(self, key: str) -> np.random.Generator:
        digest = hashlib.sha256(key.encode("utf-8")).digest()
        seed = int.from_bytes(digest[:8], "little", signed=False)
        return np.random.default_rng(seed)

    def _cache_dataset(self, name: str, dataset: xr.Dataset, suffix: str) -> Path:
        path = self.cache_dir / f"{name}_{suffix}.zarr"
        if path.exists():
            import shutil

            shutil.rmtree(path)
        dataset.to_zarr(path, mode="w", consolidated=False)
        return path

    def _cache_dataframe(self, name: str, frame: pd.DataFrame, suffix: str) -> Path:
        path = self.cache_dir / f"{name}_{suffix}.json"
        frame.to_json(path, orient="records", date_format="iso")
        return path

    def _mark_source(self, name: str, data: Any, cache_path: Path | None) -> Any:
        state = self.sources[name]
        state.active = True
        state.last_update = self._now().isoformat()
        state.cache_path = str(cache_path) if cache_path else None
        state.data = data
        return data

    def fetch_gfs(self, forecast_hour: int = 0) -> xr.Dataset:
        dataset = self._simulate_gfs_data(forecast_hour)
        cache_path = self._cache_dataset("gfs", dataset, f"{forecast_hour:03d}")
        return self._mark_source("gfs", dataset, cache_path)

    def fetch_ecmwf(self, forecast_hour: int = 0) -> xr.Dataset:
        dataset = self._simulate_ecmwf_data(forecast_hour)
        cache_path = self._cache_dataset("ecmwf", dataset, f"{forecast_hour:03d}")
        return self._mark_source("ecmwf", dataset, cache_path)

    def fetch_socib(self) -> pd.DataFrame:
        frame = self._simulate_socib_data()
        cache_path = self._cache_dataframe("socib", frame, self._now().strftime("%Y%m%dT%H%M%S"))
        return self._mark_source("socib", frame, cache_path)

    def fetch_aemet(self) -> pd.DataFrame:
        frame = self._simulate_aemet_data()
        cache_path = self._cache_dataframe("aemet", frame, self._now().strftime("%Y%m%dT%H%M%S"))
        return self._mark_source("aemet", frame, cache_path)

    def fetch_puertos(self) -> pd.DataFrame:
        frame = self._simulate_puertos_data()
        cache_path = self._cache_dataframe("puertos", frame, self._now().strftime("%Y%m%dT%H%M%S"))
        return self._mark_source("puertos", frame, cache_path)

    def fetch_copernicus_marine(self) -> xr.Dataset:
        dataset = self._simulate_copernicus_data()
        cache_path = self._cache_dataset("copernicus", dataset, self._now().strftime("%Y%m%dT%H%M%S"))
        return self._mark_source("copernicus", dataset, cache_path)

    def fetch_qcal_field(self) -> xr.Dataset:
        dataset = self._simulate_qcal_data()
        cache_path = self._cache_dataset("qcal", dataset, self._now().strftime("%Y%m%dT%H%M%S"))
        return self._mark_source("qcal", dataset, cache_path)

    def ingest_all(self, forecast_hour: int = 0) -> Dict[str, Any]:
        return {
            "gfs": self.fetch_gfs(forecast_hour),
            "ecmwf": self.fetch_ecmwf(forecast_hour),
            "socib": self.fetch_socib(),
            "aemet": self.fetch_aemet(),
            "puertos": self.fetch_puertos(),
            "copernicus": self.fetch_copernicus_marine(),
            "qcal": self.fetch_qcal_field(),
        }

    def source_summary(self) -> Dict[str, Dict[str, Any]]:
        return {
            name: {
                "active": state.active,
                "last_update": state.last_update,
                "cache_path": state.cache_path,
                "mode": state.mode,
            }
            for name, state in self.sources.items()
        }

    def _simulate_gfs_data(self, forecast_hour: int) -> xr.Dataset:
        rng = self._rng(f"gfs-{forecast_hour}")
        lat = np.linspace(35.0, 45.0, 41)
        lon = np.linspace(-5.0, 5.0, 41)
        time = self._time_index("6h")
        return xr.Dataset(
            {
                "u10": (("time", "lat", "lon"), rng.normal(6.0, 2.0, size=(1, 41, 41)).astype(np.float32)),
                "v10": (("time", "lat", "lon"), rng.normal(1.0, 2.0, size=(1, 41, 41)).astype(np.float32)),
                "t2m": (("time", "lat", "lon"), rng.normal(289.0, 3.0, size=(1, 41, 41)).astype(np.float32)),
                "mslp": (("time", "lat", "lon"), rng.normal(101325.0, 500.0, size=(1, 41, 41)).astype(np.float32)),
            },
            coords={"time": time, "lat": lat, "lon": lon},
            attrs={"source": "gfs", "forecast_hour": forecast_hour, "mode": "simulated"},
        )

    def _simulate_ecmwf_data(self, forecast_hour: int) -> xr.Dataset:
        dataset = self._simulate_gfs_data(forecast_hour).rename({"u10": "u10_ifs", "v10": "v10_ifs"})
        dataset.attrs["source"] = "ecmwf"
        return dataset

    def _simulate_socib_data(self) -> pd.DataFrame:
        rng = self._rng("socib")
        return pd.DataFrame(
            {
                "station": ["Mallorca", "Menorca", "Ibiza"],
                "latitude": [39.5, 39.9, 38.9],
                "longitude": [2.7, 4.2, 1.4],
                "temperature": rng.normal(23.0, 1.0, size=3),
                "salinity": rng.normal(37.0, 0.2, size=3),
                "wave_height": rng.normal(1.2, 0.3, size=3),
                "timestamp": [self._now().isoformat()] * 3,
            }
        )

    def _simulate_aemet_data(self) -> pd.DataFrame:
        rng = self._rng("aemet")
        return pd.DataFrame(
            {
                "station": ["Palma", "Mahon", "Ibiza"],
                "latitude": [39.57, 39.88, 38.91],
                "longitude": [2.65, 4.26, 1.43],
                "temperature": rng.normal(298.0, 1.5, size=3),
                "humidity": np.clip(rng.normal(0.65, 0.07, size=3), 0.0, 1.0),
                "pressure": rng.normal(1012.0, 4.0, size=3),
                "wind_speed": np.abs(rng.normal(6.0, 2.0, size=3)),
                "timestamp": [self._now().isoformat()] * 3,
            }
        )

    def _simulate_puertos_data(self) -> pd.DataFrame:
        rng = self._rng("puertos")
        return pd.DataFrame(
            {
                "station": ["Palma Port", "Mahon Port"],
                "latitude": [39.55, 39.89],
                "longitude": [2.63, 4.28],
                "sea_level": rng.normal(0.12, 0.04, size=2),
                "wave_height": np.abs(rng.normal(0.9, 0.2, size=2)),
                "timestamp": [self._now().isoformat()] * 2,
            }
        )

    def _simulate_copernicus_data(self) -> xr.Dataset:
        rng = self._rng("copernicus")
        lat = np.linspace(35.0, 45.0, 41)
        lon = np.linspace(-5.0, 5.0, 41)
        time = self._time_index("1D")
        return xr.Dataset(
            {
                "sst": (("time", "lat", "lon"), rng.normal(296.0, 1.0, size=(1, 41, 41)).astype(np.float32)),
                "chl": (("time", "lat", "lon"), np.abs(rng.normal(1.0, 0.2, size=(1, 41, 41))).astype(np.float32)),
            },
            coords={"time": time, "lat": lat, "lon": lon},
            attrs={"source": "copernicus", "mode": "simulated"},
        )

    def _simulate_qcal_data(self) -> xr.Dataset:
        rng = self._rng("qcal")
        lat = np.linspace(35.0, 45.0, 41)
        lon = np.linspace(-5.0, 5.0, 41)
        time = self._time_index("6h")
        psi = np.clip(rng.normal(0.999999, 1e-6, size=(1, 41, 41)), 0.999998, 1.0).astype(np.float32)
        return xr.Dataset(
            {
                "psi": (("time", "lat", "lon"), psi),
                "coherence": (("time", "lat", "lon"), psi),
                "entropy": (("time", "lat", "lon"), (-psi * np.log(psi + 1e-12)).astype(np.float32)),
                "freq_dev": (("time", "lat", "lon"), ((psi - 0.999999) * 141.7001).astype(np.float32)),
            },
            coords={"time": time, "lat": lat, "lon": lon},
            attrs={"source": "qcal", "mode": "simulated"},
        )


def main() -> None:
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    ingestion = FrontierIngestion()
    results = ingestion.ingest_all()
    print(json.dumps({"sources": list(results.keys()), "summary": ingestion.source_summary()}, indent=2))


if __name__ == "__main__":
    main()
