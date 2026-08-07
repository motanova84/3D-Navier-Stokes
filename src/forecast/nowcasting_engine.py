#!/usr/bin/env python3
"""
Real-time style nowcasting engine for Phase 4.
"""

from __future__ import annotations

import asyncio
from datetime import UTC, datetime
import logging
from pathlib import Path
from typing import Dict, List, Optional

import numpy as np
import xarray as xr

from src.forecast.temporal_predictor import PredictorConfig, TemporalPredictor


LOGGER = logging.getLogger("qcal-nowcast")


class NowcastingEngine:
    def __init__(
        self,
        update_interval: int = 300,
        forecast_hours: List[int] | None = None,
        qcal_alpha: float = 0.05,
        qcal_lambda: float = 0.01,
        output_dir: str = "data/nowcasts",
    ):
        self.update_interval = update_interval
        self.forecast_hours = forecast_hours or [1, 2, 3, 6]
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.predictor = TemporalPredictor(
            PredictorConfig(
                forecast_hours=tuple(self.forecast_hours),
                dt_seconds=600.0,
                qcal_alpha=qcal_alpha,
                qcal_lambda=qcal_lambda,
                output_dir=str(self.output_dir),
            )
        )
        self.state: xr.Dataset | None = None
        self.observations: Dict[str, xr.DataArray] | None = None
        self.nowcasts: Dict[int, xr.Dataset] = {}
        self.last_publication: Dict[str, object] | None = None
        self.is_running = False

    async def start(self, cycles: int | None = None) -> None:
        self.is_running = True
        completed = 0
        while self.is_running:
            started = datetime.now(UTC)
            observations = await self._fetch_observations()
            self.observations = observations
            self.state = await self._update_state()
            nowcast = await self._generate_nowcast()
            await self._save_nowcast(nowcast)
            await self._publish_nowcast(nowcast)
            completed += 1
            if cycles is not None and completed >= cycles:
                self.stop()
                break
            elapsed = (datetime.now(UTC) - started).total_seconds()
            await asyncio.sleep(max(0.0, self.update_interval - elapsed))

    def stop(self) -> None:
        self.is_running = False

    async def _fetch_observations(self) -> Dict[str, xr.DataArray]:
        await asyncio.sleep(0)
        if self.state is None:
            return {}
        return {
            "u": self.state["u"] + 0.05,
            "T": self.state["T"] - 0.1,
        }

    async def _update_state(self) -> xr.Dataset:
        await asyncio.sleep(0)
        if self.state is None:
            raise ValueError("Nowcasting state not initialized")
        updated = self.state.copy(deep=True)
        for var_name, observation in (self.observations or {}).items():
            if var_name in updated.data_vars:
                updated[var_name].values = 0.7 * updated[var_name].values + 0.3 * observation.values
        return updated

    async def _generate_nowcast(self) -> Dict[int, xr.Dataset]:
        await asyncio.sleep(0)
        if self.state is None:
            raise ValueError("Nowcasting state not initialized")
        self.predictor.initialize_state(self.state)
        steps = int(max(self.forecast_hours) * 3600 / self.predictor.config.dt_seconds)
        output_frequency = max(1, int(3600 / self.predictor.config.dt_seconds))
        self.nowcasts = self.predictor.integrate_forecast(steps=steps, output_frequency=output_frequency)
        return self.nowcasts

    async def _save_nowcast(self, nowcast: Dict[int, xr.Dataset]) -> None:
        await asyncio.sleep(0)
        stamp = datetime.now(UTC).strftime("%Y%m%d_%H%M")
        self.predictor.save_forecast(nowcast, name=f"nowcast_{stamp}")

    async def _publish_nowcast(self, nowcast: Dict[int, xr.Dataset]) -> None:
        await asyncio.sleep(0)
        self.last_publication = {
            "timestamp": datetime.now(UTC).isoformat(),
            "hours": sorted(nowcast.keys()),
        }

    def get_latest_nowcast(self, hour: int = 1) -> Optional[xr.Dataset]:
        return self.nowcasts.get(hour)
