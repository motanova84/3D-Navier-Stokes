#!/usr/bin/env python3
"""
Quality control helpers for frontier and observation ingestion.
"""

from __future__ import annotations

import logging
from typing import Tuple

import numpy as np
import pandas as pd
import xarray as xr


LOGGER = logging.getLogger("qcal-qc")


class QualityControl:
    @staticmethod
    def check_range(data: xr.Dataset, var: str, vmin: float, vmax: float) -> xr.Dataset:
        checked = data.copy()
        checked[var] = checked[var].where((checked[var] >= vmin) & (checked[var] <= vmax))
        return checked

    @staticmethod
    def remove_outliers(data: xr.Dataset, var: str, n_std: float = 3.0) -> xr.Dataset:
        checked = data.copy()
        mean = checked[var].mean()
        std = checked[var].std()
        checked[var] = checked[var].where(abs(checked[var] - mean) <= n_std * std)
        return checked

    @staticmethod
    def interpolate_nans(data: xr.Dataset, var: str, method: str = "linear") -> xr.Dataset:
        checked = data.copy()
        if "time" in checked[var].dims:
            checked[var] = checked[var].interpolate_na(dim="time", method=method)
        else:
            checked[var] = checked[var].fillna(checked[var].mean())
        return checked

    @staticmethod
    def sanitize_frame(frame: pd.DataFrame, columns: dict[str, tuple[float, float]]) -> pd.DataFrame:
        cleaned = frame.copy()
        for column, (lower, upper) in columns.items():
            cleaned.loc[(cleaned[column] < lower) | (cleaned[column] > upper), column] = np.nan
        return cleaned

    @staticmethod
    def check_qcal_field(psi: np.ndarray, threshold: float = 0.999999) -> Tuple[np.ndarray, np.ndarray]:
        checked = np.array(psi, copy=True, dtype=float)
        invalid = (checked < 0.0) | (checked > 1.0)
        checked[invalid] = np.nan
        below_threshold = checked < threshold
        LOGGER.info("QCAL below threshold cells: %s", int(np.nansum(below_threshold)))
        LOGGER.info("QCAL invalid cells: %s", int(np.sum(invalid)))
        return checked, below_threshold
