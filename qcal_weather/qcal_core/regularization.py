from __future__ import annotations

import numpy as np


def coherence_regularization_factor(psi: np.ndarray, strength: float = 0.12) -> np.ndarray:
    clipped = np.clip(psi, 0.0, 1.0)
    return 1.0 - strength * (1.0 - clipped)


def apply_qcal_regularization(field: np.ndarray, psi: np.ndarray, strength: float = 0.12) -> np.ndarray:
    return field * coherence_regularization_factor(psi, strength=strength)
