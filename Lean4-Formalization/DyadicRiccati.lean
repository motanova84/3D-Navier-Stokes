-- DyadicRiccati.lean
-- Wrapper for NavierStokes.DyadicRiccati module
-- Provides root-level access to dyadic Riccati inequality results

import NavierStokes.DyadicRiccati

/-!
# Dyadic Riccati Inequality

This module re-exports the dyadic Riccati inequality from NavierStokes.DyadicRiccati.

## Main Result

The dyadic Riccati coefficient becomes negative for high frequencies:

```
α_j = C_BKM(1-δ*)(1+log(C_BKM/ν)) - ν·c_B·2^{2j} < 0  for j ≥ j_d
```

This leads to exponential decay of high-frequency vorticity components,
establishing the key damping mechanism for global regularity.

## Key Theorems

- `dyadic_riccati_inequality`: α_j < 0 for j ≥ j_d
- `dissipative_threshold_definition`: Explicit formula for j_d
- `positive_damping_from_misalignment`: δ* > 1 - ν/512 implies γ > 0

All proofs are complete without sorry.

## Status: ✅ COMPLETADO

Deducción exacta de la desigualdad de Riccati diádica.
-/
