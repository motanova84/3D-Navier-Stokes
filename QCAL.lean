/-
QCAL (Quantum-Classical Analysis Library)
Root module for quantum coherence and frequency analysis

New modules for QCAL ∞³ Framework:
- ErdosUlam: Infinite set of points with rational distances
- CoherentFunction: Functions with coherence threshold ≥ 0.888
- SpectralAnalysis: Entropy and spectral properties
- NLSEquation: Modified nonlinear Schrödinger equation
- SarnakPrinciple: QCAL-Sarnak orthogonality principle
- EnergyEstimates: Energy decay and estimates
- SpacetimeFluid: Spacetime-fluid correspondence (membrane paradigm)
- Bures: Bures-Fisher metric on the quantum phase manifold
- EnergyMinimum: Minimum operator energy h = f₀ · Ψ (Liber XXII)
- QmolFormat: Extended QCAL-MOL hybrid format specification (Liber XXII)
-/

import QCAL.Frequency
import QCAL.NoeticField
import QCAL.ErdosUlam
import QCAL.CoherentFunction
import QCAL.SpectralAnalysis
import QCAL.NLSEquation
import QCAL.SarnakPrinciple
import QCAL.EnergyEstimates
import QCAL.SpacetimeFluid
import QCAL.Bures
import QCAL.EnergyMinimum
import QCAL.QmolFormat
-- Note: QCAL.FrequencyValidation.F0Derivation contains similar definitions
-- and is imported separately when needed to avoid naming conflicts
