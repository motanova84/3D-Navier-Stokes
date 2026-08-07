-- ============================================================================
-- NOESIS/SpectralAnalysis.lean
-- Análisis espectral: transformadas, varianza, cotas
-- ============================================================================

import NOESIS.Coherence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace NOESIS.Spectral

open NOESIS Real

-- ============================================================
-- §1  TRANSFORMADA DE FOURIER DISCRETA (ABSTRACTA)
-- ============================================================

/-- Coeficiente de Fourier discreto k-ésimo de una señal -/
noncomputable def fourierCoeff (sig : FieldSignal) (k : ℕ) : ℝ :=
  (Finset.range sig.n_samples).sum
    (fun n => sig.samples n * Real.cos (2 * Real.pi * k * n / sig.n_samples))

/-- Energía en el coeficiente k -/
noncomputable def spectralEnergy (sig : FieldSignal) (k : ℕ) : ℝ :=
  (fourierCoeff sig k) ^ 2

-- ============================================================
-- §2  DENSIDAD ESPECTRAL DE POTENCIA
-- ============================================================

/-- Índice espectral correspondiente a f₀ para una señal de duración T y fs muestras -/
def f0Index (n_samples : ℕ) (fs : ℝ) : ℕ :=
  (f₀ * n_samples / fs).toNat

/-- Relación señal/ruido espectral en f₀ -/
noncomputable def spectralSNR (sig : FieldSignal) (fs : ℝ) : ℝ :=
  let k0 := f0Index sig.n_samples fs
  let E_signal := spectralEnergy sig k0
  let E_total := (Finset.range sig.n_samples).sum (fun k => spectralEnergy sig k)
  if E_total = 0 then 0 else E_signal / E_total

-- ============================================================
-- §3  ANCHO DE LÍNEA Y T₂*
-- ============================================================

/-- Relación de Fourier: δf = 1 / (π · T₂*) para una lorentziana -/
noncomputable def linewidthFromT2 (T2 : ℝ) : ℝ :=
  1 / (Real.pi * T2)

/-- T₂* desde el ancho de línea -/
noncomputable def T2fromLinewidth (delta_f : ℝ) : ℝ :=
  1 / (Real.pi * delta_f)

theorem T2_linewidth_inverse (T2 : ℝ) (hT2 : T2 > 0) :
    T2fromLinewidth (linewidthFromT2 T2) = T2 := by
  unfold T2fromLinewidth linewidthFromT2
  field_simp
  rw [mul_comm]
  field_simp [Real.pi_ne_zero]

-- ============================================================
-- §4  COTA ESPECTRAL PARA Ψ
-- ============================================================

/-- Cota: δf ≤ σ_f · 2√2 (relación entre FWHM y desviación estándar) -/
noncomputable def fwhmFromSigma (sigma : ℝ) : ℝ :=
  sigma * 2 * Real.sqrt 2

/-- Inversamente: σ_f ≥ FWHM / (2√2) -/
theorem sigmaLowerBound (sigma delta_f : ℝ)
    (h : fwhmFromSigma sigma = delta_f) :
    sigma = delta_f / (2 * Real.sqrt 2) := by
  unfold fwhmFromSigma at h
  linarith [h.symm, mul_comm sigma (2 * Real.sqrt 2)]

end NOESIS.Spectral
