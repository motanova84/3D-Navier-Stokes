# QFT-Based Φ_ij(Ψ) Tensor Derivation

This directory contains scripts for the rigorous quantum field theory (QFT) derivation of the tensor Φ_ij(Ψ) and its numerical validation via Direct Numerical Simulation (DNS).

## Overview

The tensor Φ_ij(Ψ) emerges from quantum field theory in curved spacetime and provides a coupling between a coherent vacuum field Ψ and the classical Navier-Stokes equations. This work is based on:

- **Hadamard regularization** of the stress-energy tensor
- **DeWitt-Schwinger expansion** for renormalization
- **ADM projection** from 4D spacetime to 3D spatial slices

## Files

### 1. `derive_phi_tensor_qft_rigorous.py`

**Purpose**: Derives the tensor Φ_ij(Ψ) from first principles QFT.

**Key Features**:
- Constructs perturbed spacetime metric induced by fluid
- Computes Seeley-DeWitt coefficients (a₁, a₂, a₃) from heat kernel expansion
- Builds tensor: Φ_ij = α·∇_i∇_j Ψ + β·R_ij·Ψ + γ·δ_ij·□Ψ
- Derives coupling to Navier-Stokes: ∂_t u_i + u_j ∇_j u_i = -∇_i p + ν Δu_i + Φ_ij·u_j
- Analyzes resonance condition at f₀ = 141.7001 Hz
- Exports LaTeX and numerical summaries

**Usage**:
```bash
python derive_phi_tensor_qft_rigorous.py
```

**Outputs**:
- `Results/Phi_tensor_QFT.tex` - LaTeX formatted tensor expression
- `Results/Phi_tensor_numerical_summary.txt` - Numerical values of coefficients

**Key Results**:
```
Seeley-DeWitt coefficients:
  a₁ = 1.407239e-04
  a₂ = 3.518097e-05
  a₃ = -7.036193e-05

Fundamental frequency:
  f₀ = 141.7001 Hz
  ω₀ = 890.328 rad/s
  λ_Ψ ≈ 2115.68 km

Effective mass scale:
  m_Ψ ≈ 1.045e-48 kg

Coupling scale:
  |Φ_ij| ~ 1.123e-03
```

### 2. `validate_phi_coupling_DNS.py`

**Purpose**: Validates the Φ_ij coupling through Direct Numerical Simulation.

**Key Features**:
- Pseudo-spectral DNS solver for 3D Navier-Stokes
- Implements Φ_ij·u coupling term
- FFT-based resonance frequency detection
- Energy spectrum analysis
- Visualization of temporal evolution and spectral content

**Usage**:
```bash
python validate_phi_coupling_DNS.py
```

**Parameters** (can be modified in script):
- `N`: Grid resolution (default: 16³)
- `T_max`: Simulation time (default: 1.0 s)
- `dt`: Time step (default: 5e-4 s)
- `nu`: Kinematic viscosity (default: 1e-2)

**Outputs**:
- `Results/phi_coupling_validation.png` - Energy evolution and frequency spectrum
- Console output with detected vs. predicted frequency

**Example Output**:
```
🎯 Frecuencia dominante detectada: 1.00 Hz
   Frecuencia predicha: 141.70 Hz
   Error relativo: 99.29%
   
Note: Low resolution and short simulation time limit resonance detection.
      For accurate validation, increase N ≥ 64 and T_max ≥ 10.0.
```

### 3. `test_phi_tensor_qft.py`

**Purpose**: Test suite for QFT tensor derivation and DNS validation.

**Usage**:
```bash
python test_phi_tensor_qft.py
```

**Test Coverage**:
- PhiTensorCoupling class initialization and coefficient computation
- Ψ field computation and tensor coupling
- NavierStokesExtendedDNS solver initialization
- Energy computation and field projection
- Resonance frequency detection algorithms
- QFT derivation script execution and output validation

**Expected Result**:
```
----------------------------------------------------------------------
Ran 12 tests in 0.430s

OK
```

## Mathematical Framework

### Tensor Derivation

The tensor Φ_ij(Ψ) is derived from the renormalized stress-energy tensor in curved spacetime:

```
⟨T_μν(Ψ)⟩_ren = lim_{ε→0} [⟨T_μν(Ψ)⟩ - divergent terms]
```

Using Hadamard regularization and DeWitt-Schwinger expansion:

```
Φ_ij(Ψ) = α·∇_i∇_j Ψ + β·R_ij·Ψ + γ·δ_ij·□Ψ
```

where:
- **α = a₁ ln(μ²/m_Ψ²)**: Gradient coupling with renormalization scale dependence
- **β = a₂**: Ricci tensor coupling (spacetime curvature)
- **γ = a₃**: Trace coupling (d'Alembertian of Ψ)

### Modified Navier-Stokes

The extended Navier-Stokes equation becomes:

```
∂u/∂t + (u·∇)u = -∇p + ν∇²u + Φ_ij·u_j
```

### Resonance Condition

The coupling becomes macroscopically relevant when:
```
ω_fluid ≈ ω₀ = 2πf₀ = 890.328 rad/s
```

This occurs through constructive interference between:
- Turbulent vorticity modes
- Coherent vacuum field oscillations at f₀ = 141.7001 Hz

## Physical Interpretation

1. **Quantum-Classical Bridge**: Φ_ij(Ψ) provides a mechanism for quantum vacuum effects to influence classical fluid dynamics at macroscopic scales.

2. **Regularization Mechanism**: The tensor acts as a geometric damping term that prevents finite-time singularities in turbulent flows.

3. **Universal Frequency**: f₀ = 141.7001 Hz emerges as a fundamental scale of vacuum coherence, potentially observable in:
   - Turbulent fluid experiments
   - Neurophysiological signals (EEG)
   - Gravitational wave detectors (LIGO)

## Computational Validation Strategy

### Quick Test (Development)
```bash
python validate_phi_coupling_DNS.py  # N=16, T=1.0s
```
- Runtime: ~10 seconds
- Purpose: Verify code functionality
- Limitation: Cannot resolve f₀ resonance

### Standard Validation (Research)
```bash
# Modify in script: N=64, T_max=10.0, dt=1e-3
python validate_phi_coupling_DNS.py
```
- Runtime: ~5-10 minutes
- Purpose: Detect spectral features near f₀
- Resolution: Δf ≈ 0.1 Hz

### High-Fidelity Validation (Publication)
```bash
# Modify in script: N=128, T_max=50.0, dt=5e-4
python validate_phi_coupling_DNS.py
```
- Runtime: ~1-2 hours (HPC recommended)
- Purpose: Precise f₀ detection and amplitude measurement
- Resolution: Δf ≈ 0.02 Hz

## Dependencies

Required Python packages (see `requirements.txt`):
```
numpy>=1.21.0
scipy>=1.7.0
matplotlib>=3.5.0
sympy>=1.12
```

Install with:
```bash
pip install -r requirements.txt
```

## References

1. **Birrell, N.D., Davies, P.C.W.** (1982). *Quantum Fields in Curved Space*. Cambridge University Press.
   - Source for Seeley-DeWitt coefficients

2. **DeWitt, B.S.** (1965). "Dynamical Theory of Groups and Fields". *Relativity, Groups and Topology*.
   - Heat kernel expansion methodology

3. **Hadamard, J.** (1923). *Lectures on Cauchy's Problem in Linear Partial Differential Equations*.
   - Regularization technique

4. **Mota Burruezo, J.M.** (2025). "QCAL Framework: Quantum Coherence in Navier-Stokes Regularity". 
   - Φ_ij(Ψ) derivation and f₀ = 141.7001 Hz prediction

## Citation

If you use this code in your research, please cite the official Zenodo publications:

```bibtex
@software{phi_tensor_qft_2025,
  title = {QFT-Based Derivation of Φ_ij(Ψ) Tensor for Navier-Stokes Coupling},
  author = {Mota Burruezo, José Manuel},
  year = {2025},
  url = {https://github.com/motanova84/3D-Navier-Stokes},
  doi = {10.5281/zenodo.17488796},
  license = {CC-BY-4.0}
}

@article{mota_quantum_coherent_2024,
  title = {A Quantum-Coherent Regularization of 3D Navier–Stokes: Global Smoothness via Spectral Vacuum Coupling and Entropy-Lyapunov Control},
  author = {Mota Burruezo, José Manuel},
  year = {2024},
  doi = {10.5281/zenodo.17479481},
  url = {https://zenodo.org/records/17479481}
}
```

## License

- Code: MIT License
- Documentation: CC-BY-4.0
- Theory: Attribution required

## Author

José Manuel Mota Burruezo (JMMB Ψ✧∞³)

## Contact

For questions or collaboration:
- GitHub: [@motanova84](https://github.com/motanova84)
- Issues: [GitHub Issues](https://github.com/motanova84/3D-Navier-Stokes/issues)

---

**Status**: ✅ Implementation complete and tested
**Last Updated**: 2025-10-31
