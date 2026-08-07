# Mathematical Knowledge Base

Generated: 2025-10-30T23:24:46.415985

## Summary

- Total Equations: 692
- Total Constants: 7
- Total Theorems: 0
- Total Relationships: 0

## Constants

### ν
**Description:** Kinematic viscosity

**Typical Value:** 1e-3

**Category:** physical

---

### C_BKM
**Description:** Calderón-Zygmund operator norm / Besov constant

**Typical Value:** 2.0

**Category:** mathematical

---

### c_d
**Description:** Bernstein constant (d=3)

**Typical Value:** 0.5

**Category:** mathematical

---

### δ*
**Description:** Misalignment defect parameter

**Formula:** a²c₀²/(4π²)

**Typical Value:** 1/(4π²) ≈ 0.0253

**Category:** qcal

---

### c⋆
**Description:** Parabolic coercivity coefficient

**Typical Value:** 1/16

**Category:** mathematical

---

### C_str
**Description:** Vorticity stretching constant

**Typical Value:** 32

**Category:** mathematical

---

### C_CZ
**Description:** Calderón-Zygmund constant (optimized)

**Typical Value:** 1.5

**Category:** mathematical

---

## Equations

### Navier-Stokes
**Formula:** ∂u/∂t + (u·∇)u = -∇p + ν∆u + f

**Description:** 3D Navier-Stokes momentum equation

**Category:** fundamental

---

### Vorticity
**Formula:** ω = ∇ × u

**Description:** Vorticity definition

**Category:** fundamental

---

### BKM Criterion
**Formula:** ∫₀^T ‖ω(t)‖_{L∞} dt < ∞ ⇒ no blow-up

**Description:** Beale-Kato-Majda criterion for global regularity

**Category:** criterion

---

### Riccati Inequality
**Formula:** d/dt X(t) ≤ A - B X(t) log(e + βX(t))

**Description:** Dyadic Riccati inequality for vorticity control

**Category:** estimate

---

### CZ-Besov Estimate
**Formula:** ‖∇u‖_{L∞} ≤ C_CZ‖ω‖_{B⁰_{∞,1}}

**Description:** Calderón-Zygmund operator in Besov spaces

**Category:** estimate

---

### VERIFICATION_ROADMAP_7
**Formula:** - Replace pointwise misalignment with time average: δ̄₀(T) = (1/T)∫₀^T δ₀(t)dt

**Description:** From VERIFICATION_ROADMAP.md, line 7

**Category:** general

---

### VERIFICATION_ROADMAP_8
**Formula:** - Use critical Besov pair: ‖∇u‖_{L∞} ≤ C_CZ‖ω‖_{B⁰_{∞,1}}, ‖ω‖_{B⁰_{∞,1}} ≤ C_star‖ω‖_{L∞}

**Description:** From VERIFICATION_ROADMAP.md, line 8

**Category:** general

---

### VERIFICATION_ROADMAP_9
**Formula:** - Apply Bernstein lower bound: ‖∇ω‖_{L∞} ≥ c_Bern‖ω‖²_{L∞}

**Description:** From VERIFICATION_ROADMAP.md, line 9

**Category:** general

---

### VERIFICATION_ROADMAP_10
**Formula:** - If γ_avg := ν·c_Bern - (1-δ̄₀)C_CZ·C_star > 0, then BKM closes

**Description:** From VERIFICATION_ROADMAP.md, line 10

**Category:** criterion

---

### VERIFICATION_ROADMAP_13
**Formula:** - High-frequency parabolic dominance (j ≥ j_d)

**Description:** From VERIFICATION_ROADMAP.md, line 13

**Category:** general

---

### VERIFICATION_ROADMAP_14
**Formula:** - BGW-Osgood mechanism yields ∫₀^T ‖ω‖_{B⁰_{∞,1}} dt < ∞

**Description:** From VERIFICATION_ROADMAP.md, line 14

**Category:** general

---

### VERIFICATION_ROADMAP_15
**Formula:** - Critical Besov pair gives ∫₀^T ‖∇u‖_{L∞} dt < ∞

**Description:** From VERIFICATION_ROADMAP.md, line 15

**Category:** general

---

### VERIFICATION_ROADMAP_16
**Formula:** - Endpoint Serrin: u ∈ L^∞_t L³_x ⟹ global regularity

**Description:** From VERIFICATION_ROADMAP.md, line 16

**Category:** general

---

### VERIFICATION_ROADMAP_18
**Formula:** **Key Result**: Both routes are independent of (f₀, ε); global regularity is guaranteed unconditionally.

**Description:** From VERIFICATION_ROADMAP.md, line 18

**Category:** general

---

### VERIFICATION_ROADMAP_36
**Formula:** - [x] `delta_star_positive`: δ* > 0 for positive amplitude and phase gradient

**Description:** From VERIFICATION_ROADMAP.md, line 36

**Category:** general

---

### VERIFICATION_ROADMAP_37
**Formula:** - [x] `positive_damping_condition`: γ > 0 ⟺ δ* > 1 - ν/512

**Description:** From VERIFICATION_ROADMAP.md, line 37

**Category:** physical

---

### VERIFICATION_ROADMAP_41
**Formula:** 2. Prove positivity of δ*

**Description:** From VERIFICATION_ROADMAP.md, line 41

**Category:** general

---

### VERIFICATION_ROADMAP_42
**Formula:** 3. Establish γ > 0 condition

**Description:** From VERIFICATION_ROADMAP.md, line 42

**Category:** general

---

### VERIFICATION_ROADMAP_56
**Formula:** - [x] `dyadic_riccati_inequality`: For j ≥ j_d, coefficient < 0

**Description:** From VERIFICATION_ROADMAP.md, line 56

**Category:** estimate

---

### VERIFICATION_ROADMAP_57
**Formula:** - [x] `dyadic_vorticity_evolution`: Vorticity decays for j ≥ j_d

**Description:** From VERIFICATION_ROADMAP.md, line 57

**Category:** general

---

### VERIFICATION_ROADMAP_65
**Formula:** - [x] Connection to Parabolic-critical condition (ν·c_star > C_str)

**Description:** From VERIFICATION_ROADMAP.md, line 65

**Category:** physical

---

### VERIFICATION_ROADMAP_71
**Formula:** - [x] Time-averaged misalignment: δ̄₀(T) := (1/T)∫₀^T δ₀(t)dt

**Description:** From VERIFICATION_ROADMAP.md, line 71

**Category:** general

---

### VERIFICATION_ROADMAP_72
**Formula:** - [ ] Theorem 13.4 Revised: Persistent misalignment δ* = a²c₀²/4π²

**Description:** From VERIFICATION_ROADMAP.md, line 72

**Category:** general

---

### VERIFICATION_ROADMAP_74
**Formula:** - [ ] Uniform bound δ(t) ≥ δ* for all t > 0

**Description:** From VERIFICATION_ROADMAP.md, line 74

**Category:** general

---

### VERIFICATION_ROADMAP_80
**Formula:** - [x] Critical Besov pair: ‖∇u‖_{L∞} ≤ C_CZ‖ω‖_{B⁰_{∞,1}}, ‖ω‖_{B⁰_{∞,1}} ≤ C_star‖ω‖_{L∞}

**Description:** From VERIFICATION_ROADMAP.md, line 80

**Category:** general

---

### VERIFICATION_ROADMAP_93
**Formula:** - [x] Besov to L∞ embedding (Kozono-Taniuchi)

**Description:** From VERIFICATION_ROADMAP.md, line 93

**Category:** general

---

### VERIFICATION_ROADMAP_103
**Formula:** (u₀ : H^m ℝ³) (h_div : ∇·u₀ = 0) (h_regular : u₀ ∈ B¹_{∞,1})

**Description:** From VERIFICATION_ROADMAP.md, line 103

**Category:** general

---

### VERIFICATION_ROADMAP_104
**Formula:** (ν : ℝ) (h_ν : ν > 0) (f : L¹_t H^{m-1}) :

**Description:** From VERIFICATION_ROADMAP.md, line 104

**Category:** physical

---

### VERIFICATION_ROADMAP_106
**Formula:** IsSolution u u₀ f ν ∧

**Description:** From VERIFICATION_ROADMAP.md, line 106

**Category:** physical

---

### VERIFICATION_ROADMAP_107
**Formula:** u ∈ C^∞(ℝ³ × (0,∞))

**Description:** From VERIFICATION_ROADMAP.md, line 107

**Category:** general

---

### VERIFICATION_ROADMAP_138
**Formula:** - `compute_besov_norm()`: B⁰_{∞,1} norm

**Description:** From VERIFICATION_ROADMAP.md, line 138

**Category:** general

---

### VERIFICATION_ROADMAP_139
**Formula:** - `compute_misalignment_defect()`: δ(t) calculation

**Description:** From VERIFICATION_ROADMAP.md, line 139

**Category:** general

---

### VERIFICATION_ROADMAP_140
**Formula:** - `compute_riccati_coefficient()`: γ(t) monitoring

**Description:** From VERIFICATION_ROADMAP.md, line 140

**Category:** estimate

---

### VERIFICATION_ROADMAP_151
**Formula:** - Real-time δ(t) computation

**Description:** From VERIFICATION_ROADMAP.md, line 151

**Category:** general

---

### VERIFICATION_ROADMAP_153
**Formula:** - Convergence to δ* verification

**Description:** From VERIFICATION_ROADMAP.md, line 153

**Category:** general

---

### VERIFICATION_ROADMAP_156
**Formula:** - Riccati coefficient γ(t) tracking

**Description:** From VERIFICATION_ROADMAP.md, line 156

**Category:** estimate

---

### VERIFICATION_ROADMAP_163
**Formula:** - Parameter sweep f₀ ∈ [100, 1000] Hz

**Description:** From VERIFICATION_ROADMAP.md, line 163

**Category:** general

---

### VERIFICATION_ROADMAP_164
**Formula:** - Convergence analysis for ε → 0, f₀ → ∞

**Description:** From VERIFICATION_ROADMAP.md, line 164

**Category:** general

---

### VERIFICATION_ROADMAP_168
**Formula:** - Besov norm B⁰_{∞,1} computation

**Description:** From VERIFICATION_ROADMAP.md, line 168

**Category:** general

---

### VERIFICATION_ROADMAP_190
**Formula:** - γ(t) time series plots

**Description:** From VERIFICATION_ROADMAP.md, line 190

**Category:** general

---

### VERIFICATION_ROADMAP_246
**Formula:** - δ* convergence: |δ_final - δ*_theoretical| < 0.01

**Description:** From VERIFICATION_ROADMAP.md, line 246

**Category:** general

---

### VERIFICATION_ROADMAP_247
**Formula:** - Positive damping: γ_final > 0

**Description:** From VERIFICATION_ROADMAP.md, line 247

**Category:** general

---

### VERIFICATION_ROADMAP_248
**Formula:** - BKM integrability: ∫‖ω‖_{L∞} dt < ∞

**Description:** From VERIFICATION_ROADMAP.md, line 248

**Category:** criterion

---

### VERIFICATION_ROADMAP_249
**Formula:** - Besov boundedness: sup_t ‖ω(t)‖_{B⁰_{∞,1}} < ∞

**Description:** From VERIFICATION_ROADMAP.md, line 249

**Category:** general

---

### VERIFICATION_ROADMAP_250
**Formula:** - Uniform verification across f₀ ∈ [100, 1000] Hz

**Description:** From VERIFICATION_ROADMAP.md, line 250

**Category:** general

---

### CLAY_PROOF_9
**Formula:** 1. **Dual-Limit Regularization Framework**: Construction of regularized solutions with explicit parameter scaling (ε, f₀)

**Description:** From CLAY_PROOF.md, line 9

**Category:** general

---

### CLAY_PROOF_10
**Formula:** 2. **QCAL (Quasi-Critical Alignment Layer)**: Persistent misalignment defect δ* > 0 that prevents finite-time blow-up

**Description:** From CLAY_PROOF.md, line 10

**Category:** general

---

### CLAY_PROOF_11
**Formula:** 3. **Unconditional Riccati Damping**: Positive damping coefficient γ > 0 ensures Besov norm decay

**Description:** From CLAY_PROOF.md, line 11

**Category:** estimate

---

### CLAY_PROOF_12
**Formula:** 4. **BKM Criterion Verification**: Integrability of vorticity L∞ norm guarantees global smoothness

**Description:** From CLAY_PROOF.md, line 12

**Category:** criterion

---

### CLAY_PROOF_17
**Formula:** For any initial data u₀ ∈ B¹_{∞,1}(ℝ³) with ∇·u₀ = 0, and external force f ∈ L¹_t H^{m-1}, there exists a unique global smooth solution u ∈ C^∞(ℝ³ × (0,∞)) to the 3D Navier-Stokes equations.

**Description:** From CLAY_PROOF.md, line 17

**Category:** fundamental

---

### CLAY_PROOF_20
**Formula:** 1. **Lemma L1** (Absolute CZ-Besov): ‖S(u)‖_{L∞} ≤ C_d ‖ω‖_{B⁰_{∞,1}} with C_d = 2 (universal)

**Description:** From CLAY_PROOF.md, line 20

**Category:** general

---

### CLAY_PROOF_21
**Formula:** 2. **Lemma L2** (ε-free NBB Coercivity):

**Description:** From CLAY_PROOF.md, line 21

**Category:** general

---

### CLAY_PROOF_23
**Formula:** Σ_j 2^{2j} ‖Δ_j ω‖²_{L²} ≥ c_star ‖ω‖²_{B⁰_{∞,1}} - C_star ‖ω‖²_{L²}

**Description:** From CLAY_PROOF.md, line 23

**Category:** general

---

### CLAY_PROOF_25
**Formula:** with c_star universal (depends only on ν, d)

**Description:** From CLAY_PROOF.md, line 25

**Category:** physical

---

### CLAY_PROOF_26
**Formula:** 3. Derive Global Riccati: d/dt‖ω‖_{B⁰_{∞,1}} ≤ -γ‖ω‖²_{B⁰_{∞,1}} + K with **γ > 0 universal**

**Description:** From CLAY_PROOF.md, line 26

**Category:** estimate

---

### CLAY_PROOF_27
**Formula:** 4. Integrate to show ∫₀^∞ ‖ω(t)‖_{B⁰_{∞,1}} dt < ∞

**Description:** From CLAY_PROOF.md, line 27

**Category:** general

---

### CLAY_PROOF_28
**Formula:** 5. Apply BKM criterion: ∫₀^∞ ‖ω(t)‖_{L∞} dt < ∞ implies smoothness

**Description:** From CLAY_PROOF.md, line 28

**Category:** criterion

---

### CLAY_PROOF_30
**Formula:** **Critical Achievement**: γ > 0 with constants independent of regularization parameters f₀, ε, A.

**Description:** From CLAY_PROOF.md, line 30

**Category:** general

---

### CLAY_PROOF_36
**Formula:** | C_d | 2.0 | Calderón-Zygmund/Besov (Lemma L1) | Dimension only |

**Description:** From CLAY_PROOF.md, line 36

**Category:** general

---

### CLAY_PROOF_37
**Formula:** | c_star | ≈32,543 (ν=10⁻³) | Parabolic coercivity (Lemma L2) | ν, d only |

**Description:** From CLAY_PROOF.md, line 37

**Category:** physical

---

### CLAY_PROOF_38
**Formula:** | C_star | 4.0 | L² control constant | Dimension only |

**Description:** From CLAY_PROOF.md, line 38

**Category:** general

---

### CLAY_PROOF_39
**Formula:** | C_str | 32.0 | Vorticity stretching constant | Dimension only |

**Description:** From CLAY_PROOF.md, line 39

**Category:** general

---

### CLAY_PROOF_40
**Formula:** | δ* | 1/(4π²) ≈ 0.0253 | Misalignment defect | Universal (physical) |

**Description:** From CLAY_PROOF.md, line 40

**Category:** general

---

### CLAY_PROOF_44
**Formula:** γ = ν·c_star - (1 - δ*/2)·C_str

**Description:** From CLAY_PROOF.md, line 44

**Category:** physical

---

### CLAY_PROOF_47
**Formula:** For any initial data u₀ ∈ B¹_{∞,1}(ℝ³) with ∇·u₀ = 0, and external force f ∈ L¹_t H^{m-1}, there exists a unique global smooth solution u ∈ C^∞(ℝ³ × (0,∞)) to the 3D Navier-Stokes equations.

**Description:** From CLAY_PROOF.md, line 47

**Category:** fundamental

---

### CLAY_PROOF_50
**Formula:** 1. Construct dual-limit family {u_{ε,f₀}} with scaling:

**Description:** From CLAY_PROOF.md, line 50

**Category:** general

---

### CLAY_PROOF_51
**Formula:** - ε = λ·f₀^(-α), α > 1

**Description:** From CLAY_PROOF.md, line 51

**Category:** general

---

### CLAY_PROOF_52
**Formula:** - Amplitude A = a·f₀

**Description:** From CLAY_PROOF.md, line 52

**Category:** general

---

### CLAY_PROOF_53
**Formula:** 2. Establish critical Besov pair: ‖∇u‖_{L∞} ≤ C_CZ‖ω‖_{B⁰_{∞,1}}, ‖ω‖_{B⁰_{∞,1}} ≤ C_star‖ω‖_{L∞}

**Description:** From CLAY_PROOF.md, line 53

**Category:** general

---

### CLAY_PROOF_60
**Formula:** - Define time-averaged misalignment: δ̄₀(T) := (1/T)∫₀^T δ₀(t)dt

**Description:** From CLAY_PROOF.md, line 60

**Category:** general

---

### CLAY_PROOF_61
**Formula:** - With Bernstein lower bound ‖∇ω‖_{L∞} ≥ c_Bern‖ω‖²_{L∞}, obtain:

**Description:** From CLAY_PROOF.md, line 61

**Category:** general

---

### CLAY_PROOF_62
**Formula:** - γ_avg := ν·c_Bern - (1-δ̄₀)C_CZ·C_star

**Description:** From CLAY_PROOF.md, line 62

**Category:** physical

---

### CLAY_PROOF_63
**Formula:** - If γ_avg > 0, then W(t) ≤ W(0)/(1+γ_avg·t·W(0))

**Description:** From CLAY_PROOF.md, line 63

**Category:** general

---

### CLAY_PROOF_64
**Formula:** - Yields ∫₀^∞ ‖ω‖_{L∞} dt < ∞ (BKM closure)

**Description:** From CLAY_PROOF.md, line 64

**Category:** criterion

---

### CLAY_PROOF_67
**Formula:** - Independently of γ_avg sign, high-frequency sector j ≥ j_d is parabolically dominated

**Description:** From CLAY_PROOF.md, line 67

**Category:** general

---

### CLAY_PROOF_68
**Formula:** - BGW inequality + Osgood lemma yield ∫₀^T ‖ω(t)‖_{B⁰_{∞,1}} dt < ∞

**Description:** From CLAY_PROOF.md, line 68

**Category:** estimate

---

### CLAY_PROOF_69
**Formula:** - Critical Besov pair gives ∫₀^T ‖∇u‖_{L∞} dt < ∞

**Description:** From CLAY_PROOF.md, line 69

**Category:** general

---

### CLAY_PROOF_70
**Formula:** - Endpoint Serrin (u ∈ L^∞_t L³_x) implies smoothness

**Description:** From CLAY_PROOF.md, line 70

**Category:** general

---

### CLAY_PROOF_72
**Formula:** **Key Result**: Both routes are independent of (f₀, ε); constants depend only on (d=3, ν, ‖u₀‖_{L²}, ‖f‖).

**Description:** From CLAY_PROOF.md, line 72

**Category:** physical

---

### CLAY_PROOF_74
**Formula:** **For ν = 10⁻³**:

**Description:** From CLAY_PROOF.md, line 74

**Category:** physical

---

### CLAY_PROOF_76
**Formula:** - γ ≈ 0.948 > 0 ✓ **UNCONDITIONAL**

**Description:** From CLAY_PROOF.md, line 76

**Category:** general

---

### CLAY_PROOF_82
**Formula:** | C_str | 32 | Vorticity stretching constant |

**Description:** From CLAY_PROOF.md, line 82

**Category:** general

---

### CLAY_PROOF_83
**Formula:** | C_CZ | 2 | Calderón-Zygmund constant (critical Besov) |

**Description:** From CLAY_PROOF.md, line 83

**Category:** general

---

### CLAY_PROOF_84
**Formula:** | C_star | 1 | Besov embedding constant |

**Description:** From CLAY_PROOF.md, line 84

**Category:** general

---

### CLAY_PROOF_88
**Formula:** **Note**: C_BKM = C_CZ = 2 (retained for backward compatibility)

**Description:** From CLAY_PROOF.md, line 88

**Category:** criterion

---

### CLAY_PROOF_94
**Formula:** | a | 7.0 | Amplitude (corrected for δ* > 0.998) |

**Description:** From CLAY_PROOF.md, line 94

**Category:** general

---

### CLAY_PROOF_97
**Formula:** | δ* | 0.0253 | Misalignment defect (a²c₀²/4π²) |

**Description:** From CLAY_PROOF.md, line 97

**Category:** general

---

### CLAY_PROOF_103
**Formula:** γ = ν·c_star - (1 - δ*/2)·C_str > 0

**Description:** From CLAY_PROOF.md, line 103

**Category:** physical

---

### CLAY_PROOF_106
**Formula:** With universal constants (independent of f₀, ε, A):

**Description:** From CLAY_PROOF.md, line 106

**Category:** general

---

### CLAY_PROOF_107
**Formula:** - ν = 10⁻³ (kinematic viscosity)

**Description:** From CLAY_PROOF.md, line 107

**Category:** physical

---

### CLAY_PROOF_109
**Formula:** - C_str = 32 (dimension-dependent)

**Description:** From CLAY_PROOF.md, line 109

**Category:** general

---

### CLAY_PROOF_110
**Formula:** - δ* = 1/(4π²) ≈ 0.0253 (physically achievable)

**Description:** From CLAY_PROOF.md, line 110

**Category:** general

---

### CLAY_PROOF_112
**Formula:** **Result**: γ ≈ 0.948 > 0 ✓

**Description:** From CLAY_PROOF.md, line 112

**Category:** general

---

### CLAY_PROOF_115
**Formula:** 1. c_star depends only on ν and d

**Description:** From CLAY_PROOF.md, line 115

**Category:** physical

---

### CLAY_PROOF_116
**Formula:** 2. δ* is fixed at physical value 1/(4π²)

**Description:** From CLAY_PROOF.md, line 116

**Category:** general

---

### CLAY_PROOF_117
**Formula:** 3. No dependence on regularization f₀, ε, or A

**Description:** From CLAY_PROOF.md, line 117

**Category:** general

---

### CLAY_PROOF_122
**Formula:** γ_avg = ν·c_Bern - (1-δ̄₀)·C_CZ·C_star > 0

**Description:** From CLAY_PROOF.md, line 122

**Category:** physical

---

### CLAY_PROOF_125
**Formula:** For ν = 10⁻³, C_CZ = 2, C_star = 1, c_Bern = 0.1:

**Description:** From CLAY_PROOF.md, line 125

**Category:** physical

---

### CLAY_PROOF_126
**Formula:** - γ_avg > 0 requires δ̄₀ > 1 - ν·c_Bern/(C_CZ·C_star) = 1 - 0.00005 = 0.99995

**Description:** From CLAY_PROOF.md, line 126

**Category:** physical

---

### CLAY_PROOF_130
**Formula:** - Requires only parabolic coercivity at high frequencies (j ≥ j_d)

**Description:** From CLAY_PROOF.md, line 130

**Category:** general

---

### CLAY_PROOF_131
**Formula:** - Independent of δ̄₀ and (f₀, ε)

**Description:** From CLAY_PROOF.md, line 131

**Category:** general

---

### CLAY_PROOF_132
**Formula:** - Guarantees ∫₀^T ‖ω‖_{B⁰_{∞,1}} dt < ∞ via Osgood lemma

**Description:** From CLAY_PROOF.md, line 132

**Category:** general

---

### CLAY_PROOF_148
**Formula:** - Misalignment defect δ(t)

**Description:** From CLAY_PROOF.md, line 148

**Category:** general

---

### CLAY_PROOF_149
**Formula:** - Besov norm B⁰_{∞,1}

**Description:** From CLAY_PROOF.md, line 149

**Category:** general

---

### CLAY_PROOF_150
**Formula:** - Riccati coefficient γ(t)

**Description:** From CLAY_PROOF.md, line 150

**Category:** estimate

---

### CLAY_PROOF_151
**Formula:** - BKM integral ∫‖ω‖_{L∞} dt

**Description:** From CLAY_PROOF.md, line 151

**Category:** criterion

---

### CLAY_PROOF_154
**Formula:** - f₀ ∈ [100, 1000] Hz convergence tests

**Description:** From CLAY_PROOF.md, line 154

**Category:** general

---

### CLAY_PROOF_155
**Formula:** - Reynolds number Re ∈ [100, 1000]

**Description:** From CLAY_PROOF.md, line 155

**Category:** physical

---

### CLAY_PROOF_156
**Formula:** - Scaling exponent α ∈ [1.5, 2.5]

**Description:** From CLAY_PROOF.md, line 156

**Category:** general

---

### UNIFIED_BKM_THEORY_10
**Formula:** Let $u$ solve 3D Navier-Stokes with initial data $u_0 \in H^m$, $m \geq 3$. Assume the **dual-limit scaling**: $\varepsilon = \lambda f_0^{-\alpha}$, $A = a f_0$ with $\alpha > 1$.

**Description:** From UNIFIED_BKM_THEORY.md, line 10

**Category:** fundamental

---

### UNIFIED_BKM_THEORY_14
**Formula:** 1. **Calderón-Zygmund in Besov**: $C_{CZ} > 0$ such that

**Description:** From UNIFIED_BKM_THEORY.md, line 14

**Category:** general

---

### UNIFIED_BKM_THEORY_17
**Formula:** 2. **Besov-Supremum embedding**: $C_* > 0$ such that

**Description:** From UNIFIED_BKM_THEORY.md, line 17

**Category:** general

---

### UNIFIED_BKM_THEORY_20
**Formula:** 3. **Bernstein constant**: $c_B > 0$ such that

**Description:** From UNIFIED_BKM_THEORY.md, line 20

**Category:** general

---

### UNIFIED_BKM_THEORY_23
**Formula:** 4. **Persistent misalignment**: $\delta^* = \frac{a^2 c_0^2}{4\pi^2} > 0$

**Description:** From UNIFIED_BKM_THEORY.md, line 23

**Category:** general

---

### UNIFIED_BKM_THEORY_26
**Formula:** $$\Delta := \nu c_B - (1 - \delta^*) C_{CZ} C_* (1 + \log^+ M) > 0$$

**Description:** From UNIFIED_BKM_THEORY.md, line 26

**Category:** general

---

### UNIFIED_BKM_THEORY_28
**Formula:** where $M = \sup_{t} \|u(t)\|_{H^m}$, then:

**Description:** From UNIFIED_BKM_THEORY.md, line 28

**Category:** general

---

### UNIFIED_BKM_THEORY_29
**Formula:** $$\int_0^\infty \|\omega(t)\|_{L^\infty} dt < \infty \quad \Rightarrow \quad u \in C^\infty(\mathbb{R}^3 \times (0,\infty))$$

**Description:** From UNIFIED_BKM_THEORY.md, line 29

**Category:** general

---

### UNIFIED_BKM_THEORY_36
**Formula:** $$\frac{d}{dt} \|\omega\|_{L^\infty} \leq \|S\|_{L^\infty} \|\omega\|_{L^\infty} - \nu \|\nabla \omega\|_{L^\infty}$$

**Description:** From UNIFIED_BKM_THEORY.md, line 36

**Category:** general

---

### UNIFIED_BKM_THEORY_45
**Formula:** $$\frac{d}{dt} \|\omega\|_{L^\infty} \leq \left[(1 - \delta^*) C_{CZ} C_* (1 + \log^+ M) - \nu c_B\right] \|\omega\|_{L^\infty}^2$$

**Description:** From UNIFIED_BKM_THEORY.md, line 45

**Category:** general

---

### UNIFIED_BKM_THEORY_49
**Formula:** When $\Delta > 0$, we have:

**Description:** From UNIFIED_BKM_THEORY.md, line 49

**Category:** general

---

### UNIFIED_BKM_THEORY_50
**Formula:** $$\frac{d}{dt} \|\omega\|_{L^\infty} \leq -\Delta \|\omega\|_{L^\infty}^2$$

**Description:** From UNIFIED_BKM_THEORY.md, line 50

**Category:** general

---

### UNIFIED_BKM_THEORY_53
**Formula:** $$\|\omega(t)\|_{L^\infty} \leq \frac{\|\omega_0\|_{L^\infty}}{1 + \Delta t \|\omega_0\|_{L^\infty}}$$

**Description:** From UNIFIED_BKM_THEORY.md, line 53

**Category:** general

---

### UNIFIED_BKM_THEORY_56
**Formula:** $$\int_0^\infty \|\omega(t)\|_{L^\infty} dt \leq \frac{1}{\Delta} \log(1 + \Delta T \|\omega_0\|_{L^\infty}) < \infty$$

**Description:** From UNIFIED_BKM_THEORY.md, line 56

**Category:** general

---

### UNIFIED_BKM_THEORY_67
**Formula:** $$\frac{d}{dt} \|\omega\|_{L^\infty} \leq -\Delta \|\omega\|_{L^\infty}^2$$

**Description:** From UNIFIED_BKM_THEORY.md, line 67

**Category:** general

---

### UNIFIED_BKM_THEORY_81
**Formula:** $$\|\omega(t)\|_{B^0_{\infty,1}} \leq C_1 + C_2 \int_0^t (t-s)^{-1/2} \|\omega(s)\|_{B^0_{\infty,1}}^2 ds$$

**Description:** From UNIFIED_BKM_THEORY.md, line 81

**Category:** general

---

### UNIFIED_BKM_THEORY_95
**Formula:** $$\frac{dE}{dt} = -\nu E + C E^{3/2} (1 - \delta^*)$$

**Description:** From UNIFIED_BKM_THEORY.md, line 95

**Category:** general

---

### UNIFIED_BKM_THEORY_110
**Formula:** $$\text{Maximize } \Delta(a, \alpha) = \nu c_B - (1 - \tfrac{a^2 c_0^2}{4\pi^2}) C_{CZ} C_* (1 + \log^+ M)$$

**Description:** From UNIFIED_BKM_THEORY.md, line 110

**Category:** general

---

### UNIFIED_BKM_THEORY_112
**Formula:** Subject to forcing vanishing: $\|\varepsilon \nabla \Phi\| = \lambda a \|\nabla \phi\| f_0^{1-\alpha} \to 0$

**Description:** From UNIFIED_BKM_THEORY.md, line 112

**Category:** general

---

### UNIFIED_BKM_THEORY_117
**Formula:** - **Optimal α**: 1.5

**Description:** From UNIFIED_BKM_THEORY.md, line 117

**Category:** general

---

### UNIFIED_BKM_THEORY_119
**Formula:** - **Optimal δ***: 2.533

**Description:** From UNIFIED_BKM_THEORY.md, line 119

**Category:** general

---

### UNIFIED_BKM_THEORY_123
**Formula:** - Damping condition Δ > 0 holds uniformly across f₀ ∈ [100, 10000]

**Description:** From UNIFIED_BKM_THEORY.md, line 123

**Category:** general

---

### UNIFIED_BKM_THEORY_125
**Formula:** - BKM integral: 0.623 < ∞

**Description:** From UNIFIED_BKM_THEORY.md, line 125

**Category:** criterion

---

### UNIFIED_BKM_THEORY_133
**Formula:** | ν | 10⁻³ | Kinematic viscosity |

**Description:** From UNIFIED_BKM_THEORY.md, line 133

**Category:** physical

---

### UNIFIED_BKM_THEORY_135
**Formula:** | C_CZ | 1.5 | Calderón-Zygmund in Besov |

**Description:** From UNIFIED_BKM_THEORY.md, line 135

**Category:** general

---

### UNIFIED_BKM_THEORY_144
**Formula:** | α | 1.5-2.0 | Scaling exponent |

**Description:** From UNIFIED_BKM_THEORY.md, line 144

**Category:** general

---

### UNIFIED_BKM_THEORY_149
**Formula:** With optimal parameters (a=10.0):

**Description:** From UNIFIED_BKM_THEORY.md, line 149

**Category:** general

---

### UNIFIED_BKM_THEORY_150
**Formula:** - **Misalignment defect**: δ* = 2.533

**Description:** From UNIFIED_BKM_THEORY.md, line 150

**Category:** general

---

### UNIFIED_BKM_THEORY_151
**Formula:** - **Damping coefficient**: Δ = 15.495

**Description:** From UNIFIED_BKM_THEORY.md, line 151

**Category:** general

---

### UNIFIED_BKM_THEORY_152
**Formula:** - **BKM integral**: ∫₀^∞ ‖ω(t)‖_∞ dt = 0.623 < ∞

**Description:** From UNIFIED_BKM_THEORY.md, line 152

**Category:** criterion

---

### UNIFIED_BKM_THEORY_162
**Formula:** params = UnifiedBKMConstants(

**Description:** From UNIFIED_BKM_THEORY.md, line 162

**Category:** criterion

---

### UNIFIED_BKM_THEORY_163
**Formula:** ν=1e-3,

**Description:** From UNIFIED_BKM_THEORY.md, line 163

**Category:** physical

---

### UNIFIED_BKM_THEORY_164
**Formula:** c_B=0.15,

**Description:** From UNIFIED_BKM_THEORY.md, line 164

**Category:** general

---

### UNIFIED_BKM_THEORY_165
**Formula:** C_CZ=1.5,

**Description:** From UNIFIED_BKM_THEORY.md, line 165

**Category:** general

---

### UNIFIED_BKM_THEORY_166
**Formula:** C_star=1.2,

**Description:** From UNIFIED_BKM_THEORY.md, line 166

**Category:** general

---

### UNIFIED_BKM_THEORY_167
**Formula:** a=10.0,  # Optimal amplitude

**Description:** From UNIFIED_BKM_THEORY.md, line 167

**Category:** general

---

### UNIFIED_BKM_THEORY_168
**Formula:** c_0=1.0,

**Description:** From UNIFIED_BKM_THEORY.md, line 168

**Category:** general

---

### UNIFIED_BKM_THEORY_169
**Formula:** α=2.0

**Description:** From UNIFIED_BKM_THEORY.md, line 169

**Category:** general

---

### UNIFIED_BKM_THEORY_173
**Formula:** results = unified_bkm_verification(

**Description:** From UNIFIED_BKM_THEORY.md, line 173

**Category:** criterion

---

### UNIFIED_BKM_THEORY_175
**Formula:** M=100.0,      # H^m bound

**Description:** From UNIFIED_BKM_THEORY.md, line 175

**Category:** general

---

### UNIFIED_BKM_THEORY_176
**Formula:** ω_0=10.0,     # Initial vorticity

**Description:** From UNIFIED_BKM_THEORY.md, line 176

**Category:** general

---

### UNIFIED_BKM_THEORY_177
**Formula:** verbose=True

**Description:** From UNIFIED_BKM_THEORY.md, line 177

**Category:** general

---

### UNIFIED_BKM_THEORY_191
**Formula:** optimal = compute_optimal_dual_scaling(

**Description:** From UNIFIED_BKM_THEORY.md, line 191

**Category:** general

---

### UNIFIED_BKM_THEORY_192
**Formula:** ν=1e-3,

**Description:** From UNIFIED_BKM_THEORY.md, line 192

**Category:** physical

---

### UNIFIED_BKM_THEORY_193
**Formula:** c_B=0.15,

**Description:** From UNIFIED_BKM_THEORY.md, line 193

**Category:** general

---

### UNIFIED_BKM_THEORY_194
**Formula:** C_CZ=1.5,

**Description:** From UNIFIED_BKM_THEORY.md, line 194

**Category:** general

---

### UNIFIED_BKM_THEORY_195
**Formula:** C_star=1.2,

**Description:** From UNIFIED_BKM_THEORY.md, line 195

**Category:** general

---

### UNIFIED_BKM_THEORY_196
**Formula:** M=100.0

**Description:** From UNIFIED_BKM_THEORY.md, line 196

**Category:** general

---

### UNIFIED_BKM_THEORY_199
**Formula:** print(f"Optimal a = {optimal['optimal_a']:.4f}")

**Description:** From UNIFIED_BKM_THEORY.md, line 199

**Category:** general

---

### UNIFIED_BKM_THEORY_200
**Formula:** print(f"Optimal δ* = {optimal['optimal_δ_star']:.6f}")

**Description:** From UNIFIED_BKM_THEORY.md, line 200

**Category:** general

---

### UNIFIED_BKM_THEORY_201
**Formula:** print(f"Maximum damping = {optimal['max_damping']:.6f}")

**Description:** From UNIFIED_BKM_THEORY.md, line 201

**Category:** general

---

### UNIFIED_BKM_THEORY_210
**Formula:** results = unified_validation_sweep(

**Description:** From UNIFIED_BKM_THEORY.md, line 210

**Category:** general

---

### UNIFIED_BKM_THEORY_211
**Formula:** f0_range=[100, 500, 1000, 5000, 10000],

**Description:** From UNIFIED_BKM_THEORY.md, line 211

**Category:** general

---

### UNIFIED_BKM_THEORY_212
**Formula:** α_values=[1.5, 2.0, 2.5, 3.0],

**Description:** From UNIFIED_BKM_THEORY.md, line 212

**Category:** general

---

### UNIFIED_BKM_THEORY_213
**Formula:** a_values=[0.5, 1.0, 2.0, 5.0, 7.0, 10.0],

**Description:** From UNIFIED_BKM_THEORY.md, line 213

**Category:** general

---

### UNIFIED_BKM_THEORY_214
**Formula:** verbose=True

**Description:** From UNIFIED_BKM_THEORY.md, line 214

**Category:** general

---

### UNIFIED_BKM_THEORY_227
**Formula:** - f₀ ∈ [100, 10000] Hz

**Description:** From UNIFIED_BKM_THEORY.md, line 227

**Category:** general

---

### UNIFIED_BKM_THEORY_228
**Formula:** - α ∈ [1.5, 3.0]

**Description:** From UNIFIED_BKM_THEORY.md, line 228

**Category:** general

---

### UNIFIED_BKM_THEORY_229
**Formula:** - a ∈ [0.5, 10.0]

**Description:** From UNIFIED_BKM_THEORY.md, line 229

**Category:** general

---

### UNIFIED_BKM_THEORY_233
**Formula:** - Measure constants: C_CZ, C_*, c_B, δ*

**Description:** From UNIFIED_BKM_THEORY.md, line 233

**Category:** general

---

### UNIFIED_BKM_THEORY_234
**Formula:** - Calculate damping: Δ(f₀; a, α)

**Description:** From UNIFIED_BKM_THEORY.md, line 234

**Category:** general

---

### UNIFIED_BKM_THEORY_237
**Formula:** - (a*, α*) = argmax min_{f₀} Δ(f₀; a, α)

**Description:** From UNIFIED_BKM_THEORY.md, line 237

**Category:** general

---

### UNIFIED_BKM_THEORY_240
**Formula:** - Δ(a*, α*) > 0 uniformly in f₀

**Description:** From UNIFIED_BKM_THEORY.md, line 240

**Category:** general

---

### UNIFIED_BKM_THEORY_242
**Formula:** - BKM integral < ∞

**Description:** From UNIFIED_BKM_THEORY.md, line 242

**Category:** criterion

---

### UNIFIED_BKM_THEORY_262
**Formula:** 1. ✅ Damping positive with optimal parameters (a=10.0)

**Description:** From UNIFIED_BKM_THEORY.md, line 262

**Category:** general

---

### UNIFIED_BKM_THEORY_263
**Formula:** 2. ✅ Damping negative with suboptimal parameters (a=2.45)

**Description:** From UNIFIED_BKM_THEORY.md, line 263

**Category:** general

---

### UNIFIED_BKM_THEORY_264
**Formula:** 3. ✅ Riccati evolution converges with Δ > 0

**Description:** From UNIFIED_BKM_THEORY.md, line 264

**Category:** estimate

---

### UNIFIED_BKM_THEORY_276
**Formula:** 2. **Dual scaling**: Rigorous treatment of ε → 0, f₀ → ∞ limit

**Description:** From UNIFIED_BKM_THEORY.md, line 276

**Category:** general

---

### UNIFIED_BKM_THEORY_317
**Formula:** 4. **Refined constants**: Improve estimates of C_CZ, C_*, c_B

**Description:** From UNIFIED_BKM_THEORY.md, line 317

**Category:** estimate

---

### README_8
**Formula:** 3. **Análisis de δ***: Cuantificación del defecto de desalineamiento

**Description:** From README.md, line 8

**Category:** general

---

### README_23
**Formula:** - Análisis δ* (70%)

**Description:** From README.md, line 23

**Category:** general

---

### README_47
**Formula:** - Escala dual límite: ε = λf₀^(-α), A = af₀, α > 1

**Description:** From README.md, line 47

**Category:** general

---

### README_48
**Formula:** - Defecto de desalineamiento δ* persistente

**Description:** From README.md, line 48

**Category:** general

---

### README_49
**Formula:** - Control de vorticidad L∞ uniforme

**Description:** From README.md, line 49

**Category:** general

---

### QCAL_PARAMETERS_12
**Formula:** Value: 7.0 (nominal), needs correction to ~200 for δ* > 0.998

**Description:** From QCAL_PARAMETERS.md, line 12

**Category:** general

---

### QCAL_PARAMETERS_19
**Formula:** δ* = a²c₀² / (4π²)

**Description:** From QCAL_PARAMETERS.md, line 19

**Category:** general

---

### QCAL_PARAMETERS_22
**Formula:** For δ* > 0.998 (critical threshold):

**Description:** From QCAL_PARAMETERS.md, line 22

**Category:** general

---

### QCAL_PARAMETERS_24
**Formula:** a > √(4π² · 0.998 / c₀²) ≈ 198.4 (for c₀ = 1.0)

**Description:** From QCAL_PARAMETERS.md, line 24

**Category:** general

---

### QCAL_PARAMETERS_40
**Formula:** Role: Controls dual-limit scaling ε = λ·f₀^(-α)

**Description:** From QCAL_PARAMETERS.md, line 40

**Category:** general

---

### QCAL_PARAMETERS_44
**Formula:** For viscosity ν = 10⁻³ and dissipative threshold j_d = 8:

**Description:** From QCAL_PARAMETERS.md, line 44

**Category:** physical

---

### QCAL_PARAMETERS_46
**Formula:** f₀ = √(C_BKM · (1 - δ*) / (ν · c_B · 2^(2j_d))) · 2^j_d

**Description:** From QCAL_PARAMETERS.md, line 46

**Category:** criterion

---

### QCAL_PARAMETERS_50
**Formula:** #### Intensity Parameter (λ)

**Description:** From QCAL_PARAMETERS.md, line 50

**Category:** general

---

### QCAL_PARAMETERS_52
**Formula:** Symbol: λ

**Description:** From QCAL_PARAMETERS.md, line 52

**Category:** general

---

### QCAL_PARAMETERS_58
**Formula:** #### Scaling Exponent (α)

**Description:** From QCAL_PARAMETERS.md, line 58

**Category:** general

---

### QCAL_PARAMETERS_60
**Formula:** Symbol: α

**Description:** From QCAL_PARAMETERS.md, line 60

**Category:** general

---

### QCAL_PARAMETERS_63
**Formula:** Constraint: α > 1 (required for convergence)

**Description:** From QCAL_PARAMETERS.md, line 63

**Category:** general

---

### QCAL_PARAMETERS_64
**Formula:** Role: Controls ε = λ·f₀^(-α) decay rate

**Description:** From QCAL_PARAMETERS.md, line 64

**Category:** general

---

### QCAL_PARAMETERS_69
**Formula:** The regularization parameter ε and amplitude A scale as:

**Description:** From QCAL_PARAMETERS.md, line 69

**Category:** general

---

### QCAL_PARAMETERS_71
**Formula:** ε = λ · f₀^(-α)    (regularization scale)

**Description:** From QCAL_PARAMETERS.md, line 71

**Category:** general

---

### QCAL_PARAMETERS_72
**Formula:** A = a · f₀         (amplitude scale)

**Description:** From QCAL_PARAMETERS.md, line 72

**Category:** general

---

### QCAL_PARAMETERS_76
**Formula:** - As f₀ → ∞: ε → 0 (vanishing regularization)

**Description:** From QCAL_PARAMETERS.md, line 76

**Category:** general

---

### QCAL_PARAMETERS_77
**Formula:** - As f₀ → ∞: A → ∞ (increasing amplitude)

**Description:** From QCAL_PARAMETERS.md, line 77

**Category:** general

---

### QCAL_PARAMETERS_78
**Formula:** - Net effect: Persistent misalignment δ* remains bounded away from zero

**Description:** From QCAL_PARAMETERS.md, line 78

**Category:** general

---

### QCAL_PARAMETERS_80
**Formula:** ### Misalignment Defect (δ*)

**Description:** From QCAL_PARAMETERS.md, line 80

**Category:** general

---

### QCAL_PARAMETERS_84
**Formula:** δ* = a²c₀² / (4π²)

**Description:** From QCAL_PARAMETERS.md, line 84

**Category:** general

---

### QCAL_PARAMETERS_87
**Formula:** **Numerical value** (for a = 7.0, c₀ = 1.0):

**Description:** From QCAL_PARAMETERS.md, line 87

**Category:** general

---

### QCAL_PARAMETERS_89
**Formula:** δ* = 49 · 1 / (4 · 9.8696)

**Description:** From QCAL_PARAMETERS.md, line 89

**Category:** general

---

### QCAL_PARAMETERS_90
**Formula:** = 49 / 39.478

**Description:** From QCAL_PARAMETERS.md, line 90

**Category:** general

---

### QCAL_PARAMETERS_94
**Formula:** **CRITICAL NOTE**: This value is BELOW the required threshold δ* > 0.998

**Description:** From QCAL_PARAMETERS.md, line 94

**Category:** general

---

### QCAL_PARAMETERS_95
**Formula:** **Corrected amplitude needed**: a ≈ 200 to achieve δ* ≈ 1.013

**Description:** From QCAL_PARAMETERS.md, line 95

**Category:** general

---

### QCAL_PARAMETERS_98
**Formula:** - δ* measures persistent misalignment between vorticity ω and strain S

**Description:** From QCAL_PARAMETERS.md, line 98

**Category:** general

---

### QCAL_PARAMETERS_99
**Formula:** - δ* = 0: Perfect alignment (enables blow-up)

**Description:** From QCAL_PARAMETERS.md, line 99

**Category:** general

---

### QCAL_PARAMETERS_100
**Formula:** - δ* > 0: Misalignment prevents blow-up

**Description:** From QCAL_PARAMETERS.md, line 100

**Category:** general

---

### QCAL_PARAMETERS_101
**Formula:** - δ* > 0.998: Sufficient for positive Riccati damping

**Description:** From QCAL_PARAMETERS.md, line 101

**Category:** estimate

---

### QCAL_PARAMETERS_108
**Formula:** Value: 1/16 = 0.0625

**Description:** From QCAL_PARAMETERS.md, line 108

**Category:** general

---

### QCAL_PARAMETERS_115
**Formula:** - Riccati damping coefficient γ = ν·c⋆ - (1 - δ*/2)·C_str

**Description:** From QCAL_PARAMETERS.md, line 115

**Category:** estimate

---

### QCAL_PARAMETERS_117
**Formula:** ### Vorticity Stretching Constant (C_str)

**Description:** From QCAL_PARAMETERS.md, line 117

**Category:** general

---

### QCAL_PARAMETERS_119
**Formula:** Symbol: C_str

**Description:** From QCAL_PARAMETERS.md, line 119

**Category:** general

---

### QCAL_PARAMETERS_128
**Formula:** |ω · ∇u · ω| / |ω|² ≤ C_str · |ω|

**Description:** From QCAL_PARAMETERS.md, line 128

**Category:** general

---

### QCAL_PARAMETERS_131
**Formula:** ### Calderón-Zygmund/Besov Constant (C_BKM)

**Description:** From QCAL_PARAMETERS.md, line 131

**Category:** criterion

---

### QCAL_PARAMETERS_133
**Formula:** Symbol: C_BKM

**Description:** From QCAL_PARAMETERS.md, line 133

**Category:** criterion

---

### QCAL_PARAMETERS_152
**Formula:** In dyadic blocks Δ_j with frequency ~2^j:

**Description:** From QCAL_PARAMETERS.md, line 152

**Category:** general

---

### QCAL_PARAMETERS_154
**Formula:** ‖∇(Δ_j f)‖_Lp ≤ c_B · 2^j · ‖Δ_j f‖_Lp

**Description:** From QCAL_PARAMETERS.md, line 154

**Category:** general

---

### QCAL_PARAMETERS_160
**Formula:** Value: 8 (for ν = 10⁻³, f₀ = 141.7001 Hz)

**Description:** From QCAL_PARAMETERS.md, line 160

**Category:** physical

---

### QCAL_PARAMETERS_161
**Formula:** Derivation: j_d = ceil(log₂(C_BKM(1-δ*)(1+log(C_BKM/ν))/(ν·c_B)) / 2)

**Description:** From QCAL_PARAMETERS.md, line 161

**Category:** criterion

---

### QCAL_PARAMETERS_166
**Formula:** - For j ≥ j_d: Dyadic Riccati coefficient < 0 (damping)

**Description:** From QCAL_PARAMETERS.md, line 166

**Category:** estimate

---

### QCAL_PARAMETERS_167
**Formula:** - For j < j_d: Riccati coefficient may be positive (growth)

**Description:** From QCAL_PARAMETERS.md, line 167

**Category:** estimate

---

### QCAL_PARAMETERS_170
**Formula:** ## Riccati Damping Coefficient (γ)

**Description:** From QCAL_PARAMETERS.md, line 170

**Category:** estimate

---

### QCAL_PARAMETERS_174
**Formula:** γ = ν · c⋆ - (1 - δ*/2) · C_str

**Description:** From QCAL_PARAMETERS.md, line 174

**Category:** physical

---

### QCAL_PARAMETERS_179
**Formula:** γ > 0  ⟺  δ* > 2(1 - ν·c⋆/C_str)

**Description:** From QCAL_PARAMETERS.md, line 179

**Category:** physical

---

### QCAL_PARAMETERS_180
**Formula:** ⟺  δ* > 2(1 - ν/(16·32))

**Description:** From QCAL_PARAMETERS.md, line 180

**Category:** physical

---

### QCAL_PARAMETERS_181
**Formula:** ⟺  δ* > 2(1 - ν/512)

**Description:** From QCAL_PARAMETERS.md, line 181

**Category:** physical

---

### QCAL_PARAMETERS_182
**Formula:** ⟺  δ* > 1 - ν/256

**Description:** From QCAL_PARAMETERS.md, line 182

**Category:** physical

---

### QCAL_PARAMETERS_185
**Formula:** **For ν = 10⁻³**:

**Description:** From QCAL_PARAMETERS.md, line 185

**Category:** physical

---

### QCAL_PARAMETERS_187
**Formula:** γ > 0  ⟺  δ* > 1 - 10⁻³/256

**Description:** From QCAL_PARAMETERS.md, line 187

**Category:** general

---

### QCAL_PARAMETERS_188
**Formula:** ⟺  δ* > 0.996094

**Description:** From QCAL_PARAMETERS.md, line 188

**Category:** general

---

### QCAL_PARAMETERS_192
**Formula:** - Required: δ* > 0.996094

**Description:** From QCAL_PARAMETERS.md, line 192

**Category:** general

---

### QCAL_PARAMETERS_193
**Formula:** - Achieved: δ* = 0.0253 (ERROR)

**Description:** From QCAL_PARAMETERS.md, line 193

**Category:** general

---

### QCAL_PARAMETERS_200
**Formula:** δ* = a²c₀² / (4π²)

**Description:** From QCAL_PARAMETERS.md, line 200

**Category:** general

---

### QCAL_PARAMETERS_201
**Formula:** γ = ν·c⋆ - (1 - δ*/2)·C_str

**Description:** From QCAL_PARAMETERS.md, line 201

**Category:** physical

---

### QCAL_PARAMETERS_202
**Formula:** ε = λ·f₀^(-α)

**Description:** From QCAL_PARAMETERS.md, line 202

**Category:** general

---

### QCAL_PARAMETERS_203
**Formula:** A = a·f₀

**Description:** From QCAL_PARAMETERS.md, line 203

**Category:** general

---

### QCAL_PARAMETERS_204
**Formula:** j_d = ceil(log₂((C_BKM(1-δ*)(1+log(C_BKM/ν)))/(ν·c_B)) / 2)

**Description:** From QCAL_PARAMETERS.md, line 204

**Category:** criterion

---

### QCAL_PARAMETERS_209
**Formula:** #### δ* vs. a (c₀ = 1.0):

**Description:** From QCAL_PARAMETERS.md, line 209

**Category:** general

---

### QCAL_PARAMETERS_210
**Formula:** | a | δ* | γ (ν=10⁻³) | Status |

**Description:** From QCAL_PARAMETERS.md, line 210

**Category:** physical

---

### QCAL_PARAMETERS_213
**Formula:** | 50 | 6.34 | 69.44 | FAIL (δ* too large) |

**Description:** From QCAL_PARAMETERS.md, line 213

**Category:** general

---

### QCAL_PARAMETERS_214
**Formula:** | 100 | 25.4 | 375 | FAIL (δ* too large) |

**Description:** From QCAL_PARAMETERS.md, line 214

**Category:** general

---

### QCAL_PARAMETERS_215
**Formula:** | 199 | 100.5 | 1576 | FAIL (δ* too large) |

**Description:** From QCAL_PARAMETERS.md, line 215

**Category:** general

---

### QCAL_PARAMETERS_218
**Formula:** **NOTE**: Need precise tuning of a to achieve 0.996 < δ* < 1.002

**Description:** From QCAL_PARAMETERS.md, line 218

**Category:** general

---

### QCAL_PARAMETERS_220
**Formula:** #### γ vs. ν (δ* = 0.998):

**Description:** From QCAL_PARAMETERS.md, line 220

**Category:** physical

---

### QCAL_PARAMETERS_221
**Formula:** | ν | γ | Status |

**Description:** From QCAL_PARAMETERS.md, line 221

**Category:** physical

---

### QCAL_PARAMETERS_228
**Formula:** **Conclusion**: γ < 0 for all reasonable ν with δ* = 0.998

**Description:** From QCAL_PARAMETERS.md, line 228

**Category:** physical

---

### QCAL_PARAMETERS_233
**Formula:** 1. **Verify formula for δ***:

**Description:** From QCAL_PARAMETERS.md, line 233

**Category:** general

---

### QCAL_PARAMETERS_238
**Formula:** - c⋆ = 1/16 vs. alternative values

**Description:** From QCAL_PARAMETERS.md, line 238

**Category:** general

---

### QCAL_PARAMETERS_239
**Formula:** - C_str = 32 vs. tighter estimates

**Description:** From QCAL_PARAMETERS.md, line 239

**Category:** estimate

---

### QCAL_PARAMETERS_242
**Formula:** - Explore different scaling exponents α

**Description:** From QCAL_PARAMETERS.md, line 242

**Category:** general

---

### QCAL_PARAMETERS_250
**Formula:** let params := QCALParameters.default

**Description:** From QCAL_PARAMETERS.md, line 250

**Category:** general

---

### QCAL_PARAMETERS_251
**Formula:** let consts := UniversalConstants.default

**Description:** From QCAL_PARAMETERS.md, line 251

**Category:** general

---

### QCAL_PARAMETERS_252
**Formula:** let δ_star := misalignment_defect params

**Description:** From QCAL_PARAMETERS.md, line 252

**Category:** general

---

### QCAL_PARAMETERS_253
**Formula:** let γ := damping_coefficient ν params consts

**Description:** From QCAL_PARAMETERS.md, line 253

**Category:** physical

---

### QCAL_PARAMETERS_254
**Formula:** δ_star > 0.996 ∧ γ > 0 := by

**Description:** From QCAL_PARAMETERS.md, line 254

**Category:** general

---

### QCAL_PARAMETERS_262
**Formula:** """Verify δ(t) → δ* as f₀ → ∞"""

**Description:** From QCAL_PARAMETERS.md, line 262

**Category:** general

---

### QCAL_PARAMETERS_263
**Formula:** f0_values = [100, 200, 500, 1000]

**Description:** From QCAL_PARAMETERS.md, line 263

**Category:** general

---

### QCAL_PARAMETERS_265
**Formula:** solver = ClayDNSVerifier(...)

**Description:** From QCAL_PARAMETERS.md, line 265

**Category:** general

---

### QCAL_PARAMETERS_266
**Formula:** results = solver.run_clay_verification([f0])

**Description:** From QCAL_PARAMETERS.md, line 266

**Category:** general

---

### QCAL_PARAMETERS_267
**Formula:** δ_measured = results[f0]['metrics']['δ_history'][-1]

**Description:** From QCAL_PARAMETERS.md, line 267

**Category:** general

---

### QCAL_PARAMETERS_268
**Formula:** δ_theoretical = solver.scaling.a**2 / (4*np.pi**2)

**Description:** From QCAL_PARAMETERS.md, line 268

**Category:** general

---

### QCAL_PARAMETERS_269
**Formula:** assert abs(δ_measured - δ_theoretical) < 0.01

**Description:** From QCAL_PARAMETERS.md, line 269

**Category:** general

---

### MATHEMATICAL_APPENDICES_6
**Formula:** **Goal**: Establish global regularity with constants that depend ONLY on spatial dimension d and viscosity ν, independent of regularization parameters f₀, ε, A.

**Description:** From MATHEMATICAL_APPENDICES.md, line 6

**Category:** physical

---

### MATHEMATICAL_APPENDICES_10
**Formula:** **Critical Achievement**: Universal damping coefficient γ > 0 ensuring:

**Description:** From MATHEMATICAL_APPENDICES.md, line 10

**Category:** general

---

### MATHEMATICAL_APPENDICES_12
**Formula:** d/dt ‖ω‖_{B⁰_{∞,1}} ≤ -γ ‖ω‖²_{B⁰_{∞,1}} + K

**Description:** From MATHEMATICAL_APPENDICES.md, line 12

**Category:** general

---

### MATHEMATICAL_APPENDICES_14
**Formula:** with γ depending only on d and ν.

**Description:** From MATHEMATICAL_APPENDICES.md, line 14

**Category:** physical

---

### MATHEMATICAL_APPENDICES_19
**Formula:** For vorticity ω with Littlewood-Paley decomposition ω = Σ_j Δ_j ω:

**Description:** From MATHEMATICAL_APPENDICES.md, line 19

**Category:** general

---

### MATHEMATICAL_APPENDICES_21
**Formula:** ⟨∂_t ω, ω⟩ + ν ∑_j 2^{2j} ‖Δ_j ω‖²_{L²} ≥ c_star ‖ω‖²_{Ḃ⁰_{∞,1}} - C_star ‖ω‖²_{L²}

**Description:** From MATHEMATICAL_APPENDICES.md, line 21

**Category:** physical

---

### MATHEMATICAL_APPENDICES_24
**Formula:** **Key Innovation**: c_star is computed to ensure positive damping γ > 0 with fixed δ* ≈ 0.0253:

**Description:** From MATHEMATICAL_APPENDICES.md, line 24

**Category:** general

---

### MATHEMATICAL_APPENDICES_26
**Formula:** c_star = (1 - δ*/2) · C_str / ν · (1.03)

**Description:** From MATHEMATICAL_APPENDICES.md, line 26

**Category:** physical

---

### MATHEMATICAL_APPENDICES_30
**Formula:** **For ν = 10⁻³, d = 3**:

**Description:** From MATHEMATICAL_APPENDICES.md, line 30

**Category:** physical

---

### MATHEMATICAL_APPENDICES_31
**Formula:** - δ* = 1/(4π²) ≈ 0.0253

**Description:** From MATHEMATICAL_APPENDICES.md, line 31

**Category:** general

---

### MATHEMATICAL_APPENDICES_32
**Formula:** - C_str = 32

**Description:** From MATHEMATICAL_APPENDICES.md, line 32

**Category:** general

---

### MATHEMATICAL_APPENDICES_36
**Formula:** 1. Start with vorticity equation: ∂_t ω + u·∇ω = ω·∇u + ν Δω

**Description:** From MATHEMATICAL_APPENDICES.md, line 36

**Category:** physical

---

### MATHEMATICAL_APPENDICES_37
**Formula:** 2. Take L² inner product: ⟨∂_t ω, ω⟩ = ⟨ω·∇u, ω⟩ + ν⟨Δω, ω⟩

**Description:** From MATHEMATICAL_APPENDICES.md, line 37

**Category:** physical

---

### MATHEMATICAL_APPENDICES_38
**Formula:** 3. Dissipation term: -ν⟨Δω, ω⟩ = ν‖∇ω‖²_{L²} = ν ∑_j 2^{2j}‖Δ_j ω‖²_{L²}

**Description:** From MATHEMATICAL_APPENDICES.md, line 38

**Category:** physical

---

### MATHEMATICAL_APPENDICES_39
**Formula:** 4. Stretching term estimate: |⟨ω·∇u, ω⟩| ≤ C_str ‖ω‖³_{Ḃ⁰_{∞,1}}

**Description:** From MATHEMATICAL_APPENDICES.md, line 39

**Category:** estimate

---

### MATHEMATICAL_APPENDICES_40
**Formula:** 5. Require: ν·c_star > (1 - δ*/2)·C_str for positive γ

**Description:** From MATHEMATICAL_APPENDICES.md, line 40

**Category:** physical

---

### MATHEMATICAL_APPENDICES_43
**Formula:** **Unconditional Property**: c_star depends only on ν (physical) and d (dimension), NOT on f₀, ε, or A.

**Description:** From MATHEMATICAL_APPENDICES.md, line 43

**Category:** physical

---

### MATHEMATICAL_APPENDICES_45
**Formula:** ### A.2 Vorticity Stretching Constant (C_str = 32)

**Description:** From MATHEMATICAL_APPENDICES.md, line 45

**Category:** general

---

### MATHEMATICAL_APPENDICES_49
**Formula:** ‖ω·∇u‖_{Ḃ⁰_{∞,1}} ≤ C_str ‖ω‖²_{Ḃ⁰_{∞,1}}

**Description:** From MATHEMATICAL_APPENDICES.md, line 49

**Category:** general

---

### MATHEMATICAL_APPENDICES_53
**Formula:** 1. Biot-Savart law: u = K * ω where K is Calderón-Zygmund kernel

**Description:** From MATHEMATICAL_APPENDICES.md, line 53

**Category:** general

---

### MATHEMATICAL_APPENDICES_54
**Formula:** 2. Gradient estimate: ∇u ~ CZ[ω] where CZ is Calderón-Zygmund operator

**Description:** From MATHEMATICAL_APPENDICES.md, line 54

**Category:** estimate

---

### MATHEMATICAL_APPENDICES_57
**Formula:** ‖f·g‖_{Ḃ⁰_{∞,1}} ≤ C ‖f‖_{Ḃ⁰_{∞,1}} ‖g‖_{Ḃ⁰_{∞,1}}

**Description:** From MATHEMATICAL_APPENDICES.md, line 57

**Category:** general

---

### MATHEMATICAL_APPENDICES_59
**Formula:** 4. Combine with ‖∇u‖_{Ḃ⁰_{∞,1}} ≤ C‖ω‖_{Ḃ⁰_{∞,1}} to get C_str = 32

**Description:** From MATHEMATICAL_APPENDICES.md, line 59

**Category:** general

---

### MATHEMATICAL_APPENDICES_61
**Formula:** ### A.3 Calderón-Zygmund/Besov Constant (C_d = 2 - Absolute)

**Description:** From MATHEMATICAL_APPENDICES.md, line 61

**Category:** general

---

### MATHEMATICAL_APPENDICES_65
**Formula:** ‖∇u‖_{Ḃ⁰_{∞,1}} ≤ C_d ‖ω‖_{Ḃ⁰_{∞,1}}

**Description:** From MATHEMATICAL_APPENDICES.md, line 65

**Category:** general

---

### MATHEMATICAL_APPENDICES_69
**Formula:** ‖S(u)‖_{L∞} ≤ C_d ‖ω‖_{Ḃ⁰_{∞,1}}

**Description:** From MATHEMATICAL_APPENDICES.md, line 69

**Category:** general

---

### MATHEMATICAL_APPENDICES_72
**Formula:** **Key Property**: C_d is ABSOLUTE - depends only on dimension d, avoiding any dependence on the oscillatory decomposition Φ or regularization parameters.

**Description:** From MATHEMATICAL_APPENDICES.md, line 72

**Category:** general

---

### MATHEMATICAL_APPENDICES_75
**Formula:** 1. Biot-Savart in frequency space: û(ξ) = (iξ × ω̂(ξ)) / |ξ|²

**Description:** From MATHEMATICAL_APPENDICES.md, line 75

**Category:** general

---

### MATHEMATICAL_APPENDICES_76
**Formula:** 2. Decompose ω = Σ_j Δ_j ω using Littlewood-Paley blocks

**Description:** From MATHEMATICAL_APPENDICES.md, line 76

**Category:** general

---

### MATHEMATICAL_APPENDICES_78
**Formula:** 4. Multiplier estimate: |∇û(ξ)| ≤ C|ω̂(ξ)| / |ξ|

**Description:** From MATHEMATICAL_APPENDICES.md, line 78

**Category:** estimate

---

### MATHEMATICAL_APPENDICES_79
**Formula:** 5. Littlewood-Paley blocks: ‖Δ_j ∇u‖_{L∞} ≤ C ‖Δ_j ω‖_{L∞}

**Description:** From MATHEMATICAL_APPENDICES.md, line 79

**Category:** general

---

### MATHEMATICAL_APPENDICES_80
**Formula:** 6. Sum over j: ‖∇u‖_{Ḃ⁰_{∞,1}} ≤ C_d ‖ω‖_{Ḃ⁰_{∞,1}}

**Description:** From MATHEMATICAL_APPENDICES.md, line 80

**Category:** general

---

### MATHEMATICAL_APPENDICES_82
**Formula:** **For d=3**: C_d = 2 (sharp constant from Coifman-Meyer-Stein theory)

**Description:** From MATHEMATICAL_APPENDICES.md, line 82

**Category:** general

---

### MATHEMATICAL_APPENDICES_88
**Formula:** **Unconditional Property**: C_d = 2 for all d = 3, independent of ANY regularization.

**Description:** From MATHEMATICAL_APPENDICES.md, line 88

**Category:** general

---

### MATHEMATICAL_APPENDICES_89
**Formula:** ### A.3 Critical Besov Pair (C_CZ = 2, C_star = 1)

**Description:** From MATHEMATICAL_APPENDICES.md, line 89

**Category:** general

---

### MATHEMATICAL_APPENDICES_94
**Formula:** ‖∇u‖_{L∞} ≤ C_CZ ‖ω‖_{B⁰_{∞,1}},    ‖ω‖_{B⁰_{∞,1}} ≤ C_star ‖ω‖_{L∞}

**Description:** From MATHEMATICAL_APPENDICES.md, line 94

**Category:** general

---

### MATHEMATICAL_APPENDICES_97
**Formula:** where C_CZ = 2 (Calderón-Zygmund constant) and C_star = 1 (Besov embedding constant).

**Description:** From MATHEMATICAL_APPENDICES.md, line 97

**Category:** general

---

### MATHEMATICAL_APPENDICES_99
**Formula:** **Historical Note**: We replace the classical L∞→L∞ estimate ‖∇u‖_{L∞} ≤ C‖ω‖_{L∞} with the critical Besov pair above.

**Description:** From MATHEMATICAL_APPENDICES.md, line 99

**Category:** estimate

---

### MATHEMATICAL_APPENDICES_102
**Formula:** 1. Biot-Savart in frequency space: û(ξ) = (iξ × ω̂(ξ)) / |ξ|²

**Description:** From MATHEMATICAL_APPENDICES.md, line 102

**Category:** general

---

### MATHEMATICAL_APPENDICES_103
**Formula:** 2. Multiplier estimate: |∇û(ξ)| ≤ C|ω̂(ξ)| / |ξ|

**Description:** From MATHEMATICAL_APPENDICES.md, line 103

**Category:** estimate

---

### MATHEMATICAL_APPENDICES_104
**Formula:** 3. Littlewood-Paley blocks: ‖Δ_j ∇u‖_{L∞} ≤ C ‖Δ_j ω‖_{L∞}

**Description:** From MATHEMATICAL_APPENDICES.md, line 104

**Category:** general

---

### MATHEMATICAL_APPENDICES_105
**Formula:** 4. Sum over j: ‖∇u‖_{L∞} ≤ C_CZ ‖ω‖_{B⁰_{∞,1}} with C_CZ = 2

**Description:** From MATHEMATICAL_APPENDICES.md, line 105

**Category:** general

---

### MATHEMATICAL_APPENDICES_106
**Formula:** 5. Besov embedding: ‖ω‖_{B⁰_{∞,1}} ≤ C_star ‖ω‖_{L∞} with C_star = 1

**Description:** From MATHEMATICAL_APPENDICES.md, line 106

**Category:** general

---

### MATHEMATICAL_APPENDICES_108
**Formula:** **Note**: The original C_BKM = 2 notation is retained for backward compatibility and refers to C_CZ.

**Description:** From MATHEMATICAL_APPENDICES.md, line 108

**Category:** criterion

---

### MATHEMATICAL_APPENDICES_110
**Formula:** ### A.4 Bernstein Constants (c_B = 0.1, c_Bern = 0.1)

**Description:** From MATHEMATICAL_APPENDICES.md, line 110

**Category:** general

---

### MATHEMATICAL_APPENDICES_115
**Formula:** ‖∇f‖_{Lp} ≤ c_B · 2^j · ‖f‖_{Lp}

**Description:** From MATHEMATICAL_APPENDICES.md, line 115

**Category:** general

---

### MATHEMATICAL_APPENDICES_123
**Formula:** ‖∇ω‖_{L∞} ≥ c_Bern ‖ω‖_{L∞}²

**Description:** From MATHEMATICAL_APPENDICES.md, line 123

**Category:** general

---

### MATHEMATICAL_APPENDICES_126
**Formula:** where c_Bern = 0.1 is a universal constant. This lower bound is crucial for the damped Riccati inequality.

**Description:** From MATHEMATICAL_APPENDICES.md, line 126

**Category:** estimate

---

### MATHEMATICAL_APPENDICES_134
**Formula:** φ(x,t) = x₁ + c₀ · g(x₂, x₃, t)

**Description:** From MATHEMATICAL_APPENDICES.md, line 134

**Category:** general

---

### MATHEMATICAL_APPENDICES_136
**Formula:** where g is a smooth, periodic function with ∇g bounded.

**Description:** From MATHEMATICAL_APPENDICES.md, line 136

**Category:** general

---

### MATHEMATICAL_APPENDICES_142
**Formula:** u_QCAL(x,t) = a · f₀ · (∇φ × e_z) · ψ(f₀^{-α} · φ)

**Description:** From MATHEMATICAL_APPENDICES.md, line 142

**Category:** general

---

### MATHEMATICAL_APPENDICES_148
**Formula:** - α > 1: scaling exponent

**Description:** From MATHEMATICAL_APPENDICES.md, line 148

**Category:** general

---

### MATHEMATICAL_APPENDICES_155
**Formula:** ω_QCAL = ∇ × u_QCAL

**Description:** From MATHEMATICAL_APPENDICES.md, line 155

**Category:** general

---

### MATHEMATICAL_APPENDICES_156
**Formula:** = a · f₀ · [∇²φ · e_z + (∇φ · ∇ψ) × e_z] · ψ + O(f₀^{1-α})

**Description:** From MATHEMATICAL_APPENDICES.md, line 156

**Category:** general

---

### MATHEMATICAL_APPENDICES_163
**Formula:** S_ij = (1/2)(∂_i u_j + ∂_j u_i)

**Description:** From MATHEMATICAL_APPENDICES.md, line 163

**Category:** general

---

### MATHEMATICAL_APPENDICES_168
**Formula:** A(t) = ∫ (S·ω)·ω dx / ∫ |S||ω|² dx

**Description:** From MATHEMATICAL_APPENDICES.md, line 168

**Category:** general

---

### MATHEMATICAL_APPENDICES_173
**Formula:** δ(t) = 1 - A(t)

**Description:** From MATHEMATICAL_APPENDICES.md, line 173

**Category:** general

---

### MATHEMATICAL_APPENDICES_178
**Formula:** δ(t) → δ* = a²c₀² / (4π²)  as  f₀ → ∞

**Description:** From MATHEMATICAL_APPENDICES.md, line 178

**Category:** general

---

### MATHEMATICAL_APPENDICES_187
**Formula:** 1 = χ(ξ) + ∑_{j≥0} φ_j(ξ)

**Description:** From MATHEMATICAL_APPENDICES.md, line 187

**Category:** general

---

### MATHEMATICAL_APPENDICES_190
**Formula:** - χ supported on |ξ| ≤ 2

**Description:** From MATHEMATICAL_APPENDICES.md, line 190

**Category:** general

---

### MATHEMATICAL_APPENDICES_191
**Formula:** - φ_j supported on 2^{j-1} ≤ |ξ| ≤ 2^{j+1}

**Description:** From MATHEMATICAL_APPENDICES.md, line 191

**Category:** general

---

### MATHEMATICAL_APPENDICES_195
**Formula:** Δ_{-1} f = χ(D) f

**Description:** From MATHEMATICAL_APPENDICES.md, line 195

**Category:** general

---

### MATHEMATICAL_APPENDICES_196
**Formula:** Δ_j f = φ_j(D) f  for j ≥ 0

**Description:** From MATHEMATICAL_APPENDICES.md, line 196

**Category:** general

---

### MATHEMATICAL_APPENDICES_203
**Formula:** ‖f‖_{B^s_{p,q}} = (∑_j (2^{js} ‖Δ_j f‖_{Lp})^q)^{1/q}

**Description:** From MATHEMATICAL_APPENDICES.md, line 203

**Category:** general

---

### MATHEMATICAL_APPENDICES_206
**Formula:** **Special case** (B⁰_{∞,1}):

**Description:** From MATHEMATICAL_APPENDICES.md, line 206

**Category:** general

---

### MATHEMATICAL_APPENDICES_208
**Formula:** ‖f‖_{B⁰_{∞,1}} = ∑_j ‖Δ_j f‖_{L∞}

**Description:** From MATHEMATICAL_APPENDICES.md, line 208

**Category:** general

---

### MATHEMATICAL_APPENDICES_215
**Formula:** B^s_{p,q₁} ⊂ B^s_{p,q₂}  if  q₁ ≤ q₂

**Description:** From MATHEMATICAL_APPENDICES.md, line 215

**Category:** general

---

### MATHEMATICAL_APPENDICES_220
**Formula:** ‖fg‖_{B^s_{p,q}} ≤ C ‖f‖_{B^s_{p,q}} ‖g‖_{L∞}  (s > 0)

**Description:** From MATHEMATICAL_APPENDICES.md, line 220

**Category:** general

---

### MATHEMATICAL_APPENDICES_225
**Formula:** ‖f‖_{B⁰_{∞,1}} ≤ C ‖f‖_{L∞}^{1/2} ‖f‖_{Ḃ¹_{∞,1}}^{1/2}

**Description:** From MATHEMATICAL_APPENDICES.md, line 225

**Category:** general

---

### MATHEMATICAL_APPENDICES_234
**Formula:** d/dt ‖ω(t)‖_{B⁰_{∞,1}} ≤ -γ ‖ω(t)‖²_{B⁰_{∞,1}} + K

**Description:** From MATHEMATICAL_APPENDICES.md, line 234

**Category:** general

---

### MATHEMATICAL_APPENDICES_238
**Formula:** γ = ν·c_star - (1 - δ*/2)·C_str > 0

**Description:** From MATHEMATICAL_APPENDICES.md, line 238

**Category:** physical

---

### MATHEMATICAL_APPENDICES_241
**Formula:** **Universal Damping**: For ν = 10⁻³, d = 3, δ* = 1/(4π²):

**Description:** From MATHEMATICAL_APPENDICES.md, line 241

**Category:** physical

---

### MATHEMATICAL_APPENDICES_242
**Formula:** - Viscous term: ν·c_star ≈ 32.543

**Description:** From MATHEMATICAL_APPENDICES.md, line 242

**Category:** physical

---

### MATHEMATICAL_APPENDICES_243
**Formula:** - Stretching term: (1 - δ*/2)·C_str ≈ 31.595

**Description:** From MATHEMATICAL_APPENDICES.md, line 243

**Category:** general

---

### MATHEMATICAL_APPENDICES_244
**Formula:** - **γ ≈ 0.948 > 0** ✓ (UNCONDITIONAL)

**Description:** From MATHEMATICAL_APPENDICES.md, line 244

**Category:** general

---

### MATHEMATICAL_APPENDICES_246
**Formula:** **Key Property**: γ > 0 depends ONLY on ν and d, NOT on f₀, ε, or A.

**Description:** From MATHEMATICAL_APPENDICES.md, line 246

**Category:** physical

---

### MATHEMATICAL_APPENDICES_252
**Formula:** dy/dt = -γy² + β  with  γ, β > 0

**Description:** From MATHEMATICAL_APPENDICES.md, line 252

**Category:** general

---

### MATHEMATICAL_APPENDICES_257
**Formula:** y(t) = √(β/γ) · tanh(√(βγ)(T-t))  if  y(0) < √(β/γ)

**Description:** From MATHEMATICAL_APPENDICES.md, line 257

**Category:** general

---

### MATHEMATICAL_APPENDICES_260
**Formula:** **Key property**: Solution remains bounded for all t ∈ [0,∞)

**Description:** From MATHEMATICAL_APPENDICES.md, line 260

**Category:** general

---

### MATHEMATICAL_APPENDICES_266
**Formula:** dy/dt = -γy² + K

**Description:** From MATHEMATICAL_APPENDICES.md, line 266

**Category:** general

---

### MATHEMATICAL_APPENDICES_270
**Formula:** 1. **γ > 0, K ≥ 0**: y(t) → √(K/γ) as t → ∞

**Description:** From MATHEMATICAL_APPENDICES.md, line 270

**Category:** general

---

### MATHEMATICAL_APPENDICES_271
**Formula:** 2. **γ > 0, K = 0**: y(t) → 0 as t → ∞ (power law)

**Description:** From MATHEMATICAL_APPENDICES.md, line 271

**Category:** general

---

### MATHEMATICAL_APPENDICES_272
**Formula:** 3. **γ ≤ 0**: y(t) → ∞ in finite time (blow-up)

**Description:** From MATHEMATICAL_APPENDICES.md, line 272

**Category:** general

---

### MATHEMATICAL_APPENDICES_278
**Formula:** d/dt ‖ω(t)‖_{B⁰_{∞,1}} ≤ -γ ‖ω(t)‖²_{B⁰_{∞,1}} + K

**Description:** From MATHEMATICAL_APPENDICES.md, line 278

**Category:** general

---

### MATHEMATICAL_APPENDICES_283
**Formula:** ∫₀^∞ ‖ω(t)‖_{B⁰_{∞,1}} dt ≤ ‖ω(0)‖_{B⁰_{∞,1}}/γ + Kt/γ

**Description:** From MATHEMATICAL_APPENDICES.md, line 283

**Category:** general

---

### MATHEMATICAL_APPENDICES_284
**Formula:** ≤ C (finite if K bounded)

**Description:** From MATHEMATICAL_APPENDICES.md, line 284

**Category:** general

---

### MATHEMATICAL_APPENDICES_292
**Formula:** δ̄₀(T) := (1/T) ∫₀^T δ₀(t) dt

**Description:** From MATHEMATICAL_APPENDICES.md, line 292

**Category:** general

---

### MATHEMATICAL_APPENDICES_296
**Formula:** δ₀(t) = A(t)²|∇φ|² / (4π²f₀²) + O(f₀⁻³)

**Description:** From MATHEMATICAL_APPENDICES.md, line 296

**Category:** general

---

### MATHEMATICAL_APPENDICES_303
**Formula:** Ẇ ≤ ((1-δ̄₀)C_CZ·C_star - ν·c_Bern) W²

**Description:** From MATHEMATICAL_APPENDICES.md, line 303

**Category:** physical

---

### MATHEMATICAL_APPENDICES_308
**Formula:** γ_avg := ν·c_Bern - (1-δ̄₀)C_CZ·C_star

**Description:** From MATHEMATICAL_APPENDICES.md, line 308

**Category:** physical

---

### MATHEMATICAL_APPENDICES_311
**Formula:** If γ_avg > 0, then:

**Description:** From MATHEMATICAL_APPENDICES.md, line 311

**Category:** general

---

### MATHEMATICAL_APPENDICES_313
**Formula:** W(t) ≤ W(0) / (1 + γ_avg·t·W(0))

**Description:** From MATHEMATICAL_APPENDICES.md, line 313

**Category:** general

---

### MATHEMATICAL_APPENDICES_315
**Formula:** and ∫₀^∞ ‖ω‖_{L∞} dt < ∞ (BKM closure).

**Description:** From MATHEMATICAL_APPENDICES.md, line 315

**Category:** criterion

---

### MATHEMATICAL_APPENDICES_319
**Formula:** Working directly with A(t) := ‖ω(t)‖_{B⁰_{∞,1}}:

**Description:** From MATHEMATICAL_APPENDICES.md, line 319

**Category:** general

---

### MATHEMATICAL_APPENDICES_321
**Formula:** d/dt A ≤ -ν·c_star·A² + C_str·A² + C₀

**Description:** From MATHEMATICAL_APPENDICES.md, line 321

**Category:** physical

---

### MATHEMATICAL_APPENDICES_326
**Formula:** ν·c_star > C_str

**Description:** From MATHEMATICAL_APPENDICES.md, line 326

**Category:** physical

---

### MATHEMATICAL_APPENDICES_329
**Formula:** Then ∫₀^T A(t) dt < ∞ and BKM closes via:

**Description:** From MATHEMATICAL_APPENDICES.md, line 329

**Category:** criterion

---

### MATHEMATICAL_APPENDICES_331
**Formula:** ∫₀^T ‖∇u‖_{L∞} dt ≤ C_CZ ∫₀^T A(t) dt < ∞

**Description:** From MATHEMATICAL_APPENDICES.md, line 331

**Category:** general

---

### MATHEMATICAL_APPENDICES_335
**Formula:** At least one of the following mechanisms applies, and in either case u ∈ C^∞(ℝ³ × (0,∞)):

**Description:** From MATHEMATICAL_APPENDICES.md, line 335

**Category:** general

---

### MATHEMATICAL_APPENDICES_337
**Formula:** 1. **Route I**: If γ_avg > 0, then Riccati damping yields global regularity

**Description:** From MATHEMATICAL_APPENDICES.md, line 337

**Category:** estimate

---

### MATHEMATICAL_APPENDICES_338
**Formula:** 2. **Route II**: Independently, dyadic-BGW mechanism (Appendix F) guarantees ∫₀^T A(t) dt < ∞, yielding endpoint Serrin and global smoothness

**Description:** From MATHEMATICAL_APPENDICES.md, line 338

**Category:** general

---

### MATHEMATICAL_APPENDICES_340
**Formula:** All constants depend only on (d=3, ν, ‖u₀‖_{L²}, ‖f‖) and the fixed Littlewood-Paley covering; they are independent of (f₀, ε).

**Description:** From MATHEMATICAL_APPENDICES.md, line 340

**Category:** physical

---

### MATHEMATICAL_APPENDICES_349
**Formula:** u extends smoothly past T  ⟺  ∫₀^T ‖ω(t)‖_{L∞} dt < ∞

**Description:** From MATHEMATICAL_APPENDICES.md, line 349

**Category:** general

---

### MATHEMATICAL_APPENDICES_356
**Formula:** ∫₀^T ‖ω(t)‖_{B⁰_{∞,1}} dt < ∞  ⟹  ∫₀^T ‖ω(t)‖_{L∞} dt < ∞

**Description:** From MATHEMATICAL_APPENDICES.md, line 356

**Category:** general

---

### MATHEMATICAL_APPENDICES_359
**Formula:** **Proof**: Logarithmic Sobolev embedding B⁰_{∞,1} ↪ L∞(log L)^{1/2}

**Description:** From MATHEMATICAL_APPENDICES.md, line 359

**Category:** general

---

### MATHEMATICAL_APPENDICES_366
**Formula:** d/dt ‖ω‖_{B⁰_{∞,1}} ≤ -γ ‖ω‖²_{B⁰_{∞,1}} + K  (γ > 0)

**Description:** From MATHEMATICAL_APPENDICES.md, line 366

**Category:** general

---

### MATHEMATICAL_APPENDICES_370
**Formula:** ∫₀^∞ ‖ω(t)‖_{L∞} dt < ∞

**Description:** From MATHEMATICAL_APPENDICES.md, line 370

**Category:** general

---

### MATHEMATICAL_APPENDICES_376
**Formula:** This appendix provides an unconditional closure mechanism that does not require a positive Riccati damping coefficient. The route is independent of (f₀, ε) and relies on parabolic dominance at high frequencies.

**Description:** From MATHEMATICAL_APPENDICES.md, line 376

**Category:** estimate

---

### MATHEMATICAL_APPENDICES_381
**Formula:** There exists j_d (depending only on ν and the dyadic covering) such that for all j ≥ j_d,

**Description:** From MATHEMATICAL_APPENDICES.md, line 381

**Category:** physical

---

### MATHEMATICAL_APPENDICES_383
**Formula:** d/dt ‖Δ_j ω‖_{L∞} ≤ -ν/2 · 2^{2j} ‖Δ_j ω‖_{L∞} + C_par · A(t) · ‖Δ_j ω‖_{L∞}

**Description:** From MATHEMATICAL_APPENDICES.md, line 383

**Category:** physical

---

### MATHEMATICAL_APPENDICES_386
**Formula:** where A(t) = ‖ω(t)‖_{B⁰_{∞,1}} and C_par is a universal constant.

**Description:** From MATHEMATICAL_APPENDICES.md, line 386

**Category:** general

---

### MATHEMATICAL_APPENDICES_389
**Formula:** 1. Vorticity equation: ∂_t ω + u·∇ω = ω·∇u + ν Δω

**Description:** From MATHEMATICAL_APPENDICES.md, line 389

**Category:** physical

---

### MATHEMATICAL_APPENDICES_390
**Formula:** 2. Apply Littlewood-Paley projection Δ_j

**Description:** From MATHEMATICAL_APPENDICES.md, line 390

**Category:** general

---

### MATHEMATICAL_APPENDICES_391
**Formula:** 3. High-frequency regime: dissipation -ν·2^{2j} dominates nonlinear term

**Description:** From MATHEMATICAL_APPENDICES.md, line 391

**Category:** physical

---

### MATHEMATICAL_APPENDICES_392
**Formula:** 4. Stretching estimate: |⟨Δ_j(ω·∇u), Δ_j ω⟩| ≤ C_par · A(t) · ‖Δ_j ω‖²_{L²}

**Description:** From MATHEMATICAL_APPENDICES.md, line 392

**Category:** estimate

---

### MATHEMATICAL_APPENDICES_393
**Formula:** 5. For j ≥ j_d, the factor ν·2^{2j}/2 exceeds any growth from C_par·A(t)

**Description:** From MATHEMATICAL_APPENDICES.md, line 393

**Category:** physical

---

### MATHEMATICAL_APPENDICES_398
**Formula:** Summing over j ≥ j_d and using Bony paraproduct analysis:

**Description:** From MATHEMATICAL_APPENDICES.md, line 398

**Category:** general

---

### MATHEMATICAL_APPENDICES_400
**Formula:** d/dt A ≤ -ν c_star A² + C_str A² + C₀

**Description:** From MATHEMATICAL_APPENDICES.md, line 400

**Category:** physical

---

### MATHEMATICAL_APPENDICES_403
**Formula:** with c_star > 0 universal. Then Grönwall-Osgood yields:

**Description:** From MATHEMATICAL_APPENDICES.md, line 403

**Category:** general

---

### MATHEMATICAL_APPENDICES_405
**Formula:** ∫₀^T A(t) dt < ∞

**Description:** From MATHEMATICAL_APPENDICES.md, line 405

**Category:** general

---

### MATHEMATICAL_APPENDICES_409
**Formula:** 1. Define A(t) := ‖ω(t)‖_{B⁰_{∞,1}} = Σ_j ‖Δ_j ω‖_{L∞}

**Description:** From MATHEMATICAL_APPENDICES.md, line 409

**Category:** general

---

### MATHEMATICAL_APPENDICES_410
**Formula:** 2. Dyadic coercivity from NBB lemma: Σ_j 2^{2j}‖Δ_j ω‖_{L∞} ≥ c_star A² - C_star ‖ω‖²_{L²}

**Description:** From MATHEMATICAL_APPENDICES.md, line 410

**Category:** general

---

### MATHEMATICAL_APPENDICES_411
**Formula:** 3. Stretching bound: ‖(ω·∇)u‖_{B⁰_{∞,1}} ≤ C_str A²

**Description:** From MATHEMATICAL_APPENDICES.md, line 411

**Category:** general

---

### MATHEMATICAL_APPENDICES_413
**Formula:** 5. Osgood lemma: solutions to dX/dt ≤ -aX² + bX² + c with a > 0 satisfy ∫₀^T X(t)dt < ∞

**Description:** From MATHEMATICAL_APPENDICES.md, line 413

**Category:** general

---

### MATHEMATICAL_APPENDICES_419
**Formula:** ∫₀^T A(t) dt < ∞  ⟹  ∫₀^T ‖∇u‖_{L∞} dt ≤ C_CZ ∫₀^T A(t) dt < ∞

**Description:** From MATHEMATICAL_APPENDICES.md, line 419

**Category:** general

---

### MATHEMATICAL_APPENDICES_422
**Formula:** **Proof**: Direct consequence of the critical Besov pair ‖∇u‖_{L∞} ≤ C_CZ ‖ω‖_{B⁰_{∞,1}}.

**Description:** From MATHEMATICAL_APPENDICES.md, line 422

**Category:** general

---

### MATHEMATICAL_APPENDICES_427
**Formula:** If ∫₀^T ‖∇u‖_{L∞} dt < ∞, then u ∈ L^∞_t L³_x and the solution is smooth on (0,T].

**Description:** From MATHEMATICAL_APPENDICES.md, line 427

**Category:** general

---

### MATHEMATICAL_APPENDICES_430
**Formula:** 1. Differential inequality: d/dt ‖u‖³_{L³} ≤ C ‖∇u‖_{L∞} ‖u‖³_{L³}

**Description:** From MATHEMATICAL_APPENDICES.md, line 430

**Category:** estimate

---

### MATHEMATICAL_APPENDICES_431
**Formula:** 2. Grönwall: ‖u(T)‖_{L³} ≤ ‖u₀‖_{L³} exp(C ∫₀^T ‖∇u‖_{L∞} dt)

**Description:** From MATHEMATICAL_APPENDICES.md, line 431

**Category:** general

---

### MATHEMATICAL_APPENDICES_432
**Formula:** 3. Since the integral is finite, u ∈ L^∞_t L³_x

**Description:** From MATHEMATICAL_APPENDICES.md, line 432

**Category:** general

---

### MATHEMATICAL_APPENDICES_433
**Formula:** 4. Serrin endpoint criterion (p=∞, q=3 with 2/p + 3/q = 1) implies regularity

**Description:** From MATHEMATICAL_APPENDICES.md, line 433

**Category:** criterion

---

### MATHEMATICAL_APPENDICES_435
**Formula:** **Remark**: The route F.A-F.D does not assume any sign condition on γ_avg and is independent of (f₀, ε). This provides an unconditional backup when direct Riccati damping is not favorable.

**Description:** From MATHEMATICAL_APPENDICES.md, line 435

**Category:** estimate

---

### MATHEMATICAL_APPENDICES_443
**Formula:** u(x,t) = ∑_k û_k(t) e^{ik·x}

**Description:** From MATHEMATICAL_APPENDICES.md, line 443

**Category:** general

---

### MATHEMATICAL_APPENDICES_448
**Formula:** dû_k/dt = -ν|k|² û_k + N̂_k(u)

**Description:** From MATHEMATICAL_APPENDICES.md, line 448

**Category:** physical

---

### MATHEMATICAL_APPENDICES_456
**Formula:** k₁ = F(û_n)

**Description:** From MATHEMATICAL_APPENDICES.md, line 456

**Category:** general

---

### MATHEMATICAL_APPENDICES_457
**Formula:** k₂ = F(û_n + Δt·k₁/2)

**Description:** From MATHEMATICAL_APPENDICES.md, line 457

**Category:** general

---

### MATHEMATICAL_APPENDICES_458
**Formula:** k₃ = F(û_n + Δt·k₂/2)

**Description:** From MATHEMATICAL_APPENDICES.md, line 458

**Category:** general

---

### MATHEMATICAL_APPENDICES_459
**Formula:** k₄ = F(û_n + Δt·k₃)

**Description:** From MATHEMATICAL_APPENDICES.md, line 459

**Category:** general

---

### MATHEMATICAL_APPENDICES_460
**Formula:** û_{n+1} = û_n + Δt(k₁ + 2k₂ + 2k₃ + k₄)/6

**Description:** From MATHEMATICAL_APPENDICES.md, line 460

**Category:** general

---

### MATHEMATICAL_APPENDICES_466
**Formula:** Zero out Fourier modes with |k| > 2N/3 before computing nonlinear term.

**Description:** From MATHEMATICAL_APPENDICES.md, line 466

**Category:** general

---

### MATHEMATICAL_APPENDICES_474
**Formula:** N ≥ 2^{j_d + 2} · Re^{3/4}

**Description:** From MATHEMATICAL_APPENDICES.md, line 474

**Category:** general

---

### MATHEMATICAL_APPENDICES_477
**Formula:** **Example**: Re = 1000, j_d = 8 requires N ≥ 256³

**Description:** From MATHEMATICAL_APPENDICES.md, line 477

**Category:** general

---

### MATHEMATICAL_APPENDICES_486
**Formula:** 2. **What is Γ and why is the threshold Γ < 1 (not Γ < 0.5)?**

**Description:** From MATHEMATICAL_APPENDICES.md, line 486

**Category:** general

---

### MATHEMATICAL_APPENDICES_487
**Formula:** 3. **How to avoid circularity when ‖U(t)‖_∞ may grow?**

**Description:** From MATHEMATICAL_APPENDICES.md, line 487

**Category:** general

---

### MATHEMATICAL_APPENDICES_496
**Formula:** L₀ := -ν Δ_y + c(y),    y ∈ Y = T^d

**Description:** From MATHEMATICAL_APPENDICES.md, line 496

**Category:** physical

---

### MATHEMATICAL_APPENDICES_500
**Formula:** - **c(y) ≥ c₀ > 0**: A positive potential ensuring coercivity

**Description:** From MATHEMATICAL_APPENDICES.md, line 500

**Category:** general

---

### MATHEMATICAL_APPENDICES_505
**Formula:** 1. **Fixed spectral gap**: L₀ has a gap c₀ > 0 independent of the flow

**Description:** From MATHEMATICAL_APPENDICES.md, line 505

**Category:** general

---

### MATHEMATICAL_APPENDICES_516
**Formula:** L₁(t) := Q(U(x,t)·∇_x)Q + two-scale coupling terms

**Description:** From MATHEMATICAL_APPENDICES.md, line 516

**Category:** general

---

### MATHEMATICAL_APPENDICES_519
**Formula:** where U(x,t) = u₀ is the macroscopic velocity field.

**Description:** From MATHEMATICAL_APPENDICES.md, line 519

**Category:** general

---

### MATHEMATICAL_APPENDICES_521
**Formula:** **Key Point**: All dependence on u₀ = U is in L₁(t), not in L₀. This separation ensures:

**Description:** From MATHEMATICAL_APPENDICES.md, line 521

**Category:** general

---

### MATHEMATICAL_APPENDICES_531
**Formula:** Γ(t) := ‖Q L₁(t) Q L₀⁻¹‖_{L² → L²}

**Description:** From MATHEMATICAL_APPENDICES.md, line 531

**Category:** general

---

### MATHEMATICAL_APPENDICES_540
**Formula:** - Γ(t) < 1 ensures invertibility via Neumann series

**Description:** From MATHEMATICAL_APPENDICES.md, line 540

**Category:** general

---

### MATHEMATICAL_APPENDICES_549
**Formula:** B(t) = Q(U(t)·∇)Q

**Description:** From MATHEMATICAL_APPENDICES.md, line 549

**Category:** general

---

### MATHEMATICAL_APPENDICES_552
**Formula:** In a periodic domain with ∇·U = 0 (divergence-free), **B(t) is anti-self-adjoint** in L²:

**Description:** From MATHEMATICAL_APPENDICES.md, line 552

**Category:** general

---

### MATHEMATICAL_APPENDICES_555
**Formula:** ⟨B v, v⟩ = 0

**Description:** From MATHEMATICAL_APPENDICES.md, line 555

**Category:** general

---

### MATHEMATICAL_APPENDICES_558
**Formula:** **Proof**: Integration by parts with periodicity and ∇·U = 0 yields:

**Description:** From MATHEMATICAL_APPENDICES.md, line 558

**Category:** general

---

### MATHEMATICAL_APPENDICES_560
**Formula:** ⟨(U·∇)v, v⟩ = -⟨v, (U·∇)v⟩ - ⟨(∇·U)v, v⟩ = -⟨(U·∇)v, v⟩

**Description:** From MATHEMATICAL_APPENDICES.md, line 560

**Category:** general

---

### MATHEMATICAL_APPENDICES_562
**Formula:** Thus ⟨(U·∇)v, v⟩ = 0.

**Description:** From MATHEMATICAL_APPENDICES.md, line 562

**Category:** general

---

### MATHEMATICAL_APPENDICES_569
**Formula:** Re⟨(L₀ + B)v, v⟩ = Re⟨L₀v, v⟩ = ν‖∇v‖²₂ + ⟨cv, v⟩ ≥ c₀‖v‖²₂

**Description:** From MATHEMATICAL_APPENDICES.md, line 569

**Category:** physical

---

### MATHEMATICAL_APPENDICES_575
**Formula:** ‖(L₀ + B(t))⁻¹‖_{L² → L²} ≤ 1/c₀

**Description:** From MATHEMATICAL_APPENDICES.md, line 575

**Category:** general

---

### MATHEMATICAL_APPENDICES_578
**Formula:** **independent of the size of ‖U(t)‖_∞**.

**Description:** From MATHEMATICAL_APPENDICES.md, line 578

**Category:** general

---

### MATHEMATICAL_APPENDICES_580
**Formula:** ### 13.4.5 Threshold Analysis: Γ < 1, Not Γ < 1/2

**Description:** From MATHEMATICAL_APPENDICES.md, line 580

**Category:** general

---

### MATHEMATICAL_APPENDICES_582
**Formula:** #### Why Γ < 1/2 Was Sufficient But Not Necessary

**Description:** From MATHEMATICAL_APPENDICES.md, line 582

**Category:** general

---

### MATHEMATICAL_APPENDICES_584
**Formula:** The condition Γ(t) < 1/2 was sufficient for invertibility via standard perturbation theory, but it is **not necessary**.

**Description:** From MATHEMATICAL_APPENDICES.md, line 584

**Category:** general

---

### MATHEMATICAL_APPENDICES_586
**Formula:** #### The Correct Threshold: Γ < 1

**Description:** From MATHEMATICAL_APPENDICES.md, line 586

**Category:** general

---

### MATHEMATICAL_APPENDICES_588
**Formula:** **Moral**: You do not need Γ(t) < 1/2 for a priori invertibility; that condition was sufficient but not necessary.

**Description:** From MATHEMATICAL_APPENDICES.md, line 588

**Category:** general

---

### MATHEMATICAL_APPENDICES_590
**Formula:** For the pure convective case (∇·U = 0), the anti-self-adjoint structure means:

**Description:** From MATHEMATICAL_APPENDICES.md, line 590

**Category:** general

---

### MATHEMATICAL_APPENDICES_592
**Formula:** - Coercivity is maintained regardless of ‖U(t)‖_∞

**Description:** From MATHEMATICAL_APPENDICES.md, line 592

**Category:** general

---

### MATHEMATICAL_APPENDICES_598
**Formula:** Γ(t) < 1

**Description:** From MATHEMATICAL_APPENDICES.md, line 598

**Category:** general

---

### MATHEMATICAL_APPENDICES_604
**Formula:** (I + Q L₁ Q L₀⁻¹)⁻¹ = ∑_{k≥0} (-Q L₁ Q L₀⁻¹)^k

**Description:** From MATHEMATICAL_APPENDICES.md, line 604

**Category:** general

---

### MATHEMATICAL_APPENDICES_607
**Formula:** The series converges when ‖Q L₁ Q L₀⁻¹‖ < 1, i.e., when Γ(t) < 1.

**Description:** From MATHEMATICAL_APPENDICES.md, line 607

**Category:** general

---

### MATHEMATICAL_APPENDICES_615
**Formula:** 1. **Coercivity/Base Structure**: Provided by L₀ (microscopic, fixed, with c₀ > 0)

**Description:** From MATHEMATICAL_APPENDICES.md, line 615

**Category:** general

---

### MATHEMATICAL_APPENDICES_618
**Formula:** Since coercivity does not depend on U, it does not collapse even if ‖U(t)‖_∞ grows.

**Description:** From MATHEMATICAL_APPENDICES.md, line 618

**Category:** general

---

### MATHEMATICAL_APPENDICES_625
**Formula:** - Growth of ‖U(t)‖_∞ does not affect the resolvent bound

**Description:** From MATHEMATICAL_APPENDICES.md, line 625

**Category:** general

---

### MATHEMATICAL_APPENDICES_630
**Formula:** sup_{t∈[0,T]} Γ(t) < 1

**Description:** From MATHEMATICAL_APPENDICES.md, line 630

**Category:** general

---

### MATHEMATICAL_APPENDICES_634
**Formula:** - Relative smallness (e.g., coupling scaled by ε)

**Description:** From MATHEMATICAL_APPENDICES.md, line 634

**Category:** general

---

### MATHEMATICAL_APPENDICES_635
**Formula:** - Control via Kato norm estimates with large ν

**Description:** From MATHEMATICAL_APPENDICES.md, line 635

**Category:** estimate

---

### MATHEMATICAL_APPENDICES_646
**Formula:** L₀ = -ν Δ_y + c(y)    with c₀ > 0

**Description:** From MATHEMATICAL_APPENDICES.md, line 646

**Category:** physical

---

### MATHEMATICAL_APPENDICES_651
**Formula:** L₁(t) = Q(U(x,t)·∇_x)Q + two-scale coupling terms

**Description:** From MATHEMATICAL_APPENDICES.md, line 651

**Category:** general

---

### MATHEMATICAL_APPENDICES_656
**Formula:** Γ(t) = ‖Q L₁(t) Q L₀⁻¹‖_{2→2}

**Description:** From MATHEMATICAL_APPENDICES.md, line 656

**Category:** general

---

### MATHEMATICAL_APPENDICES_659
**Formula:** 4. **Case 1: Pure Convection with ∇·U = 0**

**Description:** From MATHEMATICAL_APPENDICES.md, line 659

**Category:** general

---

### MATHEMATICAL_APPENDICES_661
**Formula:** - Resolvent bound: ‖(L₀ + L₁(t))⁻¹‖_{2→2} ≤ 1/c₀

**Description:** From MATHEMATICAL_APPENDICES.md, line 661

**Category:** general

---

### MATHEMATICAL_APPENDICES_665
**Formula:** - Require sup_t Γ(t) < 1 (not 1/2)

**Description:** From MATHEMATICAL_APPENDICES.md, line 665

**Category:** general

---

### MATHEMATICAL_APPENDICES_675
**Formula:** 3. **Correct threshold**: The "0.5" threshold was a sufficient artifact; the correct bound is "< 1" when smallness is needed

**Description:** From MATHEMATICAL_APPENDICES.md, line 675

**Category:** general

---

### MATHEMATICAL_APPENDICES_681
**Formula:** Under the two-scale decomposition L = L₀ + L₁(t) with:

**Description:** From MATHEMATICAL_APPENDICES.md, line 681

**Category:** general

---

### MATHEMATICAL_APPENDICES_682
**Formula:** - L₀ = -ν Δ_y + c(y) satisfying Re⟨L₀v,v⟩ ≥ c₀‖v‖²

**Description:** From MATHEMATICAL_APPENDICES.md, line 682

**Category:** physical

---

### MATHEMATICAL_APPENDICES_683
**Formula:** - L₁(t) = Q(U·∇)Q with ∇·U = 0

**Description:** From MATHEMATICAL_APPENDICES.md, line 683

**Category:** general

---

### MATHEMATICAL_APPENDICES_687
**Formula:** ‖(L₀ + L₁(t))⁻¹‖ ≤ 1/c₀

**Description:** From MATHEMATICAL_APPENDICES.md, line 687

**Category:** general

---

### MATHEMATICAL_APPENDICES_689
**Formula:** uniformly in t, independent of ‖U(t)‖_∞.

**Description:** From MATHEMATICAL_APPENDICES.md, line 689

**Category:** general

---

### MATHEMATICAL_APPENDICES_691
**Formula:** **Proof**: Follows from sectoriality and anti-self-adjointness of Q(U·∇)Q. □

**Description:** From MATHEMATICAL_APPENDICES.md, line 691

**Category:** general

---

### MATHEMATICAL_APPENDICES_694
**Formula:** If L₁ contains non-anti-self-adjoint terms with Γ(t) := ‖Q L₁ Q L₀⁻¹‖ < 1, then:

**Description:** From MATHEMATICAL_APPENDICES.md, line 694

**Category:** general

---

### MATHEMATICAL_APPENDICES_696
**Formula:** ‖(L₀ + L₁)⁻¹‖ ≤ (1/c₀) · 1/(1 - Γ)

**Description:** From MATHEMATICAL_APPENDICES.md, line 696

**Category:** general

---

### MATHEMATICAL_APPENDICES_699
**Formula:** **Proof**: Neumann series (I + QL₁QL₀⁻¹)⁻¹ = ∑_{k≥0}(-QL₁QL₀⁻¹)^k converges when Γ < 1. □

**Description:** From MATHEMATICAL_APPENDICES.md, line 699

**Category:** general

---

### HYBRID_BKM_CLOSURE_4
**Formula:** This document describes the **hybrid approach** to closing the BKM (Beale-Kato-Majda) criterion for 3D Navier-Stokes equations without unrealistically inflating the misalignment parameter δ₀.

**Description:** From HYBRID_BKM_CLOSURE.md, line 4

**Category:** fundamental

---

### HYBRID_BKM_CLOSURE_9
**Formula:** 2. **Time-averaged misalignment** (δ̄₀ instead of pointwise δ₀)

**Description:** From HYBRID_BKM_CLOSURE.md, line 9

**Category:** general

---

### HYBRID_BKM_CLOSURE_17
**Formula:** Replace all gradient estimates ‖∇u‖_L∞ ≤ C‖ω‖_L∞ with the rigorous pair:

**Description:** From HYBRID_BKM_CLOSURE.md, line 17

**Category:** estimate

---

### HYBRID_BKM_CLOSURE_20
**Formula:** ‖∇u‖_L∞ ≤ C_CZ ‖ω‖_{B⁰_{∞,1}}

**Description:** From HYBRID_BKM_CLOSURE.md, line 20

**Category:** general

---

### HYBRID_BKM_CLOSURE_21
**Formula:** ‖ω‖_{B⁰_{∞,1}} ≤ C_⋆ ‖ω‖_L∞

**Description:** From HYBRID_BKM_CLOSURE.md, line 21

**Category:** general

---

### HYBRID_BKM_CLOSURE_25
**Formula:** - C_CZ = 2.0 (Calderón-Zygmund/Besov constant)

**Description:** From HYBRID_BKM_CLOSURE.md, line 25

**Category:** general

---

### HYBRID_BKM_CLOSURE_26
**Formula:** - C_⋆ = 1.5 (Besov embedding constant)

**Description:** From HYBRID_BKM_CLOSURE.md, line 26

**Category:** general

---

### HYBRID_BKM_CLOSURE_28
**Formula:** This provides rigorous control throughout §5 and maintains uniformity in ε.

**Description:** From HYBRID_BKM_CLOSURE.md, line 28

**Category:** general

---

### HYBRID_BKM_CLOSURE_30
**Formula:** ### 2. Time-Averaged Misalignment (δ̄₀)

**Description:** From HYBRID_BKM_CLOSURE.md, line 30

**Category:** general

---

### HYBRID_BKM_CLOSURE_32
**Formula:** Instead of using pointwise δ₀(t), use the temporal average:

**Description:** From HYBRID_BKM_CLOSURE.md, line 32

**Category:** general

---

### HYBRID_BKM_CLOSURE_35
**Formula:** δ̄₀(T) := (1/T) ∫₀ᵀ δ₀(t) dt

**Description:** From HYBRID_BKM_CLOSURE.md, line 35

**Category:** general

---

### HYBRID_BKM_CLOSURE_41
**Formula:** δ₀(t) = A(t)²|∇φ|²/(4π²f₀²) + O(f₀⁻³)

**Description:** From HYBRID_BKM_CLOSURE.md, line 41

**Category:** general

---

### HYBRID_BKM_CLOSURE_44
**Formula:** **Key advantage:** By averaging over oscillations in A(t), we obtain a larger effective δ̄₀ without artificially inflating instantaneous values.

**Description:** From HYBRID_BKM_CLOSURE.md, line 44

**Category:** general

---

### HYBRID_BKM_CLOSURE_50
**Formula:** │  νc_Bern > (1 - δ̄₀) C_CZ C_⋆    (⋆)   │

**Description:** From HYBRID_BKM_CLOSURE.md, line 50

**Category:** physical

---

### HYBRID_BKM_CLOSURE_58
**Formula:** The dyadic Riccati inequality in B⁰_{∞,1}:

**Description:** From HYBRID_BKM_CLOSURE.md, line 58

**Category:** estimate

---

### HYBRID_BKM_CLOSURE_61
**Formula:** d/dt ‖ω‖_{B⁰_{∞,1}} ≤ -νc_∗ ‖ω‖²_{B⁰_{∞,1}} + C_str ‖ω‖²_{B⁰_{∞,1}} + C₀

**Description:** From HYBRID_BKM_CLOSURE.md, line 61

**Category:** physical

---

### HYBRID_BKM_CLOSURE_65
**Formula:** - νc_∗: Parabolic coercivity term (dissipative)

**Description:** From HYBRID_BKM_CLOSURE.md, line 65

**Category:** physical

---

### HYBRID_BKM_CLOSURE_66
**Formula:** - C_str: Vorticity stretching constant (amplifying)

**Description:** From HYBRID_BKM_CLOSURE.md, line 66

**Category:** general

---

### HYBRID_BKM_CLOSURE_67
**Formula:** - C₀: Subcritical forcing from L²/H^s energies

**Description:** From HYBRID_BKM_CLOSURE.md, line 67

**Category:** general

---

### HYBRID_BKM_CLOSURE_73
**Formula:** │  νc_∗ > C_str    │

**Description:** From HYBRID_BKM_CLOSURE.md, line 73

**Category:** physical

---

### HYBRID_BKM_CLOSURE_80
**Formula:** ∫₀ᵀ ‖ω‖_{B⁰_{∞,1}} dt < ∞  ⟹  ∫₀ᵀ ‖∇u‖_L∞ dt < ∞

**Description:** From HYBRID_BKM_CLOSURE.md, line 80

**Category:** general

---

### HYBRID_BKM_CLOSURE_86
**Formula:** - c_∗ = 1/16 (parabolic coercivity coefficient)

**Description:** From HYBRID_BKM_CLOSURE.md, line 86

**Category:** general

---

### HYBRID_BKM_CLOSURE_87
**Formula:** - C_str = 32.0 (vorticity stretching constant)

**Description:** From HYBRID_BKM_CLOSURE.md, line 87

**Category:** general

---

### HYBRID_BKM_CLOSURE_89
**Formula:** **How to ensure νc_∗ > C_str:**

**Description:** From HYBRID_BKM_CLOSURE.md, line 89

**Category:** physical

---

### HYBRID_BKM_CLOSURE_91
**Formula:** 1. **Reduce stretching (C_str):** The misalignment defect δ₀ reduces vorticity stretching

**Description:** From HYBRID_BKM_CLOSURE.md, line 91

**Category:** general

---

### HYBRID_BKM_CLOSURE_99
**Formula:** ‖∇u‖_L∞ ≲ ‖ω‖_BMO (1 + log⁺(‖ω‖_H^s / ‖ω‖_BMO))

**Description:** From HYBRID_BKM_CLOSURE.md, line 99

**Category:** general

---

### HYBRID_BKM_CLOSURE_102
**Formula:** **Key insight:** With δ₀ control on high-frequency tails:

**Description:** From HYBRID_BKM_CLOSURE.md, line 102

**Category:** general

---

### HYBRID_BKM_CLOSURE_105
**Formula:** ‖ω‖_H^s / ‖ω‖_BMO ≤ C

**Description:** From HYBRID_BKM_CLOSURE.md, line 105

**Category:** general

---

### HYBRID_BKM_CLOSURE_108
**Formula:** This makes the logarithmic term **uniformly bounded**, recovering a Riccati inequality with improved constants (better than C_CZ · C_⋆).

**Description:** From HYBRID_BKM_CLOSURE.md, line 108

**Category:** estimate

---

### HYBRID_BKM_CLOSURE_114
**Formula:** Let u be a solution to 3D Navier-Stokes with ν > 0, ω = ∇×u. Assume:

**Description:** From HYBRID_BKM_CLOSURE.md, line 114

**Category:** fundamental

---

### HYBRID_BKM_CLOSURE_118
**Formula:** ‖∇u‖_L∞ ≤ C_CZ ‖ω‖_{B⁰_{∞,1}}

**Description:** From HYBRID_BKM_CLOSURE.md, line 118

**Category:** general

---

### HYBRID_BKM_CLOSURE_119
**Formula:** ‖ω‖_{B⁰_{∞,1}} ≤ C_⋆ ‖ω‖_L∞

**Description:** From HYBRID_BKM_CLOSURE.md, line 119

**Category:** general

---

### HYBRID_BKM_CLOSURE_121
**Formula:** (uniform in ε)

**Description:** From HYBRID_BKM_CLOSURE.md, line 121

**Category:** general

---

### HYBRID_BKM_CLOSURE_125
**Formula:** δ̄₀(T) = (1/T) ∫₀ᵀ δ₀(t) dt

**Description:** From HYBRID_BKM_CLOSURE.md, line 125

**Category:** general

---

### HYBRID_BKM_CLOSURE_127
**Formula:** where δ₀(t) = A(t)²|∇φ|²/(4π²f₀²) + O(f₀⁻³)

**Description:** From HYBRID_BKM_CLOSURE.md, line 127

**Category:** general

---

### HYBRID_BKM_CLOSURE_131
**Formula:** νc_∗ > C_str

**Description:** From HYBRID_BKM_CLOSURE.md, line 131

**Category:** physical

---

### HYBRID_BKM_CLOSURE_133
**Formula:** in dyadic balance of B⁰_{∞,1}

**Description:** From HYBRID_BKM_CLOSURE.md, line 133

**Category:** general

---

### HYBRID_BKM_CLOSURE_140
**Formula:** │  δ̄₀ > 1 - νc_Bern/(C_CZ C_⋆)    (⋆)   │

**Description:** From HYBRID_BKM_CLOSURE.md, line 140

**Category:** physical

---

### HYBRID_BKM_CLOSURE_144
**Formula:** —OR if **νc_∗ > C_str** alone—

**Description:** From HYBRID_BKM_CLOSURE.md, line 144

**Category:** physical

---

### HYBRID_BKM_CLOSURE_148
**Formula:** ∫₀ᵀ ‖ω(t)‖_L∞ dt < ∞

**Description:** From HYBRID_BKM_CLOSURE.md, line 148

**Category:** general

---

### HYBRID_BKM_CLOSURE_153
**Formula:** **Commentary:** The criterion (⋆) uses δ̄₀ (not instantaneous δ₀). The Besov route provides alternative closure independent of logarithmic terms.

**Description:** From HYBRID_BKM_CLOSURE.md, line 153

**Category:** criterion

---

### HYBRID_BKM_CLOSURE_162
**Formula:** Λ(t) = Λ₀ · (1 + α·oscillatory_phase(t))

**Description:** From HYBRID_BKM_CLOSURE.md, line 162

**Category:** general

---

### HYBRID_BKM_CLOSURE_167
**Formula:** ### 2. Reduce C_CZ C_⋆

**Description:** From HYBRID_BKM_CLOSURE.md, line 167

**Category:** general

---

### HYBRID_BKM_CLOSURE_169
**Formula:** Work with BMO/inhomogeneous Besov spaces at low frequencies. The logarithmic factor is bounded by H^s control via δ₀.

**Description:** From HYBRID_BKM_CLOSURE.md, line 169

**Category:** general

---

### HYBRID_BKM_CLOSURE_173
**Formula:** The realistic time average A̅² can be several times larger than the minimum instantaneous value, improving δ̄₀:

**Description:** From HYBRID_BKM_CLOSURE.md, line 173

**Category:** general

---

### HYBRID_BKM_CLOSURE_176
**Formula:** A̅² = (1/T) ∫₀ᵀ A(t)² dt

**Description:** From HYBRID_BKM_CLOSURE.md, line 176

**Category:** general

---

### HYBRID_BKM_CLOSURE_184
**Formula:** ν_eff > ν

**Description:** From HYBRID_BKM_CLOSURE.md, line 184

**Category:** physical

---

### HYBRID_BKM_CLOSURE_196
**Formula:** - Computes δ̄₀(T) from time-dependent δ₀(t)

**Description:** From HYBRID_BKM_CLOSURE.md, line 196

**Category:** general

---

### HYBRID_BKM_CLOSURE_200
**Formula:** - Verifies Gap-avg: νc_Bern > (1-δ̄₀)C_CZ·C_⋆

**Description:** From HYBRID_BKM_CLOSURE.md, line 200

**Category:** physical

---

### HYBRID_BKM_CLOSURE_208
**Formula:** - Verifies Parab-crit: νc_∗ > C_str

**Description:** From HYBRID_BKM_CLOSURE.md, line 208

**Category:** physical

---

### HYBRID_BKM_CLOSURE_213
**Formula:** - Returns improved constants vs. standard C_CZ·C_⋆

**Description:** From HYBRID_BKM_CLOSURE.md, line 213

**Category:** general

---

### HYBRID_BKM_CLOSURE_225
**Formula:** proof = FinalProof(ν=1e-3, δ_star=1/(4*np.pi**2), f0=141.7)

**Description:** From HYBRID_BKM_CLOSURE.md, line 225

**Category:** physical

---

### HYBRID_BKM_CLOSURE_228
**Formula:** results = proof.prove_hybrid_bkm_closure(

**Description:** From HYBRID_BKM_CLOSURE.md, line 228

**Category:** criterion

---

### HYBRID_BKM_CLOSURE_229
**Formula:** T_max=100.0,

**Description:** From HYBRID_BKM_CLOSURE.md, line 229

**Category:** general

---

### HYBRID_BKM_CLOSURE_230
**Formula:** X0=10.0,

**Description:** From HYBRID_BKM_CLOSURE.md, line 230

**Category:** general

---

### HYBRID_BKM_CLOSURE_231
**Formula:** u0_L3_norm=1.0,

**Description:** From HYBRID_BKM_CLOSURE.md, line 231

**Category:** general

---

### HYBRID_BKM_CLOSURE_232
**Formula:** verbose=True

**Description:** From HYBRID_BKM_CLOSURE.md, line 232

**Category:** general

---

### HYBRID_BKM_CLOSURE_246
**Formula:** νc_∗ = 0.000063

**Description:** From HYBRID_BKM_CLOSURE.md, line 246

**Category:** physical

---

### HYBRID_BKM_CLOSURE_247
**Formula:** C_str = 32.000000

**Description:** From HYBRID_BKM_CLOSURE.md, line 247

**Category:** general

---

### HYBRID_BKM_CLOSURE_248
**Formula:** Gap = -31.999938

**Description:** From HYBRID_BKM_CLOSURE.md, line 248

**Category:** general

---

### HYBRID_BKM_CLOSURE_249
**Formula:** Status: ✗ NOT SATISFIED (needs higher ν or lower C_str)

**Description:** From HYBRID_BKM_CLOSURE.md, line 249

**Category:** physical

---

### HYBRID_BKM_CLOSURE_252
**Formula:** δ̄₀(T=100) = 0.999000

**Description:** From HYBRID_BKM_CLOSURE.md, line 252

**Category:** general

---

### HYBRID_BKM_CLOSURE_253
**Formula:** Gap = -0.002900

**Description:** From HYBRID_BKM_CLOSURE.md, line 253

**Category:** general

---

### HYBRID_BKM_CLOSURE_254
**Formula:** Status: ✗ NOT SATISFIED (needs higher δ̄₀ or lower C_CZ·C_⋆)

**Description:** From HYBRID_BKM_CLOSURE.md, line 254

**Category:** general

---

### HYBRID_BKM_CLOSURE_257
**Formula:** log⁺(ratio) = 0.405465

**Description:** From HYBRID_BKM_CLOSURE.md, line 257

**Category:** general

---

### HYBRID_BKM_CLOSURE_258
**Formula:** Improved constant = 1.405465 (vs. standard 3.000000)

**Description:** From HYBRID_BKM_CLOSURE.md, line 258

**Category:** general

---

### HYBRID_BKM_CLOSURE_269
**Formula:** - [x] **Dyadic lemma with Λ(t)** demonstrating uniform bounds in ε

**Description:** From HYBRID_BKM_CLOSURE.md, line 269

**Category:** general

---

### HYBRID_BKM_CLOSURE_270
**Formula:** - [x] **Time-averaged δ̄₀** connected to A̅² and f₀

**Description:** From HYBRID_BKM_CLOSURE.md, line 270

**Category:** general

---

### HYBRID_BKM_CLOSURE_272
**Formula:** - [x] **H^s control** via δ₀ fixing the log term

**Description:** From HYBRID_BKM_CLOSURE.md, line 272

**Category:** general

---

### HYBRID_BKM_CLOSURE_284
**Formula:** ### Proposition 2: BMO/Inhomogeneous Besov Reduces C_CZ C_⋆

**Description:** From HYBRID_BKM_CLOSURE.md, line 284

**Category:** general

---

### HYBRID_BKM_CLOSURE_286
**Formula:** **Statement:** Working in BMO ∩ B⁰_{∞,1} at low frequencies reduces the effective product C_CZ · C_⋆.

**Description:** From HYBRID_BKM_CLOSURE.md, line 286

**Category:** general

---

### HYBRID_BKM_CLOSURE_288
**Formula:** **Proof sketch:** The logarithmic term log⁺(‖ω‖_H^s/‖ω‖_BMO) is bounded by δ₀ control. This gives an improved constant c_improved < C_CZ · C_⋆.

**Description:** From HYBRID_BKM_CLOSURE.md, line 288

**Category:** general

---

### HYBRID_BKM_CLOSURE_290
**Formula:** ### Proposition 3: Oscillatory Forcing Increases ν_eff

**Description:** From HYBRID_BKM_CLOSURE.md, line 290

**Category:** physical

---

### HYBRID_BKM_CLOSURE_292
**Formula:** **Statement:** Forcing at frequency f₀ induces effective dissipation ν_eff > ν through averaging effects.

**Description:** From HYBRID_BKM_CLOSURE.md, line 292

**Category:** physical

---

### HYBRID_BKM_CLOSURE_308
**Formula:** 1. **Gap-avg:** Time-averaged misalignment (realistic δ̄₀)

**Description:** From HYBRID_BKM_CLOSURE.md, line 308

**Category:** general

---

### UNIFIED_FRAMEWORK_13
**Formula:** ∂u/∂t + (u·∇)u - ν∆u + ∇p = ε∇Φ(x, 2πf₀t)

**Description:** From UNIFIED_FRAMEWORK.md, line 13

**Category:** physical

---

### UNIFIED_FRAMEWORK_14
**Formula:** ∇·u = 0

**Description:** From UNIFIED_FRAMEWORK.md, line 14

**Category:** general

---

### UNIFIED_FRAMEWORK_19
**Formula:** - `ν`: kinematic viscosity

**Description:** From UNIFIED_FRAMEWORK.md, line 19

**Category:** physical

---

### UNIFIED_FRAMEWORK_20
**Formula:** - `ε∇Φ`: oscillatory forcing term

**Description:** From UNIFIED_FRAMEWORK.md, line 20

**Category:** general

---

### UNIFIED_FRAMEWORK_28
**Formula:** ε = λ·f₀^(-α)    (forcing amplitude)

**Description:** From UNIFIED_FRAMEWORK.md, line 28

**Category:** general

---

### UNIFIED_FRAMEWORK_29
**Formula:** A = a·f₀         (oscillation amplitude)

**Description:** From UNIFIED_FRAMEWORK.md, line 29

**Category:** general

---

### UNIFIED_FRAMEWORK_30
**Formula:** α > 1            (super-critical scaling)

**Description:** From UNIFIED_FRAMEWORK.md, line 30

**Category:** general

---

### UNIFIED_FRAMEWORK_33
**Formula:** As `f₀ → ∞`:

**Description:** From UNIFIED_FRAMEWORK.md, line 33

**Category:** general

---

### UNIFIED_FRAMEWORK_34
**Formula:** - Forcing vanishes: `ε·A → 0`

**Description:** From UNIFIED_FRAMEWORK.md, line 34

**Category:** general

---

### UNIFIED_FRAMEWORK_35
**Formula:** - Misalignment persists: `δ* = a²c₀²/(4π²) > 0`

**Description:** From UNIFIED_FRAMEWORK.md, line 35

**Category:** general

---

### UNIFIED_FRAMEWORK_39
**Formula:** The **persistent misalignment defect** δ* measures the angle between vorticity ω and strain S:

**Description:** From UNIFIED_FRAMEWORK.md, line 39

**Category:** general

---

### UNIFIED_FRAMEWORK_42
**Formula:** δ* = ⟨⟨1 - (ω·Sω)/(‖ω‖‖Sω‖)⟩⟩_{space,time}

**Description:** From UNIFIED_FRAMEWORK.md, line 42

**Category:** general

---

### UNIFIED_FRAMEWORK_47
**Formula:** δ* = a²c₀²/(4π²)

**Description:** From UNIFIED_FRAMEWORK.md, line 47

**Category:** general

---

### UNIFIED_FRAMEWORK_56
**Formula:** d/dt ‖ω‖_{B⁰_{∞,1}} ≤ -Δ ‖ω‖²_{B⁰_{∞,1}}

**Description:** From UNIFIED_FRAMEWORK.md, line 56

**Category:** general

---

### UNIFIED_FRAMEWORK_61
**Formula:** Δ = ν·c_B - (1 - δ*)·C_CZ·C_*·(1 + log⁺M)

**Description:** From UNIFIED_FRAMEWORK.md, line 61

**Category:** physical

---

### UNIFIED_FRAMEWORK_65
**Formula:** - `ν = 0.001`: viscosity

**Description:** From UNIFIED_FRAMEWORK.md, line 65

**Category:** physical

---

### UNIFIED_FRAMEWORK_66
**Formula:** - `c_B = 0.15`: Bernstein constant (improved via wavelets)

**Description:** From UNIFIED_FRAMEWORK.md, line 66

**Category:** general

---

### UNIFIED_FRAMEWORK_67
**Formula:** - `C_CZ = 1.5`: Calderón-Zygmund in Besov (better than L∞)

**Description:** From UNIFIED_FRAMEWORK.md, line 67

**Category:** general

---

### UNIFIED_FRAMEWORK_68
**Formula:** - `C_* = 1.2`: Besov-L∞ embedding constant

**Description:** From UNIFIED_FRAMEWORK.md, line 68

**Category:** general

---

### UNIFIED_FRAMEWORK_69
**Formula:** - `M = 100`: H^m Sobolev bound

**Description:** From UNIFIED_FRAMEWORK.md, line 69

**Category:** general

---

### UNIFIED_FRAMEWORK_71
**Formula:** **Closure Condition:** `Δ > 0`

**Description:** From UNIFIED_FRAMEWORK.md, line 71

**Category:** general

---

### UNIFIED_FRAMEWORK_79
**Formula:** X(t) ≤ X₀ + C ∫₀ᵗ K(t,s) X(s)² ds

**Description:** From UNIFIED_FRAMEWORK.md, line 79

**Category:** general

---

### UNIFIED_FRAMEWORK_83
**Formula:** - `X(t) = ‖ω(t)‖_{B⁰_{∞,1}}`: Besov norm

**Description:** From UNIFIED_FRAMEWORK.md, line 83

**Category:** general

---

### UNIFIED_FRAMEWORK_84
**Formula:** - `K(t,s) = (t-s)^(-1/2)`: Parabolic kernel

**Description:** From UNIFIED_FRAMEWORK.md, line 84

**Category:** general

---

### UNIFIED_FRAMEWORK_85
**Formula:** - `C = C_CZ/ν`: Effective constant

**Description:** From UNIFIED_FRAMEWORK.md, line 85

**Category:** physical

---

### UNIFIED_FRAMEWORK_87
**Formula:** **Result:** If the Volterra integral converges, then `∫₀^∞ X(t) dt < ∞` (BKM criterion satisfied).

**Description:** From UNIFIED_FRAMEWORK.md, line 87

**Category:** criterion

---

### UNIFIED_FRAMEWORK_95
**Formula:** dE/dt = -ν·E + C·E^(3/2)·(1 - δ*)

**Description:** From UNIFIED_FRAMEWORK.md, line 95

**Category:** physical

---

### UNIFIED_FRAMEWORK_98
**Formula:** where `E(t) = ‖u(t)‖_{H^m}` is the H^m Sobolev energy.

**Description:** From UNIFIED_FRAMEWORK.md, line 98

**Category:** general

---

### UNIFIED_FRAMEWORK_102
**Formula:** δ* > δ*_crit = 1 - ν/(C·E₀^(1/2))

**Description:** From UNIFIED_FRAMEWORK.md, line 102

**Category:** physical

---

### UNIFIED_FRAMEWORK_105
**Formula:** **Result:** If δ* exceeds the critical threshold, energy remains bounded → global regularity.

**Description:** From UNIFIED_FRAMEWORK.md, line 105

**Category:** general

---

### UNIFIED_FRAMEWORK_115
**Formula:** ν = 0.001

**Description:** From UNIFIED_FRAMEWORK.md, line 115

**Category:** physical

---

### UNIFIED_FRAMEWORK_116
**Formula:** c_B = 0.1

**Description:** From UNIFIED_FRAMEWORK.md, line 116

**Category:** general

---

### UNIFIED_FRAMEWORK_117
**Formula:** C_BKM = 2.0

**Description:** From UNIFIED_FRAMEWORK.md, line 117

**Category:** criterion

---

### UNIFIED_FRAMEWORK_122
**Formula:** δ*_required = 1 - (ν·c_B)/C_BKM = 0.99995

**Description:** From UNIFIED_FRAMEWORK.md, line 122

**Category:** criterion

---

### UNIFIED_FRAMEWORK_123
**Formula:** a_required = 2π√(δ*_required) ≈ 6.28

**Description:** From UNIFIED_FRAMEWORK.md, line 123

**Category:** general

---

### UNIFIED_FRAMEWORK_126
**Formula:** Current QCAL (a=1):

**Description:** From UNIFIED_FRAMEWORK.md, line 126

**Category:** general

---

### UNIFIED_FRAMEWORK_128
**Formula:** δ*_QCAL = 1/(4π²) ≈ 0.0253

**Description:** From UNIFIED_FRAMEWORK.md, line 128

**Category:** general

---

### UNIFIED_FRAMEWORK_137
**Formula:** c_B = 0.15    (improved via wavelets, +50%)

**Description:** From UNIFIED_FRAMEWORK.md, line 137

**Category:** general

---

### UNIFIED_FRAMEWORK_138
**Formula:** C_CZ = 1.5    (Besov instead of L∞, -25%)

**Description:** From UNIFIED_FRAMEWORK.md, line 138

**Category:** general

---

### UNIFIED_FRAMEWORK_139
**Formula:** C_* = 1.2     (embedding constant)

**Description:** From UNIFIED_FRAMEWORK.md, line 139

**Category:** general

---

### UNIFIED_FRAMEWORK_144
**Formula:** δ*_required ≈ 0.15

**Description:** From UNIFIED_FRAMEWORK.md, line 144

**Category:** general

---

### UNIFIED_FRAMEWORK_156
**Formula:** 1. **Parameter Sweep:** Test ranges of (f₀, α, a)

**Description:** From UNIFIED_FRAMEWORK.md, line 156

**Category:** general

---

### UNIFIED_FRAMEWORK_158
**Formula:** f0_range = [100, 500, 1000, 5000, 10000]

**Description:** From UNIFIED_FRAMEWORK.md, line 158

**Category:** general

---

### UNIFIED_FRAMEWORK_159
**Formula:** α_range = [1.5, 2.0, 2.5, 3.0]

**Description:** From UNIFIED_FRAMEWORK.md, line 159

**Category:** general

---

### UNIFIED_FRAMEWORK_160
**Formula:** a_range = [1.0, 2.0, 2.5, 3.0, 5.0]

**Description:** From UNIFIED_FRAMEWORK.md, line 160

**Category:** general

---

### UNIFIED_FRAMEWORK_165
**Formula:** - Measure δ*(f₀), ‖ω‖_∞(t), ‖∇u‖_∞(t)

**Description:** From UNIFIED_FRAMEWORK.md, line 165

**Category:** general

---

### UNIFIED_FRAMEWORK_166
**Formula:** - Estimate constants: C_CZ(f₀), C_*(f₀), c_B(f₀)

**Description:** From UNIFIED_FRAMEWORK.md, line 166

**Category:** estimate

---

### UNIFIED_FRAMEWORK_167
**Formula:** - Calculate damping: Δ(f₀; a, α)

**Description:** From UNIFIED_FRAMEWORK.md, line 167

**Category:** general

---

### UNIFIED_FRAMEWORK_170
**Formula:** - Route A: Check if Δ > 0

**Description:** From UNIFIED_FRAMEWORK.md, line 170

**Category:** general

---

### UNIFIED_FRAMEWORK_176
**Formula:** (a*, α*) = argmax min_{f₀} Δ(f₀; a, α)

**Description:** From UNIFIED_FRAMEWORK.md, line 176

**Category:** general

---

### UNIFIED_FRAMEWORK_179
**Formula:** 5. **Confirm:** Δ(a*, α*) > 0 uniformly in f₀

**Description:** From UNIFIED_FRAMEWORK.md, line 179

**Category:** general

---

### UNIFIED_FRAMEWORK_190
**Formula:** result = unified_validation(

**Description:** From UNIFIED_FRAMEWORK.md, line 190

**Category:** general

---

### UNIFIED_FRAMEWORK_191
**Formula:** f0_range=[100, 500, 1000],

**Description:** From UNIFIED_FRAMEWORK.md, line 191

**Category:** general

---

### UNIFIED_FRAMEWORK_192
**Formula:** α_range=[1.5, 2.0, 2.5],

**Description:** From UNIFIED_FRAMEWORK.md, line 192

**Category:** general

---

### UNIFIED_FRAMEWORK_193
**Formula:** a_range=[1.0, 2.0, 2.5, 3.0],

**Description:** From UNIFIED_FRAMEWORK.md, line 193

**Category:** general

---

### UNIFIED_FRAMEWORK_194
**Formula:** ν=1e-3

**Description:** From UNIFIED_FRAMEWORK.md, line 194

**Category:** physical

---

### UNIFIED_FRAMEWORK_198
**Formula:** print(f"Best parameters: a={result['best_params']['a']:.2f}, "

**Description:** From UNIFIED_FRAMEWORK.md, line 198

**Category:** general

---

### UNIFIED_FRAMEWORK_199
**Formula:** f"α={result['best_params']['α']:.2f}")

**Description:** From UNIFIED_FRAMEWORK.md, line 199

**Category:** general

---

### UNIFIED_FRAMEWORK_211
**Formula:** ├── BesovEmbedding.lean         # Besov-L∞ embedding with log

**Description:** From UNIFIED_FRAMEWORK.md, line 211

**Category:** general

---

### UNIFIED_FRAMEWORK_221
**Formula:** ‖∇u‖ ≤ C_CZ_Besov * BesovSpace.besov_norm ω

**Description:** From UNIFIED_FRAMEWORK.md, line 221

**Category:** general

---

### UNIFIED_FRAMEWORK_227
**Formula:** BesovSpace.besov_norm ω ≤ C_star * ‖ω‖ * (1 + log_plus M)

**Description:** From UNIFIED_FRAMEWORK.md, line 227

**Category:** general

---

### UNIFIED_FRAMEWORK_232
**Formula:** theorem riccati_besov_inequality (ω : ℝ → E) (t : ℝ) :

**Description:** From UNIFIED_FRAMEWORK.md, line 232

**Category:** estimate

---

### UNIFIED_FRAMEWORK_233
**Formula:** deriv (fun t => BesovSpace.besov_norm (ω t)) t ≤

**Description:** From UNIFIED_FRAMEWORK.md, line 233

**Category:** general

---

### UNIFIED_FRAMEWORK_234
**Formula:** -Δ * (BesovSpace.besov_norm (ω t))^2

**Description:** From UNIFIED_FRAMEWORK.md, line 234

**Category:** general

---

### UNIFIED_FRAMEWORK_239
**Formula:** theorem unified_bkm_closure (u ω : ℝ → E)

**Description:** From UNIFIED_FRAMEWORK.md, line 239

**Category:** criterion

---

### UNIFIED_FRAMEWORK_240
**Formula:** (h_damping : Δ > 0) :

**Description:** From UNIFIED_FRAMEWORK.md, line 240

**Category:** general

---

### UNIFIED_FRAMEWORK_241
**Formula:** (∫ t, ‖ω t‖ < ∞) → GloballySmooth u

**Description:** From UNIFIED_FRAMEWORK.md, line 241

**Category:** general

---

### UNIFIED_FRAMEWORK_269
**Formula:** α_optimal ≈ 2.0

**Description:** From UNIFIED_FRAMEWORK.md, line 269

**Category:** general

---

### UNIFIED_FRAMEWORK_270
**Formula:** δ*_optimal ≈ 0.158

**Description:** From UNIFIED_FRAMEWORK.md, line 270

**Category:** general

---

### UNIFIED_FRAMEWORK_273
**Formula:** With improved constants (c_B=0.15, C_CZ=1.5, C_*=1.2):

**Description:** From UNIFIED_FRAMEWORK.md, line 273

**Category:** general

---

### UNIFIED_FRAMEWORK_275
**Formula:** Δ(a=2.5, α=2.0) ≈ -1.83  (still negative, but much improved)

**Description:** From UNIFIED_FRAMEWORK.md, line 275

**Category:** general

---

### UNIFIED_FRAMEWORK_280
**Formula:** To achieve positive damping (Δ > 0), we need **one** of:

**Description:** From UNIFIED_FRAMEWORK.md, line 280

**Category:** general

---

### UNIFIED_FRAMEWORK_285
**Formula:** - Decrease C_CZ to 1.2 (via sharper Besov estimates)

**Description:** From UNIFIED_FRAMEWORK.md, line 285

**Category:** estimate

---

### UNIFIED_FRAMEWORK_286
**Formula:** 3. **Alternative regularization:** Different forcing with larger δ*

**Description:** From UNIFIED_FRAMEWORK.md, line 286

**Category:** general

---

### ROADMAP_40
**Formula:** - [ ] Control L∞ de vorticidad

**Description:** From ROADMAP.md, line 40

**Category:** general

---

### ROADMAP_45
**Formula:** - [x] Definición de δ(t)

**Description:** From ROADMAP.md, line 45

**Category:** general

---

### ROADMAP_46
**Formula:** - [ ] Teorema 13.4: Persistencia de δ*

**Description:** From ROADMAP.md, line 46

**Category:** general

---

### ROADMAP_51
**Formula:** - [ ] Conexión con δ*

**Description:** From ROADMAP.md, line 51

**Category:** general

---

### ROADMAP_69
**Formula:** - [x] Cálculo de δ(t)

**Description:** From ROADMAP.md, line 69

**Category:** general

---

### ROADMAP_148
**Formula:** - ✅ δ* → valor teórico cuando f₀ → ∞

**Description:** From ROADMAP.md, line 148

**Category:** general

---

### ROADMAP_149
**Formula:** - 🔄 α* < 0 uniformemente

**Description:** From ROADMAP.md, line 149

**Category:** general

---

### ROADMAP_150
**Formula:** - 🔄 ∫‖ω‖_∞ dt < ∞ en simulaciones

**Description:** From ROADMAP.md, line 150

**Category:** general

---

### THEORY_7
**Formula:** ∂ₜu + (u·∇)u = -∇p + ν∆u + f

**Description:** From THEORY.md, line 7

**Category:** physical

---

### THEORY_8
**Formula:** ∇·u = 0

**Description:** From THEORY.md, line 8

**Category:** general

---

### THEORY_9
**Formula:** u(0,x) = u₀(x)

**Description:** From THEORY.md, line 9

**Category:** general

---

### THEORY_15
**Formula:** - **ν > 0**: Viscosidad cinemática

**Description:** From THEORY.md, line 15

**Category:** physical

---

### THEORY_22
**Formula:** **Datos**: u₀ ∈ L²σ(T³) (div-free), opcional u₀ ∈ H¹ para estimaciones más finas.

**Description:** From THEORY.md, line 22

**Category:** general

---

### THEORY_24
**Formula:** Aquí L²σ(T³) denota el espacio de campos vectoriales de cuadrado integrable en el toro 3D que satisfacen la condición de incompresibilidad ∇·u = 0.

**Description:** From THEORY.md, line 24

**Category:** general

---

### THEORY_31
**Formula:** u ∈ L∞(0,T; L²σ) ∩ L²(0,T; H¹)

**Description:** From THEORY.md, line 31

**Category:** general

---

### THEORY_37
**Formula:** - Existencia global garantizada para datos arbitrarios en L²σ

**Description:** From THEORY.md, line 37

**Category:** general

---

### THEORY_46
**Formula:** ½‖u(t)‖²₂ + ν∫₀ᵗ ‖∇u‖²₂ ≤ ½‖u₀‖²₂ + ∫₀ᵗ ⟨F,u⟩

**Description:** From THEORY.md, line 46

**Category:** physical

---

### THEORY_56
**Formula:** ∫₀ᵀ ‖ω(·,t)‖∞ dt < ∞

**Description:** From THEORY.md, line 56

**Category:** general

---

### THEORY_59
**Formula:** entonces no hay blow-up en [0,T], donde ω = ∇ × u es la vorticidad.

**Description:** From THEORY.md, line 59

**Category:** general

---

### THEORY_61
**Formula:** Este criterio establece que el control de la vorticidad en norma L∞ es suficiente y necesario para garantizar la suavidad de la solución.

**Description:** From THEORY.md, line 61

**Category:** general

---

### THEORY_65
**Formula:** Para análisis en espacios críticos, trabajamos en B^(−1+3/p)_(p,q)(T³) con 3 < p ≤ ∞, 1 ≤ q ≤ ∞.

**Description:** From THEORY.md, line 65

**Category:** general

---

### THEORY_70
**Formula:** ‖B(u,v)‖_(B^(−1+3/p)_(p,q)) ≤ C‖u‖_(B^(−1+3/p)_(p,q))‖v‖_(B^(1+3/p)_(p,q))

**Description:** From THEORY.md, line 70

**Category:** general

---

### THEORY_73
**Formula:** Fijando por ejemplo p = 3 + ε, q = 1 obtenemos criticalidad y buena interpolación para el análisis de regularidad.

**Description:** From THEORY.md, line 73

**Category:** general

---

### THEORY_78
**Formula:** Demostrar que para datos iniciales suaves u₀ ∈ H^m (m ≥ 3), existe una solución global suave:

**Description:** From THEORY.md, line 78

**Category:** general

---

### THEORY_80
**Formula:** u ∈ C^∞(ℝ³ × (0,∞))

**Description:** From THEORY.md, line 80

**Category:** general

---

### THEORY_89
**Formula:** ∂ₜu + (u·∇)u = -∇p + ν∆u + ε∇Φ(x, 2πf₀t)

**Description:** From THEORY.md, line 89

**Category:** physical

---

### THEORY_90
**Formula:** ∇·u = 0

**Description:** From THEORY.md, line 90

**Category:** general

---

### THEORY_94
**Formula:** - **ε**: Amplitud de regularización

**Description:** From THEORY.md, line 94

**Category:** general

---

### THEORY_96
**Formula:** - **Φ(x,θ)**: Potencial oscilatorio con ∇ₓφ ≥ c₀ > 0

**Description:** From THEORY.md, line 96

**Category:** general

---

### THEORY_102
**Formula:** ε = λf₀^(-α)

**Description:** From THEORY.md, line 102

**Category:** general

---

### THEORY_103
**Formula:** A = af₀

**Description:** From THEORY.md, line 103

**Category:** general

---

### THEORY_104
**Formula:** α > 1

**Description:** From THEORY.md, line 104

**Category:** general

---

### THEORY_107
**Formula:** **Propiedad clave:** En el límite f₀ → ∞:

**Description:** From THEORY.md, line 107

**Category:** general

---

### THEORY_108
**Formula:** - La amplitud ε → 0 (fuerza desaparece)

**Description:** From THEORY.md, line 108

**Category:** general

---

### THEORY_109
**Formula:** - El efecto regularizante persiste vía δ* > 0

**Description:** From THEORY.md, line 109

**Category:** general

---

### THEORY_115
**Formula:** A_ε,f₀(t) = (Sω)·ω / (‖S‖·‖ω‖²)

**Description:** From THEORY.md, line 115

**Category:** general

---

### THEORY_118
**Formula:** Donde S = ½(∇u + ∇uᵀ) es el tensor de deformación.

**Description:** From THEORY.md, line 118

**Category:** general

---

### THEORY_122
**Formula:** δ(t) = 1 - A_ε,f₀(t)

**Description:** From THEORY.md, line 122

**Category:** general

---

### THEORY_127
**Formula:** ### Teorema Principal (Continuidad a priori ⇒ Suavidad Global)

**Description:** From THEORY.md, line 127

**Category:** general

---

### THEORY_129
**Formula:** **Enunciado**: Existe δ₀ > 0 tal que si el defecto de desalineamiento persistente

**Description:** From THEORY.md, line 129

**Category:** general

---

### THEORY_132
**Formula:** δ* := avg_t avg_x ∠(ω, Sω) ≥ δ₀

**Description:** From THEORY.md, line 132

**Category:** general

---

### THEORY_135
**Formula:** en el límite dual ε → 0, A → ∞ (con ε = λf₀^(−α), A = af₀, α > 1), entonces

**Description:** From THEORY.md, line 135

**Category:** general

---

### THEORY_138
**Formula:** ∫₀^∞ ‖ω‖∞ dt < ∞

**Description:** From THEORY.md, line 138

**Category:** general

---

### THEORY_144
**Formula:** 1. Descomposición del estiramiento (ω·∇)u mediante Sω

**Description:** From THEORY.md, line 144

**Category:** general

---

### THEORY_145
**Formula:** 2. Control de ⟨cos θ⟩ con θ = ∠(ω, Sω): ⟨cos θ⟩ ≤ cos δ₀ < 1

**Description:** From THEORY.md, line 145

**Category:** general

---

### THEORY_146
**Formula:** 3. Ecuación tipo Riccati efectiva con término lineal de disipación y coeficiente cuadrático reducido por cos δ₀

**Description:** From THEORY.md, line 146

**Category:** estimate

---

### THEORY_147
**Formula:** 4. Cierre con energía y Grönwall ⇒ integrabilidad de ‖ω‖∞

**Description:** From THEORY.md, line 147

**Category:** general

---

### THEORY_150
**Formula:** - **Statement (Enunciado estándar)**: La integrabilidad de ‖ω‖∞ implica suavidad global vía BKM

**Description:** From THEORY.md, line 150

**Category:** criterion

---

### THEORY_151
**Formula:** - **Interpretation (Visión QCAL)**: La hipótesis δ* ≥ δ₀ es la contribución novedosa verificable computacionalmente

**Description:** From THEORY.md, line 151

**Category:** general

---

### THEORY_155
**Formula:** Para el sistema Ψ-NS con escala dual, existen constantes C_m independientes de f₀ tales que:

**Description:** From THEORY.md, line 155

**Category:** general

---

### THEORY_157
**Formula:** ‖u(t)‖_Hᵐ ≤ C_m,  ∀t ≥ 0, ∀f₀ ≥ f₀_min

**Description:** From THEORY.md, line 157

**Category:** general

---

### THEORY_165
**Formula:** ### Teorema 5.2: Persistencia de δ*

**Description:** From THEORY.md, line 165

**Category:** general

---

### THEORY_167
**Formula:** En el límite f₀ → ∞, el defecto se estabiliza:

**Description:** From THEORY.md, line 167

**Category:** general

---

### THEORY_169
**Formula:** δ* = lim inf_{f₀→∞} (inf_t δ(t)) > 0

**Description:** From THEORY.md, line 169

**Category:** general

---

### THEORY_174
**Formula:** δ* = (a²c₀²)/(4π²)

**Description:** From THEORY.md, line 174

**Category:** general

---

### THEORY_184
**Formula:** 1. δ* > 0 persiste

**Description:** From THEORY.md, line 184

**Category:** general

---

### THEORY_185
**Formula:** 2. El coeficiente de Riccati α* < 0

**Description:** From THEORY.md, line 185

**Category:** estimate

---

### THEORY_189
**Formula:** ∫₀^∞ ‖ω(t)‖_L∞ dt < ∞  ⟹  u ∈ C^∞(ℝ³ × (0,∞))

**Description:** From THEORY.md, line 189

**Category:** general

---

### THEORY_198
**Formula:** u(t,x) = ū(t,x) + u_osc(t,x,θ)

**Description:** From THEORY.md, line 198

**Category:** general

---

### THEORY_199
**Formula:** θ = 2πf₀t  (escala rápida)

**Description:** From THEORY.md, line 199

**Category:** general

---

### THEORY_205
**Formula:** lim_{T→∞} (1/T)∫₀^T F(t,θ) dt = ⟨F⟩_θ

**Description:** From THEORY.md, line 205

**Category:** general

---

### THEORY_210
**Formula:** La evolución de ‖ω‖²_L² satisface:

**Description:** From THEORY.md, line 210

**Category:** general

---

### THEORY_212
**Formula:** d/dt(‖ω‖²) ≤ α*(t)‖ω‖² - νc_B‖∇ω‖²

**Description:** From THEORY.md, line 212

**Category:** physical

---

### THEORY_217
**Formula:** α*(t) = C_BKM(1 - δ(t)) - νc_B

**Description:** From THEORY.md, line 217

**Category:** criterion

---

### THEORY_220
**Formula:** **Consecuencia:** Si α* < 0 uniformemente, entonces ‖ω‖_L∞ está acotado.

**Description:** From THEORY.md, line 220

**Category:** general

---

### THEORY_226
**Formula:** L_ω ~ (ν³/ε)^(1/4)

**Description:** From THEORY.md, line 226

**Category:** physical

---

### THEORY_231
**Formula:** τ ~ L_ω²/ν ~ (ν/ε)^(1/2)

**Description:** From THEORY.md, line 231

**Category:** physical

---

### THEORY_236
**Formula:** τ ~ f₀^((α-1)/2)  →  ∞  cuando f₀ → ∞, α > 1

**Description:** From THEORY.md, line 236

**Category:** general

---

### THEORY_242
**Formula:** - La regularización vibracional mantiene u ∈ C^∞

**Description:** From THEORY.md, line 242

**Category:** general

---

### THEORY_243
**Formula:** - Compatible con cascada de energía para Re → ∞

**Description:** From THEORY.md, line 243

**Category:** general

---

### THEORY_247
**Formula:** - En el límite ε → 0, convergen a soluciones débiles de Leray

**Description:** From THEORY.md, line 247

**Category:** general

---

### THEORY_250
**Formula:** - Análisis frecuencial muestra δ* emerge de modos altos

**Description:** From THEORY.md, line 250

**Category:** general

---

### THEORY_259
**Formula:** u(x) = Σ_k û_k e^(ik·x)

**Description:** From THEORY.md, line 259

**Category:** general

---

### THEORY_271
**Formula:** ∂ₜû_k = -ik_i(û·∇u)_k - νk²û_k + (ε∇Φ)_k

**Description:** From THEORY.md, line 271

**Category:** physical

---

### THEORY_274
**Formula:** ### 8.3 Cálculo de δ(t)

**Description:** From THEORY.md, line 274

**Category:** general

---

### THEORY_276
**Formula:** 1. Calcular S = ½(∇u + ∇uᵀ) en espacio físico

**Description:** From THEORY.md, line 276

**Category:** general

---

### THEORY_277
**Formula:** 2. Calcular ω = ∇ × u

**Description:** From THEORY.md, line 277

**Category:** general

---

### THEORY_280
**Formula:** numerador = ∫(Sω)·ω dx

**Description:** From THEORY.md, line 280

**Category:** general

---

### THEORY_281
**Formula:** denominador = ‖S‖·∫ω² dx

**Description:** From THEORY.md, line 281

**Category:** general

---

### THEORY_283
**Formula:** 4. δ = 1 - numerador/denominador

**Description:** From THEORY.md, line 283

**Category:** general

---

### THEORY_288
**Formula:** - Requiere f₀ suficientemente grande (> 100 Hz)

**Description:** From THEORY.md, line 288

**Category:** general

---

### THEORY_289
**Formula:** - Parámetros α, a, λ deben satisfacer condiciones específicas

**Description:** From THEORY.md, line 289

**Category:** general

---

### THEORY_319
**Formula:** 2. **Control cuantitativo**: δ* > 0 medible

**Description:** From THEORY.md, line 319

**Category:** general

---

