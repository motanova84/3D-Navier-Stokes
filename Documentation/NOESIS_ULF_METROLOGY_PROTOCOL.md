# NOESIS ULF Metrology Protocol (Formalized)

This repository now includes a formal, testable implementation in:

- `noesis_ulf_metrology.py`
- `test_noesis_ulf_metrology.py`

## Implemented equations

1. **Larmor frequency**

\[
 f_L = \left(\frac{\gamma}{2\pi}\right) B_0
\]

2. **GUM combined uncertainty**

\[
 u_c^2(y)=\sum_i (c_i u_i)^2 + 2\sum_{i<j} c_i c_j u(x_i, x_j)
\]

3. **Expanded uncertainty**

\[
 U = k\,u_c
\]

4. **FID model**

\[
 S(t)=A_0\Psi(t)e^{-t/T_2^*}\cos(2\pi f_0 t + \phi_0) + \sum_k A_k\cos(2\pi f_k t + \phi_k)+\eta(t)
\]

5. **Coherence envelope**

\[
 \Psi(t)=\Psi_{\infty}\left(1-e^{-t/\tau_{coh}}\right)
\]

6. **Acceptance interval**

\[
 f_{exp}\in[f_0-U, f_0+U]
\]

## Protocol logic encoded

- Negative/positive controls are represented as explicit boolean gates.
- Frequency acceptance uses expanded uncertainty interval.
- Coherence threshold and entropy bound are explicit pass/fail conditions.
- Final decision is deterministic and auditable via `evaluate_protocol(...)`.

## Reference uncertainty preset

`default_noesis_uncertainty_sources()` encodes the standard NOESIS budget values and reproduces:

- \(u_c \approx 3.518\times10^{-4}\,\text{Hz}\)
- \(U\,(k=2) \approx 7.036\times10^{-4}\,\text{Hz}\)
