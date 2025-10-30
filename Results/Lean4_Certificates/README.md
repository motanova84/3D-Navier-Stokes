# Lean4 Proof Certificates

This directory stores verification certificates from Lean4 formal proofs.

## Expected Contents

- `lemma_verification.log` - Build log showing verified lemmas
- `theorem_certificates/` - Individual theorem verification certificates
- Compiled `.olean` files (gitignored)

## Generation

Certificates are generated when building Lean4 proofs:
```bash
../../Scripts/build_lean_proofs.sh
```

## Verification

To verify a specific theorem:
```bash
cd ../../Lean4-Formalization
lean --verify Theorem13_7.lean
```

## Status

Current status: Framework established, full formal verification in progress.
