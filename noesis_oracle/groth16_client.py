# ============================================================================
# noesis_oracle/groth16_client.py
# Cliente Groth16: interfaz Python sobre snarkjs
# ============================================================================

import json
import os
import subprocess
import tempfile
from typing import Any, Dict, Optional


class Groth16Client:
    """
    Interfaz Python sobre snarkjs para operaciones Groth16.
    """

    def __init__(
        self,
        zkey: str = "build/noesis_coherence_final.zkey",
        wasm: str = "build/noesis_coherence_js/noesis_coherence.wasm",
        vkey: str = "build/verification_key.json",
    ):
        self.zkey = zkey
        self.wasm = wasm
        self.vkey = vkey

    # ------------------------------------------------------------------
    # snarkjs helpers
    # ------------------------------------------------------------------

    def _snarkjs(self, *args: str) -> subprocess.CompletedProcess:
        cmd = ["snarkjs"] + list(args)
        return subprocess.run(cmd, capture_output=True, text=True)

    def _check_artifacts(self) -> bool:
        for path in [self.zkey, self.wasm, self.vkey]:
            if not os.path.exists(path):
                print(f"⚠️  Artifact not found: {path}")
                return False
        return True

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def prove(
        self,
        witness_input: Dict[str, Any],
        workdir: Optional[str] = None,
    ) -> Dict[str, Any]:
        """
        Genera la prueba Groth16 a partir de un witness dict.

        Returns
        -------
        dict with keys: success, proof, public_signals, error
        """
        if not self._check_artifacts():
            return {"success": False, "error": "Missing ZK artifacts"}

        workdir = workdir or tempfile.mkdtemp(prefix="groth16_")
        input_path = os.path.join(workdir, "input.json")
        wtns_path = os.path.join(workdir, "witness.wtns")
        proof_path = os.path.join(workdir, "proof.json")
        public_path = os.path.join(workdir, "public.json")

        with open(input_path, "w") as f:
            json.dump(witness_input, f)

        # Step 1: compute witness
        r = self._snarkjs("wtns", "calculate", self.wasm, input_path, wtns_path)
        if r.returncode != 0:
            return {"success": False, "error": r.stderr, "stage": "wtns"}

        # Step 2: prove
        r = self._snarkjs("groth16", "prove", self.zkey, wtns_path, proof_path, public_path)
        if r.returncode != 0:
            return {"success": False, "error": r.stderr, "stage": "prove"}

        proof = json.load(open(proof_path))
        public = json.load(open(public_path))

        return {"success": True, "proof": proof, "public_signals": public}

    def verify(
        self,
        proof: Dict[str, Any],
        public_signals: list,
        workdir: Optional[str] = None,
    ) -> bool:
        """Verifica una prueba Groth16 localmente."""
        if not os.path.exists(self.vkey):
            print(f"⚠️  Verification key not found: {self.vkey}")
            return False

        workdir = workdir or tempfile.mkdtemp(prefix="groth16_verify_")
        proof_path = os.path.join(workdir, "proof.json")
        public_path = os.path.join(workdir, "public.json")

        with open(proof_path, "w") as f:
            json.dump(proof, f)
        with open(public_path, "w") as f:
            json.dump(public_signals, f)

        r = self._snarkjs("groth16", "verify", self.vkey, public_path, proof_path)
        return r.returncode == 0 and "OK" in r.stdout

    def export_calldata(
        self,
        proof: Dict[str, Any],
        public_signals: list,
        workdir: Optional[str] = None,
    ) -> Optional[str]:
        """Exporta el calldata para el contrato Solidity verificador."""
        workdir = workdir or tempfile.mkdtemp(prefix="groth16_calldata_")
        proof_path = os.path.join(workdir, "proof.json")
        public_path = os.path.join(workdir, "public.json")

        with open(proof_path, "w") as f:
            json.dump(proof, f)
        with open(public_path, "w") as f:
            json.dump(public_signals, f)

        r = self._snarkjs("zkey", "export", "soliditycalldata", public_path, proof_path)
        if r.returncode != 0:
            return None
        return r.stdout.strip()
