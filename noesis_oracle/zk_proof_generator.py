# ============================================================================
# noesis_oracle/zk_proof_generator.py
# Generador de pruebas ZK Groth16 para el pipeline NOESIS
# ============================================================================

import hashlib
import json
import os
import subprocess
import tempfile
import time
from typing import Any, Dict, Optional


class ZKProofGenerator:
    """
    Genera pruebas Groth16 a partir del witness NOESIS via snarkjs.
    """

    def __init__(
        self,
        zkey_path: str = "build/noesis_coherence_final.zkey",
        wasm_path: str = "build/noesis_coherence_js/noesis_coherence.wasm",
        vkey_path: str = "build/verification_key.json",
    ):
        self.zkey_path = zkey_path
        self.wasm_path = wasm_path
        self.vkey_path = vkey_path
        self.f0 = 141.7001
        self.psi_threshold = 0.999999

    # ------------------------------------------------------------------
    # Witness I/O
    # ------------------------------------------------------------------

    def write_witness(self, witness: Dict[str, Any], path: str) -> None:
        """Escribe el witness en disco en formato JSON."""
        with open(path, "w", encoding="utf-8") as f:
            json.dump(witness, f, indent=2)

    # ------------------------------------------------------------------
    # snarkjs wrappers
    # ------------------------------------------------------------------

    def _run(self, cmd: list[str]) -> subprocess.CompletedProcess:
        return subprocess.run(cmd, capture_output=True, text=True, check=True)

    def compute_witness(self, witness_input_path: str, witness_output_path: str) -> bool:
        """Calcula el witness binario con snarkjs."""
        try:
            self._run([
                "snarkjs", "wtns", "calculate",
                self.wasm_path,
                witness_input_path,
                witness_output_path,
            ])
            return True
        except (subprocess.CalledProcessError, FileNotFoundError) as exc:
            print(f"❌ compute_witness error: {exc}")
            return False

    def generate_proof(
        self,
        witness_path: str,
        proof_output: str = "proof.json",
        public_output: str = "public.json",
    ) -> bool:
        """Genera la prueba Groth16."""
        try:
            self._run([
                "snarkjs", "groth16", "prove",
                self.zkey_path,
                witness_path,
                proof_output,
                public_output,
            ])
            return True
        except (subprocess.CalledProcessError, FileNotFoundError) as exc:
            print(f"❌ generate_proof error: {exc}")
            return False

    def verify_proof(
        self,
        proof_path: str = "proof.json",
        public_path: str = "public.json",
    ) -> bool:
        """Verifica la prueba localmente."""
        try:
            result = self._run([
                "snarkjs", "groth16", "verify",
                self.vkey_path,
                public_path,
                proof_path,
            ])
            return "OK" in result.stdout
        except (subprocess.CalledProcessError, FileNotFoundError) as exc:
            print(f"❌ verify_proof error: {exc}")
            return False

    # ------------------------------------------------------------------
    # High-level pipeline
    # ------------------------------------------------------------------

    def run_pipeline(
        self,
        witness: Dict[str, Any],
        workdir: Optional[str] = None,
    ) -> Dict[str, Any]:
        """
        Ejecuta el pipeline completo: witness → compute → prove → verify.
        """
        workdir = workdir or tempfile.mkdtemp(prefix="noesis_zk_")
        witness_input = os.path.join(workdir, "witness_input.json")
        witness_bin = os.path.join(workdir, "witness.wtns")
        proof_path = os.path.join(workdir, "proof.json")
        public_path = os.path.join(workdir, "public.json")

        self.write_witness(witness, witness_input)

        computed = self.compute_witness(witness_input, witness_bin)
        if not computed:
            return {"status": "ERROR", "stage": "compute_witness"}

        proved = self.generate_proof(witness_bin, proof_path, public_path)
        if not proved:
            return {"status": "ERROR", "stage": "generate_proof"}

        verified = self.verify_proof(proof_path, public_path)

        proof_data: Dict[str, Any] = {}
        if os.path.exists(proof_path):
            with open(proof_path) as f:
                proof_data = json.load(f)

        return {
            "status": "VALID" if verified else "INVALID",
            "verified": verified,
            "proof": proof_data,
            "workdir": workdir,
            "timestamp": time.time(),
        }


# ============================================================================
# Entry point
# ============================================================================

def main():
    # Witness de ejemplo (cargado desde archivo si existe)
    if os.path.exists("witness_input.json"):
        with open("witness_input.json") as f:
            witness = json.load(f)
    else:
        witness = {
            "psi_real": [0.0] * 100,
            "psi_imag": [0.0] * 100,
            "fieldSalt": 0,
            "expectedStateHash": 0,
            "minCoherence": 999999,
            "maxEntropy": 10000,
            "minStability": 100,
        }

    gen = ZKProofGenerator()
    result = gen.run_pipeline(witness)
    print(f"Estado ZK: {result['status']}")
    print(json.dumps({k: v for k, v in result.items() if k != "proof"}, indent=2))


if __name__ == "__main__":
    main()
