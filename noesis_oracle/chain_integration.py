# ============================================================================
# noesis_oracle/chain_integration.py
# Integración con blockchain Ethereum
# ============================================================================

import json
import os
import subprocess
from typing import Any, Dict, Optional


class ChainIntegration:
    """
    Envía pruebas Groth16 al contrato de gobernanza NOESIS on-chain.
    Requiere: Foundry (cast), SEPOLIA_RPC y PRIVATE_KEY en el entorno.
    """

    def __init__(
        self,
        contract_address: Optional[str] = None,
        rpc_url: Optional[str] = None,
        private_key: Optional[str] = None,
    ):
        self.contract_address = contract_address or os.getenv("NOESIS_CONTRACT_ADDRESS")
        self.rpc_url = rpc_url or os.getenv("SEPOLIA_RPC")
        self.private_key = private_key or os.getenv("PRIVATE_KEY")

    def _ready(self) -> bool:
        if not self.contract_address:
            print("⚠️  NOESIS_CONTRACT_ADDRESS no configurada")
            return False
        if not self.rpc_url:
            print("⚠️  SEPOLIA_RPC no configurada")
            return False
        if not self.private_key:
            print("⚠️  PRIVATE_KEY no configurada")
            return False
        return True

    def _cast(self, *args: str) -> subprocess.CompletedProcess:
        cmd = ["cast"] + list(args)
        return subprocess.run(cmd, capture_output=True, text=True)

    # ------------------------------------------------------------------
    # Calldata
    # ------------------------------------------------------------------

    def build_calldata(
        self,
        proof: Dict[str, Any],
        public_signals: list,
    ) -> Optional[str]:
        """Construye el calldata para verifyAndRegisterZKState."""
        try:
            pi_a = f"[{proof['pi_a'][0]},{proof['pi_a'][1]}]"
            pi_b = (
                f"[[{proof['pi_b'][0][0]},{proof['pi_b'][0][1]}],"
                f"[{proof['pi_b'][1][0]},{proof['pi_b'][1][1]}]]"
            )
            pi_c = f"[{proof['pi_c'][0]},{proof['pi_c'][1]}]"
            pub = f"[{','.join(str(x) for x in public_signals[:4])}]"

            r = self._cast(
                "calldata",
                "verifyAndRegisterZKState(uint256[2],uint256[2][2],uint256[2],uint256[])",
                pi_a, pi_b, pi_c, pub,
            )
            if r.returncode != 0:
                print(f"❌ cast calldata error: {r.stderr}")
                return None
            return r.stdout.strip()
        except (KeyError, IndexError) as exc:
            print(f"❌ build_calldata error: {exc}")
            return None

    # ------------------------------------------------------------------
    # Send transaction
    # ------------------------------------------------------------------

    def send_proof(
        self,
        proof: Dict[str, Any],
        public_signals: list,
    ) -> Dict[str, Any]:
        """
        Envía la prueba al contrato on-chain.

        Returns
        -------
        dict with keys: success, tx_hash, error
        """
        if not self._ready():
            return {"success": False, "error": "Configuración incompleta"}

        calldata = self.build_calldata(proof, public_signals)
        if not calldata:
            return {"success": False, "error": "No se pudo generar calldata"}

        r = self._cast(
            "send",
            self.contract_address,
            calldata,
            "--rpc-url", self.rpc_url,
            "--private-key", self.private_key,
        )

        if r.returncode != 0:
            return {"success": False, "error": r.stderr}

        # Extraer tx hash de la salida de cast
        tx_hash = None
        for line in r.stdout.splitlines():
            if line.startswith("0x") and len(line) == 66:
                tx_hash = line.strip()
                break

        return {"success": True, "tx_hash": tx_hash, "output": r.stdout}

    # ------------------------------------------------------------------
    # Read state
    # ------------------------------------------------------------------

    def read_state(self) -> Optional[str]:
        """Lee el estado actual del contrato."""
        if not self._ready():
            return None
        r = self._cast(
            "call", self.contract_address,
            "getSystemState()(string)",
            "--rpc-url", self.rpc_url,
        )
        return r.stdout.strip() if r.returncode == 0 else None
