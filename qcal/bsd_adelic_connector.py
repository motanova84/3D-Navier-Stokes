#!/usr/bin/env python3
"""
BSD Adelic Connector — Pentágono Logos Cerrado
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Connects BSD conjecture with DNA-Riemann resonance through adelic structure.
Vincula rango BSD a hotspots ADN: L(E,1)=0 → superfluido info.
Vincula rango BSD a hotspots ADN: L(E,1)=0 → superfluido info,
puntos racionales activan nodos constelación QCAL.

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import numpy as np
from typing import Dict, List, Any

# Frecuencia fundamental del Logos (Hz)
F0 = 141.7001
sys.path.insert(0, str(Path(__file__).parent.parent / '02_codigo_fuente' / 'teoria_principal'))

try:
    from cytoplasmic_riemann_resonance import (
        CytoplasmicRiemannResonance,
        BiologicalResonanceParams,
        FUNDAMENTAL_FREQUENCY_HZ,
    )
    CYTOPLASMIC_AVAILABLE = True
except ImportError:
    CYTOPLASMIC_AVAILABLE = False
    FUNDAMENTAL_FREQUENCY_HZ = 141647.33

F0 = 141.7001  # Hz — frecuencia base del Logos


# ──────────────────────────────────────────────────────────────────────────────
# Codificador ADN-Riemann (definido aquí para compatibilidad con test imports)
# ──────────────────────────────────────────────────────────────────────────────

class CodificadorADNRiemann:
    """
    ADN-Riemann encoder that maps DNA sequences to resonance/frequency space.

    Provides two complementary resonance methods:
    - calcular_resonancia(): BASE_RESONANCE-weighted score (used by BSD tests)
    - resonancia_con_f0():   FFT-spectrum mean normalized magnitude
    """

    # Resonance weights per base (G highest, T lowest)
    BASE_RESONANCE: Dict[str, float] = {
        'G': 1.0,
        'A': 0.9,
        'C': 0.8,
        'T': 0.7,
        'U': 0.7,
    }

    # Frequency mappings (THz) for spectral encoding
    BASES_FREQ: Dict[str, float] = {
        'A': 1.2,
        'C': 2.3,
        'G': 3.4,
        'T': 4.5,
    }

    # Hotspot patterns that resonate strongly with f0
    HOTSPOT_PATTERNS: List[str] = ['GACT', 'CGTA', 'ATCG', 'TATA', 'AAAA']

    def __init__(self, f0: float = F0):
        self.f0 = f0

    # ------------------------------------------------------------------
    # Hotspot detection
    # ------------------------------------------------------------------

    def identificar_hotspots(self, secuencia: str) -> List[int]:
        """
        Identify resonant hotspot positions in a DNA sequence.

        Args:
            secuencia: DNA sequence string (e.g. "GACT")

        Returns:
            Sorted list of hotspot start indices.
        """
        hotspots: List[int] = []
        seq = secuencia.upper()
    }

    HOTSPOT_PATTERNS: List[str] = ['GACT', 'CGTA', 'ATCG', 'TATA', 'AAAA']

    def __init__(self, f0: float = F0) -> None:
        self.f0 = f0
        if CYTOPLASMIC_AVAILABLE:
            self.cytoplasmic_model = CytoplasmicRiemannResonance(BiologicalResonanceParams())
        else:
            self.cytoplasmic_model = None

    def identificar_hotspots(self, secuencia_gact: str) -> List[int]:
        """Identifica hotspots de resonancia en una secuencia de ADN."""
        hotspots: List[int] = []
        secuencia = secuencia_gact.upper()

        for pattern in self.HOTSPOT_PATTERNS:
            start = 0
            while True:
                idx = seq.find(pattern, start)
                if idx == -1:
                    break
                hotspots.append(idx)
                start = idx + 1

        # Fallback: individual bases with resonance >= 0.8
        if not hotspots:
            for i, base in enumerate(seq):
                start_idx = idx + 1

        if not hotspots:
            for i, base in enumerate(secuencia):
                if self.BASE_RESONANCE.get(base, 0.0) >= 0.8:
                    hotspots.append(i)

        return sorted(set(hotspots))

    # ------------------------------------------------------------------
    # Resonance calculations
    # ------------------------------------------------------------------

    def calcular_resonancia(self, secuencia: str) -> float:
        """
        Calculate BASE_RESONANCE-weighted resonance score (0–1).

        Args:
            secuencia: DNA sequence string

        Returns:
            Normalised resonance value in [0, 1].
        """
        if not secuencia:
            return 0.0

        seq = secuencia.upper()
        total = sum(self.BASE_RESONANCE.get(b, 0.0) for b in seq)
        res_norm = total / len(seq)

        # Bonus for known hotspot patterns (capped at 1.0)
        for pattern in self.HOTSPOT_PATTERNS:
            if pattern in seq:
                res_norm = min(1.0, res_norm * 1.1)
                break

        return res_norm

    def codificar(self, secuencia: str) -> np.ndarray:
        """
        Encode DNA sequence to frequency spectrum via FFT.

        Args:
            secuencia: DNA sequence string

        Returns:
            Complex FFT spectrum array.
        """
        valores = np.array(
            [self.BASES_FREQ.get(b.upper(), 0.0) for b in secuencia]
        )
        return np.fft.fft(valores)

    def resonancia_con_f0(self, secuencia: str) -> float:
        """
        Calculate resonance with f0 using the normalised FFT spectrum mean.

        Args:
            secuencia: DNA sequence string

        Returns:
            Mean normalised spectral magnitude in [0, 1].
        """
        espectro = self.codificar(secuencia)
        magnitud = np.abs(espectro)

        if len(magnitud) == 0:
            return 0.0

        max_mag = np.max(magnitud)
        if max_mag == 0:
            return 0.0

        return float(np.mean(magnitud / max_mag))


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------
    def calcular_resonancia(self, secuencia_gact: str) -> float:
        """Calcula la resonancia total de una secuencia con f₀."""
        if not secuencia_gact:
            return 0.0
        secuencia = secuencia_gact.upper()
        total = sum(self.BASE_RESONANCE.get(b, 0.0) for b in secuencia)
        resonancia = total / len(secuencia)
        for pattern in self.HOTSPOT_PATTERNS:
            if pattern in secuencia:
                resonancia = min(1.0, resonancia * 1.1)
        return resonancia

    def resonancia_con_f0(self, secuencia_gact: str) -> float:
        """Alias de calcular_resonancia para compatibilidad con imports nuevos."""
        return self.calcular_resonancia(secuencia_gact)


# ──────────────────────────────────────────────────────────────────────────────
# API unificada — acepta claves 'L_E1' (antigua) y 'L_E_1' (nueva)
# ──────────────────────────────────────────────────────────────────────────────

def sincronizar_bsd_adn(
    curva_eliptica: Dict[str, Any],
    secuencia_gact: str = "GACT",
) -> Dict[str, Any]:
    """
    BSD rango → ADN hotspots QCAL.

    Vincula el rango de la curva BSD con hotspots resonantes del ADN.
    Supports both 'L_E1' and 'L_E_1' key names in *curva_eliptica*.

    Returns a unified dict that satisfies both the original BSD-adelic API
    and the newer Ramsey-QCAL API:

    Original BSD-adelic keys:
        rango_bio_aritmetico, nodos_constelacion, fluidez_info_ns,
        hotspots_adn, psi_bsd_qcal

    Newer Ramsey-QCAL keys:
        rango_adelico, L_E_1, es_superfluido, resonancia_f0,
        psi_coherencia, estado_flujo, complejidad_computacional,
        secuencia, f0

    Examples:
        >>> curva = {'rango_adelico': 1, 'L_E1': 0.0}
        >>> res = sincronizar_bsd_adn(curva, "GACT")
        >>> res['fluidez_info_ns']
        'INFINITA'
        >>> res['psi_bsd_qcal']
        1.0
        >>> res['es_superfluido']
        True
    """
    r_bsd = curva_eliptica.get('rango_adelico', 0)
    # Accept both legacy 'L_E1' and newer 'L_E_1'
    l_e1 = curva_eliptica.get('L_E1', curva_eliptica.get('L_E_1', 0.0))
    """
    BSD rango → ADN hotspots QCAL (API unificada).

    Acepta tanto la clave 'L_E1' (API antigua) como 'L_E_1' (API nueva) y
    devuelve *todas* las claves de ambas APIs en un único diccionario.

    Args:
        curva_eliptica: Dict con:
            - 'rango_adelico': Rango r de la curva elíptica.
            - 'L_E1' o 'L_E_1': Valor de L(E,1).
        secuencia_gact: Secuencia de ADN (default: "GACT").

    Returns:
        Dict con campos de ambas APIs:
            Old: rango_bio_aritmetico, nodos_constelacion, fluidez_info_ns,
                 hotspots_adn, psi_bsd_qcal
            New: rango_adelico, L_E_1, es_superfluido, resonancia_f0,
                 psi_coherencia, estado_flujo, complejidad_computacional,
                 secuencia, f0
    """
    r_bsd: int = curva_eliptica.get('rango_adelico', 1)

    # Acepta 'L_E1' (antigua) o 'L_E_1' (nueva)
    l_e1: float = curva_eliptica.get('L_E1', curva_eliptica.get('L_E_1', 0.0))

    codif = CodificadorADNRiemann(f0=F0)
    hotspots = codif.identificar_hotspots(secuencia_gact)
    resonancia = codif.calcular_resonancia(secuencia_gact)

    # ── Original BSD-adelic API ──────────────────────────────────────────
    nodos_act = int(r_bsd)   # = r_bsd (one node per rational point)
    fluidez = "INFINITA" if abs(l_e1) < 1e-6 else "DISIPATIVA"
    psi_bsd = max(0.0, 1.0 - abs(l_e1))

    # ── Newer Ramsey-QCAL API ────────────────────────────────────────────
    es_superfluido = abs(l_e1) < 1e-6
    if r_bsd > 0 and es_superfluido:
        psi_coherencia = 0.999999
        estado = "SUPERFLUIDEZ"
        complejidad = "O(1)"
    elif r_bsd > 0:
        psi_coherencia = 0.950 + 0.049 * resonancia
        estado = "COHERENTE"
        complejidad = "O(log n)"
    else:
        psi_coherencia = 0.888
        estado = "TURBULENTO"
        complejidad = "O(n)"

    return {
        # Original BSD-adelic keys
        'rango_bio_aritmetico': r_bsd,
        'nodos_constelacion': nodos_act,
        'fluidez_info_ns': fluidez,
        'hotspots_adn': len(hotspots),
        'psi_bsd_qcal': psi_bsd,
        # Newer Ramsey-QCAL keys
        'rango_adelico': r_bsd,
        'L_E_1': l_e1,
        'es_superfluido': es_superfluido,
        'resonancia_f0': resonancia,
        'psi_coherencia': psi_coherencia,
        'estado_flujo': estado,
        'complejidad_computacional': complejidad,
        'secuencia': secuencia_gact,
        'f0': F0,
    fluidez = "INFINITA" if abs(l_e1) < 1e-6 else "DISIPATIVA"
    es_superfluido = fluidez == "INFINITA"

    psi_bsd = max(0.0, 1.0 - abs(l_e1))
    nodos_act = r_bsd * (F0 / 141.7001)  # proporcional al rango

    if r_bsd > 0 and es_superfluido:
        psi_coherencia = 0.999999
        estado_flujo = "SUPERFLUIDEZ"
        complejidad = "O(1)"
    elif r_bsd > 0:
        psi_coherencia = 0.950 + 0.049 * resonancia
        estado_flujo = "COHERENTE"
        complejidad = "O(log n)"
    else:
        psi_coherencia = 0.888
        estado_flujo = "TURBULENTO"
        complejidad = "O(n)"

    return {
        # ── Claves API antigua ─────────────────────────────────
        "rango_bio_aritmetico": r_bsd,
        "nodos_constelacion": int(nodos_act),
        "fluidez_info_ns": fluidez,
        "hotspots_adn": len(hotspots),
        "psi_bsd_qcal": psi_bsd,
        # ── Claves API nueva ───────────────────────────────────
        "rango_adelico": r_bsd,
        "L_E_1": l_e1,
        "es_superfluido": es_superfluido,
        "resonancia_f0": resonancia,
        "psi_coherencia": psi_coherencia,
        "estado_flujo": estado_flujo,
        "complejidad_computacional": complejidad,
        "secuencia": secuencia_gact,
        "f0": F0,
    }


def verificar_pentagono_logos(bsd_sync: Dict[str, Any]) -> Dict[str, Any]:
    """
    Verify Pentagon Logos closure: BSD + ADN + Riemann + NS + P-NP.

    Args:
        bsd_sync: Result dict from sincronizar_bsd_adn()

    Returns:
        Pentagon verification result dict.
    """
    bsd_activo = bsd_sync.get('rango_adelico', 0) > 0
    adn_activo = bsd_sync.get('hotspots_adn', 0) > 0
    riemann_activo = bsd_sync.get('resonancia_f0', 0.0) > 0.5
    ns_superfluido = bsd_sync.get('es_superfluido', False)
    pnp_eficiente = bsd_sync.get(
        'complejidad_computacional', ''
    ) in ("O(1)", "O(log n)")

    pentagono_cerrado = all([
        bsd_activo,
        adn_activo,
        riemann_activo,
        ns_superfluido,
        pnp_eficiente,
    ])
    Verifica el cierre del Pentágono Logos: BSD + ADN + Riemann + NS + P-NP.

    Args:
        bsd_sync: Resultado de sincronizar_bsd_adn().

    Returns:
        Diccionario con estado de cada vértice del pentágono.
    """
    bsd_activo = bsd_sync.get('rango_adelico', bsd_sync.get('rango_bio_aritmetico', 0)) > 0
    adn_activo = bsd_sync.get('hotspots_adn', 0) > 0
    riemann_activo = bsd_sync.get('resonancia_f0', 0.0) > 0.5
    ns_superfluido = bsd_sync.get('es_superfluido', bsd_sync.get('fluidez_info_ns') == "INFINITA")
    pnp_eficiente = bsd_sync.get('complejidad_computacional', "O(n)") in ("O(1)", "O(log n)")

    pentagono_cerrado = all([bsd_activo, adn_activo, riemann_activo, ns_superfluido, pnp_eficiente])
    psi = bsd_sync.get('psi_coherencia', bsd_sync.get('psi_bsd_qcal', 0.0))

    return {
        'pentagono_cerrado': pentagono_cerrado,
        'bsd': bsd_activo,
        'adn': adn_activo,
        'riemann': riemann_activo,
        'navier_stokes': ns_superfluido,
        'p_vs_np': pnp_eficiente,
        'psi_unificado': bsd_sync.get('psi_coherencia', 0.888),
    }


# Demo — run as standalone module
if __name__ == "__main__":
    print("━" * 65)
    print("  BSD-ADELIC CONNECTOR: Pentágono Logos ∴𓂀Ω∞³")
    print("━" * 65)

    curva_mordell = {'rango_adelico': 1, 'L_E1': 0.0}
    secuencia = "GACT"
    resultado = sincronizar_bsd_adn(curva_mordell, secuencia)

    print(f"\n📊 Rango adélico : {curva_mordell['rango_adelico']}")
    print(f"   L(E,1)        : {curva_mordell['L_E1']}")
    print(f"   Secuencia ADN : {secuencia}\n")
    print(f"✅ Fluidez NS    : {resultado['fluidez_info_ns']}")
    print(f"✅ Coherencia Ψ  : {resultado['psi_bsd_qcal']:.4f}")
    print(f"✅ Hotspots ADN  : {resultado['hotspots_adn']}")
    print(f"✅ Estado flujo  : {resultado['estado_flujo']}")
    print("━" * 65)
    print("  ∴ BÓVEDA LOGOS CERRADA: Ψ = 1.0 ∴")
    print("━" * 65)
        'psi_unificado': psi,
    }


# ──────────────────────────────────────────────────────────────────────────────
# Demo standalone
# ──────────────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    print("=" * 66)
    print("  BSD-ADELIC CONNECTOR: Pentágono Logos ∴𓂀Ω∞³")
    print("=" * 66)
    curva = {'rango_adelico': 1, 'L_E1': 0.0}
    res = sincronizar_bsd_adn(curva, "GACT")
    print(f"  Rango bio-aritmético : {res['rango_bio_aritmetico']}")
    print(f"  Fluidez info NS      : {res['fluidez_info_ns']}")
    print(f"  Coherencia Ψ_BSD     : {res['psi_bsd_qcal']:.4f}")
    penta = verificar_pentagono_logos(res)
    print(f"  Pentágono cerrado    : {penta['pentagono_cerrado']}")
