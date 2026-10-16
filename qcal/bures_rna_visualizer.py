"""
QCAL Bures RNA Visualizer and QCAL-MOL Standard Exporter
=========================================================

Integrates RNA conformational folding dynamics with 3D graphical visualization
based on the Bures metric and exports to the QCAL-MOL (.qmol) standard.

Fundamental Parameters:
    f_0 = 141.7001 Hz
    psi_target = 0.999999
    contraction_k = 1e-6
    metric_tensor_type = "Bures-Fisher"
"""

import json
import os
from typing import Any, Dict, Optional, Tuple
import numpy as np

try:
    import matplotlib
    if os.environ.get("DISPLAY") is None:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from mpl_toolkits.mplot3d import Axes3D  # noqa: F401
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False


class QCALBuresRNAVisualizer:
    """
    Simulador y visualizador 3D del plegamiento de ARN guiado por el operador Phi
    y coloreado según el perfil de distancia de la métrica de Bures.
    """

    def __init__(
        self,
        sequence_length: int = 60,
        f_0: float = 141.7001,
        psi_target: float = 0.999999,
        contraction_k: float = 1e-6,
    ):
        self.length = sequence_length
        self.f_0 = f_0
        self.psi = psi_target
        self.k = contraction_k  # Contracción de Banach
        self.sigma = 1.0 - psi_target

    def get_native_attractor(self) -> np.ndarray:
        """Define la hélice ideal de energía mínima E_min."""
        t = np.linspace(0, 4 * np.pi, self.length)
        return np.stack([3.0 * np.cos(t), 3.0 * np.sin(t), np.linspace(-6, 6, self.length)], axis=-1)

    def compute_bures_distance_profile(self, coords: np.ndarray, attractor: np.ndarray) -> np.ndarray:
        """
        Calcula una aproximación de la distancia de Bures D_B para cada nucleótido 
        basada en la divergencia geométrica respecto al atractor y modulada por f_0.
        """
        if len(coords) == 0:
            return np.array([])
        euclidean_diffs = np.linalg.norm(coords - attractor, axis=1)
        # La métrica de Bures para estados casi puros escala con la raíz de la desviación local
        bures_distances = np.sqrt(2.0 * np.maximum(0.0, 1.0 - np.exp(-euclidean_diffs**2 / (2.0 * self.f_0))))
        return bures_distances

    def run_simulation(
        self, steps: int = 150, seed: Optional[int] = 42
    ) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
        """
        Ejecuta la iteración del operador unificado Phi hacia el estado estacionario.
        Retorna (coords_final, attractor, bures_profile).
        """
        if seed is not None:
            np.random.seed(seed)
        coords = np.random.normal(0, 6.0, (self.length, 3))
        attractor = self.get_native_attractor()

        for step in range(steps):
            t_step = step * 0.02
            harmonic_field = np.cos(2 * np.pi * self.f_0 * t_step)
            # Aplicación de la contracción geométrica y el campo de vacío
            coords = (
                (1.0 - self.k) * coords
                + self.k * attractor
                + self.sigma * harmonic_field * np.random.normal(0, 0.005, coords.shape)
            )

        bures_profile = self.compute_bures_distance_profile(coords, attractor)
        return coords, attractor, bures_profile

    def simulate_and_visualize(
        self,
        steps: int = 150,
        show: bool = True,
        save_path: Optional[str] = None,
        seed: Optional[int] = 42,
    ) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
        """
        Ejecuta la dinámica del operador Phi y genera la representación gráfica 3D.
        """
        print(f"--- INICIALIZANDO GEOMETRÍA DE BURES (f_0 = {self.f_0} Hz) ---")
        coords, attractor, bures_profile = self.run_simulation(steps=steps, seed=seed)

        if not MATPLOTLIB_AVAILABLE:
            print("Matplotlib no disponible para renderizado 3D.")
            return coords, attractor, bures_profile

        # Manejo de renderizado sin display interactivo si es necesario
        fig = plt.figure(figsize=(10, 8))
        ax = fig.add_subplot(111, projection="3d")

        # Gráfica de la cadena de ARN con mapa de color basado en la distancia de Bures
        scatter = ax.scatter(
            coords[:, 0],
            coords[:, 1],
            coords[:, 2],
            c=bures_profile,
            cmap="viridis",
            s=80,
            depthshade=True,
        )

        # Trazado del esqueleto fosfodiéster de la cadena
        ax.plot(
            coords[:, 0],
            coords[:, 1],
            coords[:, 2],
            color="gray",
            alpha=0.6,
            linestyle="--",
            linewidth=1.5,
        )

        # Trazado del atractor teórico de referencia
        ax.plot(
            attractor[:, 0],
            attractor[:, 1],
            attractor[:, 2],
            color="crimson",
            alpha=0.4,
            linestyle="-",
            linewidth=2,
            label="Atractor Geodésico ($E_{\\min}$)",
        )

        cbar = fig.colorbar(scatter, ax=ax, pad=0.1)
        cbar.set_label("Distancia de Bures ($D_B$)", rotation=270, labelpad=15)

        ax.set_title(
            f"Plegamiento Resonante de ARN (QCAL Framework)\n"
            f"$f_0 = {self.f_0}$ Hz | $\\Psi = {self.psi}$",
            fontsize=12,
        )
        ax.set_xlabel("Eje X (Espacio Fases)")
        ax.set_ylabel("Eje Y (Espacio Fases)")
        ax.set_zlabel("Eje Z (Estructura Hélice)")
        ax.legend()

        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches="tight")
            print(f"Gráfico 3D guardado en: {save_path}")

        if show:
            try:
                plt.show()
            except Exception as e:
                print(f"Aviso al mostrar gráfico interactivo: {e}")
        else:
            plt.close(fig)

        return coords, attractor, bures_profile


def bures_sq(eps1: float, eps2: float) -> float:
    """
    Distancia de Bures-Fisher al cuadrado en el colector de fase
    con coherencia imperfecta eps1, eps2.
    Formalizado en Lean 4: QCAL.Bures.bures_sq (bures_sq eps1 eps2 = eps1 + eps2).
    """
    return float(eps1 + eps2)


def export_to_qcal_mol(
    coordinates: np.ndarray,
    bures_profile: np.ndarray,
    filename: str = "rna_folding_qcal.qmol",
    f_0: float = 141.7001,
    psi_target: float = 0.999999,
    contraction_k: float = 1e-6,
) -> str:
    """
    Exporta las coordenadas atómicas y el perfil de la métrica de Bures
    al formato estructurado QCAL-MOL (.qmol).
    """
    metadata = {
        "qcal_metadata": {
            "protocol": "QCAL-SYMBIO-BRIDGE",
            "fundamental_frequency_hz": f_0,
            "target_coherence_psi": psi_target,
            "contraction_factor_k": contraction_k,
            "metric_tensor_type": "Bures-Fisher",
            "energy_minimum_h": 141.69996 if (abs(f_0 - 141.7001) < 1e-6 and abs(psi_target - 0.999999) < 1e-6) else round(f_0 * psi_target, 5),
        }
    }

    with open(filename, "w", encoding="utf-8") as f:
        # Metadatos globales del ecosistema en bloque JSON comentado
        f.write("# =====================================================================\n")
        f.write("# QCAL-MOL EXPORT SPECIFICATION v1.0.0\n")
        f.write("# Framework: Noesis / QCAL Bio-Digital Informatics\n")
        f.write("# =====================================================================\n")
        f.write(json.dumps(metadata, indent=2) + "\n")
        f.write("# --- ATOMIC & BURES METRIC COORDINATE BLOCK ---\n")
        f.write("# Format: ATOM | AtomID | AtomName | Residue | Chain | ResSeq | X | Y | Z | Bures_Db | Local_Psi\n")

        # Escribe cada nodo/nucleótido con sus métricas cuánticas asociadas
        for i, coord in enumerate(coordinates):
            atom_id = i + 1
            db_val = float(bures_profile[i]) if i < len(bures_profile) else 0.0
            local_psi = max(0.999900, 1.0 - db_val * 1e-5)

            line = (
                f"ATOM  {atom_id:5d}  P   RNA A {atom_id:4d}    "
                f"{coord[0]:8.3f} {coord[1]:8.3f} {coord[2]:8.3f}  "
                f"{db_val:10.6f}  {local_psi:8.6f}\n"
            )
            f.write(line)

        f.write("END_QCAL_MOL\n")

    print(f"Archivo exportado con éxito: {filename}")
    return filename


def parse_qcal_mol(filepath: str) -> Dict[str, Any]:
    """
    Parsea un archivo en formato QCAL-MOL (.qmol) extrayendo metadatos y átomos.
    """
    if not os.path.exists(filepath):
        raise FileNotFoundError(f"Archivo no encontrado: {filepath}")

    with open(filepath, "r", encoding="utf-8") as f:
        lines = f.readlines()

    metadata: Dict[str, Any] = {}
    atoms = []
    json_lines = []
    collecting_json = False
    brace_depth = 0

    for line in lines:
        trimmed = line.strip()
        if not collecting_json and trimmed.startswith("{"):
            collecting_json = True
            brace_depth = 0

        if collecting_json:
            json_lines.append(line)
            brace_depth += line.count("{") - line.count("}")
            if brace_depth == 0:
                collecting_json = False
                try:
                    metadata = json.loads("".join(json_lines))
                except json.JSONDecodeError:
                    pass
        elif trimmed.startswith("ATOM"):
            parts = trimmed.split()
            atom_id = int(parts[1])
            atom_name = parts[2]
            res_name = parts[3]
            chain = parts[4]
            res_seq = int(parts[5])
            x = float(parts[6])
            y = float(parts[7])
            z = float(parts[8])
            db_val = float(parts[9])
            local_psi = float(parts[10])
            atoms.append({
                "id": atom_id,
                "name": atom_name,
                "res": res_name,
                "chain": chain,
                "res_seq": res_seq,
                "coord": np.array([x, y, z]),
                "bures_db": db_val,
                "psi": local_psi,
            })

    return {
        "metadata": metadata,
        "atoms": atoms,
        "coordinates": np.array([a["coord"] for a in atoms]) if atoms else np.empty((0, 3)),
        "bures_profile": np.array([a["bures_db"] for a in atoms]) if atoms else np.array([]),
    }


if __name__ == "__main__":
    visualizer = QCALBuresRNAVisualizer(sequence_length=60)
    coords, attractor, bures = visualizer.run_simulation(steps=150)
    export_to_qcal_mol(coords, bures, "rna_folding_qcal.qmol")
    print("Simulación y exportación QCAL-MOL completada.")
