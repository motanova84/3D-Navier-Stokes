#!/usr/bin/env python3
"""
QCAL Bures RNA Visualizer and Exporter CLI
==========================================

Runs the QCAL RNA folding simulation under Operator Phi,
computes the Bures metric distance profile, exports the structure
in QCAL-MOL (.qmol) format, and generates a 3D visualization.

Usage:
    python3 qcal_bures_rna_visualizer.py [--steps 150] [--output rna_folding_qcal.qmol] [--save-plot bures_3d.png]
"""

import argparse
import sys
from qcal.bures_rna_visualizer import (
    QCALBuresRNAVisualizer,
    export_to_qcal_mol,
    parse_qcal_mol,
)


def main():
    parser = argparse.ArgumentParser(
        description="QCAL RNA Bures Metric Simulator, Visualizer, and .qmol Exporter"
    )
    parser.add_argument("--length", type=int, default=60, help="Longitud de secuencia de ARN (default: 60)")
    parser.add_argument("--steps", type=int, default=150, help="Pasos de simulación (default: 150)")
    parser.add_argument("--f0", type=float, default=141.7001, help="Frecuencia fundamental f_0 en Hz")
    parser.add_argument("--psi", type=float, default=0.999999, help="Coherencia cuántica objetivo Psi")
    parser.add_argument("--output", type=str, default="rna_folding_qcal.qmol", help="Ruta de exportación .qmol")
    parser.add_argument("--save-plot", type=str, default="visualizations/rna_bures_3d.png", help="Guardar gráfico 3D como imagen")
    parser.add_argument("--no-show", action="store_true", help="No abrir ventana interactiva de visualización")

    args = parser.parse_args()

    print("=====================================================================")
    print("      QCAL BURES RNA VISUALIZATION & QMOL EXPORT PROTOCOL           ")
    print(f"      f_0 = {args.f0} Hz | Psi = {args.psi} | k = 1e-6               ")
    print("=====================================================================")

    visualizer = QCALBuresRNAVisualizer(
        sequence_length=args.length,
        f_0=args.f0,
        psi_target=args.psi,
    )

    coords, attractor, bures_profile = visualizer.simulate_and_visualize(
        steps=args.steps,
        show=not args.no_show,
        save_path=args.save_plot,
    )

    export_path = export_to_qcal_mol(
        coords,
        bures_profile,
        filename=args.output,
        f_0=args.f0,
        psi_target=args.psi,
    )

    # Verificación de integridad del archivo exportado
    parsed = parse_qcal_mol(export_path)
    print(f"Verificación de archivo: {len(parsed['atoms'])} átomos correctamente serializados en .qmol")
    print(f"Distancia media de Bures: {bures_profile.mean():.6e}")
    print(f"Distancia mínima de Bures (Atractor E_min): {bures_profile.min():.6e}")
    print("--- PROTOCOLO COMPLETADO EXITOSAMENTE ---")


if __name__ == "__main__":
    main()
