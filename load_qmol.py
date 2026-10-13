#!/usr/bin/env python3
"""
PyMOL Loader for QCAL-MOL (.qmol) Files
========================================

Loads custom .qmol files into PyMOL, extracts Bures distance (D_B)
from the extended atomic columns and injects it into B-factors for
colorimetric visualization under f_0 = 141.7001 Hz.

Usage in PyMOL:
    run load_qmol.py
    load_qmol rna_folding_qcal.qmol
"""

import os
import sys

try:
    import pymol
    from pymol import cmd
    PYMOL_AVAILABLE = True
except ImportError:
    PYMOL_AVAILABLE = False


def load_qcal_mol(filepath: str):
    """
    Carga un archivo .qmol personalizado en PyMOL, extrae la distancia de Bures
    de la columna extendida y la inyecta en el B-factor para visualización colorimétrica.
    """
    if not os.path.exists(filepath):
        print(f"Error: No se encontró el archivo {filepath}")
        return

    # Nombre del objeto basado en el archivo
    obj_name = os.path.splitext(os.path.basename(filepath))[0]

    # 1. Leer y parsear el archivo .qmol
    atom_data = []
    with open(filepath, "r", encoding="utf-8") as f:
        lines = f.readlines()

    for line in lines:
        if line.startswith("ATOM"):
            parts = line.split()
            atom_id = int(parts[1])
            atom_name = parts[2]
            res_name = parts[3]
            chain = parts[4]
            res_seq = int(parts[5])
            x = float(parts[6])
            y = float(parts[7])
            z = float(parts[8])
            bures_db = float(parts[9])   # Distancia de Bures almacenada
            local_psi = float(parts[10]) # Coherencia local Psi

            atom_data.append({
                "id": atom_id,
                "name": atom_name,
                "res": res_name,
                "chain": chain,
                "res_seq": res_seq,
                "coord": (x, y, z),
                "bures_db": bures_db,
                "psi": local_psi,
            })

    if not PYMOL_AVAILABLE:
        print(f"PyMOL no está instalado en este entorno de Python.")
        print(f"Se procesaron {len(atom_data)} átomos del archivo {filepath}.")
        return

    # 2. Construir la molécula en PyMOL cargando un PDB temporal
    temp_pdb = f"temp_render_qcal_{obj_name}.pdb"
    with open(temp_pdb, "w", encoding="utf-8") as p_file:
        for a in atom_data:
            line = (
                f"ATOM  {a['id']:5d}  {a['name']:<4s} {a['res']:3s} {a['chain']}{a['res_seq']:4d}    "
                f"{a['coord'][0]:8.3f}{a['coord'][1]:8.3f}{a['coord'][2]:8.3f}  "
                f"1.00 {a['bures_db']*1e5:6.2f}          {a['name'][0]:1s}\n"
            )
            p_file.write(line)
        p_file.write("END\n")

    # Cargar el archivo temporal en PyMOL
    cmd.load(temp_pdb, obj_name)
    if os.path.exists(temp_pdb):
        os.remove(temp_pdb)

    # 3. Aplicar propiedades estéticas y coloración basada en la Métrica de Bures
    cmd.hide("everything", obj_name)
    cmd.show("cartoon", obj_name)
    cmd.show("spheres", f"{obj_name} and name P")
    cmd.set("sphere_scale", 0.4, obj_name)

    # Configurar el espectro de color basado en el B-factor (que almacena D_B escalado)
    cmd.color("white", obj_name)
    cmd.spectrum("b", "blue_white_red", obj_name)

    # Modificaciones visuales del entorno QCAL
    cmd.bg_color("black")
    cmd.set("ray_shadows", 1)
    cmd.set("antialias", 2)

    print(f"--- QCAL-MOL CARGADO EXITOSAMENTE: {obj_name} ---")
    print(f"Visualización coloreada por Distancia de Bures (f_0 = 141.7001 Hz)")


if PYMOL_AVAILABLE:
    cmd.extend("load_qmol", load_qcal_mol)

if __name__ == "__main__":
    if len(sys.argv) > 1:
        load_qcal_mol(sys.argv[1])
    else:
        print("Uso en consola: python3 load_qmol.py <archivo.qmol>")
        print("Uso en PyMOL: run load_qmol.py; load_qmol <archivo.qmol>")
