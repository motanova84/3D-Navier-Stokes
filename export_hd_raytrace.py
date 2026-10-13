#!/usr/bin/env python3
"""
PyMOL HD Raytracing Automation Script (export_hd_raytrace.py)
=============================================================

Automates high-definition raytracing visualization of RNA structures
under the Bures metric at fundamental frequency f_0 = 141.7001 Hz.

Usage in PyMOL:
    run load_qmol.py
    load_qmol rna_folding_qcal.qmol
    run export_hd_raytrace.py
    export_qcal_hd
"""

import os
import sys

try:
    import pymol
    from pymol import cmd
    PYMOL_AVAILABLE = True
except ImportError:
    PYMOL_AVAILABLE = False


def export_qcal_hd_image(
    object_name: str = "rna_folding_qcal",
    filename: str = "qcal_rna_bures_hd.png",
    width: int = 3840,
    height: int = 2160,
    dpi: int = 300,
):
    """
    Automatiza la configuración visual de alta definición y exporta un renderizado 
    por trazado de rayos (raytracing) de la estructura de ARN bajo la métrica de Bures.
    """
    print(f"--- INICIALIZANDO RENDERIZADO HD QCAL (Objeto: {object_name}) ---")

    if not PYMOL_AVAILABLE:
        print("Error: PyMOL no está disponible en este entorno.")
        return

    if object_name not in cmd.get_object_list():
        print(f"Error: El objeto '{object_name}' no está cargado en la sesión de PyMOL.")
        return

    # 1. Configuración geométrica y estética de la escena
    cmd.bg_color("black")
    cmd.hide("everything", object_name)

    # Representación en cinta (cartoon) para el esqueleto de ARN
    cmd.show("cartoon", object_name)
    cmd.set("cartoon_oval_profile", 1.0, object_name)
    cmd.set("cartoon_transparency", 0.15, object_name)

    # Resaltar los átomos de Fósforo (P) como nodos nodales de resonancia
    cmd.show("spheres", f"{object_name} and name P")
    cmd.set("sphere_scale", 0.35, f"{object_name} and name P")

    # 2. Configuración avanzada de iluminación y sombras para Raytracing
    cmd.set("ray_shadows", 1)
    cmd.set("ray_shadow_decay_factor", 0.1)
    cmd.set("ray_shadow_decay_range", 2.0)
    cmd.set("ambient", 0.4)
    cmd.set("direct", 0.6)
    cmd.set("reflect", 0.2)
    cmd.set("shininess", 50)
    cmd.set("specular", 0.5)
    cmd.set("antialias", 3)

    # Centrar y orientar la vista óptima
    cmd.center(object_name)
    cmd.zoom(object_name, buffer=4.0)
    cmd.turn("y", 45)
    cmd.turn("x", 15)

    # 3. Ejecución del Raytracing y Exportación en Alta Definición (4K UHD)
    print(f"Ejecutando Raytracing a {width}x{height} píxeles ({dpi} DPI)...")

    # ray_trace_mode=1 activa el modo de líneas de contorno y sombreado avanzado
    cmd.set("ray_trace_mode", 1)

    # Renderizado y guardado de la imagen final
    cmd.ray(width, height, angle=0, dpi=dpi)
    cmd.png(filename)

    print(f"--- IMAGEN EXPORTADA CON ÉXITO: {os.path.abspath(filename)} ---")
    print("La geometría de Bures ha quedado sellada en el archivo de imagen.")


if PYMOL_AVAILABLE:
    cmd.extend("export_qcal_hd", export_qcal_hd_image)

if __name__ == "__main__":
    if len(sys.argv) > 1:
        export_qcal_hd_image(object_name=sys.argv[1])
    else:
        print("Uso en consola: python3 export_hd_raytrace.py <nombre_objeto>")
        print("Uso en PyMOL: run export_hd_raytrace.py; export_qcal_hd")
