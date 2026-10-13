#!/usr/bin/env python3
"""
PyMOL 360-Degree Rotation Sequence and Movie Generator (export_rotation_movie.py)
==================================================================================

Generates a 360-degree rotation frame sequence with raytracing in PyMOL
for molecular dynamics video compilation under the Bures metric and QCAL.

Usage in PyMOL:
    run load_qmol.py
    load_qmol rna_folding_qcal.qmol
    run export_rotation_movie.py
    export_qcal_movie
"""

import os
import sys

try:
    import pymol
    from pymol import cmd
    PYMOL_AVAILABLE = True
except ImportError:
    PYMOL_AVAILABLE = False


def generate_qcal_rotation_movie(
    object_name: str = "rna_folding_qcal",
    output_dir: str = "qcal_movie_frames",
    total_frames: int = 120,
    width: int = 1920,
    height: int = 1080,
):
    """
    Genera una secuencia de fotogramas de rotación 360 grados con raytracing 
    y prepara la exportación del video del plegamiento de ARN bajo QCAL.
    """
    print(f"--- INICIALIZANDO GENERACIÓN DE SECUENCIA DE VÍDEO (Frames: {total_frames}) ---")

    if not PYMOL_AVAILABLE:
        print("Error: PyMOL no está disponible en este entorno.")
        return

    if object_name not in cmd.get_object_list():
        print(f"Error: El objeto '{object_name}' no está cargado en la sesión de PyMOL.")
        return

    # Crear directorio para los fotogramas si no existe
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    # Configuración estética de la escena
    cmd.bg_color("black")
    cmd.hide("everything", object_name)
    cmd.show("cartoon", object_name)
    cmd.show("spheres", f"{object_name} and name P")
    cmd.set("sphere_scale", 0.35, f"{object_name} and name P")

    # Parámetros de renderizado y trazado de rayos
    cmd.set("ray_shadows", 1)
    cmd.set("ray_trace_mode", 1)
    cmd.set("antialias", 3)

    cmd.center(object_name)
    cmd.zoom(object_name, buffer=4.0)

    # Ángulo de rotación por fotograma
    angle_step = 360.0 / total_frames

    print(f"Renderizando {total_frames} fotogramas en resolución {width}x{height}...")

    for frame in range(total_frames):
        # Rotar la vista en el eje Y
        cmd.turn("y", angle_step)

        # Nombre del fotograma formateado con ceros a la izquierda
        frame_filename = os.path.join(output_dir, f"frame_{frame:04d}.png")

        # Renderizar fotograma con trazado de rayos
        cmd.ray(width, height)
        cmd.png(frame_filename)

        if frame % 15 == 0:
            print(f"Progreso: Fotograma {frame}/{total_frames} renderizado...")

    print("--- SECUENCIA COMPLETADA CON ÉXITO ---")
    print(f"Los fotogramas se han guardado en la carpeta: {os.path.abspath(output_dir)}")
    print("Puedes ensamblarlos en un archivo MP4 utilizando herramientas externas como FFmpeg con el comando:")
    print(f"ffmpeg -framerate 30 -i {output_dir}/frame_%04d.png -c:v libx264 -pix_fmt yuv420p qcal_rna_rotation.mp4")


if PYMOL_AVAILABLE:
    cmd.extend("export_qcal_movie", generate_qcal_rotation_movie)

if __name__ == "__main__":
    if len(sys.argv) > 1:
        generate_qcal_rotation_movie(object_name=sys.argv[1])
    else:
        print("Uso en consola: python3 export_rotation_movie.py <nombre_objeto>")
        print("Uso en PyMOL: run export_rotation_movie.py; export_qcal_movie")
