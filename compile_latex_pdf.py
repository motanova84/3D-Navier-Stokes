#!/usr/bin/env python3
"""
Compila el documento LaTeX a PDF profesional.
"""

import subprocess
import os
from pathlib import Path

def compile_latex_to_pdf():
    """
    Compila el documento LaTeX completo.
    """
    
    # Crear directorio
    Path("artifacts/paper").mkdir(parents=True, exist_ok=True)
    
    # Guardar LaTeX
    # Read the proof content from file
    with open('rigorous_proof_psi_nse.tex', 'r', encoding='utf-8') as f:
        proof_content = f.read()
    
    # Extract content between \begin{document} and \end{document}
    proof_body = proof_content.split(r'\begin{document}')[1].split(r'\end{document}')[0]
    
    latex_content = r"""
\documentclass[12pt,a4paper]{article}
\usepackage[utf8]{inputenc}
\usepackage{amsmath,amsthm,amssymb}
\usepackage{mathtools}
\usepackage{hyperref}
\usepackage{geometry}
\usepackage{graphicx}
\usepackage{tikz}
\usepackage{pgfplots}

\geometry{margin=1in}

\newtheorem{theorem}{Teorema}
\newtheorem{lemma}{Lema}
\newtheorem{proposition}{Proposición}
\newtheorem{corollary}{Corolario}
\theoremstyle{definition}
\newtheorem{definition}{Definición}
\theoremstyle{remark}
\newtheorem{remark}{Observación}

\title{\textbf{Regularidad Global para las Ecuaciones \\
       Tridimensionales de Navier-Stokes \\
       con Acoplamiento Cuántico-Geométrico}}
\author{José Manuel Mota Burruezo \\
        Instituto Consciencia Cuántica \\
        \texttt{jmmb@conscienciaquantica.org}}
\date{Noviembre 2025}

\begin{document}

\maketitle

\begin{abstract}
Demostramos la regularidad global de soluciones para las ecuaciones tridimensionales 
de Navier-Stokes modificadas por un término de acoplamiento cuántico-geométrico 
$\Phi_{ij}(\Psi)$ derivado desde primeros principios de teoría cuántica de campos 
en espacio-tiempo curvo. La prueba se basa en una estimación uniforme de la 
vorticidad mediante el criterio de Beale-Kato-Majda, explotando las propiedades 
regularizantes del tensor $\Phi_{ij}$. Mostramos que el campo de coherencia 
$\Psi = \mathcal{I}[u] \times A_{\text{eff}}^2$ actúa como un ``amortiguador 
geométrico'' que previene la formación de singularidades. La frecuencia fundamental 
$f_0 = 141.7001$ Hz emerge naturalmente de la conexión con los zeros de la función 
zeta de Riemann.

\noindent \textbf{Palabras clave:} Navier-Stokes, regularidad global, coherencia 
cuántica, teoría cuántica de campos, problema del milenio

\noindent \textbf{MSC 2020:} 35Q30, 76D05, 81T20, 35B65
\end{abstract}

\tableofcontents
\newpage

""" + proof_body + r"""

\end{document}
"""
    
    # Guardar
    tex_file = "artifacts/paper/psi_nse_global_regularity.tex"
    with open(tex_file, 'w', encoding='utf-8') as f:
        f.write(latex_content)
    
    print(f"✅ Archivo LaTeX guardado: {tex_file}")
    
    # Compilar (requiere pdflatex instalado)
    try:
        # Primera compilación
        subprocess.run(['pdflatex', '-interaction=nonstopmode', 
                       '-output-directory=artifacts/paper', tex_file],
                      check=True, capture_output=True)
        
        # Segunda compilación (para referencias)
        subprocess.run(['pdflatex', '-interaction=nonstopmode',
                       '-output-directory=artifacts/paper', tex_file],
                      check=True, capture_output=True)
        
        print(f"✅ PDF compilado: artifacts/paper/psi_nse_global_regularity.pdf")
        
    except subprocess.CalledProcessError:
        print("⚠️  pdflatex no disponible. Instalando Overleaf online:")
        print("   1. Ir a https://www.overleaf.com")
        print("   2. Subir archivo .tex")
        print("   3. Compilar online")
    except FileNotFoundError:
        print("⚠️  pdflatex no instalado. Opciones:")
        print("   - Linux: sudo apt-get install texlive-full")
        print("   - Mac: brew install mactex")
        print("   - Windows: https://miktex.org/download")
        print("   - Online: https://www.overleaf.com")

if __name__ == '__main__':
    compile_latex_to_pdf()
