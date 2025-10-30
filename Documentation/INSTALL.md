# 📋 Guía de Instalación

## Requisitos del Sistema

### Software Base
- **Sistema Operativo**: Linux (Ubuntu 20.04+), macOS 10.15+, o WSL2 en Windows
- **RAM**: Mínimo 8 GB (recomendado 16 GB para simulaciones grandes)
- **Espacio en disco**: ~10 GB libres

## Instalación de Lean4

### Método 1: Usando elan (recomendado)
```bash
# Instalar elan (gestor de versiones de Lean)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Agregar al PATH
source ~/.profile  # o ~/.bashrc / ~/.zshrc según tu shell

# Verificar instalación
lean --version
lake --version
```

### Método 2: Instalación manual
Consulte https://leanprover-community.github.io/install/linux.html

## Instalación del Entorno Computacional

### Opción A: Usando Conda (recomendado)
```bash
# Crear entorno desde archivo
cd Configuration
conda env create -f environment.yml

# Activar entorno
conda activate navier-stokes-qcal

# Verificar instalación
python -c "import numpy, scipy, matplotlib; print('OK')"
```

### Opción B: Usando pip
```bash
# Crear entorno virtual
python3 -m venv venv
source venv/bin/activate  # En Windows: venv\Scripts\activate

# Instalar dependencias
pip install -r Configuration/requirements.txt
```

## Construcción del Proyecto Lean4

```bash
# Navegar al directorio Lean4
cd Lean4-Formalization

# Descargar cache de mathlib (acelera compilación)
lake exe cache get

# Compilar proyecto
lake build

# Verificar que compila sin errores
lake env lean --version
```

## Verificación de la Instalación

### Test Lean4
```bash
cd Lean4-Formalization
lake build
# Si compila sin errores, Lean4 está correctamente configurado
```

### Test Computacional
```bash
cd Computational-Verification/DNS-Solver
python -c "from psi_ns_solver import PsiNSSolver; print('OK')"
```

### Ejecución de Pruebas Iniciales
```bash
# Desde la raíz del proyecto
./Scripts/deploy.sh
```

## Solución de Problemas Comunes

### Lean4 no encuentra mathlib
```bash
cd Lean4-Formalization
lake clean
lake exe cache get
lake build
```

### Error de módulos Python
```bash
conda activate navier-stokes-qcal
pip install --upgrade -r Configuration/requirements.txt
```

### Problemas de permisos en Linux
```bash
chmod +x Scripts/*.sh
```

## Configuración Avanzada

### Configuración para HPC
Si ejecuta en cluster de alto rendimiento:
```bash
# Módulos típicos
module load python/3.9
module load gcc/11.2
module load openmpi/4.1

# Instalar en espacio de usuario
pip install --user -r Configuration/requirements.txt
```

### Configuración de GPU (opcional)
Para acelerar simulaciones grandes:
```bash
# Instalar CuPy (equivalente GPU de NumPy)
conda install -c conda-forge cupy
```

## Siguientes Pasos

Después de la instalación exitosa:
1. Revise `THEORY.md` para entender el marco teórico
2. Explore ejemplos en `Computational-Verification/`
3. Consulte `ROADMAP.md` para el plan de desarrollo

## Soporte

Para problemas o preguntas:
- Revise la documentación en `Documentation/`
- Consulte los issues en GitHub
- Revise los logs de error detalladamente
