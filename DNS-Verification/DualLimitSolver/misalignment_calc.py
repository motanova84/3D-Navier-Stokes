#!/usr/bin/env python3
"""
Configuration files for Clay Millennium project
"""

# Python dependencies
requirements_txt = """numpy>=1.21.0
scipy>=1.7.0
matplotlib>=3.4.0
h5py>=3.6.0
pytest>=7.0.0
"""

# Conda environment
environment_yml = """name: clay_navier_stokes
channels:
  - conda-forge
  - defaults
dependencies:
  - python=3.9
  - numpy>=1.21
  - scipy>=1.7
  - matplotlib>=3.4
  - h5py>=3.6
  - pytest>=7.0
  - pip
  - pip:
    - -r requirements.txt
"""

# Docker compose
docker_compose_yml = """version: '3.8'

services:
  clay-verification:
    build:
      context: .
      dockerfile: Dockerfile
    volumes:
      - ./Results:/workspace/Results
      - ./DNS-Verification:/workspace/DNS-Verification
      - ./Lean4-Formalization:/workspace/Lean4-Formalization
    environment:
      - PYTHONPATH=/workspace
    command: bash -c "python3 DNS-Verification/DualLimitSolver/psi_ns_solver.py"

  lean4-builder:
    image: leanprover/lean4:latest
    volumes:
      - ./Lean4-Formalization:/workspace
    working_dir: /workspace
    command: lake build
"""

# Lean lakefile
lakefile_lean = """import Lake
open Lake DSL

package NavierStokes {
  -- Add configuration here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib NavierStokes {
  -- Lean library configuration
}
"""

# Save files
import os

def create_configuration_files(base_dir: str):
    """Create all configuration files"""
    
    config_dir = os.path.join(base_dir, "Configuration")
    
    files = {
        "requirements.txt": requirements_txt,
        "environment.yml": environment_yml,
        "docker-compose.yml": docker_compose_yml,
        "lakefile.lean": lakefile_lean
    }
    
    for filename, content in files.items():
        filepath = os.path.join(config_dir, filename)
        with open(filepath, 'w') as f:
            f.write(content.strip())
        print(f"Created: {filepath}")

if __name__ == "__main__":
    print("Configuration file templates created")
    print("Run create_configuration_files() to generate files")
