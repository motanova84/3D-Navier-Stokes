#!/usr/bin/env python3
"""
Visualización del tensor Φ_ij y su efecto en NSE
"""

import numpy as np

try:
    import matplotlib
    matplotlib.use('Agg')  # Use non-interactive backend
    import matplotlib.pyplot as plt
    from mpl_toolkits.mplot3d import Axes3D
    PLOTTING_AVAILABLE = True
except ImportError:
    PLOTTING_AVAILABLE = False
    print("Warning: matplotlib not available. Cannot generate visualization.")

if not PLOTTING_AVAILABLE:
    import sys
    sys.exit(1)

# Configuración estética ∞³
plt.style.use('dark_background')
colors = ['#00ff41', '#ff006e', '#8338ec', '#ffbe0b']

# Physical parameters
F0 = 141.7001  # Hz - Resonance frequency
DECAY_FACTOR = 0.5  # Spatial decay rate
ENERGY_INITIAL = 100  # Initial energy value
ENERGY_GROWTH_RATE = 2  # NSE growth rate
ENERGY_SATURATION = 50  # Psi-NSE saturation factor
SPATIAL_SCALE = 100  # Scale for interference pattern

fig = plt.figure(figsize=(15, 10))

# ══════════════════════════════════════════
# Panel 1: Espectro de Φ_ij vs frecuencia
# ══════════════════════════════════════════
ax1 = fig.add_subplot(2, 2, 1)
f = np.linspace(0, 300, 1000)
f0 = F0

# Respuesta resonante del acoplamiento
Phi_response = 1 / (1 + ((f - f0)/10)**2)

ax1.plot(f, Phi_response, color=colors[0], linewidth=2)
ax1.axvline(f0, color=colors[1], linestyle='--', label=f'f₀ = {f0} Hz')
ax1.fill_between(f, 0, Phi_response, alpha=0.3, color=colors[0])
ax1.set_xlabel('Frecuencia (Hz)', fontsize=12)
ax1.set_ylabel('|Φ| (u.a.)', fontsize=12)
ax1.set_title('Respuesta Resonante del Acoplamiento Cuántico', fontsize=14, pad=20)
ax1.legend()
ax1.grid(alpha=0.3)

# ══════════════════════════════════════════
# Panel 2: Campo Ψ(x,t) oscilatorio
# ══════════════════════════════════════════
ax2 = fig.add_subplot(2, 2, 2)
x = np.linspace(0, 2*np.pi, 200)
t_snapshots = [0, 0.25, 0.5, 0.75]

for i, t in enumerate(t_snapshots):
    Psi = np.sin(2*np.pi*f0*t) * np.exp(-DECAY_FACTOR*x)
    ax2.plot(x, Psi, color=colors[i], alpha=0.7, label=f't = {t}T₀')

ax2.set_xlabel('Posición x', fontsize=12)
ax2.set_ylabel('Ψ(x,t)', fontsize=12)
ax2.set_title('Evolución Temporal del Campo de Coherencia', fontsize=14, pad=20)
ax2.legend()
ax2.grid(alpha=0.3)

# ══════════════════════════════════════════
# Panel 3: Comparación Energía: NSE vs Ψ-NSE
# ══════════════════════════════════════════
ax3 = fig.add_subplot(2, 2, 3)
t = np.linspace(0, 2, 500)

# NSE clásico: crecimiento hacia blow-up
E_NSE = ENERGY_INITIAL * np.exp(ENERGY_GROWTH_RATE*t)

# Ψ-NSE: estabilización por acoplamiento
E_PsiNSE = ENERGY_INITIAL * (1 + ENERGY_SATURATION*(1 - np.exp(-DECAY_FACTOR*t)))

ax3.plot(t, E_NSE, color=colors[1], linewidth=2, label='NSE clásico (blow-up)')
ax3.plot(t, E_PsiNSE, color=colors[0], linewidth=2, label='Ψ-NSE (estabilizado)')
ax3.axhline(E_PsiNSE[-1], color=colors[0], linestyle=':', alpha=0.5)
ax3.set_xlabel('Tiempo (s)', fontsize=12)
ax3.set_ylabel('Energía E(t)', fontsize=12)
ax3.set_title('Evolución Energética: NSE vs Ψ-NSE', fontsize=14, pad=20)
ax3.legend()
ax3.grid(alpha=0.3)
ax3.set_yscale('log')

# ══════════════════════════════════════════
# Panel 4: Mapa de coherencia espacial
# ══════════════════════════════════════════
ax4 = fig.add_subplot(2, 2, 4)
x = np.linspace(0, 10, 100)
y = np.linspace(0, 10, 100)
X, Y = np.meshgrid(x, y)

# Patrón de interferencia coherente
Z = np.sin(2*np.pi*f0/SPATIAL_SCALE * X) * np.cos(2*np.pi*f0/SPATIAL_SCALE * Y)

im = ax4.contourf(X, Y, Z, levels=20, cmap='viridis')
plt.colorbar(im, ax=ax4, label='Amplitud Ψ')
ax4.set_xlabel('x', fontsize=12)
ax4.set_ylabel('y', fontsize=12)
ax4.set_title('Estructura Espacial del Campo Coherente', fontsize=14, pad=20)

plt.tight_layout()
plt.savefig('Phi_coupling_visualization.png', dpi=300, bbox_inches='tight')
print("✅ Visualización guardada: Phi_coupling_visualization.png")
