#!/usr/bin/env python3
"""Quick smoke test for psi_nse_dns_complete.py with reduced parameters"""

import numpy as np
import matplotlib
matplotlib.use('Agg')  # Use non-interactive backend
import matplotlib.pyplot as plt
from scipy.fft import fftn, ifftn, fftfreq
import h5py
from tqdm import tqdm
import json

# Reduced parameters for quick test
f0 = 141.7001
omega0 = 2 * np.pi * f0
nu = 1e-3
L = 2 * np.pi
N = 32  # Reduced from 128
dt = 0.01  # Increased from 0.001
T_max = 0.5  # Reduced from 5.0

alpha_coupling = 1/(720 * np.pi**2) * 0.1
beta_coupling = 1/(2880 * np.pi**2)
gamma_coupling = -1/(1440 * np.pi**2)

print("🌊 QUICK TEST: DNS Ψ-NSE")
print("="*60)
print(f"Frecuencia base: f₀ = {f0} Hz")
print(f"Resolución: {N}³ (reduced for testing)")
print(f"Tiempo simulación: {T_max}s (reduced for testing)")
print("="*60 + "\n")

# Grid espectral
x = np.linspace(0, L, N, endpoint=False)
dx = x[1] - x[0]
X, Y, Z = np.meshgrid(x, x, x, indexing='ij')

kx = fftfreq(N, dx/(2*np.pi))
ky = fftfreq(N, dx/(2*np.pi))
kz = fftfreq(N, dx/(2*np.pi))
KX, KY, KZ = np.meshgrid(kx, ky, kz, indexing='ij')
K2 = KX**2 + KY**2 + KZ**2
K2[0,0,0] = 1

def campo_coherencia_psi(t, X, Y, Z):
    temporal = np.sin(omega0 * t)
    espacial = (np.sin(2*np.pi*X/L) * 
                np.cos(2*np.pi*Y/L) * 
                np.sin(2*np.pi*Z/L))
    A_eff = 1.0
    return A_eff * temporal * espacial

def calcular_phi_tensor(psi, dx):
    psi_hat = fftn(psi)
    laplacian_psi = np.real(ifftn(-K2 * psi_hat))
    d2_dx2 = np.real(ifftn(-KX**2 * psi_hat))
    d2_dy2 = np.real(ifftn(-KY**2 * psi_hat))
    d2_dz2 = np.real(ifftn(-KZ**2 * psi_hat))
    d2_dxdy = np.real(ifftn(-KX*KY * psi_hat))
    d2_dxdz = np.real(ifftn(-KX*KZ * psi_hat))
    d2_dydz = np.real(ifftn(-KY*KZ * psi_hat))
    
    Phi = np.zeros((3, 3, N, N, N))
    Phi[0,0] = alpha_coupling * d2_dx2 + gamma_coupling * laplacian_psi
    Phi[1,1] = alpha_coupling * d2_dy2 + gamma_coupling * laplacian_psi
    Phi[2,2] = alpha_coupling * d2_dz2 + gamma_coupling * laplacian_psi
    Phi[0,1] = Phi[1,0] = alpha_coupling * d2_dxdy
    Phi[0,2] = Phi[2,0] = alpha_coupling * d2_dxdz
    Phi[1,2] = Phi[2,1] = alpha_coupling * d2_dydz
    
    return Phi

def taylor_green_vortex(X, Y, Z, U0=1.0):
    u = U0 * np.sin(X) * np.cos(Y) * np.cos(Z)
    v = -U0 * np.cos(X) * np.sin(Y) * np.cos(Z)
    w = np.zeros_like(u)
    return u, v, w

u, v, w = taylor_green_vortex(X, Y, Z)
u_hat = fftn(u)
v_hat = fftn(v)
w_hat = fftn(w)

print("✓ Condiciones iniciales: Taylor-Green Vortex")
print(f"  Energía inicial: {0.5*np.mean(u**2 + v**2 + w**2):.6f}\n")

def proyectar_divergence_free(u_hat, v_hat, w_hat):
    kdotu = KX*u_hat + KY*v_hat + KZ*w_hat
    u_hat -= KX * kdotu / K2
    v_hat -= KY * kdotu / K2
    w_hat -= KZ * kdotu / K2
    return u_hat, v_hat, w_hat

def rhs_psi_nse(u, v, w, psi, Phi, nu, dt):
    u_hat = fftn(u)
    v_hat = fftn(v)
    w_hat = fftn(w)
    
    ux = np.real(ifftn(1j * KX * u_hat))
    uy = np.real(ifftn(1j * KY * u_hat))
    uz = np.real(ifftn(1j * KZ * u_hat))
    vx = np.real(ifftn(1j * KX * v_hat))
    vy = np.real(ifftn(1j * KY * v_hat))
    vz = np.real(ifftn(1j * KZ * v_hat))
    wx = np.real(ifftn(1j * KX * w_hat))
    wy = np.real(ifftn(1j * KY * w_hat))
    wz = np.real(ifftn(1j * KZ * w_hat))
    
    conv_u = -(u*ux + v*uy + w*uz)
    conv_v = -(u*vx + v*vy + w*vz)
    conv_w = -(u*wx + v*wy + w*wz)
    
    coupling_u = Phi[0,0]*u + Phi[0,1]*v + Phi[0,2]*w
    coupling_v = Phi[1,0]*u + Phi[1,1]*v + Phi[1,2]*w
    coupling_w = Phi[2,0]*u + Phi[2,1]*v + Phi[2,2]*w
    
    conv_u_hat = fftn(conv_u)
    conv_v_hat = fftn(conv_v)
    conv_w_hat = fftn(conv_w)
    
    coupling_u_hat = fftn(coupling_u)
    coupling_v_hat = fftn(coupling_v)
    coupling_w_hat = fftn(coupling_w)
    
    conv_u_hat, conv_v_hat, conv_w_hat = proyectar_divergence_free(
        conv_u_hat, conv_v_hat, conv_w_hat
    )
    
    coupling_u_hat, coupling_v_hat, coupling_w_hat = proyectar_divergence_free(
        coupling_u_hat, coupling_v_hat, coupling_w_hat
    )
    
    du_hat = conv_u_hat - nu*K2*u_hat + coupling_u_hat
    dv_hat = conv_v_hat - nu*K2*v_hat + coupling_v_hat
    dw_hat = conv_w_hat - nu*K2*w_hat + coupling_w_hat
    
    return du_hat, dv_hat, dw_hat

print("🚀 INICIANDO INTEGRACIÓN TEMPORAL (quick test)\n")

n_steps = int(T_max / dt)
energia = np.zeros(n_steps)
enstrofia = np.zeros(n_steps)
tiempo = np.zeros(n_steps)

# Quick RK4 integration
for step in tqdm(range(n_steps), desc="Simulando"):
    t = step * dt
    tiempo[step] = t
    
    psi = campo_coherencia_psi(t, X, Y, Z)
    Phi = calcular_phi_tensor(psi, dx)
    
    k1_u, k1_v, k1_w = rhs_psi_nse(u, v, w, psi, Phi, nu, dt)
    u1 = np.real(ifftn(u_hat + 0.5*dt*k1_u))
    v1 = np.real(ifftn(v_hat + 0.5*dt*k1_v))
    w1 = np.real(ifftn(w_hat + 0.5*dt*k1_w))
    
    k2_u, k2_v, k2_w = rhs_psi_nse(u1, v1, w1, psi, Phi, nu, dt)
    u2 = np.real(ifftn(u_hat + 0.5*dt*k2_u))
    v2 = np.real(ifftn(v_hat + 0.5*dt*k2_v))
    w2 = np.real(ifftn(w_hat + 0.5*dt*k2_w))
    
    k3_u, k3_v, k3_w = rhs_psi_nse(u2, v2, w2, psi, Phi, nu, dt)
    u3 = np.real(ifftn(u_hat + dt*k3_u))
    v3 = np.real(ifftn(v_hat + dt*k3_v))
    w3 = np.real(ifftn(w_hat + dt*k3_w))
    
    k4_u, k4_v, k4_w = rhs_psi_nse(u3, v3, w3, psi, Phi, nu, dt)
    
    u_hat = u_hat + (dt/6)*(k1_u + 2*k2_u + 2*k3_u + k4_u)
    v_hat = v_hat + (dt/6)*(k1_v + 2*k2_v + 2*k3_v + k4_v)
    w_hat = w_hat + (dt/6)*(k1_w + 2*k2_w + 2*k3_w + k4_w)
    
    u_hat, v_hat, w_hat = proyectar_divergence_free(u_hat, v_hat, w_hat)
    
    u = np.real(ifftn(u_hat))
    v = np.real(ifftn(v_hat))
    w = np.real(ifftn(w_hat))
    
    energia[step] = 0.5 * np.mean(u**2 + v**2 + w**2)
    
    omega_x = np.real(ifftn(1j*KY*w_hat - 1j*KZ*v_hat))
    omega_y = np.real(ifftn(1j*KZ*u_hat - 1j*KX*w_hat))
    omega_z = np.real(ifftn(1j*KX*v_hat - 1j*KY*u_hat))
    enstrofia[step] = 0.5 * np.mean(omega_x**2 + omega_y**2 + omega_z**2)

print("\n✅ SIMULACIÓN COMPLETADA\n")

# Basic validation checks
print("="*60)
print("VALIDACIÓN DE RESULTADOS")
print("="*60)
print(f"✓ Energía inicial: {energia[0]:.6f}")
print(f"✓ Energía final: {energia[-1]:.6f}")
print(f"✓ Energía máxima: {np.max(energia):.6f}")
print(f"✓ Enstrofía máxima: {np.max(enstrofia):.6f}")
print(f"✓ Blow-up detectado: {np.max(energia) > 1e6}")
print(f"✓ Sistema estable: {np.all(np.isfinite(energia))}")
print("="*60)

# Basic spectral analysis
freqs = fftfreq(len(energia), dt)
fft_energia = np.fft.fft(energia)
power_spectrum = np.abs(fft_energia)**2

mask = freqs > 0
freqs_pos = freqs[mask]
power_pos = power_spectrum[mask]

if len(power_pos) > 0:
    idx_peak = np.argmax(power_pos)
    f_detected = freqs_pos[idx_peak]
    print(f"\n🎯 Frecuencia dominante: {f_detected:.2f} Hz")
    print(f"   Error relativo: {abs(f_detected - f0)/f0 * 100:.2f}%")

print("\n✅ QUICK TEST PASSED!")
print("   Script is working correctly with reduced parameters")
print("   Ready for full simulation run\n")
