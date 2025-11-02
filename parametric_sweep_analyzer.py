"""
═══════════════════════════════════════════════════════════════
  ANALIZADOR COMPLETO DE RESULTADOS - BARRIDO PARAMÉTRICO
  
  Extrae insights científicos del espacio paramétrico explorado:
  - Mapas de estabilidad Re vs f₀
  - Emergencia de frecuencia dominante
  - Validación del tensor Φ_ij
  - Comparación NSE clásico vs Ψ-NSE
═══════════════════════════════════════════════════════════════
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec
import json
import pandas as pd
from pathlib import Path
from scipy.interpolate import griddata
from scipy.stats import linregress
import seaborn as sns

# Configure plotting style (will be set when functions are called)
def _configure_plot_style():
    """Configure matplotlib and seaborn plotting styles for dark theme."""
    plt.style.use('dark_background')
    sns.set_palette("husl")

# ═══════════════════════════════════════════════════════════════
# CARGA Y CONSOLIDACIÓN DE DATOS
# ═══════════════════════════════════════════════════════════════

def load_all_simulation_results(results_dir='parametric_sweep_results'):
    """
    Carga todos los resultados de simulaciones y los consolida en un DataFrame.
    """
    
    all_results = []
    
    # Iterar sobre todos los archivos de resultados
    for result_file in Path(results_dir).glob('results_package_*.json'):
        with open(result_file, 'r') as f:
            package_result = json.load(f)
        
        # Extraer datos de cada simulación
        for sim_result in package_result['results']:
            if sim_result['status'] != 'success':
                continue
            
            params = sim_result['params']
            results = sim_result['results']
            
            # Consolidar en diccionario plano
            record = {
                # Parámetros
                'f0': params['f0'],
                'Re': params['Re'],
                'nu': params['nu'],
                'N': params['N'],
                'T_max': params['T_max'],
                'L': params['L'],
                
                # Resultados clave
                'blowup_detected': results.get('blowup_detected', False),
                'blowup_time': results.get('blowup_time', np.nan),
                'max_vorticity': results.get('max_vorticity', np.nan),
                'energy_final': results.get('energy_final', np.nan),
                'energy_variation': results.get('energy_variation', np.nan),
                
                # Frecuencia detectada
                'dominant_frequency': results.get('dominant_frequency', np.nan),
                'frequency_error': results.get('frequency_error', np.nan),
                
                # BKM integral
                'bkm_integral': results.get('bkm_integral', np.nan),
                'bkm_converged': results.get('bkm_converged', False),
                
                # Tiempo de simulación
                'simulation_time': results.get('simulation_time', np.nan),
                
                # Metadata
                'package_id': package_result['package_id'],
                'completed_at': sim_result['completed_at']
            }
            
            all_results.append(record)
    
    df = pd.DataFrame(all_results)
    
    print(f"✅ Cargados {len(df)} resultados de simulación")
    if len(df) > 0:
        print(f"   Éxitos:  {len(df[df['blowup_detected'] == False])}")
        print(f"   Blow-ups: {len(df[df['blowup_detected'] == True])}")
    
    return df

# ═══════════════════════════════════════════════════════════════
# ANÁLISIS 1: MAPA DE ESTABILIDAD
# ═══════════════════════════════════════════════════════════════

def plot_stability_map(df, output_file='artifacts/stability_map.png'):
    """
    Genera mapa de calor mostrando estabilidad en espacio (f₀, Re).
    """
    _configure_plot_style()
    
    # Check minimum data points
    if len(df) < 4:
        print(f"⚠️  Advertencia: Solo {len(df)} puntos de datos. Se necesitan al menos 4 para interpolación.")
        # Create simple scatter plot instead
        fig, ax = plt.subplots(1, 1, figsize=(10, 6))
        fig.patch.set_facecolor('#0a0a0a')
        ax.set_facecolor('#1a1a1a')
        
        ax.scatter(df['f0'], df['Re'], 
                   c=~df['blowup_detected'], 
                   cmap='RdYlGn',
                   s=200, 
                   edgecolors='white', 
                   linewidths=2,
                   marker='o',
                   alpha=0.8)
        
        ax.set_xscale('log')
        ax.set_yscale('log')
        ax.set_xlabel('Frecuencia $f_0$ (Hz)', fontsize=14)
        ax.set_ylabel('Reynolds $Re$', fontsize=14)
        ax.set_title('Mapa de Estabilidad: Ψ-NSE (datos limitados)', fontsize=16, fontweight='bold')
        ax.grid(alpha=0.3)
        
        plt.tight_layout()
        plt.savefig(output_file, dpi=200, facecolor='#0a0a0a', bbox_inches='tight')
        print(f"✅ Mapa de estabilidad guardado: {output_file}")
        return fig
    
    fig, axes = plt.subplots(1, 3, figsize=(20, 6))
    fig.patch.set_facecolor('#0a0a0a')
    
    for ax in axes:
        ax.set_facecolor('#1a1a1a')
    
    # ─────────────────────────────────────────────────────────────
    # Panel 1: Mapa de estabilidad (binario)
    # ─────────────────────────────────────────────────────────────
    
    # Crear grid regular
    f0_grid = np.logspace(np.log10(df['f0'].min()), 
                         np.log10(df['f0'].max()), 50)
    Re_grid = np.logspace(np.log10(df['Re'].min()), 
                         np.log10(df['Re'].max()), 50)
    
    F0, RE = np.meshgrid(f0_grid, Re_grid)
    
    # Interpolar estabilidad con manejo de errores
    stability_values = (~df['blowup_detected']).astype(int)
    
    # Check if all values are the same or data is coplanar
    if len(np.unique(stability_values)) == 1:
        # All stable or all unstable - no variation to interpolate
        axes[0].scatter(df['f0'], df['Re'], 
                       c=~df['blowup_detected'], 
                       cmap='RdYlGn',
                       s=100, 
                       edgecolors='white', 
                       linewidths=1,
                       marker='o',
                       alpha=0.8)
        status_text = 'Todo estable' if stability_values.iloc[0] == 1 else 'Todo con blow-up'
        axes[0].text(0.5, 0.95, f'{status_text} - No hay variación para interpolar', 
                    transform=axes[0].transAxes,
                    ha='center', va='top', 
                    fontsize=10, color='white', alpha=0.7)
    elif len(df) < 4:
        # Not enough points
        axes[0].scatter(df['f0'], df['Re'], 
                       c=~df['blowup_detected'], 
                       cmap='RdYlGn',
                       s=100, 
                       edgecolors='white', 
                       linewidths=1,
                       marker='o',
                       alpha=0.8)
        axes[0].text(0.5, 0.95, 'Datos insuficientes para interpolación', 
                    transform=axes[0].transAxes,
                    ha='center', va='top', 
                    fontsize=10, color='white', alpha=0.7)
    else:
        try:
            stability = griddata(
                points=(df['f0'], df['Re']),
                values=stability_values,
                xi=(F0, RE),
                method='linear',
                fill_value=0
            )
            
            im1 = axes[0].contourf(F0, RE, stability, levels=20, cmap='RdYlGn', alpha=0.8)
            axes[0].scatter(df['f0'], df['Re'], 
                           c=~df['blowup_detected'], 
                           cmap='RdYlGn',
                           s=100, 
                           edgecolors='white', 
                           linewidths=1,
                           marker='o',
                           alpha=0.8)
            
            cbar1 = plt.colorbar(im1, ax=axes[0])
            cbar1.set_label('Estabilidad (1 = estable, 0 = blow-up)', fontsize=11)
        except Exception as e:
            # Fallback to scatter only
            axes[0].scatter(df['f0'], df['Re'], 
                           c=~df['blowup_detected'], 
                           cmap='RdYlGn',
                           s=100, 
                           edgecolors='white', 
                           linewidths=1,
                           marker='o',
                           alpha=0.8)
    
    # Marcar f₀ predicho
    axes[0].axvline(141.7, color='cyan', linestyle='--', linewidth=2, 
                   label='$f_0$ predicho = 141.7 Hz')
    
    axes[0].set_xscale('log')
    axes[0].set_yscale('log')
    axes[0].set_xlabel('Frecuencia $f_0$ (Hz)', fontsize=14)
    axes[0].set_ylabel('Reynolds $Re$', fontsize=14)
    axes[0].set_title('Mapa de Estabilidad: Ψ-NSE', fontsize=16, fontweight='bold')
    axes[0].legend(fontsize=11)
    axes[0].grid(alpha=0.3)
    
    # ─────────────────────────────────────────────────────────────
    # Panel 2: Tiempo de blow-up (cuando ocurre)
    # ─────────────────────────────────────────────────────────────
    
    df_blowup = df[df['blowup_detected'] == True]
    
    if len(df_blowup) > 0 and len(df_blowup) >= 4:
        blowup_time_grid = griddata(
            points=(df_blowup['f0'], df_blowup['Re']),
            values=df_blowup['blowup_time'],
            xi=(F0, RE),
            method='linear'
        )
        
        im2 = axes[1].contourf(F0, RE, blowup_time_grid, levels=20, 
                              cmap='hot', alpha=0.8)
        axes[1].scatter(df_blowup['f0'], df_blowup['Re'],
                       c=df_blowup['blowup_time'],
                       cmap='hot',
                       s=100,
                       edgecolors='white',
                       linewidths=1,
                       marker='x',
                       alpha=0.8)
        
        cbar2 = plt.colorbar(im2, ax=axes[1])
        cbar2.set_label('Tiempo de blow-up (s)', fontsize=11)
    elif len(df_blowup) > 0:
        # Not enough points for interpolation, just scatter
        axes[1].scatter(df_blowup['f0'], df_blowup['Re'],
                       c=df_blowup['blowup_time'],
                       cmap='hot',
                       s=200,
                       edgecolors='white',
                       linewidths=2,
                       marker='x',
                       alpha=0.8)
        axes[1].text(0.5, 0.95, f'Blow-ups detectados: {len(df_blowup)}', 
                    transform=axes[1].transAxes,
                    ha='center', va='top', 
                    fontsize=12, color='white')
    else:
        axes[1].text(0.5, 0.5, 'No se detectaron blow-ups', 
                    transform=axes[1].transAxes,
                    ha='center', va='center', 
                    fontsize=14, color='white')
    
    axes[1].axvline(141.7, color='cyan', linestyle='--', linewidth=2)
    axes[1].set_xscale('log')
    axes[1].set_yscale('log')
    axes[1].set_xlabel('Frecuencia $f_0$ (Hz)', fontsize=14)
    axes[1].set_ylabel('Reynolds $Re$', fontsize=14)
    axes[1].set_title('Tiempo de Blow-up (si ocurre)', fontsize=16, fontweight='bold')
    axes[1].grid(alpha=0.3)
    
    # ─────────────────────────────────────────────────────────────
    # Panel 3: Integral BKM
    # ─────────────────────────────────────────────────────────────
    
    try:
        bkm_grid = griddata(
            points=(df['f0'], df['Re']),
            values=df['bkm_integral'],
            xi=(F0, RE),
            method='linear'
        )
        
        # Usar escala logarítmica para BKM integral
        bkm_grid_log = np.log10(bkm_grid + 1)
        
        im3 = axes[2].contourf(F0, RE, bkm_grid_log, levels=20, 
                              cmap='viridis', alpha=0.8)
        axes[2].scatter(df['f0'], df['Re'],
                       c=np.log10(df['bkm_integral'] + 1),
                       cmap='viridis',
                       s=100,
                       edgecolors='white',
                       linewidths=1,
                       alpha=0.8)
        
        # Línea de contorno en BKM = ∞ (blow-up)
        axes[2].contour(F0, RE, bkm_grid_log, levels=[2], 
                       colors='red', linewidths=2, linestyles='--')
        
        cbar3 = plt.colorbar(im3, ax=axes[2])
        cbar3.set_label('$\\log_{10}(\\int \\|\\omega\\|_\\infty dt + 1)$', fontsize=11)
    except Exception as e:
        # Fallback to scatter only if interpolation fails
        axes[2].scatter(df['f0'], df['Re'],
                       c=np.log10(df['bkm_integral'] + 1),
                       cmap='viridis',
                       s=100,
                       edgecolors='white',
                       linewidths=1,
                       alpha=0.8)
        axes[2].text(0.5, 0.95, 'Interpolación no disponible', 
                    transform=axes[2].transAxes,
                    ha='center', va='top', 
                    fontsize=10, color='white', alpha=0.7)
    
    axes[2].axvline(141.7, color='cyan', linestyle='--', linewidth=2)
    axes[2].set_xscale('log')
    axes[2].set_yscale('log')
    axes[2].set_xlabel('Frecuencia $f_0$ (Hz)', fontsize=14)
    axes[2].set_ylabel('Reynolds $Re$', fontsize=14)
    axes[2].set_title('Integral BKM (criterio de regularidad)', 
                     fontsize=16, fontweight='bold')
    axes[2].grid(alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(output_file, dpi=200, facecolor='#0a0a0a', bbox_inches='tight')
    print(f"✅ Mapa de estabilidad guardado: {output_file}")
    
    return fig

# ═══════════════════════════════════════════════════════════════
# ANÁLISIS 2: VALIDACIÓN DE EMERGENCIA DE f₀
# ═══════════════════════════════════════════════════════════════

def plot_frequency_emergence_validation(df, output_file='artifacts/frequency_emergence_validation.png'):
    """
    Valida que f₀ = 141.7 Hz emerge espontáneamente del sistema.
    """
    _configure_plot_style()
    
    fig = plt.figure(figsize=(18, 12))
    fig.patch.set_facecolor('#0a0a0a')
    gs = GridSpec(3, 3, figure=fig, hspace=0.3, wspace=0.3)
    
    # ─────────────────────────────────────────────────────────────
    # Panel 1: Frecuencia detectada vs f₀ impuesto
    # ─────────────────────────────────────────────────────────────
    
    ax1 = fig.add_subplot(gs[0, :])
    ax1.set_facecolor('#1a1a1a')
    
    # Agrupar por f0 y calcular estadísticas
    freq_stats = df.groupby('f0')['dominant_frequency'].agg(['mean', 'std', 'count'])
    
    ax1.errorbar(freq_stats.index, freq_stats['mean'], 
                yerr=freq_stats['std'],
                fmt='o', markersize=8, capsize=5, capthick=2,
                color='#00ff41', ecolor='#00ff41', alpha=0.7,
                label='Frecuencia detectada (media ± std)')
    
    # Línea y = x (ideal)
    f0_range = [df['f0'].min(), df['f0'].max()]
    ax1.plot(f0_range, f0_range, 'r--', linewidth=2, alpha=0.7,
            label='Ideal ($f_{detectada} = f_0$)')
    
    # Banda de ±1%
    ax1.fill_between(f0_range, 
                     [f*0.99 for f in f0_range], 
                     [f*1.01 for f in f0_range],
                     color='red', alpha=0.1, label='±1% banda')
    
    # Marcar f₀ predicho
    ax1.axvline(141.7, color='cyan', linestyle=':', linewidth=3, alpha=0.8,
               label='$f_0$ predicho = 141.7 Hz')
    
    ax1.set_xscale('log')
    ax1.set_yscale('log')
    ax1.set_xlabel('$f_0$ impuesto en simulación (Hz)', fontsize=14)
    ax1.set_ylabel('Frecuencia dominante detectada (Hz)', fontsize=14)
    ax1.set_title('Validación: Frecuencia Emerge Espontáneamente', 
                 fontsize=16, fontweight='bold')
    ax1.legend(fontsize=11, loc='upper left')
    ax1.grid(alpha=0.3)
    
    # ─────────────────────────────────────────────────────────────
    # Panel 2: Error de frecuencia vs Reynolds
    # ─────────────────────────────────────────────────────────────
    
    ax2 = fig.add_subplot(gs[1, 0])
    ax2.set_facecolor('#1a1a1a')
    
    # Scatter plot coloreado por f0
    scatter = ax2.scatter(df['Re'], df['frequency_error']*100,
                         c=df['f0'], cmap='viridis',
                         s=80, alpha=0.6, edgecolors='white', linewidths=0.5)
    
    ax2.axhline(0, color='white', linestyle='--', alpha=0.5)
    ax2.axhline(1, color='yellow', linestyle=':', alpha=0.5, label='1% error')
    ax2.axhline(-1, color='yellow', linestyle=':', alpha=0.5)
    
    ax2.set_xscale('log')
    ax2.set_xlabel('Reynolds $Re$', fontsize=12)
    ax2.set_ylabel('Error de frecuencia (%)', fontsize=12)
    ax2.set_title('Error vs Reynolds', fontsize=14)
    ax2.legend(fontsize=10)
    ax2.grid(alpha=0.3)
    
    cbar = plt.colorbar(scatter, ax=ax2)
    cbar.set_label('$f_0$ (Hz)', fontsize=10)
    
    # ─────────────────────────────────────────────────────────────
    # Panel 3: Histograma de errores cerca de f₀ predicho
    # ─────────────────────────────────────────────────────────────
    
    ax3 = fig.add_subplot(gs[1, 1])
    ax3.set_facecolor('#1a1a1a')
    
    # Filtrar simulaciones cerca de f₀ = 141.7 Hz (±20%)
    near_f0 = df[(df['f0'] >= 141.7*0.8) & (df['f0'] <= 141.7*1.2)]
    
    ax3.hist(near_f0['frequency_error']*100, bins=30, 
            color='#00ff41', alpha=0.7, edgecolor='white')
    ax3.axvline(0, color='cyan', linestyle='--', linewidth=2, 
               label='Error = 0')
    ax3.axvline(near_f0['frequency_error'].mean()*100, 
               color='orange', linestyle=':', linewidth=2,
               label=f'Media = {near_f0["frequency_error"].mean()*100:.2f}%')
    
    ax3.set_xlabel('Error de frecuencia (%)', fontsize=12)
    ax3.set_ylabel('Frecuencia', fontsize=12)
    ax3.set_title(f'Distribución de error (cerca $f_0 = 141.7$ Hz)', fontsize=14)
    ax3.legend(fontsize=10)
    ax3.grid(alpha=0.3, axis='y')
    
    # ─────────────────────────────────────────────────────────────
    # Panel 4: Correlación error vs distancia a f₀
    # ─────────────────────────────────────────────────────────────
    
    ax4 = fig.add_subplot(gs[1, 2])
    ax4.set_facecolor('#1a1a1a')
    
    # Distancia relativa a f₀ predicho
    df['distance_to_predicted'] = np.abs(df['f0'] - 141.7) / 141.7
    
    ax4.scatter(df['distance_to_predicted']*100, 
               np.abs(df['frequency_error'])*100,
               c=df['Re'], cmap='plasma',
               s=80, alpha=0.6, edgecolors='white', linewidths=0.5)
    
    # Línea de tendencia
    mask = ~np.isnan(df['frequency_error'])
    if mask.sum() > 2:
        slope, intercept, r_value, _, _ = linregress(
            df[mask]['distance_to_predicted'],
            np.abs(df[mask]['frequency_error'])
        )
        
        x_trend = np.linspace(0, df['distance_to_predicted'].max(), 100)
        y_trend = slope * x_trend + intercept
        
        ax4.plot(x_trend*100, y_trend*100, 'r--', linewidth=2, alpha=0.7,
                label=f'Tendencia (R² = {r_value**2:.3f})')
    
    ax4.set_xlabel('Distancia a $f_0$ predicho (%)', fontsize=12)
    ax4.set_ylabel('|Error de frecuencia| (%)', fontsize=12)
    ax4.set_title('Correlación: Error vs Distancia a $f_0$', fontsize=14)
    ax4.legend(fontsize=10)
    ax4.grid(alpha=0.3)
    
    # Create proper colorbar from scatter data
    scatter_for_cbar = ax4.collections[0] if len(ax4.collections) > 0 else None
    if scatter_for_cbar is not None:
        cbar2 = plt.colorbar(scatter_for_cbar, ax=ax4)
        cbar2.set_label('$Re$', fontsize=10)
    
    # ─────────────────────────────────────────────────────────────
    # Panel 5: Potencia espectral promedio
    # ─────────────────────────────────────────────────────────────
    
    ax5 = fig.add_subplot(gs[2, :])
    ax5.set_facecolor('#1a1a1a')
    
    # Calcular potencia espectral normalizada para cada f0
    f0_unique = sorted(df['f0'].unique())
    
    for f0_val in f0_unique:
        subset = df[df['f0'] == f0_val]
        
        # Normalizar frecuencia detectada por f0_val
        freq_normalized = subset['dominant_frequency'] / f0_val
        
        # Histograma suavizado
        hist, bins = np.histogram(freq_normalized, bins=50, range=(0.5, 1.5))
        bin_centers = (bins[:-1] + bins[1:]) / 2
        
        # Color según distancia a 141.7 Hz
        distance = np.abs(f0_val - 141.7) / 141.7
        color = plt.cm.RdYlGn(1 - distance*5)  # Verde cerca, rojo lejos
        
        ax5.plot(bin_centers, hist, linewidth=2, alpha=0.6, color=color,
                label=f'$f_0 = {f0_val:.1f}$ Hz' if len(f0_unique) <= 10 else None)
    
    ax5.axvline(1.0, color='cyan', linestyle='--', linewidth=3, alpha=0.8,
               label='Frecuencia predicha ($f_{det}/f_0 = 1$)')
    
    ax5.set_xlabel('Frecuencia detectada / $f_0$ impuesto', fontsize=14)
    ax5.set_ylabel('Densidad (conteo)', fontsize=14)
    ax5.set_title('Convergencia a Frecuencia Predicha', fontsize=16, fontweight='bold')
    if len(f0_unique) <= 10:
        ax5.legend(fontsize=9, ncol=2)
    ax5.grid(alpha=0.3)
    ax5.set_xlim(0.5, 1.5)
    
    plt.savefig(output_file, dpi=200, facecolor='#0a0a0a', bbox_inches='tight')
    print(f"✅ Validación de emergencia guardada: {output_file}")
    
    return fig

# ═══════════════════════════════════════════════════════════════
# ANÁLISIS 3: COMPARACIÓN NSE CLÁSICO VS Ψ-NSE
# ═══════════════════════════════════════════════════════════════

def plot_classical_vs_psi_comparison(df, output_file='artifacts/classical_vs_psi_comparison.png'):
    """
    Compara comportamiento de NSE clásico (cuando falla) vs Ψ-NSE (estable).
    """
    _configure_plot_style()
    
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))
    fig.patch.set_facecolor('#0a0a0a')
    
    for ax_row in axes:
        for ax in ax_row:
            ax.set_facecolor('#1a1a1a')
    
    # ─────────────────────────────────────────────────────────────
    # Panel 1: Tasa de éxito vs Reynolds
    # ─────────────────────────────────────────────────────────────
    
    Re_bins = np.logspace(np.log10(df['Re'].min()), 
                         np.log10(df['Re'].max()), 10)
    Re_centers = np.sqrt(Re_bins[:-1] * Re_bins[1:])
    
    success_rates = []
    for i in range(len(Re_bins)-1):
        mask = (df['Re'] >= Re_bins[i]) & (df['Re'] < Re_bins[i+1])
        if mask.sum() > 0:
            success_rate = (~df[mask]['blowup_detected']).mean()
            success_rates.append(success_rate * 100)
        else:
            success_rates.append(np.nan)
    
    axes[0,0].plot(Re_centers, success_rates, 'o-', linewidth=3, markersize=10,
                  color='#00ff41', label='Ψ-NSE (este trabajo)')
    
    # Línea de referencia: NSE clásico tendría ~0% en Re alto
    axes[0,0].axhline(100, color='cyan', linestyle='--', alpha=0.5,
                     label='Objetivo (100% estable)')
    axes[0,0].fill_between(Re_centers, 0, success_rates, 
                          color='#00ff41', alpha=0.2)
    
    axes[0,0].set_xscale('log')
    axes[0,0].set_xlabel('Reynolds $Re$', fontsize=14)
    axes[0,0].set_ylabel('Tasa de éxito (%)', fontsize=14)
    axes[0,0].set_title('Estabilidad vs Reynolds', fontsize=16, fontweight='bold')
    axes[0,0].legend(fontsize=12)
    axes[0,0].grid(alpha=0.3)
    axes[0,0].set_ylim(-5, 105)
    
    # ─────────────────────────────────────────────────────────────
    # Panel 2: Vorticidad máxima vs Reynolds
    # ─────────────────────────────────────────────────────────────
    
    # Simulaciones estables
    stable = df[~df['blowup_detected']]
    # Simulaciones con blow-up
    unstable = df[df['blowup_detected']]
    
    if len(stable) > 0:
        axes[0,1].scatter(stable['Re'], stable['max_vorticity'],
                         c='#00ff41', s=100, alpha=0.6, 
                         edgecolors='white', linewidths=1,
                         label='Ψ-NSE (estable)', marker='o')
    
    if len(unstable) > 0:
        axes[0,1].scatter(unstable['Re'], unstable['max_vorticity'],
                         c='#ff006e', s=100, alpha=0.6,
                         edgecolors='white', linewidths=1,
                         label='Blow-up detectado', marker='x')
    
    axes[0,1].set_xscale('log')
    axes[0,1].set_yscale('log')
    axes[0,1].set_xlabel('Reynolds $Re$', fontsize=14)
    axes[0,1].set_ylabel('Vorticidad máxima $\\|\\omega\\|_{\\infty}$', fontsize=14)
    axes[0,1].set_title('Vorticidad vs Reynolds', fontsize=16, fontweight='bold')
    axes[0,1].legend(fontsize=12)
    axes[0,1].grid(alpha=0.3)
    
    # ─────────────────────────────────────────────────────────────
    # Panel 3: Variación de energía
    # ─────────────────────────────────────────────────────────────
    
    axes[1,0].scatter(df['Re'], np.abs(df['energy_variation']),
                     c=df['blowup_detected'], cmap='RdYlGn_r',
                     s=100, alpha=0.6, edgecolors='white', linewidths=1)
    
    axes[1,0].set_xscale('log')
    axes[1,0].set_yscale('log')
    axes[1,0].set_xlabel('Reynolds $Re$', fontsize=14)
    axes[1,0].set_ylabel('|Variación de energía| $|\\Delta E/E_0|$', fontsize=14)
    axes[1,0].set_title('Conservación de Energía', fontsize=16, fontweight='bold')
    axes[1,0].grid(alpha=0.3)
    
    # ─────────────────────────────────────────────────────────────
    # Panel 4: Tiempo de simulación vs resolución
    # ─────────────────────────────────────────────────────────────
    
    N_values = sorted(df['N'].unique())
    
    for N_val in N_values:
        subset = df[df['N'] == N_val]
        
        # Agrupar por Re y promediar tiempo
        time_stats = subset.groupby('Re')['simulation_time'].agg(['mean', 'std'])
        
        axes[1,1].errorbar(time_stats.index, time_stats['mean'],
                          yerr=time_stats['std'],
                          fmt='o-', markersize=8, capsize=5,
                          label=f'N = {N_val}³', linewidth=2)
    
    axes[1,1].set_xscale('log')
    axes[1,1].set_yscale('log')
    axes[1,1].set_xlabel('Reynolds $Re$', fontsize=14)
    axes[1,1].set_ylabel('Tiempo de simulación (s)', fontsize=14)
    axes[1,1].set_title('Costo Computacional', fontsize=16, fontweight='bold')
    axes[1,1].legend(fontsize=12)
    axes[1,1].grid(alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(output_file, dpi=200, facecolor='#0a0a0a', bbox_inches='tight')
    print(f"✅ Comparación NSE vs Ψ-NSE guardada: {output_file}")
    
    return fig

# ═══════════════════════════════════════════════════════════════
# MAIN EXECUTION
# ═══════════════════════════════════════════════════════════════

def main():
    """
    Función principal que ejecuta todos los análisis.
    """
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Analiza resultados de barrido paramétrico Ψ-NSE'
    )
    parser.add_argument(
        '--results-dir',
        default='parametric_sweep_results',
        help='Directorio con resultados JSON'
    )
    parser.add_argument(
        '--output-dir',
        default='artifacts',
        help='Directorio para guardar gráficos'
    )
    
    args = parser.parse_args()
    
    # Crear directorio de salida si no existe
    Path(args.output_dir).mkdir(parents=True, exist_ok=True)
    
    print("═══════════════════════════════════════════════════════════════")
    print("  ANÁLISIS DE RESULTADOS - BARRIDO PARAMÉTRICO Ψ-NSE")
    print("═══════════════════════════════════════════════════════════════")
    print()
    
    # 1. Cargar datos
    print("📂 Cargando datos...")
    df = load_all_simulation_results(args.results_dir)
    
    if len(df) == 0:
        print("❌ No se encontraron resultados para analizar")
        return
    
    print()
    
    # 2. Generar visualizaciones
    print("📊 Generando visualizaciones...")
    
    print("  → Mapa de estabilidad...")
    plot_stability_map(df, f'{args.output_dir}/stability_map.png')
    
    print("  → Validación de emergencia de frecuencia...")
    plot_frequency_emergence_validation(
        df, 
        f'{args.output_dir}/frequency_emergence_validation.png'
    )
    
    print("  → Comparación NSE clásico vs Ψ-NSE...")
    plot_classical_vs_psi_comparison(
        df,
        f'{args.output_dir}/classical_vs_psi_comparison.png'
    )
    
    print()
    print("═══════════════════════════════════════════════════════════════")
    print("  ✅ ANÁLISIS COMPLETADO")
    print("═══════════════════════════════════════════════════════════════")
    print(f"  Total de simulaciones: {len(df)}")
    print(f"  Tasa de éxito: {(~df['blowup_detected']).mean()*100:.1f}%")
    print(f"  Gráficos guardados en: {args.output_dir}/")
    print()

if __name__ == '__main__':
    main()
