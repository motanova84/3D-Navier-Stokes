"""
Análisis de escala dual-límite para sistema Ψ-NS

Este módulo proporciona herramientas para analizar el comportamiento
del sistema en el límite dual f0 → ∞.
"""

import numpy as np
from typing import Dict, Tuple


class DualLimitAnalyzer:
    """Analizador para el límite dual"""
    
    def __init__(self, lambda_val: float = 1.0, a: float = 1.0, alpha: float = 2.0):
        """
        Inicializar analizador
        
        Args:
            lambda_val: Intensidad base
            a: Amplitud base
            alpha: Exponente de escala (debe ser > 1)
        """
        self.lambda_val = lambda_val
        self.a = a
        self.alpha = alpha
        
        if alpha <= 1:
            raise ValueError("alpha debe ser mayor que 1 para convergencia")
    
    def theoretical_delta_star(self, c0: float = 1.0) -> float:
        """
        Calcular delta* teórico
        
        Args:
            c0: Cota inferior del gradiente de fase
            
        Returns:
            Valor teórico de delta*
        """
        return (self.a**2 * c0**2) / (4 * np.pi**2)
    
    def forcing_magnitude(self, f0: float) -> float:
        """
        Calcular magnitud de fuerza oscilatoria
        
        Args:
            f0: Frecuencia
            
        Returns:
            ‖epsilonnablaPhi‖ ~ lambda_valaf0^(1-alpha)
        """
        epsilon = self.lambda_val * f0**(-self.alpha)
        A = self.a * f0
        return self.lambda_val * self.a * f0**(1 - self.alpha)
    
    def characteristic_time_scale(self, f0: float, nu: float = 0.001) -> float:
        """
        Calcular escala de tiempo característica
        
        Args:
            f0: Frecuencia
            nu: Viscosidad
            
        Returns:
            τ ~ f0^((alpha-1)/2)
        """
        epsilon = self.lambda_val * f0**(-self.alpha)
        return (nu / epsilon)**0.5
    
    def convergence_rate(self, f0: float, delta_computed: float) -> float:
        """
        Estimar tasa de convergencia a delta*
        
        Args:
            f0: Frecuencia
            delta_computed: Valor computado de delta*
            
        Returns:
            Tasa de convergencia
        """
        delta_theory = self.theoretical_delta_star()
        return abs(delta_computed - delta_theory) / delta_theory
    
    def optimal_frequency_range(self, nu: float = 0.001) -> Tuple[float, float]:
        """
        Determinar rango óptimo de frecuencias
        
        Args:
            nu: Viscosidad
            
        Returns:
            (f_min, f_max): Rango de frecuencias recomendado
        """
        # f_min: suficientemente grande para observar régimen dual
        f_min = 100.0
        
        # f_max: limitado por estabilidad numérica
        # dt < 1/(2πf0) para resolver oscilaciones
        f_max = 10000.0
        
        return f_min, f_max
    
    def analyze_convergence(self, results: Dict) -> Dict:
        """
        Analizar convergencia de resultados computacionales
        
        Args:
            results: Diccionario con resultados de simulaciones
                     {f0: {'delta_star': valor, ...}}
            
        Returns:
            Análisis de convergencia
        """
        f0_values = sorted(results.keys())
        delta_star_values = [results[f0]['delta_star'] for f0 in f0_values]
        
        delta_theory = self.theoretical_delta_star()
        
        analysis = {
            'f0_values': f0_values,
            'delta_star_computed': delta_star_values,
            'delta_star_theoretical': delta_theory,
            'relative_errors': [abs(delta - delta_theory)/delta_theory for delta in delta_star_values],
            'convergence_rate': None,
            'extrapolated_limit': None
        }
        
        # Estimar convergencia por regresión
        if len(f0_values) >= 3:
            # Ajustar delta(f0) ~ delta* + C/f0^beta
            log_f = np.log(f0_values[-3:])
            log_error = np.log([abs(delta - delta_theory) + 1e-10 
                               for delta in delta_star_values[-3:]])
            
            coeffs = np.polyfit(log_f, log_error, 1)
            analysis['convergence_rate'] = -coeffs[0]  # beta
            
            # Extrapolar al límite
            if len(delta_star_values) >= 2:
                analysis['extrapolated_limit'] = delta_star_values[-1]
        
        return analysis
    
    def dual_limit_conditions(self, f0: float, nu: float = 0.001) -> Dict[str, bool]:
        """
        Verificar condiciones del límite dual
        
        Args:
            f0: Frecuencia
            nu: Viscosidad
            
        Returns:
            Diccionario con condiciones verificadas
        """
        epsilon = self.lambda_val * f0**(-self.alpha)
        A = self.a * f0
        
        conditions = {
            'alpha_greater_than_one': self.alpha > 1,
            'epsilon_decreasing': epsilon < self.lambda_val * 100**(-self.alpha),  # Comparar con f0=100
            'amplitude_increasing': A > self.a * 100,
            'forcing_vanishing': self.forcing_magnitude(f0) < self.forcing_magnitude(100),
            'time_scale_diverging': self.characteristic_time_scale(f0, nu) > 
                                   self.characteristic_time_scale(100, nu)
        }
        
        return conditions
    
    def parameter_sensitivity(self, f0: float, 
                            param_name: str, 
                            param_range: np.ndarray) -> np.ndarray:
        """
        Analizar sensibilidad con respecto a parámetros
        
        Args:
            f0: Frecuencia base
            param_name: Nombre del parámetro ('lambda', 'a', 'alpha')
            param_range: Rango de valores del parámetro
            
        Returns:
            Array de delta* para cada valor del parámetro
        """
        delta_star_values = []
        
        for param_val in param_range:
            if param_name == 'lambda':
                delta_star = (self.a**2) / (4 * np.pi**2)
            elif param_name == 'a':
                delta_star = (param_val**2) / (4 * np.pi**2)
            elif param_name == 'alpha':
                # alpha no afecta delta* directamente en la teoría
                delta_star = self.theoretical_delta_star()
            else:
                raise ValueError(f"Parámetro desconocido: {param_name}")
            
            delta_star_values.append(delta_star)
        
        return np.array(delta_star_values)


def compute_riccati_coefficient(delta: float, C_BKM: float = 1.0, 
                               nu: float = 0.001, c_B: float = 0.8) -> float:
    """
    Calcular coeficiente alpha* de la ecuación de Riccati
    
    Args:
        delta: Defecto de desalineamiento
        C_BKM: Constante BKM
        nu: Viscosidad
        c_B: Parámetro de disipación
        
    Returns:
        alpha* = C_BKM(1-delta) - nuc_B
    """
    return C_BKM * (1 - delta) - nu * c_B


def analyze_blow_up_criterion(delta_star: float, nu: float = 0.001) -> Dict:
    """
    Analizar criterio de blow-up basado en delta*
    
    Args:
        delta_star: Valor de delta*
        nu: Viscosidad
        
    Returns:
        Análisis del criterio
    """
    C_BKM = 1.0  # Estimación conservadora
    c_B = 0.8
    
    alpha_star = compute_riccati_coefficient(delta_star, C_BKM, nu, c_B)
    
    analysis = {
        'delta_star': delta_star,
        'alpha_star': alpha_star,
        'regularization_achieved': alpha_star < 0,
        'safety_margin': -alpha_star if alpha_star < 0 else 0,
        'critical_delta': nu * c_B / C_BKM,  # delta crítico para alpha* = 0
        'interpretation': 'Regularización exitosa' if alpha_star < 0 else 
                         'Regularización insuficiente'
    }
    
    return analysis


if __name__ == "__main__":
    # Ejemplo de uso
    analyzer = DualLimitAnalyzer(lambda_val=1.0, a=1.0, alpha=2.0)
    
    print("Análisis de Límite Dual")
    print("=" * 50)
    
    # Valor teórico
    delta_theory = analyzer.theoretical_delta_star()
    print(f"\ndelta* teórico: {delta_theory:.6f}")
    
    # Análisis para diferentes frecuencias
    f0_values = [100, 500, 1000, 5000]
    print("\nAnálisis por frecuencia:")
    for f0 in f0_values:
        forcing = analyzer.forcing_magnitude(f0)
        τ = analyzer.characteristic_time_scale(f0)
        print(f"  f0 = {f0} Hz: ‖epsilonnablaPhi‖ = {forcing:.6f}, τ = {τ:.2f}")
    
    # Criterio de blow-up
    blow_up = analyze_blow_up_criterion(delta_theory)
    print(f"\nCriterio de blow-up:")
    print(f"  alpha* = {blow_up['alpha_star']:.6f}")
    print(f"  {blow_up['interpretation']}")
