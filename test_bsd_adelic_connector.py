#!/usr/bin/env python3
"""
Tests for BSD-Adelic Connector
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Pruebas unitarias para el módulo qcal.bsd_adelic_connector que conecta
la Conjetura BSD con el ecosistema ADN-Riemann-NS-PNP.

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: 8 de marzo de 2026
License: MIT
"""

import unittest
import sys
from pathlib import Path

# Asegurar que el módulo qcal esté en el path
sys.path.insert(0, str(Path(__file__).parent))

from qcal.bsd_adelic_connector import (
    sincronizar_bsd_adn,
    CodificadorADNRiemann,
    F0
)


class TestCodificadorADNRiemann(unittest.TestCase):
    """Tests para la clase CodificadorADNRiemann"""
    
    def setUp(self):
        """Configurar codificador para cada test"""
        self.codificador = CodificadorADNRiemann()
    
    def test_identificar_hotspots_gact(self):
        """Test identificación de hotspots en secuencia GACT"""
        hotspots = self.codificador.identificar_hotspots("GACT")
        self.assertGreater(len(hotspots), 0, "GACT debe tener hotspots")
    
    def test_identificar_hotspots_secuencia_larga(self):
        """Test identificación de hotspots en secuencia larga"""
        secuencia = "ATCGGACTCGTAGACTATCG"
        hotspots = self.codificador.identificar_hotspots(secuencia)
        # Debe encontrar al menos el patrón GACT
        self.assertGreater(len(hotspots), 0)
    
    def test_identificar_hotspots_vacio(self):
        """Test con secuencia vacía"""
        hotspots = self.codificador.identificar_hotspots("")
        self.assertEqual(len(hotspots), 0, "Secuencia vacía no debe tener hotspots")
    
    def test_calcular_resonancia_gact(self):
        """Test cálculo de resonancia para GACT"""
        resonancia = self.codificador.calcular_resonancia("GACT")
        self.assertGreater(resonancia, 0.0)
        self.assertLessEqual(resonancia, 1.0)
        # GACT debe tener alta resonancia
        self.assertGreater(resonancia, 0.7)
    
    def test_calcular_resonancia_bases_individuales(self):
        """Test resonancia de bases individuales"""
        # Guanina debe tener la mayor resonancia
        res_g = self.codificador.calcular_resonancia("G")
        res_a = self.codificador.calcular_resonancia("A")
        res_c = self.codificador.calcular_resonancia("C")
        res_t = self.codificador.calcular_resonancia("T")
        
        self.assertGreaterEqual(res_g, res_a)
        self.assertGreaterEqual(res_a, res_c)
        self.assertGreaterEqual(res_c, res_t)
    
    def test_resonancia_case_insensitive(self):
        """Test que la resonancia es case-insensitive"""
        res_upper = self.codificador.calcular_resonancia("GACT")
        res_lower = self.codificador.calcular_resonancia("gact")
        res_mixed = self.codificador.calcular_resonancia("GaCt")
        
        self.assertEqual(res_upper, res_lower)
        self.assertEqual(res_upper, res_mixed)


class TestSincronizarBSDADN(unittest.TestCase):
    """Tests para la función sincronizar_bsd_adn"""
    
    def test_curva_mordell_r1_l0(self):
        """Test con curva de Mordell: r=1, L(E,1)=0"""
        curva = {'rango_adelico': 1, 'L_E1': 0.0}
        resultado = sincronizar_bsd_adn(curva, "GACT")
        
        # Verificar estructura del resultado
        self.assertIn('rango_bio_aritmetico', resultado)
        self.assertIn('nodos_constelacion', resultado)
        self.assertIn('fluidez_info_ns', resultado)
        self.assertIn('hotspots_adn', resultado)
        self.assertIn('psi_bsd_qcal', resultado)
        
        # Verificar valores
        self.assertEqual(resultado['rango_bio_aritmetico'], 1)
        self.assertEqual(resultado['fluidez_info_ns'], "INFINITA")
        self.assertEqual(resultado['psi_bsd_qcal'], 1.0)
        self.assertGreater(resultado['hotspots_adn'], 0)
    
    def test_superfluidez_l_e1_cero(self):
        """Test que L(E,1)=0 produce superfluidez"""
        curva = {'rango_adelico': 2, 'L_E1': 0.0}
        resultado = sincronizar_bsd_adn(curva, "ATCG")
        
        self.assertEqual(resultado['fluidez_info_ns'], "INFINITA")
        self.assertEqual(resultado['psi_bsd_qcal'], 1.0)
    
    def test_disipacion_l_e1_nonzero(self):
        """Test que L(E,1)≠0 produce disipación"""
        curva = {'rango_adelico': 0, 'L_E1': 0.5}
        resultado = sincronizar_bsd_adn(curva, "TATA")
        
        self.assertEqual(resultado['fluidez_info_ns'], "DISIPATIVA")
        self.assertLess(resultado['psi_bsd_qcal'], 1.0)
        self.assertEqual(resultado['psi_bsd_qcal'], 0.5)
    
    def test_rango_cero(self):
        """Test con rango r=0"""
        curva = {'rango_adelico': 0, 'L_E1': 0.0}
        resultado = sincronizar_bsd_adn(curva, "AAAA")
        
        self.assertEqual(resultado['rango_bio_aritmetico'], 0)
        self.assertEqual(resultado['nodos_constelacion'], 0)
    
    def test_rango_alto(self):
        """Test con rango alto r=5"""
        curva = {'rango_adelico': 5, 'L_E1': 0.0}
        resultado = sincronizar_bsd_adn(curva, "CGTA")
        
        self.assertEqual(resultado['rango_bio_aritmetico'], 5)
        self.assertEqual(resultado['nodos_constelacion'], 5)
        self.assertEqual(resultado['fluidez_info_ns'], "INFINITA")
    
    def test_nodos_constelacion_proporcional_rango(self):
        """Test que los nodos activados son proporcionales al rango"""
        curva1 = {'rango_adelico': 1, 'L_E1': 0.0}
        curva2 = {'rango_adelico': 2, 'L_E1': 0.0}
        curva3 = {'rango_adelico': 3, 'L_E1': 0.0}
        
        res1 = sincronizar_bsd_adn(curva1, "GACT")
        res2 = sincronizar_bsd_adn(curva2, "GACT")
        res3 = sincronizar_bsd_adn(curva3, "GACT")
        
        self.assertEqual(res2['nodos_constelacion'], 2 * res1['nodos_constelacion'])
        self.assertEqual(res3['nodos_constelacion'], 3 * res1['nodos_constelacion'])
    
    def test_viscosidad_pequena(self):
        """Test con viscosidad muy pequeña pero no cero"""
        curva = {'rango_adelico': 1, 'L_E1': 1e-7}
        resultado = sincronizar_bsd_adn(curva, "GACT")
        
        # Tolerancia de 1e-6, así que 1e-7 debe dar superfluidez
        self.assertEqual(resultado['fluidez_info_ns'], "INFINITA")
    
    def test_coherencia_psi_boundaries(self):
        """Test que Ψ está siempre en [0, 1]"""
        test_cases = [
            {'rango_adelico': 1, 'L_E1': -0.5},  # Valor negativo
            {'rango_adelico': 1, 'L_E1': 0.0},   # Cero
            {'rango_adelico': 1, 'L_E1': 0.5},   # Medio
            {'rango_adelico': 1, 'L_E1': 1.0},   # Uno
            {'rango_adelico': 1, 'L_E1': 2.0},   # Mayor que 1
        ]
        
        for curva in test_cases:
            resultado = sincronizar_bsd_adn(curva, "GACT")
            psi = resultado['psi_bsd_qcal']
            self.assertGreaterEqual(psi, 0.0, f"Ψ debe ser >= 0 para L_E1={curva['L_E1']}")
            self.assertLessEqual(psi, 1.0, f"Ψ debe ser <= 1 para L_E1={curva['L_E1']}")


class TestConstantes(unittest.TestCase):
    """Tests para constantes del módulo"""
    
    def test_f0_value(self):
        """Test que F0 tiene el valor correcto"""
        self.assertEqual(F0, 141.7001)
    
    def test_f0_positive(self):
        """Test que F0 es positiva"""
        self.assertGreater(F0, 0)


class TestPentagonoLogos(unittest.TestCase):
    """Tests de integración para el Pentágono Logos completo"""
    
    def test_pentagono_unificacion_completa(self):
        """Test de unificación de los 5 componentes del Pentágono"""
        # Curva con rango positivo y superfluidez
        curva = {'rango_adelico': 1, 'L_E1': 0.0}
        
        # Secuencia ADN resonante
        secuencia = "GACT"
        
        # Sincronizar
        resultado = sincronizar_bsd_adn(curva, secuencia)
        
        # Verificar unificación
        # 1. BSD: rango > 0
        self.assertGreater(resultado['rango_bio_aritmetico'], 0)
        
        # 2. ADN: hotspots presentes
        self.assertGreater(resultado['hotspots_adn'], 0)
        
        # 3. Navier-Stokes: superfluidez
        self.assertEqual(resultado['fluidez_info_ns'], "INFINITA")
        
        # 4. Coherencia cuántica: Ψ = 1.0
        self.assertEqual(resultado['psi_bsd_qcal'], 1.0)
        
        # 5. Nodos activos (constelación QCAL)
        self.assertGreater(resultado['nodos_constelacion'], 0)


def suite():
    """Construir suite de tests"""
    suite = unittest.TestSuite()
    
    # Añadir todos los tests
    suite.addTests(unittest.TestLoader().loadTestsFromTestCase(TestCodificadorADNRiemann))
    suite.addTests(unittest.TestLoader().loadTestsFromTestCase(TestSincronizarBSDADN))
    suite.addTests(unittest.TestLoader().loadTestsFromTestCase(TestConstantes))
    suite.addTests(unittest.TestLoader().loadTestsFromTestCase(TestPentagonoLogos))
    
    return suite


if __name__ == '__main__':
    # Ejecutar tests con verbosidad
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite())
    
    # Retornar código de salida apropiado
    exit(0 if result.wasSuccessful() else 1)
