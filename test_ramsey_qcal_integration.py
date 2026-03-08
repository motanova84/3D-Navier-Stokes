#!/usr/bin/env python3
"""
Test suite for Ramsey Logos Attractor and QCAL integration
"""

import unittest
from qcal.ramsey_logos_attractor import emergencia_ramsey_qcal, escanear_orden_ramsey_bsd
from qcal.bsd_adelic_connector import sincronizar_bsd_adn, verificar_pentagono_logos
from qcal.adn_riemann import CodificadorADNRiemann
from integrate_qcal_compact import ramsey_bsd_logos_boveda


class TestRamseyLogosAttractor(unittest.TestCase):
    """Test Ramsey theory integration"""
    
    def test_emergencia_ramsey_below_threshold(self):
        """Test Ramsey emergence below critical threshold"""
        result = emergencia_ramsey_qcal(30)
        self.assertEqual(result['ramsey_status'], 'CAOS_TRANSITORIO')
        self.assertFalse(result['logos_manifestado'])
        self.assertEqual(result['nodos_critico'], 51)
        # Below threshold, psi can be high but logos is not manifested
        self.assertLessEqual(result['psi_emergencia'], 1.0)
    
    def test_emergencia_ramsey_at_threshold(self):
        """Test Ramsey emergence at critical threshold"""
        result = emergencia_ramsey_qcal(51)
        self.assertEqual(result['ramsey_status'], 'ORDEN_INEVITABLE')
        self.assertTrue(result['logos_manifestado'])
        self.assertEqual(result['nodos_critico'], 51)
        self.assertAlmostEqual(result['psi_emergencia'], 0.999999, places=5)
    
    def test_emergencia_ramsey_above_threshold(self):
        """Test Ramsey emergence above critical threshold"""
        result = emergencia_ramsey_qcal(100)
        self.assertEqual(result['ramsey_status'], 'ORDEN_INEVITABLE')
        self.assertTrue(result['logos_manifestado'])
        self.assertAlmostEqual(result['psi_emergencia'], 0.999999, places=5)
    
    def test_escanear_orden_ramsey_bsd_with_rank(self):
        """Test Ramsey-BSD scan with positive rank"""
        curva = {'rango_adelico': 1}
        result = escanear_orden_ramsey_bsd(curva, "GACT")
        
        self.assertEqual(result['status'], 'ORDEN_MANIFESTADO')
        self.assertEqual(result['nodo_central'], 'GACT')
        self.assertAlmostEqual(result['coherencia_ramsey'], 0.999999, places=5)
        self.assertEqual(result['conexion_bsd'], 'VALIDADA')
        self.assertEqual(result['rango_bsd'], 1)
    
    def test_escanear_orden_ramsey_bsd_without_rank(self):
        """Test Ramsey-BSD scan without rank"""
        curva = {'rango_adelico': 0}
        result = escanear_orden_ramsey_bsd(curva, "GACT")
        
        self.assertEqual(result['status'], 'ESPERA')
        self.assertIsNone(result['nodo_central'])
        self.assertAlmostEqual(result['coherencia_ramsey'], 0.888, places=3)
        self.assertEqual(result['conexion_bsd'], 'REPOSO')
        self.assertEqual(result['rango_bsd'], 0)


class TestADNRiemann(unittest.TestCase):
    """Test ADN-Riemann encoder"""
    
    def test_codificador_initialization(self):
        """Test encoder initialization"""
        codif = CodificadorADNRiemann()
        self.assertEqual(codif.f0, 141.7001)
    
    def test_codificar_sequence(self):
        """Test DNA sequence encoding"""
        codif = CodificadorADNRiemann()
        result = codif.codificar("GACT")
        self.assertEqual(len(result), 4)
    
    def test_identificar_hotspots(self):
        """Test hotspot identification"""
        codif = CodificadorADNRiemann()
        hotspots = codif.identificar_hotspots("GACTGACT")
        self.assertIsInstance(hotspots, list)
    
    def test_resonancia_con_f0(self):
        """Test resonance calculation"""
        codif = CodificadorADNRiemann()
        resonancia = codif.resonancia_con_f0("GACT")
        self.assertGreaterEqual(resonancia, 0.0)
        self.assertLessEqual(resonancia, 1.0)


class TestBSDAdelicConnector(unittest.TestCase):
    """Test BSD-Adelic connector"""
    
    def test_sincronizar_bsd_adn_superfluido(self):
        """Test BSD-DNA synchronization in superfluid state"""
        curva = {'rango_adelico': 1, 'L_E_1': 0.0}
        result = sincronizar_bsd_adn(curva, "GACT")
        
        self.assertTrue(result['es_superfluido'])
        self.assertEqual(result['estado_flujo'], 'SUPERFLUIDEZ')
        self.assertEqual(result['complejidad_computacional'], 'O(1)')
        self.assertAlmostEqual(result['psi_coherencia'], 0.999999, places=5)
    
    def test_sincronizar_bsd_adn_coherente(self):
        """Test BSD-DNA synchronization in coherent state"""
        curva = {'rango_adelico': 1, 'L_E_1': 0.5}
        result = sincronizar_bsd_adn(curva, "GACT")
        
        self.assertFalse(result['es_superfluido'])
        self.assertEqual(result['estado_flujo'], 'COHERENTE')
        self.assertEqual(result['complejidad_computacional'], 'O(log n)')
        self.assertGreater(result['psi_coherencia'], 0.888)
    
    def test_sincronizar_bsd_adn_turbulento(self):
        """Test BSD-DNA synchronization in turbulent state"""
        curva = {'rango_adelico': 0, 'L_E_1': 1.0}
        result = sincronizar_bsd_adn(curva, "GACT")
        
        self.assertFalse(result['es_superfluido'])
        self.assertEqual(result['estado_flujo'], 'TURBULENTO')
        self.assertEqual(result['complejidad_computacional'], 'O(n)')
        self.assertAlmostEqual(result['psi_coherencia'], 0.888, places=3)
    
    def test_verificar_pentagono_logos_closed(self):
        """Test Pentagon Logos verification when closed"""
        bsd_sync = {
            'rango_adelico': 1,
            'hotspots_adn': 4,
            'resonancia_f0': 0.8,
            'es_superfluido': True,
            'complejidad_computacional': 'O(1)',
            'psi_coherencia': 0.999999
        }
        
        result = verificar_pentagono_logos(bsd_sync)
        self.assertTrue(result['pentagono_cerrado'])
        self.assertTrue(result['bsd'])
        self.assertTrue(result['adn'])
        self.assertTrue(result['riemann'])
        self.assertTrue(result['navier_stokes'])
        self.assertTrue(result['p_vs_np'])
    
    def test_verificar_pentagono_logos_open(self):
        """Test Pentagon Logos verification when open"""
        bsd_sync = {
            'rango_adelico': 0,
            'hotspots_adn': 0,
            'resonancia_f0': 0.3,
            'es_superfluido': False,
            'complejidad_computacional': 'O(n)',
            'psi_coherencia': 0.888
        }
        
        result = verificar_pentagono_logos(bsd_sync)
        self.assertFalse(result['pentagono_cerrado'])


class TestIntegrateQCALCompact(unittest.TestCase):
    """Test integrated QCAL compact framework"""
    
    def test_ramsey_bsd_logos_boveda(self):
        """Test Ramsey-BSD closure of truth vault"""
        cert = ramsey_bsd_logos_boveda()
        
        # Check master certification structure
        self.assertIn('ramsey_bsd_logos', cert)
        self.assertTrue(cert['boveda_verdad_cerrada'])
        self.assertEqual(cert['pilares'], 21)
        self.assertEqual(cert['problemas_milenio'], 6)
        
        # Check Ramsey-BSD specific fields
        ramsey_bsd = cert['ramsey_bsd_logos']
        self.assertEqual(ramsey_bsd['nodos_critico'], 51)
        self.assertEqual(ramsey_bsd['nodos_actuales'], 60)
        self.assertAlmostEqual(ramsey_bsd['psi_ramsey'], 0.999999, places=5)
        self.assertEqual(ramsey_bsd['nodo_central'], 'GACT')
        self.assertEqual(ramsey_bsd['milenio_unificados'], 6)


if __name__ == '__main__':
    unittest.main(verbosity=2)
