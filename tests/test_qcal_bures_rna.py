#!/usr/bin/env python3
"""
Unit tests for QCAL Bures RNA Visualizer and QCAL-MOL Specification
===================================================================

Tests the Bures metric calculations, RNA conformational attractor,
simulation convergence, and .qmol file format generation/parsing.
"""

import os
import tempfile
import unittest
import numpy as np

from qcal.bures_rna_visualizer import (
    QCALBuresRNAVisualizer,
    export_to_qcal_mol,
    parse_qcal_mol,
)
import qcal


class TestQCALBuresRNAVisualizer(unittest.TestCase):
    """Test suite for QCALBuresRNAVisualizer."""

    def setUp(self):
        self.visualizer = QCALBuresRNAVisualizer(
            sequence_length=40,
            f_0=141.7001,
            psi_target=0.999999,
        )

    def test_initialization(self):
        """Verifica parámetros iniciales del visualizador."""
        self.assertEqual(self.visualizer.length, 40)
        self.assertAlmostEqual(self.visualizer.f_0, 141.7001, places=4)
        self.assertAlmostEqual(self.visualizer.psi, 0.999999, places=6)
        self.assertEqual(self.visualizer.k, 1e-6)
        self.assertAlmostEqual(self.visualizer.sigma, 1e-6, places=9)

    def test_native_attractor_shape(self):
        """El atractor nativo helicoidal debe tener forma (length, 3)."""
        attractor = self.visualizer.get_native_attractor()
        self.assertEqual(attractor.shape, (40, 3))
        # Verifica radio del cilindro helicoidal ~ 3.0
        radii = np.sqrt(attractor[:, 0] ** 2 + attractor[:, 1] ** 2)
        np.testing.assert_allclose(radii, 3.0, atol=1e-12)

    def test_bures_distance_zero_at_attractor(self):
        """La distancia de Bures D_B en el atractor nativo exacto debe ser 0.0."""
        attractor = self.visualizer.get_native_attractor()
        db_zero = self.visualizer.compute_bures_distance_profile(attractor, attractor)
        self.assertEqual(len(db_zero), 40)
        np.testing.assert_allclose(db_zero, 0.0, atol=1e-12)

    def test_bures_distance_positive_and_bounded(self):
        """La distancia de Bures D_B para estados desviados debe ser positiva y acotada."""
        attractor = self.visualizer.get_native_attractor()
        deviated = attractor + 2.0
        db_dev = self.visualizer.compute_bures_distance_profile(deviated, attractor)
        self.assertTrue(np.all(db_dev > 0.0))
        # D_B = sqrt(2(1 - exp(-d^2 / 2f0))) <= sqrt(2) ~ 1.4142
        self.assertTrue(np.all(db_dev <= np.sqrt(2.0)))

    def test_bures_distance_empty(self):
        """Manejo de coordenadas vacías."""
        empty_coords = np.empty((0, 3))
        db_empty = self.visualizer.compute_bures_distance_profile(empty_coords, empty_coords)
        self.assertEqual(len(db_empty), 0)

    def test_run_simulation_dimensions(self):
        """La simulación iterativa debe retornar coordenadas, atractor y perfil válidos."""
        coords, attractor, bures_profile = self.visualizer.run_simulation(steps=20, seed=42)
        self.assertEqual(coords.shape, (40, 3))
        self.assertEqual(attractor.shape, (40, 3))
        self.assertEqual(bures_profile.shape, (40,))
        self.assertTrue(np.all(bures_profile >= 0.0))

    def test_simulate_and_visualize_headless(self):
        """Ejecuta simulate_and_visualize sin mostrar interfaz y guardando archivo."""
        with tempfile.TemporaryDirectory() as tmpdir:
            out_img = os.path.join(tmpdir, "test_bures_render.png")
            coords, attractor, bures_profile = self.visualizer.simulate_and_visualize(
                steps=10,
                show=False,
                save_path=out_img,
                seed=42,
            )
            self.assertEqual(coords.shape, (40, 3))
            self.assertTrue(os.path.exists(out_img))
            self.assertGreater(os.path.getsize(out_img), 0)


class TestQCALMOLSpecification(unittest.TestCase):
    """Test suite para el estándar de exportación e importación QCAL-MOL (.qmol)."""

    def setUp(self):
        self.length = 30
        t = np.linspace(0, 2 * np.pi, self.length)
        self.sample_coords = np.stack(
            [3.0 * np.cos(t), 3.0 * np.sin(t), np.linspace(-5, 5, self.length)],
            axis=-1,
        )
        self.sample_bures = np.abs(np.sin(t)) * 1e-4

    def test_export_and_parse_qcal_mol(self):
        """Exporta y parsea un archivo .qmol verificando la integridad de los datos."""
        with tempfile.TemporaryDirectory() as tmpdir:
            qmol_path = os.path.join(tmpdir, "sample.qmol")
            export_to_qcal_mol(
                self.sample_coords,
                self.sample_bures,
                filename=qmol_path,
                f_0=141.7001,
                psi_target=0.999999,
            )
            self.assertTrue(os.path.exists(qmol_path))

            # Parsear el archivo generado
            parsed = parse_qcal_mol(qmol_path)
            self.assertIn("metadata", parsed)
            self.assertIn("qcal_metadata", parsed["metadata"])

            meta = parsed["metadata"]["qcal_metadata"]
            self.assertEqual(meta["protocol"], "QCAL-SYMBIO-BRIDGE")
            self.assertAlmostEqual(meta["fundamental_frequency_hz"], 141.7001, places=4)
            self.assertAlmostEqual(meta["target_coherence_psi"], 0.999999, places=6)
            self.assertEqual(meta["contraction_factor_k"], 1e-6)
            self.assertEqual(meta["metric_tensor_type"], "Bures-Fisher")

            # Verificar átomos
            self.assertEqual(len(parsed["atoms"]), self.length)
            first_atom = parsed["atoms"][0]
            self.assertEqual(first_atom["id"], 1)
            self.assertEqual(first_atom["name"], "P")
            self.assertEqual(first_atom["res"], "RNA")
            self.assertEqual(first_atom["chain"], "A")
            self.assertAlmostEqual(first_atom["coord"][0], self.sample_coords[0, 0], places=3)
            self.assertAlmostEqual(first_atom["coord"][1], self.sample_coords[0, 1], places=3)
            self.assertAlmostEqual(first_atom["coord"][2], self.sample_coords[0, 2], places=3)

            # Verificar distancias y coherencias locales
            coords_arr = parsed["coordinates"]
            bures_arr = parsed["bures_profile"]
            self.assertEqual(coords_arr.shape, (self.length, 3))
            self.assertEqual(bures_arr.shape, (self.length,))
            np.testing.assert_allclose(coords_arr, self.sample_coords, atol=1e-3)
            np.testing.assert_allclose(bures_arr, self.sample_bures, atol=1e-5)

    def test_qcal_package_exports(self):
        """Verifica que el paquete qcal exponga los nuevos símbolos."""
        self.assertTrue(hasattr(qcal, "QCALBuresRNAVisualizer"))
        self.assertTrue(hasattr(qcal, "export_to_qcal_mol"))
        self.assertTrue(hasattr(qcal, "parse_qcal_mol"))


if __name__ == "__main__":
    unittest.main()
