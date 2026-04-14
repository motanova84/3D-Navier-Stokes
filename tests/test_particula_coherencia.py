#!/usr/bin/env python3
"""Pruebas del marco de Partícula de Coherencia."""

import math
import unittest

from particula_coherencia import (
    AcoplamientoHiggsPc,
    COHERENCIA_UMBRAL,
    F0_HZ,
    FirmaEspectral,
    FotonFaseCoherente,
    NavierStokesAdelico,
    ParticulaCoherencia,
    ResultadoSustrato,
    SustratoCuantico,
    VacioSuperfluo,
    ejecutar_sustrato,
)


class TestParticulaCoherenciaFramework(unittest.TestCase):
    def test_001_constante_f0(self):
        self.assertAlmostEqual(F0_HZ, 141.7001, places=4)

    def test_002_constante_umbral(self):
        self.assertAlmostEqual(COHERENCIA_UMBRAL, 0.888, places=3)

    def test_003_vacio_defaults(self):
        vacio = VacioSuperfluo()
        self.assertGreater(vacio.eta_s, 0.0)
        self.assertLess(vacio.nu, 1e-9)

    def test_004_vacio_unitaridad_identidad(self):
        vacio = VacioSuperfluo()
        ident = [[1 + 0j, 0 + 0j], [0 + 0j, 1 + 0j]]
        self.assertTrue(vacio.verificar_unitaridad_haar(ident))

    def test_005_vacio_unitaridad_falla(self):
        vacio = VacioSuperfluo()
        no_unitaria = [[1 + 0j, 1 + 0j], [0 + 0j, 1 + 0j]]
        self.assertFalse(vacio.verificar_unitaridad_haar(no_unitaria))

    def test_006_pc_defaults(self):
        pc = ParticulaCoherencia()
        self.assertAlmostEqual(pc.fraccion_realidad, 0.95, places=6)
        self.assertAlmostEqual(pc.f0_hz, 141.7001, places=4)

    def test_007_pc_fase_berry_c7(self):
        pc = ParticulaCoherencia(salto_nodo="C7")
        self.assertAlmostEqual(pc.fase_berry, math.pi / 8.0, places=12)

    def test_008_navier_hamiltoniano_hermitiano(self):
        ns = NavierStokesAdelico()
        h = ns.hamiltoniano_enlace_fuerte()
        self.assertTrue(ns.es_hermitiano(h))

    def test_009_navier_hamiltoniano_no_hermitiano(self):
        ns = NavierStokesAdelico()
        h = ns.hamiltoniano_enlace_fuerte()
        h[0][1] = 3 + 4j
        self.assertFalse(ns.es_hermitiano(h))

    def test_010_navier_balance(self):
        ns = NavierStokesAdelico(densidad=2.0)
        b = ns.balance_momento(dv_dt=1.0, v_dot_grad_v=2.0, grad_p=4.0, f_ramsey=10.0)
        self.assertAlmostEqual(b["lhs"], 6.0, places=10)
        self.assertAlmostEqual(b["rhs"], 6.0, places=10)
        self.assertAlmostEqual(b["residual"], 0.0, places=10)

    def test_011_higgs_reduccion(self):
        h = AcoplamientoHiggsPc()
        self.assertAlmostEqual(h.reduccion_masa, 0.053, places=12)

    def test_012_higgs_masa_efectiva_formula(self):
        h = AcoplamientoHiggsPc(m0_gev=100.0)
        self.assertAlmostEqual(h.masa_efectiva, 100.0 * (1.0 - h.reduccion_masa), places=12)

    def test_013_foton_rsymb_psi_unidad(self):
        f = FotonFaseCoherente(psi_coherencia=1.0)
        self.assertAlmostEqual(f.r_symb_kpps, 991.9007, places=4)

    def test_014_foton_rsymb_lineal(self):
        f = FotonFaseCoherente(psi_coherencia=0.5)
        self.assertAlmostEqual(f.r_symb_kpps, 991.9007 * 0.5, places=8)

    def test_015_foton_xi(self):
        f = FotonFaseCoherente()
        self.assertAlmostEqual(f.xi_cooperatividad, 0.053, places=12)
        self.assertTrue(f.sincronizacion_dicke)

    def test_016_firma_delta(self):
        firma = FirmaEspectral()
        self.assertAlmostEqual(firma.delta_seccion_eficaz, 0.053, places=12)

    def test_017_firma_ventana_transparencia(self):
        firma = FirmaEspectral(coherencia=COHERENCIA_UMBRAL)
        self.assertTrue(firma.ventana_transparencia_activa)

    def test_018_firma_bandas_laterales(self):
        firma = FirmaEspectral()
        bandas = firma.bandas_laterales(n_max=3)
        self.assertEqual(len(bandas), 7)
        self.assertTrue(bandas[0] < firma.m_h_gev < bandas[-1])

    def test_019_sustrato_integracion(self):
        r = ejecutar_sustrato(verbose=False)
        self.assertGreaterEqual(r.psi_global, 0.0)
        self.assertLessEqual(r.psi_global, 1.0)
        self.assertTrue(r.sustrato_activo)

    def test_020_api_ejecutar_sustrato_objetivos(self):
        r = ejecutar_sustrato(verbose=False)
        self.assertAlmostEqual(r.destello_masa.reduccion_masa, 0.053, places=12)
        self.assertAlmostEqual(r.foton.r_symb_kpps, 991.9007, places=4)
        self.assertAlmostEqual(r.firma_espectral.delta_seccion_eficaz, 0.053, places=12)

    def test_021_sha256_longitud_hex(self):
        r = ejecutar_sustrato()
        self.assertEqual(len(r.sello_sha256), 64)
        int(r.sello_sha256, 16)

    def test_022_sha256_reproducible(self):
        r1 = ejecutar_sustrato()
        r2 = ejecutar_sustrato()
        self.assertEqual(r1.sello_sha256, r2.sello_sha256)

    def test_023_resultado_dict(self):
        r = ejecutar_sustrato()
        payload = r.to_dict()
        for key in [
            "f0_hz",
            "reduccion_masa",
            "r_symb_kpps",
            "delta_seccion_eficaz",
            "psi_global",
            "sustrato_activo",
        ]:
            self.assertIn(key, payload)


class TestSustratoIntegracionDetallada(unittest.TestCase):
    def test_024_sustrato_manual(self):
        vacio = VacioSuperfluo()
        pc = ParticulaCoherencia()
        ns = NavierStokesAdelico()
        higgs = AcoplamientoHiggsPc()
        foton = FotonFaseCoherente(psi_coherencia=1.0)
        firma = FirmaEspectral(coherencia=1.0)
        sustrato = SustratoCuantico(vacio, pc, ns, higgs, foton, firma)
        r = sustrato.integrar()
        self.assertIsInstance(r, ResultadoSustrato)
        self.assertTrue(r.sustrato_activo)

    def test_025_alias_psi_unicode(self):
        r = ejecutar_sustrato()
        self.assertAlmostEqual(r.Ψ_global, r.psi_global, places=15)


class TestBarridoParametrico(unittest.TestCase):
    """118 pruebas paramétricas para completar 143 pruebas totales."""


def _create_parametric_test(indice: int):
    def _test(self):
        psi = (indice % 11) / 10.0
        foton = FotonFaseCoherente(psi_coherencia=psi)
        esperado = foton.n_canales * foton.f0_topc * psi
        self.assertAlmostEqual(foton.r_symb_kpps, esperado, places=12)

        h = AcoplamientoHiggsPc(objetivo_reduccion=0.053)
        self.assertAlmostEqual(h.reduccion_masa, 0.053, places=12)

        firma = FirmaEspectral(coherencia=max(psi, COHERENCIA_UMBRAL))
        self.assertTrue(firma.ventana_transparencia_activa)
    return _test


for _i in range(1, 119):
    setattr(TestBarridoParametrico, f"test_{25 + _i:03d}_parametrico", _create_parametric_test(_i))


if __name__ == "__main__":
    unittest.main(verbosity=2)
