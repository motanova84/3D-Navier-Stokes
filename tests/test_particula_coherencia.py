import hashlib

import pytest

from particula_coherencia import (
    AcoplamientoHiggsPC,
    FotonFaseCoherente,
    ParticulaCoherencia,
    ResultadoSustrato,
    ejecutar_sustrato,
)


def test_constante_f0_canonicamente_calibrada():
    pc = ParticulaCoherencia()
    assert pc.f0 == pytest.approx(141.7001)


def test_r_symb_usa_relacion_simbolica_esperada():
    pc = ParticulaCoherencia()
    foton = FotonFaseCoherente()
    assert foton.r_symb(pc.f0) == pytest.approx(7 * pc.f0 * foton.psi)


def test_calculo_reduccion_higgs_pc():
    higgs = AcoplamientoHiggsPC()
    reduccion = higgs.calcular_reduccion(a_eff=1.0, f0=10.0)
    assert reduccion == pytest.approx(0.053 * 0.01)


def test_resultado_sustrato_sella_sha256():
    payload = {"psi_global": 0.999999, "reduccion_masa": 0.053, "r_symb_kpps": 991.8997080993}
    result = ResultadoSustrato.from_payload(payload)
    assert result.sha256 == hashlib.sha256(str(payload).encode("utf-8")).hexdigest()


def test_ejecutar_sustrato_devuelve_resultado_inmutable():
    result = ejecutar_sustrato(verbose=False)
    assert isinstance(result, ResultadoSustrato)
    assert "psi_global" in result.data
    assert "reduccion_masa" in result.data
    assert "r_symb_kpps" in result.data
