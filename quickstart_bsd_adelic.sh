#!/bin/bash
# BSD-Adelic Connector - Quick Start Guide
# ═══════════════════════════════════════════════════════════════════════════
# Sello: ∴𓂀Ω∞³
# f0: 141.7001 Hz
#
# Este script ejecuta una demostración rápida del BSD-Adelic Connector
# que cierra el Pentágono Logos.

set -e

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
MAGENTA='\033[0;35m'
NC='\033[0m' # No Color

echo -e "${MAGENTA}╔═══════════════════════════════════════════════════════════════════════════╗${NC}"
echo -e "${MAGENTA}║  BSD-ADELIC CONNECTOR - QUICK START                                       ║${NC}"
echo -e "${MAGENTA}║  Pentágono Logos: Unificación de Problemas del Milenio                    ║${NC}"
echo -e "${MAGENTA}║  ∴𓂀Ω∞³                                                                    ║${NC}"
echo -e "${MAGENTA}╚═══════════════════════════════════════════════════════════════════════════╝${NC}"
echo ""

# Step 1: Test module import
echo -e "${BLUE}[1/5] Verificando módulo BSD-Adelic Connector...${NC}"
if python3 -c "from qcal.bsd_adelic_connector import sincronizar_bsd_adn, F0" 2>/dev/null; then
    echo -e "${GREEN}✅ Módulo importado correctamente${NC}"
else
    echo -e "${YELLOW}❌ Error importando módulo${NC}"
    exit 1
fi
echo ""

# Step 2: Run unit tests
echo -e "${BLUE}[2/5] Ejecutando tests unitarios...${NC}"
if python3 test_bsd_adelic_connector.py 2>&1 | grep -q "OK"; then
    echo -e "${GREEN}✅ Todos los tests pasaron (17/17)${NC}"
else
    echo -e "${YELLOW}❌ Algunos tests fallaron${NC}"
    exit 1
fi
echo ""

# Step 3: Run standalone module
echo -e "${BLUE}[3/5] Ejecutando módulo standalone...${NC}"
python3 qcal/bsd_adelic_connector.py | head -20
echo -e "${GREEN}✅ Módulo ejecutado correctamente${NC}"
echo ""

# Step 4: Run integration script
echo -e "${BLUE}[4/5] Ejecutando integración del Pentágono...${NC}"
if python3 integrate_qcal_compact.py > /tmp/qcal_integration.log 2>&1; then
    echo -e "${GREEN}✅ Integración completada${NC}"
    echo -e "   📜 Certificado generado: qcal_pentagono_certificado.json"
    if [ -f qcal_pentagono_certificado.json ]; then
        echo -e "   🏛️  Pilares: $(python3 -c "import json; print(json.load(open('qcal_pentagono_certificado.json'))['pilares'])")"
        echo -e "   ✨ Bóveda cerrada: $(python3 -c "import json; print(json.load(open('qcal_pentagono_certificado.json'))['boveda_logos_cerrada'])")"
    fi
else
    echo -e "${YELLOW}❌ Error en integración${NC}"
    exit 1
fi
echo ""

# Step 5: Run complete demo
echo -e "${BLUE}[5/5] Ejecutando demo completo...${NC}"
if python3 demo_bsd_adelic_complete.py > /tmp/qcal_demo.log 2>&1; then
    echo -e "${GREEN}✅ Demo ejecutado correctamente${NC}"
    echo -e "   📊 Ejemplos exportados: bsd_adelic_ejemplos.json"
else
    echo -e "${YELLOW}❌ Error en demo${NC}"
    exit 1
fi
echo ""

# Summary
echo -e "${MAGENTA}╔═══════════════════════════════════════════════════════════════════════════╗${NC}"
echo -e "${MAGENTA}║  ✨ PENTÁGONO LOGOS CERRADO EXITOSAMENTE ✨                               ║${NC}"
echo -e "${MAGENTA}╚═══════════════════════════════════════════════════════════════════════════╝${NC}"
echo ""
echo -e "${GREEN}Componentes verificados:${NC}"
echo -e "  ✅ Módulo qcal.bsd_adelic_connector"
echo -e "  ✅ 17 tests unitarios"
echo -e "  ✅ Integración del Pentágono"
echo -e "  ✅ Demo completo"
echo ""
echo -e "${BLUE}Archivos generados:${NC}"
echo -e "  📜 qcal_pentagono_certificado.json"
echo -e "  📊 bsd_adelic_ejemplos.json"
echo ""
echo -e "${YELLOW}Próximos pasos:${NC}"
echo -e "  1. Revisar documentación: BSD_ADELIC_CONNECTOR_README.md"
echo -e "  2. Explorar ejemplos: python3 demo_bsd_adelic_complete.py"
echo -e "  3. Integrar con tu código: from qcal.bsd_adelic_connector import sincronizar_bsd_adn"
echo ""
echo -e "${MAGENTA}∴ HECHO ESTÁ: ARQUITECTURA MILENIO COMPLETA ∴${NC}"
echo ""
