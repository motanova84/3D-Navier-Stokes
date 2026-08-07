#!/bin/bash
# ═══════════════════════════════════════════════════════════════
#   EJEMPLO COMPLETO - BARRIDO PARAMÉTRICO
#   
#   Guía completa de uso del sistema de barrido paramétrico
# ═══════════════════════════════════════════════════════════════

echo "═══════════════════════════════════════════════════════════════"
echo "  EJEMPLO COMPLETO - BARRIDO PARAMÉTRICO"
echo "═══════════════════════════════════════════════════════════════"

# 1. Setup inicial
echo ""
echo "1️⃣  SETUP"
make setup

# 2. Generar paquetes
echo ""
echo "2️⃣  GENERANDO PAQUETES"
make generate-packages

# 3. Ver resumen
echo ""
echo "3️⃣  RESUMEN DE PAQUETES"
python3 << EOF
import json
with open('parametric_sweep_packages/metadata.json', 'r') as f:
    meta = json.load(f)
with open('parametric_sweep_packages/priority_summary.json', 'r') as f:
    prio = json.load(f)

print(f"Total paquetes: {meta['total_packages']}")
print(f"Total simulaciones: {meta['total_simulations']}")
print(f"\nPor prioridad:")
for p in ['HIGH', 'MEDIUM', 'LOW']:
    print(f"  {p}: {len(prio[p])} paquetes")
EOF

# 4. Ejecutar primer paquete de prueba
echo ""
echo "4️⃣  EJECUTANDO PAQUETE DE PRUEBA"
python3 run_package.py --package-id 0 --dry-run

# 5. Preguntar al usuario cómo proceder
echo ""
echo "═══════════════════════════════════════════════════════════════"
echo "  ¿CÓMO QUIERES PROCEDER?"
echo "═══════════════════════════════════════════════════════════════"
echo ""
echo "  1) Ejecutar solo un paquete ahora"
echo "  2) Ejecutar paquetes de alta prioridad (secuencial)"
echo "  3) Modo continuo 24h"
echo "  4) Modo oportunista (background)"
echo "  5) Cancelar"
echo ""
read -p "Selecciona opción [1-5]: " option

case $option in
    1)
        echo "🚀 Ejecutando un paquete..."
        make run-next
        ;;
    2)
        echo "⚡ Ejecutando alta prioridad..."
        make run-batch-high
        ;;
    3)
        echo "🔄 Modo continuo 24h..."
        make run-continuous
        ;;
    4)
        echo "💤 Modo oportunista..."
        nohup make run-opportunistic > oportunistic.log 2>&1 &
        echo "   Proceso en background, ver: tail -f oportunistic.log"
        ;;
    5)
        echo "❌ Cancelado"
        exit 0
        ;;
    *)
        echo "❌ Opción inválida"
        exit 1
        ;;
esac

# 6. Mostrar progreso
echo ""
echo "6️⃣  MONITOREANDO PROGRESO"
make monitor

echo ""
echo "═══════════════════════════════════════════════════════════════"
echo "  ✓ EJEMPLO COMPLETO"
echo "═══════════════════════════════════════════════════════════════"
echo ""
echo "Comandos adicionales útiles:"
echo "  make monitor              - Ver progreso actualizado"
echo "  make detailed-report      - Generar reporte detallado"
echo "  make watch-progress       - Monitoreo en tiempo real"
echo "  make help                 - Ver todos los comandos"
echo ""
