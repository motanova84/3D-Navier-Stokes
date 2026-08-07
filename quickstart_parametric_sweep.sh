#!/bin/bash
# quickstart_parametric_sweep.sh

echo "╔═══════════════════════════════════════════════════════════════╗"
echo "║  QUICK START - BARRIDO PARAMÉTRICO                            ║"
echo "╚═══════════════════════════════════════════════════════════════╝"

# 1. Generar paquetes
echo ""
echo "📦 PASO 1: Generando paquetes..."
python3 parametric_sweep_orchestrator.py

# 2. Mostrar resumen
echo ""
echo "📊 PASO 2: Resumen de paquetes generados"
cat parametric_sweep_packages/priority_summary.json | python3 -m json.tool | head -n 30

# 3. Opciones de ejecución
echo ""
echo "╔═══════════════════════════════════════════════════════════════╗"
echo "║  OPCIONES DE EJECUCIÓN                                        ║"
echo "╚═══════════════════════════════════════════════════════════════╝"
echo ""
echo "OPCIÓN A: Ejecutar un paquete específico"
echo "  python3 run_package.py --package-id 0"
echo ""
echo "OPCIÓN B: Ejecutar paquetes de alta prioridad (secuencial)"
echo "  ./batch_execution.sh --mode sequential --priority HIGH"
echo ""
echo "OPCIÓN C: Ejecutar en paralelo (4 simultáneos)"
echo "  ./batch_execution.sh --mode parallel --priority HIGH --max-parallel 4"
echo ""
echo "OPCIÓN D: Modo continuo inteligente (hasta 24 horas)"
echo "  python3 intelligent_executor.py --mode continuous --max-hours 24"
echo ""
echo "OPCIÓN E: Modo oportunista (solo cuando CPU < 50%)"
echo "  python3 intelligent_executor.py --mode opportunistic --cpu-threshold 50"
echo ""
echo "═══════════════════════════════════════════════════════════════"
echo ""
echo "💡 RECOMENDACIÓN:"
echo "   Para comenzar rápido, ejecuta:"
echo "   python3 intelligent_executor.py --mode next"
echo ""
