#!/bin/bash
# batch_execution.sh
#
# Script para ejecutar múltiples paquetes en secuencia o paralelo
# Uso: ./batch_execution.sh [--mode sequential|parallel] [--priority HIGH|MEDIUM|LOW|ALL]

set -e  # Exit on error

# ═══════════════════════════════════════════════════════════════
# CONFIGURACIÓN
# ═══════════════════════════════════════════════════════════════

PACKAGES_DIR="parametric_sweep_packages"
RESULTS_DIR="parametric_sweep_results"
LOGS_DIR="parametric_sweep_logs"

MODE="sequential"
PRIORITY="ALL"
MAX_PARALLEL=4
CONTINUE_ON_ERROR=true

# ═══════════════════════════════════════════════════════════════
# PARSEAR ARGUMENTOS
# ═══════════════════════════════════════════════════════════════

while [[ $# -gt 0 ]]; do
    case $1 in
        --mode)
            MODE="$2"
            shift 2
            ;;
        --priority)
            PRIORITY="$2"
            shift 2
            ;;
        --max-parallel)
            MAX_PARALLEL="$2"
            shift 2
            ;;
        --stop-on-error)
            CONTINUE_ON_ERROR=false
            shift
            ;;
        *)
            echo "Opción desconocida: $1"
            exit 1
            ;;
    esac
done

# ═══════════════════════════════════════════════════════════════
# FUNCIONES AUXILIARES
# ═══════════════════════════════════════════════════════════════

log() {
    echo -e "[$(date '+%Y-%m-%d %H:%M:%S')] $1" | tee -a "$LOGS_DIR/batch.log"
}

get_packages_by_priority() {
    local priority=$1
    
    if [ "$priority" == "ALL" ]; then
        # Todos los paquetes, ordenados por prioridad
        python3 << EOF
import json
with open('$PACKAGES_DIR/priority_summary.json', 'r') as f:
    priorities = json.load(f)

packages = []
for p in ['HIGH', 'MEDIUM', 'LOW']:
    for pkg in priorities[p]:
        packages.append(pkg['package_id'])

print(' '.join(map(str, packages)))
EOF
    else
        # Solo paquetes de prioridad especificada
        python3 << EOF
import json
with open('$PACKAGES_DIR/priority_summary.json', 'r') as f:
    priorities = json.load(f)

packages = [pkg['package_id'] for pkg in priorities['$priority']]
print(' '.join(map(str, packages)))
EOF
    fi
}

is_package_completed() {
    local pkg_id=$1
    [ -f "$RESULTS_DIR/results_package_$(printf '%04d' $pkg_id).json" ]
}

run_package_safe() {
    local pkg_id=$1
    local log_file="$LOGS_DIR/package_$(printf '%04d' $pkg_id).log"
    
    log "🚀 Iniciando paquete $pkg_id"
    
    if is_package_completed $pkg_id; then
        log "⏭️  Paquete $pkg_id ya completado, saltando..."
        return 0
    fi
    
    # Ejecutar con timeout de 24 horas
    if timeout 86400 python3 run_package.py \
        --package-id $pkg_id \
        --output-dir "$RESULTS_DIR" \
        > "$log_file" 2>&1; then
        log "✅ Paquete $pkg_id completado exitosamente"
        return 0
    else
        local exit_code=$?
        log "❌ Paquete $pkg_id falló (exit code: $exit_code)"
        
        if [ "$CONTINUE_ON_ERROR" = false ]; then
            log "🛑 Deteniendo ejecución (--stop-on-error activo)"
            exit 1
        fi
        return 1
    fi
}

# ═══════════════════════════════════════════════════════════════
# SETUP
# ═══════════════════════════════════════════════════════════════

# Crear directorios primero
mkdir -p "$RESULTS_DIR" "$LOGS_DIR"

log "╔═══════════════════════════════════════════════════════════════╗"
log "║  EJECUCIÓN BATCH - BARRIDO PARAMÉTRICO                        ║"
log "╚═══════════════════════════════════════════════════════════════╝"

# Obtener lista de paquetes
PACKAGES=$(get_packages_by_priority "$PRIORITY")
N_PACKAGES=$(echo $PACKAGES | wc -w)

log "Modo:       $MODE"
log "Prioridad:  $PRIORITY"
log "Paquetes:   $N_PACKAGES"

if [ "$MODE" == "parallel" ]; then
    log "Paralelos:  $MAX_PARALLEL"
fi

# ═══════════════════════════════════════════════════════════════
# EJECUCIÓN SECUENCIAL
# ═══════════════════════════════════════════════════════════════

if [ "$MODE" == "sequential" ]; then
    log "\n🔄 Modo SECUENCIAL activado\n"
    
    success_count=0
    failed_count=0
    skipped_count=0
    
    for pkg_id in $PACKAGES; do
        if is_package_completed $pkg_id; then
            log "⏭️  Paquete $pkg_id ya completado, saltando..."
            skipped_count=$((skipped_count + 1))
            continue
        fi
        
        if run_package_safe $pkg_id; then
            success_count=$((success_count + 1))
        else
            failed_count=$((failed_count + 1))
        fi
        
        # Reporte intermedio cada 5 paquetes
        total_processed=$((success_count + failed_count))
        if [ $((total_processed % 5)) -eq 0 ] && [ $total_processed -gt 0 ]; then
            log "\n📊 PROGRESO: $total_processed/$N_PACKAGES paquetes"
            log "   ✅ Éxitos:  $success_count"
            log "   ❌ Fallos:   $failed_count"
            log "   ⏭️  Saltados: $skipped_count\n"
        fi
    done
    
    log "\n╔═══════════════════════════════════════════════════════════════╗"
    log "║  RESUMEN FINAL - EJECUCIÓN SECUENCIAL                         ║"
    log "╚═══════════════════════════════════════════════════════════════╝"
    log "Total procesados: $((success_count + failed_count))"
    log "Éxitos:           $success_count"
    log "Fallos:           $failed_count"
    log "Saltados:         $skipped_count"
    
    # Evitar división por cero
    if [ $((success_count + failed_count)) -gt 0 ]; then
        log "Tasa de éxito:    $(bc <<< "scale=1; 100*$success_count/($success_count+$failed_count)")%"
    else
        log "Tasa de éxito:    N/A (no se procesaron paquetes)"
    fi

# ═══════════════════════════════════════════════════════════════
# EJECUCIÓN PARALELA
# ═══════════════════════════════════════════════════════════════

elif [ "$MODE" == "parallel" ]; then
    log "\n⚡ Modo PARALELO activado (max $MAX_PARALLEL simultáneos)\n"
    
    # Usar GNU parallel si está disponible
    if command -v parallel &> /dev/null; then
        log "Usando GNU parallel"
        
        # Crear función wrapper para parallel
        run_one_package() {
            pkg_id=$1
            log_file="$LOGS_DIR/package_$(printf '%04d' $pkg_id).log"
            
            if [ -f "$RESULTS_DIR/results_package_$(printf '%04d' $pkg_id).json" ]; then
                return 0
            fi
            
            if timeout 86400 python3 run_package.py \
                --package-id $pkg_id \
                --output-dir "$RESULTS_DIR" \
                > "$log_file" 2>&1; then
                return 0
            else
                return 1
            fi
        }
        export -f run_one_package
        export LOGS_DIR RESULTS_DIR
        
        echo $PACKAGES | tr ' ' '\n' | \
        parallel -j $MAX_PARALLEL --progress --joblog "$LOGS_DIR/parallel.log" \
            run_one_package {}
        
        # Análisis de joblog
        success_count=$(awk 'NR>1 && $7==0' "$LOGS_DIR/parallel.log" | wc -l)
        failed_count=$(awk 'NR>1 && $7!=0' "$LOGS_DIR/parallel.log" | wc -l)
        
        log "\n╔═══════════════════════════════════════════════════════════════╗"
        log "║  RESUMEN FINAL - EJECUCIÓN PARALELA                           ║"
        log "╚═══════════════════════════════════════════════════════════════╝"
        log "Total procesados: $N_PACKAGES"
        log "Éxitos:           $success_count"
        log "Fallos:           $failed_count"
        
    else
        # Fallback: paralelización manual con backgrounding
        log "GNU parallel no disponible, usando backgrounding"
        
        pids=()
        active_count=0
        
        for pkg_id in $PACKAGES; do
            if is_package_completed $pkg_id; then
                continue
            fi
            
            # Esperar si ya hay MAX_PARALLEL procesos activos
            while [ $active_count -ge $MAX_PARALLEL ]; do
                sleep 5
                
                # Revisar procesos terminados
                for i in "${!pids[@]}"; do
                    if ! kill -0 ${pids[$i]} 2>/dev/null; then
                        unset 'pids[$i]'
                        active_count=$((active_count - 1))
                    fi
                done
                pids=("${pids[@]}")  # Re-index array
            done
            
            # Lanzar nuevo proceso
            run_package_safe $pkg_id &
            pids+=($!)
            active_count=$((active_count + 1))
            
            log "Lanzado paquete $pkg_id (PID: $!, activos: $active_count)"
        done
        
        # Esperar a que terminen todos
        log "\nEsperando a que terminen todos los procesos..."
        wait
        
        log "\n✅ Todos los procesos han terminado"
    fi
fi

# ═══════════════════════════════════════════════════════════════
# GENERAR REPORTE FINAL
# ═══════════════════════════════════════════════════════════════

log "\n📊 Generando reporte final..."
python3 parametric_sweep_monitor.py

log "\n✅ EJECUCIÓN BATCH COMPLETADA"
log "   Ver logs en: $LOGS_DIR/"
log "   Ver resultados en: $RESULTS_DIR/"
log "   Ver reporte en: artifacts/parametric_sweep_progress.png"
