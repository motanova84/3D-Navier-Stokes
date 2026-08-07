#!/bin/bash
# ============================================================================
# scripts/emergency_pause.sh
# Pausa de emergencia del sistema NOESIS on-chain
# ============================================================================

set -e

echo "🚨 NOESIS — PAUSA DE EMERGENCIA"
echo "================================"
echo "⚠️  Esta acción pausará el contrato de gobernanza."
echo "⚠️  Confirmar con 'PAUSE':"
read -r CONFIRM

if [ "$CONFIRM" != "PAUSE" ]; then
    echo "Operación cancelada."
    exit 0
fi

: "${SEPOLIA_RPC:?'Variable SEPOLIA_RPC no definida'}"
: "${PRIVATE_KEY:?'Variable PRIVATE_KEY no definida'}"

if [ ! -f ".testnet_addresses.json" ]; then
    echo "❌ .testnet_addresses.json no encontrado"
    exit 1
fi

GOVERNANCE=$(jq -r '.NOESISGovernance' .testnet_addresses.json)

echo "🛑 Enviando transacción de pausa a $GOVERNANCE..."
TX=$(cast send "$GOVERNANCE" \
    "pause()" \
    --rpc-url "$SEPOLIA_RPC" \
    --private-key "$PRIVATE_KEY" \
    --json | jq -r '.transactionHash')

echo "  ✅ Transacción enviada: $TX"
echo "  ⏸️  Sistema NOESIS en PAUSA"

# Registrar la pausa
cat > .emergency_pause_log.json << EOF
{
  "action": "EMERGENCY_PAUSE",
  "contract": "$GOVERNANCE",
  "tx_hash": "$TX",
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
}
EOF

echo "✅ Pausa registrada en .emergency_pause_log.json"
