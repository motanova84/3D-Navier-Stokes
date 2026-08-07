#!/bin/bash
# ============================================================================
# scripts/upgrade_contracts.sh
# Actualización de contratos NOESIS (patrón proxy)
# ============================================================================

set -e

echo "🌊 NOESIS — Actualización de Contratos"
echo "======================================="

: "${SEPOLIA_RPC:?'Variable SEPOLIA_RPC no definida'}"
: "${PRIVATE_KEY:?'Variable PRIVATE_KEY no definida'}"

if [ ! -f ".testnet_addresses.json" ]; then
    echo "❌ .testnet_addresses.json no encontrado"
    exit 1
fi

GOVERNANCE=$(jq -r '.NOESISGovernance' .testnet_addresses.json)
echo "  ℹ️  Contrato de gobernanza: $GOVERNANCE"

echo "🔨 Compilando nueva implementación..."
forge build

echo "🚀 Desplegando nueva implementación..."
NEW_IMPL=$(forge create \
    contracts/NOESISStateVerifier.sol:NOESISStateVerifier \
    --rpc-url "$SEPOLIA_RPC" \
    --private-key "$PRIVATE_KEY" \
    --json | jq -r '.deployedTo')

echo "  ✅ Nueva implementación: $NEW_IMPL"

echo "🔄 Actualizando proxy via gobernanza..."
cast send "$GOVERNANCE" \
    "upgradeImplementation(address)" "$NEW_IMPL" \
    --rpc-url "$SEPOLIA_RPC" \
    --private-key "$PRIVATE_KEY"

echo "✅ Contratos actualizados"
