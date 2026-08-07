#!/bin/bash
# ============================================================================
# scripts/deploy_governance.sh
# Despliegue del contrato de gobernanza NOESIS
# ============================================================================

set -e

echo "🌊 NOESIS — Despliegue de Gobernanza On-Chain"
echo "=============================================="

: "${SEPOLIA_RPC:?'Variable SEPOLIA_RPC no definida'}"
: "${PRIVATE_KEY:?'Variable PRIVATE_KEY no definida'}"

# Cargar dirección del StateVerifier
if [ -f ".testnet_addresses.json" ]; then
    STATE_VERIFIER=$(jq -r '.NOESISStateVerifier' .testnet_addresses.json)
    echo "  ℹ️  Usando NOESISStateVerifier: $STATE_VERIFIER"
else
    echo "  ❌ .testnet_addresses.json no encontrado. Ejecutar deploy_testnet.sh primero."
    exit 1
fi

echo "🔨 Compilando contrato de gobernanza..."
forge build

echo "🚀 Desplegando NOESISGovernance..."
GOVERNANCE=$(forge create \
    contracts/NOESISGovernance.sol:NOESISGovernance \
    --constructor-args "$STATE_VERIFIER" \
    --rpc-url "$SEPOLIA_RPC" \
    --private-key "$PRIVATE_KEY" \
    --json | jq -r '.deployedTo')

echo "  ✅ NOESISGovernance: $GOVERNANCE"

# Actualizar archivo de direcciones
jq --arg addr "$GOVERNANCE" '.NOESISGovernance = $addr' \
    .testnet_addresses.json > .testnet_addresses_tmp.json && \
    mv .testnet_addresses_tmp.json .testnet_addresses.json

echo "✅ Gobernanza desplegada: $GOVERNANCE"
