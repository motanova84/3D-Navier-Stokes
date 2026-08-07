#!/bin/bash
# ============================================================================
# scripts/deploy_mainnet.sh
# Despliegue de contratos NOESIS en Ethereum Mainnet
# ============================================================================

set -e

echo "🌊 NOESIS — Despliegue en Ethereum Mainnet"
echo "==========================================="
echo "⚠️  ATENCIÓN: Despliegue en mainnet. Confirmar con 'yes':"
read -r CONFIRM
if [ "$CONFIRM" != "yes" ]; then
    echo "Despliegue cancelado."
    exit 0
fi

: "${MAINNET_RPC:?'Variable MAINNET_RPC no definida'}"
: "${PRIVATE_KEY:?'Variable PRIVATE_KEY no definida'}"

echo "🔨 Compilando contratos..."
forge build

echo "🔍 Ejecutando pruebas finales antes del despliegue..."
forge test --gas-report
echo "  ✅ Pruebas superadas"

echo "🚀 Desplegando NOESISZKVerifier..."
ZK_VERIFIER=$(forge create \
    contracts/NOESISZKVerifier.sol:NOESISZKVerifier \
    --rpc-url "$MAINNET_RPC" \
    --private-key "$PRIVATE_KEY" \
    --verify \
    --json | jq -r '.deployedTo')
echo "  ✅ NOESISZKVerifier: $ZK_VERIFIER"

echo "🚀 Desplegando NOESISStateVerifier..."
STATE_VERIFIER=$(forge create \
    contracts/NOESISStateVerifier.sol:NOESISStateVerifier \
    --constructor-args "$ZK_VERIFIER" \
    --rpc-url "$MAINNET_RPC" \
    --private-key "$PRIVATE_KEY" \
    --verify \
    --json | jq -r '.deployedTo')
echo "  ✅ NOESISStateVerifier: $STATE_VERIFIER"

echo "🚀 Desplegando NOESISGovernance..."
GOVERNANCE=$(forge create \
    contracts/NOESISGovernance.sol:NOESISGovernance \
    --constructor-args "$STATE_VERIFIER" \
    --rpc-url "$MAINNET_RPC" \
    --private-key "$PRIVATE_KEY" \
    --verify \
    --json | jq -r '.deployedTo')
echo "  ✅ NOESISGovernance: $GOVERNANCE"

cat > .mainnet_addresses.json << EOF
{
  "network": "mainnet",
  "NOESISZKVerifier": "$ZK_VERIFIER",
  "NOESISStateVerifier": "$STATE_VERIFIER",
  "NOESISGovernance": "$GOVERNANCE",
  "deployed_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
}
EOF

echo "✅ Despliegue en mainnet completado."
