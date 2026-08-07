#!/bin/bash
# ============================================================================
# scripts/deploy_testnet.sh
# Despliegue de contratos NOESIS en Sepolia testnet
# ============================================================================

set -e

echo "🌊 NOESIS — Despliegue en Sepolia Testnet"
echo "=========================================="

: "${SEPOLIA_RPC:?'Variable SEPOLIA_RPC no definida'}"
: "${PRIVATE_KEY:?'Variable PRIVATE_KEY no definida'}"

echo "🔨 Compilando contratos..."
forge build

echo "🚀 Desplegando NOESISZKVerifier..."
ZK_VERIFIER=$(forge create \
    contracts/NOESISZKVerifier.sol:NOESISZKVerifier \
    --rpc-url "$SEPOLIA_RPC" \
    --private-key "$PRIVATE_KEY" \
    --json | jq -r '.deployedTo')
echo "  ✅ NOESISZKVerifier: $ZK_VERIFIER"

echo "🚀 Desplegando NOESISStateVerifier..."
STATE_VERIFIER=$(forge create \
    contracts/NOESISStateVerifier.sol:NOESISStateVerifier \
    --constructor-args "$ZK_VERIFIER" \
    --rpc-url "$SEPOLIA_RPC" \
    --private-key "$PRIVATE_KEY" \
    --json | jq -r '.deployedTo')
echo "  ✅ NOESISStateVerifier: $STATE_VERIFIER"

echo "🚀 Desplegando NOESISGovernance..."
GOVERNANCE=$(forge create \
    contracts/NOESISGovernance.sol:NOESISGovernance \
    --constructor-args "$STATE_VERIFIER" \
    --rpc-url "$SEPOLIA_RPC" \
    --private-key "$PRIVATE_KEY" \
    --json | jq -r '.deployedTo')
echo "  ✅ NOESISGovernance: $GOVERNANCE"

# Guardar direcciones
cat > .testnet_addresses.json << EOF
{
  "network": "sepolia",
  "NOESISZKVerifier": "$ZK_VERIFIER",
  "NOESISStateVerifier": "$STATE_VERIFIER",
  "NOESISGovernance": "$GOVERNANCE",
  "deployed_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
}
EOF

echo "✅ Despliegue completado. Direcciones guardadas en .testnet_addresses.json"
