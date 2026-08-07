#!/bin/bash
# ============================================================================
# scripts/verify_onchain.sh
# Verificación End-to-End On-Chain
# ============================================================================

set -e

echo "🌊 NOESIS — Verificación End-to-End On-Chain"
echo "============================================"

# 1. Generar prueba Groth16
echo "🔐 Generando prueba Groth16..."
if [ ! -f "witness_input.json" ]; then
    echo "  ❌ witness_input.json no encontrado"
    exit 1
fi

snarkjs groth16 prove \
    build/noesis_coherence_final.zkey \
    build/noesis_coherence_js/noesis_coherence.wasm \
    witness_input.json \
    proof.json \
    public.json

echo "  ✅ Prueba generada"

# 2. Verificar la prueba localmente
echo "🔍 Verificando prueba..."
snarkjs groth16 verify \
    build/verification_key.json \
    public.json \
    proof.json

echo "  ✅ Prueba verificada"

# 3. Preparar y enviar transacción al contrato
echo "⛓️ Preparando transacción..."
CONTRACT_ADDRESS=$(cat .mainnet_state_address 2>/dev/null || true)

if [ -z "$CONTRACT_ADDRESS" ] || [ "$CONTRACT_ADDRESS" = "0x..." ]; then
    echo "  ⚠️  Dirección del contrato no configurada — omitiendo envío on-chain"
    echo "  ℹ️  Configure .mainnet_state_address con la dirección del contrato"
    exit 0
fi

# Generar calldata con cast (Foundry)
PI_A=$(jq -r '.pi_a[0:2] | @sh' proof.json)
PI_B=$(jq -r '.pi_b[0:2] | map(@sh) | .[]' proof.json)
PI_C=$(jq -r '.pi_c[0:2] | @sh' proof.json)
PUBLIC=$(jq -r '.[0:4] | @sh' public.json)

CALLDATA=$(cast calldata \
    "verifyAndRegisterZKState(uint256[2],uint256[2][2],uint256[2],uint256[4])" \
    $PI_A $PI_B $PI_C $PUBLIC)

echo "  📋 Calldata generada"

# Enviar transacción (requiere SEPOLIA_RPC y PRIVATE_KEY en el entorno)
if [ -n "$SEPOLIA_RPC" ] && [ -n "$PRIVATE_KEY" ]; then
    echo "  📡 Enviando transacción a $CONTRACT_ADDRESS..."
    cast send "$CONTRACT_ADDRESS" "$CALLDATA" \
        --rpc-url "$SEPOLIA_RPC" \
        --private-key "$PRIVATE_KEY"
    echo "  ✅ Transacción enviada"
else
    echo "  ⚠️  Variables SEPOLIA_RPC y/o PRIVATE_KEY no definidas — transacción omitida"
fi

echo "✅ Verificación End-to-End completada"
