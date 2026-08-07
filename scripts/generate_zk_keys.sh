#!/bin/bash
# ============================================================================
# scripts/generate_zk_keys.sh
# Generación de claves ZK (Powers of Tau + zkey)
# ============================================================================

set -e

echo "🌊 NOESIS — Generación de Claves ZK"
echo "====================================="

mkdir -p build

# 1. Compilar circuito
echo "📐 Compilando circuito Circom..."
circom circuits/noesis_coherence.circom \
    --r1cs --wasm --sym \
    -o build/

echo "  ✅ R1CS generado: build/noesis_coherence.r1cs"
echo "  ✅ WASM generado: build/noesis_coherence_js/"

# 2. Powers of Tau (ceremony pública)
echo "🔑 Iniciando Powers of Tau (potq12)..."
if [ ! -f "build/pot12_final.ptau" ]; then
    snarkjs powersoftau new bn128 12 build/pot12_0000.ptau -v
    snarkjs powersoftau contribute build/pot12_0000.ptau build/pot12_0001.ptau \
        --name="NOESIS-Contributor-1" -v -e="$(openssl rand -hex 32)"
    snarkjs powersoftau prepare phase2 build/pot12_0001.ptau build/pot12_final.ptau -v
    echo "  ✅ Powers of Tau completado"
else
    echo "  ℹ️  Powers of Tau ya existe — omitiendo"
fi

# 3. Fase 2: zkey
echo "🔐 Generando zkey (Groth16 Phase 2)..."
snarkjs groth16 setup \
    build/noesis_coherence.r1cs \
    build/pot12_final.ptau \
    build/noesis_coherence_0000.zkey

snarkjs zkey contribute \
    build/noesis_coherence_0000.zkey \
    build/noesis_coherence_final.zkey \
    --name="NOESIS-ZKey-Contributor" \
    -v -e="$(openssl rand -hex 32)"

# 4. Exportar verification key
snarkjs zkey export verificationkey \
    build/noesis_coherence_final.zkey \
    build/verification_key.json

echo "  ✅ zkey final: build/noesis_coherence_final.zkey"
echo "  ✅ Verification key: build/verification_key.json"

# 5. Exportar verificador Solidity
echo "⛓️ Exportando verificador Solidity..."
snarkjs zkey export solidityverifier \
    build/noesis_coherence_final.zkey \
    contracts/NOESISZKVerifier.sol

echo "  ✅ NOESISZKVerifier.sol generado"
echo "✅ Generación de claves ZK completada"
