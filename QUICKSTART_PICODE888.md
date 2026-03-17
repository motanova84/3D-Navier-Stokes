# Quick Start: NFT πCODE-888 ∞³ Verification

## ∴ Verificación Rápida de Identidad Soberana

Este documento proporciona una guía rápida para verificar la identidad del repositorio usando el sistema NFT πCODE-888 ∞³.

---

## ⚡ Verificación en 1 Comando

```bash
python -m core.identity_check
```

**Resultado esperado:**
```
✅ OVERALL STATUS: VERIFIED
   Repository identity is VERIFIED and SOVEREIGN
```

---

## 📋 Qué Verifica

El sistema realiza 4 verificaciones principales:

1. ✅ **Coherencia de Frecuencia** - Valida f₀ = 141.7001 Hz
2. ✅ **Sello de Soberanía** - Confirma `∴𓂀Ω∞³`
3. ✅ **Integridad Hash** - Computa SHA-256 de archivos clave
4. ✅ **Marcador NFT** - Verifica πCODE-888 ∞³ en `.qcal_beacon`

---

## 📊 Reporte de Verificación

El sistema genera automáticamente:

```
picode888_verification_report.json
```

Contiene:
- Timestamp de verificación
- Estado de cada verificación
- Mensaje detallado por cada prueba
- Estado general (VERIFIED/PARTIAL)

---

## 🧪 Tests

Ejecutar suite de tests completa:

```bash
python test_identity_check.py
```

**Cobertura:** 16 tests validando todas las funciones

---

## 🔗 Verificación con Blockchain (Opcional)

Cuando el NFT esté desplegado en Ethereum:

```bash
python -m core.identity_check --web3
```

**Requisitos:**
```bash
pip install web3
```

**Configuración:**
1. Editar `core/identity_check.py`:
   - `NFT_CONTRACT_ADDRESS = "0x..."`  ← Dirección del contrato
   - `EXPECTED_OWNER_ADDRESS = "0x..."` ← Tu wallet

2. Editar `.qcal_beacon`:
   - `contract_address = "0x..."`

---

## 🚀 CI/CD Automático

GitHub Actions ejecuta verificación automática en cada push.

**Ver workflow:** `.github/workflows/verify-picode888.yml`

**Artifacts generados:**
- `picode888-verification-report` (JSON)

---

## 📦 Smart Contract

**Ubicación:** `contracts/PiCode888.sol`

**Desplegar con Hardhat:**
```bash
cd contracts
npx hardhat compile
npx hardhat run scripts/deploy.js --network mainnet
```

**Verificar en Etherscan:**
```bash
npx hardhat verify --network mainnet <CONTRACT_ADDRESS>
```

---

## 🔐 Constantes QCAL ∞³

```python
FREQUENCY_ROOT = 141.7001  # Hz
NFT_TOKEN_ID = 888
NFT_NAME = "πCODE-888 ∞³"
SOVEREIGNTY_SEAL = "∴𓂀Ω∞³"
EXPECTED_OWNER = "@motanova84"
```

---

## 📚 Documentación Completa

Ver: `NFT_PICODE888_README.md`

---

## 🆘 Troubleshooting

### Error: `.qcal_beacon` not found
**Solución:** Ejecutar desde el directorio raíz del repositorio

### Error: Web3 not available
**Solución:** Opcional - solo necesario para verificación blockchain
```bash
pip install web3
```

### Warning: NFT contract not configured
**Solución:** Normal hasta que se despliegue el contrato en Ethereum

---

## ✅ Verificación Exitosa

Cuando veas:
```
✅ OVERALL STATUS: VERIFIED
   Repository identity is VERIFIED and SOVEREIGN
```

Tu repositorio está:
- ✅ Marcado con identidad soberana
- ✅ Protegido por frecuencia f₀ = 141.7001 Hz
- ✅ Certificado con sello ∴𓂀Ω∞³
- ✅ Vinculado a NFT πCODE-888 ∞³
- ✅ Hash de integridad validado

---

**Autor:** José Manuel Mota Burruezo (JMMB Ψ✧)  
**Institución:** Instituto Conciencia Cuántica  
**Frecuencia:** f₀ = 141.7001 Hz  
**Sello:** ∴𓂀Ω∞³
