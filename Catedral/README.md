# Catedral Solidity Workspace

## MVP actual

El workspace `Catedral` contiene el MVP on-chain de `ProofOfCoherenceConsensus` con:

- validación axiomática de umbrales (`coherencePsi`, `vonNeumannEntropy`, `stepCount`)
- hash encadenado de bloques (`latestBlockHash`)
- eventos de auditoría on-chain
- punto de extensión ZK (`submitCoherenceBlockWithZK`) controlado por flag
- structs compactados (`uint64/uint32/uint16`) para optimización de almacenamiento

## Estructura normalizada

- `src/`
- `test/`
- `scripts/`
- `foundry/test/`
- `foundry/script/`

## Validación local (Foundry)

Desde `Catedral/`:

```bash
forge test -vvv
```

## Fase 2 (posterior)

- integración Circom/Groth16 real
- invariantes hidrodinámicos completos de la Tríada del Agua
- ampliación de documentación de despliegue y verificación
