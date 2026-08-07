# API Reference — ProofOfCoherenceConsensus (MVP)

## Contrato

`ProofOfCoherenceConsensus`

## Constantes

- `COHERENCE_THRESHOLD = 99999900` (escala 1e8)
- `MAX_VON_NEUMANN_ENTROPY = 10000` (escala 1e6)
- `MIN_STEP_COUNT = 100`

## Estructuras

```solidity
struct CoherenceState {
  uint64 coherencePsi;
  uint32 vonNeumannEntropy;
  uint32 harmonicDispersion;
  uint32 stepCount;
  uint16 reservedWaterMetricA;
  uint16 reservedWaterMetricB;
}

struct PoCBlock {
  uint64 blockId;
  uint64 timestamp;
  address validator;
  bytes32 nodeIdHash;
  bytes32 fieldHashPsi;
  bytes32 stateHash;
  CoherenceState state;
}
```

## Funciones principales

- `submitCoherenceBlock(...) returns (bytes32)` (permissionless)
- `submitCoherenceBlockWithZK(...) returns (bytes32)` (permissionless, gated by `zkValidationEnabled`)
- `getBlock(uint64 blockId) returns (PoCBlock)`
- `setZKVerifier(address)`
- `setZKValidationEnabled(bool)`

## Eventos

- `CoherenceBlockSubmitted(...)`
- `WavefunctionValidated(bytes32,bool)`
- `ZKVerifierUpdated(address,bool)`

## Nota de alcance

La verificación ZK está disponible como punto de extensión controlado; la integración completa de circuito Groth16/Circom se reserva para fase 2.
