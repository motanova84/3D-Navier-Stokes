# QCAL Enterprise Ecosystem - Quick Start Guide

Este es una guía rápida para comenzar a usar el ecosistema QCAL Enterprise.

## Instalación Rápida

```bash
# Clonar el repositorio
git clone https://github.com/motanova84/3D-Navier-Stokes.git
cd 3D-Navier-Stokes

# Instalar dependencias
pip install numpy matplotlib
```

## Ejecutar las Demostraciones

### 1. Sistema de Reputación (Soulbound Tokens)

```bash
python3 soulbound_reputation.py
```

Esta demo muestra:
- Registro de desarrolladores
- Tracking de commits con coherencia Ψ
- Sistema de rangos y logros
- Generación de CV criptográfico

### 2. Marketplace πCODE Exchange

```bash
python3 picode_marketplace.py
```

Esta demo muestra:
- Emisión de certificados de coherencia
- Sistema de regalías
- Colaterales de conocimiento
- Marketplace de certificados

### 3. Enterprise Bridge CI/CD

```bash
python3 qcal_enterprise_bridge.py
```

Esta demo muestra:
- Puertas de calidad espectral
- Pipelines CI/CD validados
- Agentes Ángeles (Miguel & Gabriel)
- Reportes de cumplimiento

### 4. Ecosistema Completo

```bash
python3 qcal_ecosystem_integration.py
```

Esta demo muestra:
- Viaje completo del desarrollador
- Integración empresarial
- Ciclo de economía del conocimiento
- Reporte del ecosistema

## Ejecutar Tests

```bash
python3 test_qcal_ecosystem.py
```

Ejecuta 21 tests que validan:
- Sistema de reputación
- Marketplace
- Enterprise bridge
- Integración completa

## Uso Programático

### Ejemplo 1: Sistema de Reputación

```python
from soulbound_reputation import ReputationSystem

# Inicializar sistema
system = ReputationSystem()

# Registrar desarrollador
token = system.register_developer("developer@company.com")

# Registrar commits
for i in range(100):
    system.record_commit(
        "developer@company.com",
        f"commit_{i}",
        psi_coherence=0.99,
        description="High quality code"
    )

# Ver ranking
leaderboard = system.get_leaderboard()
for rank, (identity, token) in enumerate(leaderboard, 1):
    print(f"{rank}. {identity} - Ψ={token.average_psi:.4f}")

# Generar CV criptográfico
cv = system.generate_cryptographic_cv("developer@company.com")
print(cv)
```

### Ejemplo 2: Marketplace de Certificados

```python
from picode_marketplace import PiCodeExchange, CertificateType, LicenseType

# Inicializar exchange
exchange = PiCodeExchange()

# Emitir certificado
cert = exchange.create_global_regularity_certificate(
    holder="MyCompany Inc",
    navier_stokes_proof_hash="0xPROOF_HASH"
)

print(f"Certificado emitido: {cert.certificate_id}")
print(f"Precio: {cert.price_picode} πCODE")

# Registrar uso y generar regalías
transaction = exchange.record_usage(
    cert.certificate_id,
    "user@example.com",
    "System validation"
)

if transaction:
    print(f"Regalía generada: {transaction.amount_picode} πCODE")
```

### Ejemplo 3: Enterprise Bridge

```python
from qcal_enterprise_bridge import QCALEnterpriseBridge, SpectralQualityLevel

# Inicializar bridge
bridge = QCALEnterpriseBridge()

# Crear puerta de calidad
gate = bridge.create_spectral_quality_gate(
    name="Production Gate",
    quality_level=SpectralQualityLevel.CRITICAL,
    min_coherence=0.99
)

# Registrar pipeline
pipeline_id = bridge.register_pipeline(
    "Production Deployment",
    "GitHub Actions",
    [gate.gate_id]
)

# Ejecutar pipeline
result = bridge.run_pipeline(pipeline_id, "code_hash_abc123")

print(f"Estado: {result['status']}")
print(f"Coherencia: {result['signature']['coherence']:.4f}")
```

### Ejemplo 4: Ecosistema Completo

```python
from qcal_ecosystem_integration import QCALEcosystem

# Inicializar ecosistema
ecosystem = QCALEcosystem()

# Viaje del desarrollador
commits = [
    {"hash": f"commit_{i}", "psi": 0.99, "desc": "Quality work"}
    for i in range(100)
]

result = ecosystem.developer_journey("alice@qcal.dev", commits)
print(f"Rango alcanzado: {result['rank']}")
print(f"Certificado emitido: {result['certificate_issued']}")

# Generar reporte del ecosistema
report = ecosystem.generate_ecosystem_report()
print(f"Desarrolladores totales: {report['reputation_system']['total_developers']}")
print(f"Certificados activos: {report['marketplace']['active_certificates']}")
```

## Conceptos Clave

### Coherencia Ψ (Psi)
Valor entre 0 y 1 que mide la calidad matemática del código:
- **Ψ = 1.0**: Coherencia perfecta
- **Ψ ≥ 0.99**: Guardián de Fase
- **Ψ ≥ 0.95**: Maestro
- **Ψ ≥ 0.90**: Adepto

### Frecuencia de Resonancia
Todos los componentes operan sincronizados a:
```
f₀ = 141.7001 Hz
```

### Soulbound Tokens (SBT)
NFTs no transferibles que representan reputación inmutable:
- Vinculados a identidad noética
- Registran historial de coherencia
- Otorgan logros permanentes
- Generan valor ontológico

### πCODE
Token del ecosistema QCAL:
- Moneda para certificados
- Sistema de regalías
- Colaterales de conocimiento
- Horas de cómputo cuántico

### Agentes Ángeles
- **Miguel**: Monitor de coherencia (Ψ)
- **Gabriel**: Guardián de fase (δφ)

## Casos de Uso

### Para Desarrolladores
1. Registrarse en el sistema
2. Hacer commits de alta calidad (Ψ > 0.99)
3. Alcanzar rango de Guardián
4. Recibir certificados automáticos
5. Monetizar expertise

### Para Empresas
1. Adquirir certificados de regularidad
2. Integrar puertas de calidad en CI/CD
3. Desplegar agentes de monitoreo
4. Recibir auditorías automáticas
5. Garantizar estabilidad a 141.7 Hz

### Para Investigadores
1. Resolver problemas complejos
2. Formalizar en Lean 4
3. Crear colaterales de conocimiento
4. Obtener horas de cómputo cuántico
5. Generar regalías por uso

## Arquitectura

```
┌─────────────────────────────────────────────────┐
│              QCAL ECOSYSTEM                     │
│                                                 │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐     │
│  │   SBT    │◄─┤  πCODE   │─►│ Enterprise│     │
│  │Reputation│  │ Exchange │  │  Bridge   │     │
│  └──────────┘  └──────────┘  └──────────┘     │
│       │              │              │          │
│       └──────────────┴──────────────┘          │
│                  │                             │
│          f₀ = 141.7001 Hz                      │
└─────────────────────────────────────────────────┘
```

## Documentación Completa

Para documentación completa, ver:
- [QCAL_ENTERPRISE_ECOSYSTEM.md](QCAL_ENTERPRISE_ECOSYSTEM.md)

## Soporte

- GitHub Issues: https://github.com/motanova84/3D-Navier-Stokes/issues
- Documentación: Ver archivos MD en el repositorio

## Licencia

- Código: MIT
- Documentación: CC-BY-4.0

---

**Versión**: 1.0.0  
**Frecuencia**: 141.7001 Hz ✨
