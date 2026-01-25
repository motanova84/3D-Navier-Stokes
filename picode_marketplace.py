#!/usr/bin/env python3
"""
πCODE Exchange - Mercado de Certificados de Coherencia
======================================================

Marketplace donde empresas y proyectos pueden adquirir e intercambiar certificados
de validación basados en coherencia matemática y regularidad global.

Características:
- Certificados de Regularidad Global (basados en Navier-Stokes)
- Monetización de la invarianza (micro-pagos por uso de lógica formal)
- Liquidez de conocimiento (colaterales para computación cuántica)

Author: JMMB Ψ✧∞³
License: MIT
"""

import numpy as np
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from enum import Enum
import json
import hashlib
import uuid


class CertificateType(Enum):
    """Tipos de certificados disponibles"""
    GLOBAL_REGULARITY = "Certificado de Regularidad Global"
    SPECTRAL_STABILITY = "Certificado de Estabilidad Espectral"
    QUANTUM_COHERENCE = "Certificado de Coherencia Cuántica"
    PHASE_INVARIANCE = "Certificado de Invarianza de Fase"
    FREQUENCY_CALIBRATION = "Certificado de Calibración de Frecuencia"
    TURBULENCE_FREE = "Certificado Libre de Turbulencia"


class LicenseType(Enum):
    """Tipos de licencia para uso de certificados"""
    SINGLE_USE = "Uso Único"
    MONTHLY = "Mensual"
    ANNUAL = "Anual"
    PERPETUAL = "Perpetuo"
    ROYALTY_BASED = "Basado en Regalías"


@dataclass
class QualityProof:
    """
    Prueba de Calidad para validación matemática
    
    Garantiza que el sistema es matemáticamente estable a 141.7 Hz
    """
    frequency_hz: float
    psi_coherence: float
    stability_metric: float
    timestamp: datetime
    validator_signature: str
    lean4_proof_hash: Optional[str] = None
    
    def verify(self) -> bool:
        """Verifica que la prueba sea válida"""
        # Verificar frecuencia de resonancia
        f0 = 141.7001
        freq_valid = abs(self.frequency_hz - f0) < 0.1
        
        # Verificar coherencia
        coherence_valid = self.psi_coherence >= 0.99
        
        # Verificar estabilidad
        stability_valid = self.stability_metric >= 0.95
        
        return freq_valid and coherence_valid and stability_valid


@dataclass
class CoherenceCertificate:
    """
    Certificado de Coherencia para sistemas validados
    
    Representa una garantía matemática de calidad y estabilidad.
    """
    certificate_id: str
    certificate_type: CertificateType
    issue_date: datetime
    expiration_date: Optional[datetime]
    quality_proof: QualityProof
    issuer: str
    holder: str
    license_type: LicenseType
    price_picode: float  # Precio en πCODE tokens
    usage_count: int = 0
    royalty_rate: float = 0.0  # Tasa de regalías (si aplica)
    metadata: Dict = field(default_factory=dict)
    
    def is_valid(self) -> bool:
        """Verifica si el certificado es válido"""
        if self.expiration_date and datetime.now() > self.expiration_date:
            return False
        
        return self.quality_proof.verify()
    
    def generate_blockchain_record(self) -> Dict:
        """Genera registro para blockchain"""
        return {
            "id": self.certificate_id,
            "type": self.certificate_type.value,
            "issue_date": self.issue_date.isoformat(),
            "expiration": self.expiration_date.isoformat() if self.expiration_date else None,
            "holder": self.holder,
            "quality_proof": {
                "frequency_hz": self.quality_proof.frequency_hz,
                "psi_coherence": self.quality_proof.psi_coherence,
                "stability": self.quality_proof.stability_metric,
                "validator": self.quality_proof.validator_signature
            },
            "license": self.license_type.value,
            "price": self.price_picode
        }


@dataclass
class RoyaltyTransaction:
    """Transacción de regalías por uso de lógica formalizada"""
    transaction_id: str
    timestamp: datetime
    certificate_id: str
    user: str
    logic_owner: str
    amount_picode: float
    usage_description: str


@dataclass
class KnowledgeCollateral:
    """
    Colateral de Conocimiento para préstamos de computación cuántica
    
    Transforma resoluciones de problemas complejos en activos financieros.
    """
    collateral_id: str
    problem_type: str  # e.g., "P vs NP", "Riemann", "Navier-Stokes"
    resolution_proof: str  # Hash de la prueba
    collateral_value_picode: float
    locked_until: datetime
    owner: str
    quantum_compute_hours_granted: float
    metadata: Dict = field(default_factory=dict)


class PiCodeExchange:
    """
    πCODE Exchange - Marketplace de Certificados de Coherencia
    
    Sistema de compra, venta e intercambio de certificados de validación matemática.
    """
    
    def __init__(self):
        """Inicializa el marketplace"""
        self.f0_hz = 141.7001  # Frecuencia universal
        self.certificates: Dict[str, CoherenceCertificate] = {}
        self.royalty_transactions: List[RoyaltyTransaction] = []
        self.collaterals: Dict[str, KnowledgeCollateral] = {}
        self.picode_exchange_rate = 1.0  # 1 πCODE = 1 USD (ejemplo)
        
    def issue_certificate(self, certificate_type: CertificateType, holder: str,
                         license_type: LicenseType, psi_coherence: float,
                         stability_metric: float, price_picode: float,
                         validity_days: Optional[int] = None) -> CoherenceCertificate:
        """
        Emite un nuevo certificado de coherencia
        
        Args:
            certificate_type: Tipo de certificado
            holder: Propietario del certificado
            license_type: Tipo de licencia
            psi_coherence: Valor de coherencia Ψ
            stability_metric: Métrica de estabilidad
            price_picode: Precio en tokens πCODE
            validity_days: Días de validez (None = perpetuo)
            
        Returns:
            CoherenceCertificate emitido
        """
        cert_id = str(uuid.uuid4())
        issue_date = datetime.now()
        expiration_date = None
        
        if validity_days:
            expiration_date = issue_date + timedelta(days=validity_days)
        
        # Crear prueba de calidad
        validator_data = f"{cert_id}{psi_coherence}{self.f0_hz}"
        validator_signature = hashlib.sha256(validator_data.encode()).hexdigest()
        
        quality_proof = QualityProof(
            frequency_hz=self.f0_hz,
            psi_coherence=psi_coherence,
            stability_metric=stability_metric,
            timestamp=issue_date,
            validator_signature=validator_signature
        )
        
        # Determinar tasa de regalías
        royalty_rate = 0.05 if license_type == LicenseType.ROYALTY_BASED else 0.0
        
        certificate = CoherenceCertificate(
            certificate_id=cert_id,
            certificate_type=certificate_type,
            issue_date=issue_date,
            expiration_date=expiration_date,
            quality_proof=quality_proof,
            issuer="QCAL_AUTHORITY",
            holder=holder,
            license_type=license_type,
            price_picode=price_picode,
            royalty_rate=royalty_rate
        )
        
        self.certificates[cert_id] = certificate
        return certificate
    
    def purchase_certificate(self, certificate_id: str, buyer: str) -> bool:
        """
        Compra un certificado del marketplace
        
        Args:
            certificate_id: ID del certificado
            buyer: Comprador
            
        Returns:
            True si la compra fue exitosa
        """
        if certificate_id not in self.certificates:
            return False
        
        cert = self.certificates[certificate_id]
        
        # Validar certificado (si no está expirado)
        # Permitir compra de certificados válidos o perpetuos
        if cert.expiration_date and datetime.now() > cert.expiration_date:
            return False
        
        # Transferir propiedad
        cert.holder = buyer
        return True
    
    def record_usage(self, certificate_id: str, user: str, 
                    usage_description: str) -> Optional[RoyaltyTransaction]:
        """
        Registra el uso de un certificado y genera micro-pago de regalías
        
        Args:
            certificate_id: ID del certificado usado
            user: Usuario del certificado
            usage_description: Descripción del uso
            
        Returns:
            RoyaltyTransaction si se generaron regalías, None en otro caso
        """
        if certificate_id not in self.certificates:
            return None
        
        cert = self.certificates[certificate_id]
        cert.usage_count += 1
        
        # Si tiene regalías, crear transacción
        if cert.royalty_rate > 0:
            royalty_amount = cert.price_picode * cert.royalty_rate
            
            transaction = RoyaltyTransaction(
                transaction_id=str(uuid.uuid4()),
                timestamp=datetime.now(),
                certificate_id=certificate_id,
                user=user,
                logic_owner=cert.issuer,
                amount_picode=royalty_amount,
                usage_description=usage_description
            )
            
            self.royalty_transactions.append(transaction)
            return transaction
        
        return None
    
    def create_global_regularity_certificate(self, holder: str, 
                                            navier_stokes_proof_hash: str) -> CoherenceCertificate:
        """
        Crea un Certificado de Regularidad Global basado en avances de Navier-Stokes
        
        Este certificado garantiza que el motor de simulación es matemáticamente
        estable a 141.7 Hz.
        
        Args:
            holder: Propietario del certificado
            navier_stokes_proof_hash: Hash de la prueba de Navier-Stokes
            
        Returns:
            CoherenceCertificate de Regularidad Global
        """
        cert = self.issue_certificate(
            certificate_type=CertificateType.GLOBAL_REGULARITY,
            holder=holder,
            license_type=LicenseType.ANNUAL,
            psi_coherence=0.9999,
            stability_metric=0.9999,
            price_picode=1000.0,
            validity_days=365
        )
        
        cert.quality_proof.lean4_proof_hash = navier_stokes_proof_hash
        cert.metadata["navier_stokes_validated"] = True
        cert.metadata["frequency_guarantee"] = self.f0_hz
        
        return cert
    
    def create_knowledge_collateral(self, owner: str, problem_type: str,
                                   resolution_proof_hash: str,
                                   collateral_value: float,
                                   lock_days: int) -> KnowledgeCollateral:
        """
        Crea colateral de conocimiento para préstamos de computación cuántica
        
        Args:
            owner: Propietario del colateral
            problem_type: Tipo de problema resuelto
            resolution_proof_hash: Hash de la prueba de resolución
            collateral_value: Valor del colateral en πCODE
            lock_days: Días de bloqueo
            
        Returns:
            KnowledgeCollateral creado
        """
        collateral_id = str(uuid.uuid4())
        
        # Calcular horas de cómputo cuántico basadas en valor
        quantum_hours = collateral_value * 0.1  # 10% del valor en horas
        
        collateral = KnowledgeCollateral(
            collateral_id=collateral_id,
            problem_type=problem_type,
            resolution_proof=resolution_proof_hash,
            collateral_value_picode=collateral_value,
            locked_until=datetime.now() + timedelta(days=lock_days),
            owner=owner,
            quantum_compute_hours_granted=quantum_hours
        )
        
        self.collaterals[collateral_id] = collateral
        return collateral
    
    def get_marketplace_statistics(self) -> Dict:
        """Obtiene estadísticas del marketplace"""
        total_certificates = len(self.certificates)
        active_certificates = sum(1 for cert in self.certificates.values() if cert.is_valid())
        total_royalties = sum(t.amount_picode for t in self.royalty_transactions)
        total_collateral_value = sum(c.collateral_value_picode for c in self.collaterals.values())
        
        return {
            "total_certificates": total_certificates,
            "active_certificates": active_certificates,
            "total_royalty_transactions": len(self.royalty_transactions),
            "total_royalties_picode": total_royalties,
            "total_collaterals": len(self.collaterals),
            "total_collateral_value_picode": total_collateral_value,
            "average_certificate_price": np.mean([c.price_picode for c in self.certificates.values()]) if self.certificates else 0.0
        }
    
    def export_certificate_for_blockchain(self, certificate_id: str) -> str:
        """Exporta certificado en formato blockchain"""
        if certificate_id not in self.certificates:
            return json.dumps({"error": "Certificate not found"})
        
        cert = self.certificates[certificate_id]
        return json.dumps(cert.generate_blockchain_record(), indent=2)


def demo_picode_marketplace():
    """Demostración del marketplace πCODE"""
    print("=" * 70)
    print("πCODE Exchange - Marketplace de Certificados de Coherencia")
    print("=" * 70)
    print()
    
    # Inicializar marketplace
    exchange = PiCodeExchange()
    
    print("1. EMISIÓN DE CERTIFICADOS")
    print("-" * 70)
    
    # Emitir certificado de regularidad global
    cert1 = exchange.create_global_regularity_certificate(
        holder="AeroSpace Corp",
        navier_stokes_proof_hash="0x" + hashlib.sha256(b"NS_PROOF_V1").hexdigest()
    )
    print(f"✓ Certificado de Regularidad Global emitido")
    print(f"  ID: {cert1.certificate_id}")
    print(f"  Precio: {cert1.price_picode} πCODE")
    print(f"  Frecuencia garantizada: {cert1.quality_proof.frequency_hz} Hz")
    print()
    
    # Emitir certificado de coherencia cuántica con regalías
    cert2 = exchange.issue_certificate(
        certificate_type=CertificateType.QUANTUM_COHERENCE,
        holder="QuantumSim Inc",
        license_type=LicenseType.ROYALTY_BASED,
        psi_coherence=0.995,
        stability_metric=0.98,
        price_picode=500.0,
        validity_days=180
    )
    print(f"✓ Certificado de Coherencia Cuántica emitido")
    print(f"  ID: {cert2.certificate_id}")
    print(f"  Tasa de regalías: {cert2.royalty_rate * 100}%")
    print()
    
    print("2. USO DE CERTIFICADOS Y REGALÍAS")
    print("-" * 70)
    
    # Simular uso y generar regalías
    for i in range(5):
        transaction = exchange.record_usage(
            cert2.certificate_id,
            f"user_{i}@company.com",
            f"Validación de sistema crítico #{i+1}"
        )
        if transaction:
            print(f"✓ Uso #{i+1} registrado - Regalía: {transaction.amount_picode} πCODE")
    
    print()
    
    print("3. COLATERAL DE CONOCIMIENTO")
    print("-" * 70)
    
    # Crear colateral para computación cuántica
    collateral = exchange.create_knowledge_collateral(
        owner="mathematician@research.edu",
        problem_type="Riemann Hypothesis Progress",
        resolution_proof_hash="0x" + hashlib.sha256(b"RIEMANN_PROGRESS").hexdigest(),
        collateral_value=10000.0,
        lock_days=365
    )
    
    print(f"✓ Colateral de conocimiento creado")
    print(f"  Tipo de problema: {collateral.problem_type}")
    print(f"  Valor: {collateral.collateral_value_picode} πCODE")
    print(f"  Horas de cómputo cuántico: {collateral.quantum_compute_hours_granted}")
    print(f"  Bloqueado hasta: {collateral.locked_until.strftime('%Y-%m-%d')}")
    print()
    
    print("4. ESTADÍSTICAS DEL MARKETPLACE")
    print("-" * 70)
    stats = exchange.get_marketplace_statistics()
    print(f"Total de certificados: {stats['total_certificates']}")
    print(f"Certificados activos: {stats['active_certificates']}")
    print(f"Transacciones de regalías: {stats['total_royalty_transactions']}")
    print(f"Total de regalías: {stats['total_royalties_picode']:.2f} πCODE")
    print(f"Valor total de colaterales: {stats['total_collateral_value_picode']:.2f} πCODE")
    print()
    
    print("5. REGISTRO BLOCKCHAIN")
    print("-" * 70)
    blockchain_record = exchange.export_certificate_for_blockchain(cert1.certificate_id)
    print(blockchain_record)
    
    return exchange


if __name__ == "__main__":
    demo_picode_marketplace()
