#!/usr/bin/env python3
"""
QCAL Soulbound Token (SBT) Reputation System
=============================================

Sistema de reputación basado en NFTs no transferibles (Soulbound Tokens)
vinculados a la identidad noética de desarrolladores y nodos en el ecosistema QCAL.

La reputación se calcula mediante el historial de Ψ (coherencia) en commits.
Los logros se graban en blockchain como currículum criptográfico inmutable.

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


class RankLevel(Enum):
    """Niveles de rango en el sistema de reputación"""
    NOVICE = "Novato"
    APPRENTICE = "Aprendiz"
    ADEPT = "Adepto"
    GUARDIAN = "Guardián de Fase"
    MASTER = "Maestro de Coherencia"
    ARCHITECT = "Arquitecto Noético"


class AchievementType(Enum):
    """Tipos de logros desbloqueables"""
    SPECTRAL_ANOMALY_RESOLVED = "Resolución de Anomalía Espectral"
    PERFECT_COHERENCE_STREAK = "Racha de Coherencia Perfecta"
    PHASE_GUARDIAN_UNLOCKED = "Guardián de Fase Desbloqueado"
    FREQUENCY_CALIBRATION = "Calibración de Frecuencia"
    INVARIANCE_CONTRIBUTION = "Contribución de Invarianza"
    QUANTUM_STABILITY = "Estabilidad Cuántica"
    GLOBAL_REGULARITY = "Regularidad Global"


@dataclass
class CommitRecord:
    """Registro de un commit con su coherencia Ψ"""
    commit_hash: str
    timestamp: datetime
    psi_coherence: float  # Valor de Ψ entre 0 y 1
    frequency_hz: float  # Frecuencia de resonancia
    author: str
    description: str


@dataclass
class Achievement:
    """Logro inmutable en blockchain"""
    achievement_type: AchievementType
    timestamp: datetime
    psi_value: float
    proof_hash: str  # Hash de prueba criptográfica
    description: str
    metadata: Dict = field(default_factory=dict)
    
    def to_blockchain_record(self) -> Dict:
        """Convierte el logro a formato de registro blockchain"""
        return {
            "type": self.achievement_type.value,
            "timestamp": self.timestamp.isoformat(),
            "psi": self.psi_value,
            "proof": self.proof_hash,
            "description": self.description,
            "metadata": self.metadata
        }


@dataclass
class SoulboundToken:
    """
    Token Soulbound (SBT) no transferible vinculado a identidad noética
    
    Representa la reputación acumulada de un desarrollador o nodo.
    """
    noetic_identity: str  # Identidad noética única
    creation_date: datetime
    rank: RankLevel
    total_commits: int
    average_psi: float
    current_streak_days: int
    achievements: List[Achievement] = field(default_factory=list)
    commit_history: List[CommitRecord] = field(default_factory=list)
    ontological_value: float = 0.0  # Valor ontológico del token
    
    def calculate_ontological_value(self, network_validators: List['SoulboundToken']) -> float:
        """
        Calcula el valor ontológico basado en la reputación de validadores
        
        Efecto de Red: Cuanto mayor es la reputación de los nodos que validan,
        mayor es el valor ontológico del certificado.
        """
        if not network_validators:
            return self.average_psi
        
        validator_weights = [v.average_psi for v in network_validators]
        avg_validator_reputation = np.mean(validator_weights)
        
        # Valor ontológico = coherencia propia * promedio de validadores
        self.ontological_value = self.average_psi * avg_validator_reputation
        return self.ontological_value
    
    def to_dict(self) -> Dict:
        """Serializa el SBT a diccionario"""
        return {
            "noetic_identity": self.noetic_identity,
            "creation_date": self.creation_date.isoformat(),
            "rank": self.rank.value,
            "total_commits": self.total_commits,
            "average_psi": self.average_psi,
            "current_streak_days": self.current_streak_days,
            "achievements": [a.to_blockchain_record() for a in self.achievements],
            "ontological_value": self.ontological_value
        }


class ReputationSystem:
    """
    Sistema de Reputación QCAL basado en Soulbound Tokens
    
    Rastrea coherencia Ψ en commits y otorga rangos y logros inmutables.
    """
    
    def __init__(self):
        """Inicializa el sistema de reputación"""
        self.f0_hz = 141.7001  # Frecuencia universal de resonancia
        self.guardian_threshold = 0.99  # Ψ mínimo para Guardián de Fase
        self.guardian_days = 88  # Días requeridos para Guardián
        self.tokens: Dict[str, SoulboundToken] = {}
    
    def register_developer(self, noetic_identity: str) -> SoulboundToken:
        """
        Registra un nuevo desarrollador en el sistema
        
        Args:
            noetic_identity: Identificador único noético del desarrollador
            
        Returns:
            SoulboundToken creado
        """
        if noetic_identity in self.tokens:
            return self.tokens[noetic_identity]
        
        token = SoulboundToken(
            noetic_identity=noetic_identity,
            creation_date=datetime.now(),
            rank=RankLevel.NOVICE,
            total_commits=0,
            average_psi=0.0,
            current_streak_days=0
        )
        
        self.tokens[noetic_identity] = token
        return token
    
    def record_commit(self, noetic_identity: str, commit_hash: str, 
                      psi_coherence: float, description: str = "") -> CommitRecord:
        """
        Registra un nuevo commit con su coherencia Ψ
        
        Args:
            noetic_identity: Identidad del autor
            commit_hash: Hash del commit
            psi_coherence: Valor de coherencia Ψ (0-1)
            description: Descripción del commit
            
        Returns:
            CommitRecord creado
        """
        if noetic_identity not in self.tokens:
            self.register_developer(noetic_identity)
        
        token = self.tokens[noetic_identity]
        
        # Calcular frecuencia basada en coherencia
        frequency_hz = self.f0_hz * psi_coherence
        
        commit = CommitRecord(
            commit_hash=commit_hash,
            timestamp=datetime.now(),
            psi_coherence=psi_coherence,
            frequency_hz=frequency_hz,
            author=noetic_identity,
            description=description
        )
        
        token.commit_history.append(commit)
        token.total_commits += 1
        
        # Actualizar promedio de Ψ
        self._update_average_psi(token)
        
        # Verificar logros
        self._check_achievements(token, commit)
        
        # Actualizar rango
        self._update_rank(token)
        
        return commit
    
    def _update_average_psi(self, token: SoulboundToken):
        """Actualiza el promedio de Ψ del token"""
        if not token.commit_history:
            token.average_psi = 0.0
            return
        
        psi_values = [c.psi_coherence for c in token.commit_history]
        token.average_psi = np.mean(psi_values)
    
    def _update_rank(self, token: SoulboundToken):
        """Actualiza el rango basado en métricas"""
        psi = token.average_psi
        commits = token.total_commits
        
        if psi >= 0.989 and token.current_streak_days >= self.guardian_days:
            token.rank = RankLevel.GUARDIAN
        elif psi >= 0.95 and commits >= 100:
            token.rank = RankLevel.MASTER
        elif psi >= 0.89 and commits >= 50:
            token.rank = RankLevel.ADEPT
        elif psi >= 0.80 and commits >= 20:
            token.rank = RankLevel.APPRENTICE
        else:
            token.rank = RankLevel.NOVICE
    
    def _check_achievements(self, token: SoulboundToken, commit: CommitRecord):
        """Verifica y otorga logros basados en el commit"""
        # Verificar racha de coherencia perfecta
        if commit.psi_coherence >= 0.999:
            self._calculate_streak(token)
            
            if token.current_streak_days >= 88:
                self._grant_achievement(
                    token,
                    AchievementType.PHASE_GUARDIAN_UNLOCKED,
                    commit.psi_coherence,
                    f"88 días consecutivos con Ψ > 0.99"
                )
        
        # Verificar resolución de anomalía espectral
        if abs(commit.frequency_hz - self.f0_hz) < 0.1:
            self._grant_achievement(
                token,
                AchievementType.SPECTRAL_ANOMALY_RESOLVED,
                commit.psi_coherence,
                f"Frecuencia resonante: {commit.frequency_hz:.4f} Hz"
            )
        
        # Verificar estabilidad cuántica
        if commit.psi_coherence == 1.0:
            self._grant_achievement(
                token,
                AchievementType.QUANTUM_STABILITY,
                commit.psi_coherence,
                "Coherencia perfecta alcanzada"
            )
    
    def _calculate_streak(self, token: SoulboundToken):
        """Calcula la racha actual de días con Ψ > 0.99"""
        if not token.commit_history:
            token.current_streak_days = 0
            return
        
        # Ordenar commits por fecha
        sorted_commits = sorted(token.commit_history, key=lambda c: c.timestamp, reverse=True)
        
        streak_days = 0
        last_date = None
        
        for commit in sorted_commits:
            if commit.psi_coherence < self.guardian_threshold:
                break
            
            commit_date = commit.timestamp.date()
            
            if last_date is None:
                streak_days = 1
                last_date = commit_date
            elif (last_date - commit_date).days == 1:
                streak_days += 1
                last_date = commit_date
            elif last_date == commit_date:
                continue  # Mismo día
            else:
                break  # Racha rota
        
        token.current_streak_days = streak_days
    
    def _grant_achievement(self, token: SoulboundToken, achievement_type: AchievementType,
                          psi_value: float, description: str):
        """Otorga un logro al token si no lo tiene ya"""
        # Verificar si ya tiene este logro
        for achievement in token.achievements:
            if achievement.achievement_type == achievement_type:
                return
        
        # Generar hash de prueba
        proof_data = f"{token.noetic_identity}{achievement_type.value}{datetime.now().isoformat()}"
        proof_hash = hashlib.sha256(proof_data.encode()).hexdigest()
        
        achievement = Achievement(
            achievement_type=achievement_type,
            timestamp=datetime.now(),
            psi_value=psi_value,
            proof_hash=proof_hash,
            description=description
        )
        
        token.achievements.append(achievement)
    
    def get_leaderboard(self, top_n: int = 10) -> List[Tuple[str, SoulboundToken]]:
        """
        Obtiene el ranking de los mejores desarrolladores
        
        Args:
            top_n: Número de desarrolladores a retornar
            
        Returns:
            Lista de tuplas (identidad, token) ordenadas por reputación
        """
        sorted_tokens = sorted(
            self.tokens.items(),
            key=lambda x: (x[1].average_psi, x[1].total_commits),
            reverse=True
        )
        
        return sorted_tokens[:top_n]
    
    def export_blockchain_records(self, noetic_identity: str) -> str:
        """
        Exporta los registros del token en formato blockchain
        
        Args:
            noetic_identity: Identidad del desarrollador
            
        Returns:
            JSON con registros para blockchain
        """
        if noetic_identity not in self.tokens:
            return json.dumps({"error": "Token not found"})
        
        token = self.tokens[noetic_identity]
        return json.dumps(token.to_dict(), indent=2)
    
    def generate_cryptographic_cv(self, noetic_identity: str) -> Dict:
        """
        Genera un currículum criptográfico inmutable
        
        Args:
            noetic_identity: Identidad del desarrollador
            
        Returns:
            Diccionario con CV criptográfico
        """
        if noetic_identity not in self.tokens:
            return {"error": "Token not found"}
        
        token = self.tokens[noetic_identity]
        
        # Generar hash del CV completo
        cv_data = json.dumps(token.to_dict(), sort_keys=True)
        cv_hash = hashlib.sha256(cv_data.encode()).hexdigest()
        
        return {
            "noetic_identity": noetic_identity,
            "cv_hash": cv_hash,
            "rank": token.rank.value,
            "average_coherence": token.average_psi,
            "total_commits": token.total_commits,
            "achievements": [a.achievement_type.value for a in token.achievements],
            "ontological_value": token.ontological_value,
            "verified_at": datetime.now().isoformat(),
            "immutable_proof": cv_hash[:16]  # Primeros 16 caracteres como prueba
        }


def demo_reputation_system():
    """Demostración del sistema de reputación"""
    print("=" * 70)
    print("QCAL Soulbound Token (SBT) Reputation System")
    print("Sistema de Reputación basado en NFTs no transferibles")
    print("=" * 70)
    print()
    
    # Inicializar sistema
    system = ReputationSystem()
    
    # Registrar desarrolladores
    dev1 = system.register_developer("alice@noetic.qcal")
    dev2 = system.register_developer("bob@noetic.qcal")
    
    print(f"✓ Desarrolladores registrados: {len(system.tokens)}")
    print()
    
    # Simular commits con diferentes coherencias
    print("Registrando commits...")
    for i in range(100):
        # Alice: alta coherencia consistente
        psi_alice = 0.99 + np.random.normal(0, 0.005)
        psi_alice = np.clip(psi_alice, 0.98, 1.0)
        system.record_commit("alice@noetic.qcal", f"commit_a_{i}", psi_alice, "High quality commit")
        
        # Bob: coherencia variable
        psi_bob = 0.85 + np.random.normal(0, 0.1)
        psi_bob = np.clip(psi_bob, 0.7, 0.95)
        system.record_commit("bob@noetic.qcal", f"commit_b_{i}", psi_bob, "Variable quality")
    
    print(f"✓ Commits registrados: {dev1.total_commits + dev2.total_commits}")
    print()
    
    # Mostrar estadísticas
    print("ESTADÍSTICAS DE DESARROLLADORES")
    print("-" * 70)
    for identity, token in system.tokens.items():
        print(f"\n{identity}")
        print(f"  Rango: {token.rank.value}")
        print(f"  Coherencia promedio Ψ: {token.average_psi:.6f}")
        print(f"  Total de commits: {token.total_commits}")
        print(f"  Racha actual: {token.current_streak_days} días")
        print(f"  Logros: {len(token.achievements)}")
        for achievement in token.achievements[:3]:
            print(f"    • {achievement.achievement_type.value}")
    
    print()
    print("=" * 70)
    print("LEADERBOARD")
    print("=" * 70)
    leaderboard = system.get_leaderboard()
    for i, (identity, token) in enumerate(leaderboard, 1):
        print(f"{i}. {identity} - Ψ={token.average_psi:.4f} - {token.rank.value}")
    
    # Generar CV criptográfico
    print()
    print("=" * 70)
    print("CURRÍCULUM CRIPTOGRÁFICO")
    print("=" * 70)
    cv = system.generate_cryptographic_cv("alice@noetic.qcal")
    print(json.dumps(cv, indent=2))
    
    return system


if __name__ == "__main__":
    demo_reputation_system()
