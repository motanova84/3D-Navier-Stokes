#!/usr/bin/env python3
"""
Tests for QCAL Ecosystem - Three Pillars Integration

Tests the reputation system, marketplace, and enterprise bridge.
"""

import unittest
import numpy as np
from datetime import datetime, timedelta

from soulbound_reputation import (
    ReputationSystem, RankLevel, AchievementType
)
from picode_marketplace import (
    PiCodeExchange, CertificateType, LicenseType
)
from qcal_enterprise_bridge import (
    QCALEnterpriseBridge, SpectralQualityLevel, PipelineStatus
)
from qcal_ecosystem_integration import QCALEcosystem


class TestReputationSystem(unittest.TestCase):
    """Test suite for Soulbound Token reputation system"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.system = ReputationSystem()
    
    def test_register_developer(self):
        """Test developer registration"""
        token = self.system.register_developer("test@dev.qcal")
        
        self.assertEqual(token.noetic_identity, "test@dev.qcal")
        self.assertEqual(token.rank, RankLevel.NOVICE)
        self.assertEqual(token.total_commits, 0)
        self.assertEqual(token.average_psi, 0.0)
    
    def test_record_commit(self):
        """Test commit recording"""
        self.system.register_developer("alice@qcal")
        
        commit = self.system.record_commit(
            "alice@qcal",
            "commit_hash_123",
            0.99,
            "High quality commit"
        )
        
        self.assertEqual(commit.psi_coherence, 0.99)
        self.assertAlmostEqual(commit.frequency_hz, 141.7001 * 0.99, places=4)
        
        token = self.system.tokens["alice@qcal"]
        self.assertEqual(token.total_commits, 1)
        self.assertEqual(token.average_psi, 0.99)
    
    def test_rank_progression(self):
        """Test that rank progresses with high coherence commits"""
        dev_id = "bob@qcal"
        self.system.register_developer(dev_id)
        
        # Record many high-quality commits
        for i in range(100):
            self.system.record_commit(dev_id, f"commit_{i}", 0.99)
        
        token = self.system.tokens[dev_id]
        self.assertGreaterEqual(token.average_psi, 0.989)  # Account for floating point
        # Should at least be ADEPT
        self.assertIn(token.rank, [RankLevel.ADEPT, RankLevel.MASTER, RankLevel.GUARDIAN])
    
    def test_achievement_grant(self):
        """Test achievement granting"""
        dev_id = "carol@qcal"
        self.system.register_developer(dev_id)
        
        # Record commit with perfect coherence
        self.system.record_commit(dev_id, "perfect_commit", 1.0)
        
        token = self.system.tokens[dev_id]
        achievement_types = [a.achievement_type for a in token.achievements]
        
        # Should have quantum stability achievement
        self.assertIn(AchievementType.QUANTUM_STABILITY, achievement_types)
    
    def test_leaderboard(self):
        """Test leaderboard generation"""
        # Register multiple developers
        self.system.register_developer("alice@qcal")
        self.system.register_developer("bob@qcal")
        
        # Alice gets higher coherence
        for i in range(10):
            self.system.record_commit("alice@qcal", f"a_{i}", 0.99)
            self.system.record_commit("bob@qcal", f"b_{i}", 0.85)
        
        leaderboard = self.system.get_leaderboard(top_n=2)
        
        # Alice should be first
        self.assertEqual(leaderboard[0][0], "alice@qcal")
        self.assertGreater(leaderboard[0][1].average_psi, leaderboard[1][1].average_psi)


class TestPiCodeMarketplace(unittest.TestCase):
    """Test suite for πCODE Exchange marketplace"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.exchange = PiCodeExchange()
    
    def test_issue_certificate(self):
        """Test certificate issuance"""
        cert = self.exchange.issue_certificate(
            certificate_type=CertificateType.GLOBAL_REGULARITY,
            holder="company@example.com",
            license_type=LicenseType.ANNUAL,
            psi_coherence=0.99,
            stability_metric=0.98,
            price_picode=1000.0,
            validity_days=365
        )
        
        self.assertEqual(cert.holder, "company@example.com")
        self.assertEqual(cert.certificate_type, CertificateType.GLOBAL_REGULARITY)
        self.assertTrue(cert.is_valid())
        self.assertAlmostEqual(cert.quality_proof.frequency_hz, 141.7001, places=4)
    
    def test_purchase_certificate(self):
        """Test certificate purchase"""
        cert = self.exchange.issue_certificate(
            CertificateType.SPECTRAL_STABILITY,
            "seller@example.com",
            LicenseType.PERPETUAL,
            0.95,
            0.95,
            500.0
        )
        
        success = self.exchange.purchase_certificate(cert.certificate_id, "buyer@example.com")
        
        self.assertTrue(success)
        self.assertEqual(cert.holder, "buyer@example.com")
    
    def test_royalty_tracking(self):
        """Test royalty transaction recording"""
        cert = self.exchange.issue_certificate(
            CertificateType.QUANTUM_COHERENCE,
            "owner@example.com",
            LicenseType.ROYALTY_BASED,
            0.99,
            0.99,
            1000.0
        )
        
        # Record usage
        transaction = self.exchange.record_usage(
            cert.certificate_id,
            "user@example.com",
            "System validation"
        )
        
        self.assertIsNotNone(transaction)
        self.assertEqual(cert.usage_count, 1)
        self.assertGreater(transaction.amount_picode, 0)
    
    def test_global_regularity_certificate(self):
        """Test Global Regularity Certificate creation"""
        cert = self.exchange.create_global_regularity_certificate(
            "aerospace@company.com",
            "0xNS_PROOF_HASH"
        )
        
        self.assertEqual(cert.certificate_type, CertificateType.GLOBAL_REGULARITY)
        self.assertTrue(cert.metadata.get("navier_stokes_validated", False))
        self.assertEqual(cert.quality_proof.lean4_proof_hash, "0xNS_PROOF_HASH")
    
    def test_knowledge_collateral(self):
        """Test knowledge collateral creation"""
        collateral = self.exchange.create_knowledge_collateral(
            owner="researcher@university.edu",
            problem_type="P vs NP",
            resolution_proof_hash="0xPROOF",
            collateral_value=5000.0,
            lock_days=180
        )
        
        self.assertEqual(collateral.problem_type, "P vs NP")
        self.assertEqual(collateral.collateral_value_picode, 5000.0)
        self.assertEqual(collateral.quantum_compute_hours_granted, 500.0)


class TestQCALEnterpriseBridge(unittest.TestCase):
    """Test suite for QCAL Enterprise Bridge"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.bridge = QCALEnterpriseBridge()
    
    def test_create_quality_gate(self):
        """Test quality gate creation"""
        gate = self.bridge.create_spectral_quality_gate(
            name="Test Gate",
            quality_level=SpectralQualityLevel.HIGH,
            min_coherence=0.95
        )
        
        self.assertEqual(gate.name, "Test Gate")
        self.assertEqual(gate.min_coherence, 0.95)
        self.assertIn(gate.gate_id, self.bridge.quality_gates)
    
    def test_register_pipeline(self):
        """Test pipeline registration"""
        gate = self.bridge.create_spectral_quality_gate("Gate1", SpectralQualityLevel.MEDIUM)
        
        pipeline_id = self.bridge.register_pipeline(
            "Test Pipeline",
            "GitHub Actions",
            [gate.gate_id]
        )
        
        self.assertIn(pipeline_id, self.bridge.pipelines)
        pipeline = self.bridge.pipelines[pipeline_id]
        self.assertEqual(pipeline["name"], "Test Pipeline")
        self.assertEqual(pipeline["platform"], "GitHub Actions")
    
    def test_analyze_code_signature(self):
        """Test code signature analysis"""
        signature = self.bridge.analyze_code_signature("test_hash_123")
        
        self.assertAlmostEqual(signature.frequency_hz, 141.7001, places=4)
        self.assertGreaterEqual(signature.coherence_psi, 0.0)
        self.assertLessEqual(signature.coherence_psi, 1.0)
    
    def test_run_pipeline(self):
        """Test pipeline execution"""
        gate = self.bridge.create_spectral_quality_gate(
            "Test Gate",
            SpectralQualityLevel.MEDIUM,
            min_coherence=0.90
        )
        
        pipeline_id = self.bridge.register_pipeline(
            "Test Pipeline",
            "GitLab CI",
            [gate.gate_id]
        )
        
        result = self.bridge.run_pipeline(pipeline_id, "code_hash_456")
        
        self.assertIn("status", result)
        self.assertIn("signature", result)
        self.assertIn("gate_results", result)
    
    def test_compliance_report_generation(self):
        """Test compliance report generation"""
        signature = self.bridge.analyze_code_signature("system_hash")
        report = self.bridge.generate_compliance_report("Test System", signature)
        
        self.assertEqual(report.system_name, "Test System")
        self.assertIsInstance(report.coherence_score, float)
        self.assertIsInstance(report.compliance_level, str)
        self.assertIsNotNone(report.to_json())
    
    def test_angel_agents_deployment(self):
        """Test Angel Agents deployment"""
        systems = ["api-server", "database", "cache"]
        self.bridge.deploy_angel_agents(systems)
        
        miguel = self.bridge.angel_agents["MIGUEL_01"]
        gabriel = self.bridge.angel_agents["GABRIEL_01"]
        
        total_monitored = len(miguel.monitored_systems) + len(gabriel.monitored_systems)
        self.assertEqual(total_monitored, len(systems))


class TestQCALEcosystemIntegration(unittest.TestCase):
    """Test suite for full ecosystem integration"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.ecosystem = QCALEcosystem()
    
    def test_ecosystem_initialization(self):
        """Test that ecosystem initializes all components"""
        self.assertIsNotNone(self.ecosystem.reputation_system)
        self.assertIsNotNone(self.ecosystem.marketplace)
        self.assertIsNotNone(self.ecosystem.enterprise_bridge)
        self.assertAlmostEqual(self.ecosystem.f0_hz, 141.7001, places=4)
    
    def test_developer_journey(self):
        """Test complete developer journey"""
        commits = [
            {"hash": f"commit_{i}", "psi": 0.99, "desc": "Quality work"}
            for i in range(50)
        ]
        
        result = self.ecosystem.developer_journey("dev@test.com", commits)
        
        self.assertEqual(result["developer_id"], "dev@test.com")
        self.assertEqual(result["total_commits"], 50)
        self.assertGreaterEqual(result["average_psi"], 0.99)
    
    def test_enterprise_integration_flow(self):
        """Test enterprise integration flow"""
        result = self.ecosystem.enterprise_integration_flow(
            "Test Corp",
            "TestProject"
        )
        
        self.assertEqual(result["company"], "Test Corp")
        self.assertEqual(result["project"], "TestProject")
        self.assertIn("certificate_id", result)
        self.assertIn("pipeline_id", result)
        self.assertIn("compliance_level", result)
    
    def test_knowledge_economy_cycle(self):
        """Test knowledge economy cycle"""
        result = self.ecosystem.knowledge_economy_cycle(
            "researcher@test.edu",
            "Test Problem",
            0.995
        )
        
        self.assertEqual(result["researcher_id"], "researcher@test.edu")
        self.assertEqual(result["problem_type"], "Test Problem")
        self.assertGreater(result["collateral_value"], 0)
        self.assertGreater(result["quantum_hours"], 0)
    
    def test_ecosystem_report(self):
        """Test ecosystem report generation"""
        report = self.ecosystem.generate_ecosystem_report()
        
        self.assertIn("ecosystem_status", report)
        self.assertIn("resonance_frequency_hz", report)
        self.assertIn("reputation_system", report)
        self.assertIn("marketplace", report)
        self.assertIn("enterprise_bridge", report)
        self.assertAlmostEqual(report["resonance_frequency_hz"], 141.7001, places=4)


def run_tests():
    """Run all tests"""
    print("=" * 70)
    print("Running QCAL Ecosystem Test Suite")
    print("=" * 70)
    print()
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestReputationSystem))
    suite.addTests(loader.loadTestsFromTestCase(TestPiCodeMarketplace))
    suite.addTests(loader.loadTestsFromTestCase(TestQCALEnterpriseBridge))
    suite.addTests(loader.loadTestsFromTestCase(TestQCALEcosystemIntegration))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Print summary
    print()
    print("=" * 70)
    print("Test Summary")
    print("=" * 70)
    print(f"Tests run: {result.testsRun}")
    print(f"Successes: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"Failures: {len(result.failures)}")
    print(f"Errors: {len(result.errors)}")
    
    if result.wasSuccessful():
        print("\n✅ All tests passed!")
    else:
        print("\n❌ Some tests failed")
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    exit(0 if success else 1)
