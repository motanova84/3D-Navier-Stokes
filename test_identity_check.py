#!/usr/bin/env python3
"""
Tests for QCAL ∞³ Identity Verification System
===============================================

Test suite for core/identity_check.py NFT πCODE-888 ∞³ verification.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Frequency: f₀ = 141.7001 Hz
"""

import unittest
import json
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

from core.identity_check import IdentityVerifier


class TestIdentityVerifier(unittest.TestCase):
    """Test suite for NFT πCODE-888 ∞³ identity verification."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.verifier = IdentityVerifier(enable_web3=False)
    
    def test_initialization(self):
        """Test that the verifier initializes correctly."""
        self.assertIsNotNone(self.verifier)
        self.assertEqual(self.verifier.FREQUENCY_ROOT, 141.7001)
        self.assertEqual(self.verifier.NFT_TOKEN_ID, 888)
        self.assertEqual(self.verifier.NFT_NAME, "πCODE-888 ∞³")
        self.assertEqual(self.verifier.SOVEREIGNTY_SEAL, "∴𓂀Ω∞³")
        self.assertEqual(self.verifier.EXPECTED_OWNER, "@motanova84")
    
    def test_find_repo_root(self):
        """Test that the repo root is found correctly."""
        repo_root = self.verifier.repo_root
        self.assertIsNotNone(repo_root)
        self.assertTrue(repo_root.exists())
        # Should have .git or .qcal_beacon
        self.assertTrue(
            (repo_root / '.git').exists() or 
            (repo_root / '.qcal_beacon').exists()
        )
    
    def test_verify_frequency_coherence(self):
        """Test frequency coherence verification."""
        success, message = self.verifier.verify_frequency_coherence()
        self.assertTrue(success, f"Frequency verification failed: {message}")
        self.assertIn("141.7001", message)
        self.assertIn("✅", message)
    
    def test_verify_sovereignty_seal(self):
        """Test sovereignty seal verification."""
        success, message = self.verifier.verify_sovereignty_seal()
        self.assertTrue(success, f"Sovereignty seal verification failed: {message}")
        self.assertIn("∞³", message)
        self.assertIn("✅", message)
    
    def test_verify_hash_seal(self):
        """Test hash seal computation."""
        success, message = self.verifier.verify_hash_seal()
        self.assertTrue(success, f"Hash seal verification failed: {message}")
        self.assertIn("SHA256", message)
        self.assertIn("✅", message)
    
    def test_verify_nft_ownership_local(self):
        """Test local NFT ownership verification."""
        success, message = self.verifier.verify_nft_ownership_local()
        self.assertTrue(success, f"NFT local verification failed: {message}")
        self.assertIn("πCODE-888 ∞³", message)
        self.assertIn("✅", message)
    
    def test_verify_nft_ownership_web3_without_config(self):
        """Test Web3 verification returns warning when not configured."""
        # Initialize with web3 disabled
        verifier = IdentityVerifier(enable_web3=False)
        success, message = verifier.verify_nft_ownership_web3()
        self.assertFalse(success)
        self.assertIn("⚠️", message)
    
    def test_generate_verification_report(self):
        """Test verification report generation."""
        report = self.verifier.generate_verification_report()
        
        # Check report structure
        self.assertIn("timestamp", report)
        self.assertIn("nft_name", report)
        self.assertIn("nft_token_id", report)
        self.assertIn("frequency_root", report)
        self.assertIn("sovereignty_seal", report)
        self.assertIn("expected_owner", report)
        self.assertIn("verifications", report)
        self.assertIn("overall_status", report)
        
        # Check values
        self.assertEqual(report["nft_name"], "πCODE-888 ∞³")
        self.assertEqual(report["nft_token_id"], 888)
        self.assertEqual(report["frequency_root"], 141.7001)
        self.assertEqual(report["sovereignty_seal"], "∴𓂀Ω∞³")
        self.assertEqual(report["expected_owner"], "@motanova84")
        
        # Check verifications
        self.assertIn("frequency_coherence", report["verifications"])
        self.assertIn("sovereignty_seal", report["verifications"])
        self.assertIn("hash_seal", report["verifications"])
        self.assertIn("nft_ownership_local", report["verifications"])
        
        # All local verifications should pass
        self.assertTrue(report["verifications"]["frequency_coherence"]["passed"])
        self.assertTrue(report["verifications"]["sovereignty_seal"]["passed"])
        self.assertTrue(report["verifications"]["hash_seal"]["passed"])
        
        # Overall status should be VERIFIED (web3 not required)
        self.assertEqual(report["overall_status"], "VERIFIED")
    
    def test_report_serialization(self):
        """Test that the report can be serialized to JSON."""
        report = self.verifier.generate_verification_report()
        
        # Should be JSON serializable
        try:
            json_str = json.dumps(report, indent=2)
            self.assertIsNotNone(json_str)
            
            # Should be deserializable
            report_copy = json.loads(json_str)
            self.assertEqual(report["nft_name"], report_copy["nft_name"])
            self.assertEqual(report["frequency_root"], report_copy["frequency_root"])
        except Exception as e:
            self.fail(f"Report serialization failed: {e}")
    
    def test_constants_accuracy(self):
        """Test that all constants are accurate."""
        # Frequency
        self.assertAlmostEqual(self.verifier.FREQUENCY_ROOT, 141.7001, places=4)
        
        # Token ID
        self.assertEqual(self.verifier.NFT_TOKEN_ID, 888)
        
        # Names and seals
        self.assertIn("πCODE", self.verifier.NFT_NAME)
        self.assertIn("888", self.verifier.NFT_NAME)
        self.assertIn("∞³", self.verifier.NFT_NAME)
        
        self.assertIn("∞³", self.verifier.SOVEREIGNTY_SEAL)
        
        # Owner
        self.assertEqual(self.verifier.EXPECTED_OWNER, "@motanova84")


class TestIdentityVerifierWithWeb3Enabled(unittest.TestCase):
    """Test suite with Web3 enabled (but not configured)."""
    
    def test_web3_initialization_without_library(self):
        """Test Web3 initialization when library is not available."""
        verifier = IdentityVerifier(enable_web3=True)
        # Should not crash, just disable web3
        self.assertIsNotNone(verifier)
    
    def test_verification_report_with_web3_enabled(self):
        """Test report generation with Web3 enabled."""
        verifier = IdentityVerifier(enable_web3=True)
        report = verifier.generate_verification_report()
        
        # Should include web3 verification attempt
        # But overall status should still be reasonable
        self.assertIn("overall_status", report)
        self.assertIsNotNone(report["overall_status"])


class TestNFTConstants(unittest.TestCase):
    """Test NFT πCODE-888 ∞³ constants."""
    
    def test_frequency_root(self):
        """Test the fundamental frequency."""
        self.assertAlmostEqual(IdentityVerifier.FREQUENCY_ROOT, 141.7001, places=4)
    
    def test_nft_token_id(self):
        """Test NFT token ID is 888."""
        self.assertEqual(IdentityVerifier.NFT_TOKEN_ID, 888)
    
    def test_nft_name(self):
        """Test NFT name contains required elements."""
        name = IdentityVerifier.NFT_NAME
        self.assertIn("πCODE", name)
        self.assertIn("888", name)
        self.assertIn("∞³", name)
    
    def test_sovereignty_seal(self):
        """Test sovereignty seal format."""
        seal = IdentityVerifier.SOVEREIGNTY_SEAL
        self.assertIn("∞³", seal)
        # Should have symbolic characters
        self.assertTrue(len(seal) > 2)


def run_tests():
    """Run all tests and return success status."""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestIdentityVerifier))
    suite.addTests(loader.loadTestsFromTestCase(TestIdentityVerifierWithWeb3Enabled))
    suite.addTests(loader.loadTestsFromTestCase(TestNFTConstants))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Print summary
    print("\n" + "="*70)
    print("  TEST SUMMARY - NFT πCODE-888 ∞³ Identity Verification")
    print("="*70)
    print(f"Tests run: {result.testsRun}")
    print(f"Successes: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"Failures: {len(result.failures)}")
    print(f"Errors: {len(result.errors)}")
    print("="*70 + "\n")
    
    return result.wasSuccessful()


if __name__ == '__main__':
    success = run_tests()
    sys.exit(0 if success else 1)
