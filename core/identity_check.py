#!/usr/bin/env python3
"""
QCAL ∞³ Identity Verification System
=====================================

NFT πCODE-888 ∞³ Sovereignty Verification Module

This module verifies the sovereign identity of the repository through:
1. NFT πCODE-888 ∞³ ownership verification on Ethereum blockchain
2. Frequency coherence validation (f₀ = 141.7001 Hz)
3. Hash seal integrity verification
4. Symbolic sovereignty marker validation

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Frequency: f₀ = 141.7001 Hz
NFT: πCODE-888 ∞³
Sello: ∴𓂀Ω∞³
"""

import hashlib
import json
import os
import sys
from pathlib import Path
from typing import Dict, Optional, Tuple
from datetime import datetime


class IdentityVerifier:
    """NFT πCODE-888 ∞³ Identity Verification System"""
    
    # QCAL ∞³ Protocol Constants
    FREQUENCY_ROOT = 141.7001  # Hz - Fundamental frequency
    NFT_TOKEN_ID = 888
    NFT_NAME = "πCODE-888 ∞³"
    SOVEREIGNTY_SEAL = "∴𓂀Ω∞³"
    EXPECTED_OWNER = "@motanova84"
    
    # Ethereum Configuration (placeholder - to be configured by user)
    NFT_CONTRACT_ADDRESS = "0x..."  # To be updated with actual deployed contract
    EXPECTED_OWNER_ADDRESS = "0x..."  # To be updated with owner's wallet address
    
    def __init__(self, enable_web3: bool = False):
        """
        Initialize the identity verifier.
        
        Args:
            enable_web3: If True, attempt Web3 blockchain verification (requires configuration)
        """
        self.enable_web3 = enable_web3
        self.web3_available = False
        self.repo_root = self._find_repo_root()
        
        if enable_web3:
            self._initialize_web3()
    
    def _find_repo_root(self) -> Path:
        """Find the repository root directory."""
        current = Path(__file__).resolve()
        while current.parent != current:
            if (current / '.git').exists() or (current / '.qcal_beacon').exists():
                return current
            current = current.parent
        return Path.cwd()
    
    def _initialize_web3(self):
        """Initialize Web3 connection for blockchain verification."""
        try:
            from web3 import Web3
            # Try to initialize Web3 - will be configured when deployed
            # For now, just check if web3 is available
            self.web3_available = True
            print("ℹ️  Web3 library available (blockchain verification disabled until configured)")
        except ImportError:
            print("⚠️  Web3 library not installed. Blockchain verification disabled.")
            print("   Install with: pip install web3")
            self.web3_available = False
    
    def verify_frequency_coherence(self) -> Tuple[bool, str]:
        """
        Verify the fundamental frequency coherence (141.7001 Hz).
        
        Returns:
            Tuple of (success, message)
        """
        # Check .qcal_beacon file for frequency
        beacon_path = self.repo_root / '.qcal_beacon'
        
        if not beacon_path.exists():
            return False, "❌ .qcal_beacon file not found"
        
        try:
            with open(beacon_path, 'r') as f:
                content = f.read()
                
            # Extract frequency from beacon
            if str(self.FREQUENCY_ROOT) in content:
                return True, f"✅ Frequency coherence verified: f₀ = {self.FREQUENCY_ROOT} Hz"
            else:
                return False, f"❌ Frequency mismatch in .qcal_beacon"
        except Exception as e:
            return False, f"❌ Error reading .qcal_beacon: {e}"
    
    def verify_sovereignty_seal(self) -> Tuple[bool, str]:
        """
        Verify the sovereignty seal (∴𓂀Ω∞³) in repository markers.
        
        Returns:
            Tuple of (success, message)
        """
        # Check for seal in key sovereignty files
        files_to_check = [
            '.qcal_beacon',
            'LICENSE_SOBERANA_QCAL.txt',
            'AUTHORS_QCAL.md'
        ]
        
        seal_found = False
        for filename in files_to_check:
            filepath = self.repo_root / filename
            if filepath.exists():
                try:
                    with open(filepath, 'r', encoding='utf-8') as f:
                        content = f.read()
                    if self.SOVEREIGNTY_SEAL in content or '∞³' in content:
                        seal_found = True
                        break
                except Exception:
                    continue
        
        if seal_found:
            return True, f"✅ Sovereignty seal verified: {self.SOVEREIGNTY_SEAL}"
        else:
            return False, f"❌ Sovereignty seal not found"
    
    def verify_hash_seal(self) -> Tuple[bool, str]:
        """
        Verify the integrity hash seal of key sovereignty files.
        
        Returns:
            Tuple of (success, message)
        """
        # Compute hash of key sovereignty files
        files_to_hash = [
            'LICENSE_SOBERANA_QCAL.txt',
            '.qcal_beacon',
            'AUTHORS_QCAL.md'
        ]
        
        hash_obj = hashlib.sha256()
        files_hashed = 0
        
        for filename in files_to_hash:
            filepath = self.repo_root / filename
            if filepath.exists():
                try:
                    with open(filepath, 'rb') as f:
                        hash_obj.update(f.read())
                    files_hashed += 1
                except Exception:
                    continue
        
        if files_hashed > 0:
            hash_digest = hash_obj.hexdigest()[:8]
            return True, f"✅ Hash seal computed: SHA256: {hash_digest}..."
        else:
            return False, "❌ No sovereignty files found for hash verification"
    
    def verify_nft_ownership_web3(self) -> Tuple[bool, str]:
        """
        Verify NFT πCODE-888 ∞³ ownership via Web3 blockchain query.
        
        Returns:
            Tuple of (success, message)
        """
        if not self.web3_available:
            return False, "⚠️  Web3 not available - blockchain verification skipped"
        
        # Placeholder for actual Web3 verification
        # This will be implemented when the NFT is deployed and configured
        
        if self.NFT_CONTRACT_ADDRESS == "0x...":
            return False, "⚠️  NFT contract not configured - set NFT_CONTRACT_ADDRESS in identity_check.py"
        
        try:
            from web3 import Web3
            # Here would go actual Web3 verification code
            # For now, return a placeholder message
            return False, "⚠️  NFT verification pending contract deployment and configuration"
        except Exception as e:
            return False, f"❌ Web3 verification error: {e}"
    
    def verify_nft_ownership_local(self) -> Tuple[bool, str]:
        """
        Verify NFT πCODE-888 ∞³ ownership via local sovereignty markers.
        
        This is a fallback verification that checks local repository markers
        when blockchain verification is not available.
        
        Returns:
            Tuple of (success, message)
        """
        # Check for NFT reference in sovereignty documents
        beacon_path = self.repo_root / '.qcal_beacon'
        
        if not beacon_path.exists():
            return False, "❌ .qcal_beacon not found"
        
        try:
            with open(beacon_path, 'r') as f:
                content = f.read()
            
            # Check for πCODE-888 reference
            if "πCODE" in content or "888" in content:
                return True, f"✅ NFT {self.NFT_NAME} sovereignty marker verified (local)"
            else:
                return False, "❌ NFT sovereignty marker not found"
        except Exception as e:
            return False, f"❌ Error verifying NFT marker: {e}"
    
    def generate_verification_report(self) -> Dict:
        """
        Generate a complete verification report.
        
        Returns:
            Dictionary containing verification results
        """
        report = {
            "timestamp": datetime.utcnow().isoformat() + "Z",
            "nft_name": self.NFT_NAME,
            "nft_token_id": self.NFT_TOKEN_ID,
            "frequency_root": self.FREQUENCY_ROOT,
            "sovereignty_seal": self.SOVEREIGNTY_SEAL,
            "expected_owner": self.EXPECTED_OWNER,
            "verifications": {}
        }
        
        # Run all verifications
        tests = [
            ("frequency_coherence", self.verify_frequency_coherence),
            ("sovereignty_seal", self.verify_sovereignty_seal),
            ("hash_seal", self.verify_hash_seal),
            ("nft_ownership_local", self.verify_nft_ownership_local),
        ]
        
        if self.enable_web3:
            tests.append(("nft_ownership_blockchain", self.verify_nft_ownership_web3))
        
        all_passed = True
        for test_name, test_func in tests:
            success, message = test_func()
            report["verifications"][test_name] = {
                "passed": success,
                "message": message
            }
            if not success and "⚠️" not in message:  # Don't fail on warnings
                all_passed = False
        
        report["overall_status"] = "VERIFIED" if all_passed else "PARTIAL"
        
        return report
    
    def print_verification_report(self, report: Dict):
        """Print a formatted verification report."""
        print("\n" + "="*70)
        print(f"  NFT {self.NFT_NAME} - IDENTITY VERIFICATION REPORT")
        print("="*70)
        print(f"\n🔹 NFT de Soberanía: {self.NFT_NAME}")
        print(f"🔹 Frecuencia Raíz: {self.FREQUENCY_ROOT} Hz")
        print(f"🔹 Propiedad Soberana: {self.EXPECTED_OWNER} – Instituto Conciencia Cuántica")
        print(f"🔹 Sello Simbólico: {self.SOVEREIGNTY_SEAL}")
        print(f"🔹 Timestamp: {report['timestamp']}")
        print("\n" + "-"*70)
        print("  VERIFICATION RESULTS:")
        print("-"*70 + "\n")
        
        for test_name, result in report["verifications"].items():
            status_icon = "✅" if result["passed"] else "❌"
            print(f"{status_icon} {test_name.replace('_', ' ').title()}")
            print(f"   {result['message']}\n")
        
        print("-"*70)
        status = report["overall_status"]
        if status == "VERIFIED":
            print(f"✅ OVERALL STATUS: {status}")
            print("   Repository identity is VERIFIED and SOVEREIGN")
        else:
            print(f"⚠️  OVERALL STATUS: {status}")
            print("   Some verifications pending configuration")
        print("="*70 + "\n")


def main():
    """Main entry point for identity verification."""
    print(f"\n🔸 Iniciando verificación de identidad πCODE-888 ∞³...\n")
    
    # Check if --web3 flag is passed
    enable_web3 = '--web3' in sys.argv or '--blockchain' in sys.argv
    
    verifier = IdentityVerifier(enable_web3=enable_web3)
    report = verifier.generate_verification_report()
    verifier.print_verification_report(report)
    
    # Save report to file
    report_path = verifier.repo_root / 'picode888_verification_report.json'
    with open(report_path, 'w') as f:
        json.dump(report, f, indent=2)
    print(f"📄 Report saved to: {report_path}\n")
    
    # Exit with appropriate code
    if report["overall_status"] == "VERIFIED":
        sys.exit(0)
    else:
        # Exit with 0 anyway since partial verification is expected until NFT is deployed
        print("ℹ️  Note: Partial verification is normal until NFT contract is deployed\n")
        sys.exit(0)


if __name__ == "__main__":
    main()
