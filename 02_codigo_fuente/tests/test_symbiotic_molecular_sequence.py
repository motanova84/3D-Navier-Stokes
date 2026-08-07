#!/usr/bin/env python3
"""
Tests for Symbiotic Molecular Sequence Generator
================================================

Tests para verificar:
1. Validación de secuencia RNA
2. Cálculo de contenido GC
3. Traducción a proteína
4. Generación de hash SHA-256
5. Generación de XML ST.26
6. Conexión con resonancia Riemann-NS

Author: José Manuel Mota Burruezo
Date: 31 de enero de 2026
"""

import sys
import os
import unittest
import tempfile
import hashlib
import xml.etree.ElementTree as ET

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'teoria_principal'))

from symbiotic_molecular_sequence import (
    SymbioticMolecularSequence,
    SequenceMetadata
)


class TestSequenceMetadata(unittest.TestCase):
    """Test SequenceMetadata dataclass"""
    
    def test_default_metadata(self):
        """Test default metadata values"""
        metadata = SequenceMetadata()
        
        self.assertEqual(metadata.name, "πCODE–1417–CYTO–RNS")
        self.assertEqual(metadata.sequence_type, "RNA")
        self.assertEqual(metadata.frequency_hz, 141.7001)
        self.assertEqual(metadata.date, "2026-01-31")
    
    def test_hash_generation(self):
        """Test SHA-256 hash generation"""
        metadata = SequenceMetadata()
        hash_id = metadata.get_hash()
        
        # Hash should be 12 characters
        self.assertEqual(len(hash_id), 12)
        
        # Hash should be hexadecimal
        self.assertTrue(all(c in '0123456789abcdef' for c in hash_id))
    
    def test_hash_consistency(self):
        """Test that hash is consistent for same inputs"""
        metadata1 = SequenceMetadata()
        metadata2 = SequenceMetadata()
        
        self.assertEqual(metadata1.get_hash(), metadata2.get_hash())
    
    def test_hash_uniqueness(self):
        """Test that different parameters give different hashes"""
        metadata1 = SequenceMetadata(name="Test1")
        metadata2 = SequenceMetadata(name="Test2")
        
        self.assertNotEqual(metadata1.get_hash(), metadata2.get_hash())


class TestSequenceValidation(unittest.TestCase):
    """Test sequence validation"""
    
    def test_default_sequence_is_valid(self):
        """Test that default RNA sequence is valid"""
        seq = SymbioticMolecularSequence()
        
        self.assertTrue(seq.validate_sequence())
    
    def test_sequence_length(self):
        """Test sequence length"""
        seq = SymbioticMolecularSequence()
        
        # Should be 53 nucleotides
        self.assertEqual(seq.get_sequence_length(), 53)
    
    def test_sequence_contains_only_rna_bases(self):
        """Test that sequence contains only A, C, G, U"""
        seq = SymbioticMolecularSequence()
        
        valid_bases = set('ACGU')
        sequence_bases = set(seq.sequence)
        
        self.assertTrue(sequence_bases.issubset(valid_bases))
    
    def test_sequence_value(self):
        """Test the actual sequence value"""
        seq = SymbioticMolecularSequence()
        
        expected = "AUGUUUGGAGCUAGUGCUCGAUUAAGAGGGUCUACCUCGUACUGAAGGCGUAG"
        self.assertEqual(seq.sequence, expected)


class TestGCContent(unittest.TestCase):
    """Test GC content calculation"""
    
    def test_gc_content_range(self):
        """Test that GC content is between 0 and 100"""
        seq = SymbioticMolecularSequence()
        gc = seq.get_gc_content()
        
        self.assertGreaterEqual(gc, 0.0)
        self.assertLessEqual(gc, 100.0)
    
    def test_gc_content_value(self):
        """Test GC content calculation"""
        seq = SymbioticMolecularSequence()
        
        # Count G and C manually
        g_count = seq.sequence.count('G')
        c_count = seq.sequence.count('C')
        expected_gc = ((g_count + c_count) / len(seq.sequence)) * 100
        
        self.assertAlmostEqual(seq.get_gc_content(), expected_gc, places=2)


class TestProteinTranslation(unittest.TestCase):
    """Test RNA to protein translation"""
    
    def test_translation_returns_string(self):
        """Test that translation returns a string"""
        seq = SymbioticMolecularSequence()
        protein = seq.translate_to_protein()
        
        self.assertIsInstance(protein, str)
    
    def test_translation_starts_with_methionine(self):
        """Test that translation starts with M (methionine from AUG)"""
        seq = SymbioticMolecularSequence()
        protein = seq.translate_to_protein()
        
        # Sequence starts with AUG, which codes for M
        if protein:
            self.assertEqual(protein[0], 'M')
    
    def test_protein_length(self):
        """Test protein length is approximately 1/3 of RNA length"""
        seq = SymbioticMolecularSequence()
        protein = seq.translate_to_protein()
        
        # Each amino acid comes from 3 nucleotides
        expected_max_length = seq.get_sequence_length() // 3
        self.assertLessEqual(len(protein), expected_max_length)
    
    def test_protein_contains_valid_amino_acids(self):
        """Test that protein contains only valid amino acid codes"""
        seq = SymbioticMolecularSequence()
        protein = seq.translate_to_protein()
        
        valid_amino_acids = set('ACDEFGHIKLMNPQRSTVWY*X')
        protein_chars = set(protein)
        
        self.assertTrue(protein_chars.issubset(valid_amino_acids))


class TestResonanceConnection(unittest.TestCase):
    """Test connection to Riemann-Navier-Stokes resonance"""
    
    def test_resonance_frequency(self):
        """Test that resonance frequency is correct"""
        seq = SymbioticMolecularSequence()
        resonance = seq.get_resonance_connection()
        
        self.assertEqual(resonance["fundamental_frequency_hz"], 141.7001)
    
    def test_resonance_includes_hash(self):
        """Test that resonance connection includes hash"""
        seq = SymbioticMolecularSequence()
        resonance = seq.get_resonance_connection()
        
        self.assertIn("hash_id", resonance)
        self.assertEqual(len(resonance["hash_id"]), 12)
    
    def test_resonance_includes_all_fields(self):
        """Test that resonance connection has all required fields"""
        seq = SymbioticMolecularSequence()
        resonance = seq.get_resonance_connection()
        
        required_fields = [
            "fundamental_frequency_hz",
            "sequence_length",
            "gc_content_percent",
            "protein_sequence",
            "hash_id",
            "connection"
        ]
        
        for field in required_fields:
            self.assertIn(field, resonance)


class TestST26XMLGeneration(unittest.TestCase):
    """Test ST.26 XML generation"""
    
    def test_xml_generation(self):
        """Test that XML is generated without errors"""
        seq = SymbioticMolecularSequence()
        xml = seq.generate_st26_xml()
        
        self.assertIsInstance(xml, str)
        self.assertGreater(len(xml), 0)
    
    def test_xml_is_valid(self):
        """Test that generated XML is valid"""
        seq = SymbioticMolecularSequence()
        xml = seq.generate_st26_xml()
        
        # Should be parseable
        try:
            ET.fromstring(xml)
            valid = True
        except ET.ParseError:
            valid = False
        
        self.assertTrue(valid)
    
    def test_xml_contains_sequence(self):
        """Test that XML contains the RNA sequence"""
        seq = SymbioticMolecularSequence()
        xml = seq.generate_st26_xml()
        
        # Sequence should be in lowercase in ST.26
        self.assertIn(seq.sequence.lower(), xml)
    
    def test_xml_contains_metadata(self):
        """Test that XML contains metadata"""
        seq = SymbioticMolecularSequence()
        xml = seq.generate_st26_xml()
        
        # Should contain key metadata
        self.assertIn("141.7001", xml)
        self.assertIn("2026-01-31", xml)
    
    def test_xml_save_to_file(self):
        """Test saving XML to file"""
        seq = SymbioticMolecularSequence()
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.xml', delete=False) as f:
            temp_path = f.name
        
        try:
            seq.save_st26_xml(temp_path)
            
            # File should exist
            self.assertTrue(os.path.exists(temp_path))
            
            # File should contain XML
            with open(temp_path, 'r') as f:
                content = f.read()
            
            self.assertGreater(len(content), 0)
            self.assertIn("ST26SequenceListing", content)
        finally:
            # Clean up
            if os.path.exists(temp_path):
                os.remove(temp_path)
    
    def test_xml_structure(self):
        """Test XML structure elements"""
        seq = SymbioticMolecularSequence()
        xml = seq.generate_st26_xml()
        
        root = ET.fromstring(xml)
        
        # Check root element
        self.assertEqual(root.tag, "ST26SequenceListing")
        
        # Check for required elements
        self.assertIsNotNone(root.find("ApplicationIdentification"))
        self.assertIsNotNone(root.find("SequenceTotalQuantity"))
        self.assertIsNotNone(root.find("SequenceData"))


class TestSummary(unittest.TestCase):
    """Test summary generation"""
    
    def test_summary_contains_all_keys(self):
        """Test that summary contains all required keys"""
        seq = SymbioticMolecularSequence()
        summary = seq.get_summary()
        
        required_keys = [
            "name",
            "type",
            "sequence",
            "length",
            "gc_content_percent",
            "protein_sequence",
            "frequency_hz",
            "date",
            "hash_id",
            "description",
            "organism",
            "valid"
        ]
        
        for key in required_keys:
            self.assertIn(key, summary)
    
    def test_summary_values(self):
        """Test summary values"""
        seq = SymbioticMolecularSequence()
        summary = seq.get_summary()
        
        self.assertEqual(summary["name"], "πCODE–1417–CYTO–RNS")
        self.assertEqual(summary["type"], "RNA")
        self.assertEqual(summary["length"], 53)
        self.assertEqual(summary["frequency_hz"], 141.7001)
        self.assertTrue(summary["valid"])
    
    def test_print_summary_runs(self):
        """Test that print_summary runs without error"""
        import io
        from contextlib import redirect_stdout
        
        seq = SymbioticMolecularSequence()
        
        # Capture output
        f = io.StringIO()
        with redirect_stdout(f):
            seq.print_summary()
        
        output = f.getvalue()
        
        # Check that output contains key information
        self.assertIn("πCODE–1417–CYTO–RNS", output)
        self.assertIn("141.7001", output)
        self.assertIn("RIEMANN-NAVIER-STOKES", output)


class TestIntegration(unittest.TestCase):
    """Integration tests"""
    
    def test_complete_workflow(self):
        """Test complete workflow from creation to XML generation"""
        # Create sequence
        seq = SymbioticMolecularSequence()
        
        # Validate
        self.assertTrue(seq.validate_sequence())
        
        # Get properties
        self.assertEqual(seq.get_sequence_length(), 53)
        self.assertGreater(seq.get_gc_content(), 0)
        
        # Translate
        protein = seq.translate_to_protein()
        self.assertGreater(len(protein), 0)
        
        # Get resonance
        resonance = seq.get_resonance_connection()
        self.assertEqual(resonance["fundamental_frequency_hz"], 141.7001)
        
        # Generate XML
        xml = seq.generate_st26_xml()
        self.assertIn("ST26SequenceListing", xml)
        
        # Get summary
        summary = seq.get_summary()
        self.assertTrue(summary["valid"])


def run_tests():
    """Run all tests"""
    unittest.main(argv=[''], verbosity=2, exit=False)


if __name__ == "__main__":
    run_tests()
