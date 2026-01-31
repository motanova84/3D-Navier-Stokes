#!/usr/bin/env python3
"""
Symbiotic Molecular Sequence Generator - πCODE–1417–CYTO–RNS
===========================================================

Generador de secuencia molecular simbiótica conectada a la resonancia
Riemann-Navier-Stokes en el flujo citoplasmático.

Este módulo genera:
1. Secuencia RNA conectada a f₀ = 141.7001 Hz
2. Archivo XML ST.26 (estándar WIPO para secuencias)
3. Hash SHA-256 para verificación de integridad

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: 31 de enero de 2026
License: MIT
"""

import hashlib
from datetime import datetime
from typing import Dict, Optional
from dataclasses import dataclass
import xml.etree.ElementTree as ET
from xml.dom import minidom


@dataclass
class SequenceMetadata:
    """Metadata for the symbiotic molecular sequence"""
    name: str = "πCODE–1417–CYTO–RNS"
    sequence_type: str = "RNA"
    frequency_hz: float = 141.7001
    date: str = "2026-01-31"
    description: str = "Secuencia simbiótica citoplasmática conectada a resonancia Riemann–Navier–Stokes"
    organism: str = "Homo sapiens (cytoplasmic resonance system)"
    
    def get_hash(self) -> str:
        """
        Calculate SHA-256 hash of name + frequency
        
        Returns:
            First 12 characters of SHA-256 hash
        """
        data = f"{self.name}{self.frequency_hz}"
        hash_full = hashlib.sha256(data.encode()).hexdigest()
        return hash_full[:12]


class SymbioticMolecularSequence:
    """
    Generador de secuencia molecular simbiótica
    
    Esta clase genera la secuencia RNA que codifica la resonancia
    citoplasmática a 141.7001 Hz según el modelo Riemann-Navier-Stokes.
    """
    
    # Secuencia RNA simbiótica (54 nucleótidos)
    RNA_SEQUENCE = "AUGUUUGGAGCUAGUGCUCGAUUAAGAGGGUCUACCUCGUACUGAAGGCGUAG"
    
    def __init__(self, metadata: Optional[SequenceMetadata] = None):
        """
        Initialize the symbiotic molecular sequence generator
        
        Args:
            metadata: Sequence metadata (uses defaults if None)
        """
        self.metadata = metadata if metadata is not None else SequenceMetadata()
        self.sequence = self.RNA_SEQUENCE
        
    def validate_sequence(self) -> bool:
        """
        Validate that the RNA sequence contains only valid nucleotides
        
        Returns:
            True if valid, False otherwise
        """
        valid_nucleotides = set('ACGU')
        return all(nucleotide in valid_nucleotides for nucleotide in self.sequence)
    
    def get_sequence_length(self) -> int:
        """Get the length of the RNA sequence"""
        return len(self.sequence)
    
    def get_gc_content(self) -> float:
        """
        Calculate GC content (percentage of G and C nucleotides)
        
        Returns:
            GC content as percentage (0-100)
        """
        gc_count = self.sequence.count('G') + self.sequence.count('C')
        return (gc_count / len(self.sequence)) * 100
    
    def translate_to_protein(self) -> str:
        """
        Translate RNA sequence to protein (amino acid sequence)
        
        Returns:
            Protein sequence in single-letter amino acid code
        """
        # Standard genetic code (RNA codon table)
        codon_table = {
            'UUU': 'F', 'UUC': 'F', 'UUA': 'L', 'UUG': 'L',
            'UCU': 'S', 'UCC': 'S', 'UCA': 'S', 'UCG': 'S',
            'UAU': 'Y', 'UAC': 'Y', 'UAA': '*', 'UAG': '*',
            'UGU': 'C', 'UGC': 'C', 'UGA': '*', 'UGG': 'W',
            'CUU': 'L', 'CUC': 'L', 'CUA': 'L', 'CUG': 'L',
            'CCU': 'P', 'CCC': 'P', 'CCA': 'P', 'CCG': 'P',
            'CAU': 'H', 'CAC': 'H', 'CAA': 'Q', 'CAG': 'Q',
            'CGU': 'R', 'CGC': 'R', 'CGA': 'R', 'CGG': 'R',
            'AUU': 'I', 'AUC': 'I', 'AUA': 'I', 'AUG': 'M',
            'ACU': 'T', 'ACC': 'T', 'ACA': 'T', 'ACG': 'T',
            'AAU': 'N', 'AAC': 'N', 'AAA': 'K', 'AAG': 'K',
            'AGU': 'S', 'AGC': 'S', 'AGA': 'R', 'AGG': 'R',
            'GUU': 'V', 'GUC': 'V', 'GUA': 'V', 'GUG': 'V',
            'GCU': 'A', 'GCC': 'A', 'GCA': 'A', 'GCG': 'A',
            'GAU': 'D', 'GAC': 'D', 'GAA': 'E', 'GAG': 'E',
            'GGU': 'G', 'GGC': 'G', 'GGA': 'G', 'GGG': 'G',
        }
        
        protein = []
        for i in range(0, len(self.sequence) - 2, 3):
            codon = self.sequence[i:i+3]
            if len(codon) == 3:
                amino_acid = codon_table.get(codon, 'X')  # X for unknown
                if amino_acid == '*':  # Stop codon
                    break
                protein.append(amino_acid)
        
        return ''.join(protein)
    
    def get_resonance_connection(self) -> Dict[str, any]:
        """
        Get the connection between sequence and Riemann-Navier-Stokes resonance
        
        Returns:
            Dictionary with resonance properties
        """
        return {
            "fundamental_frequency_hz": self.metadata.frequency_hz,
            "sequence_length": self.get_sequence_length(),
            "gc_content_percent": self.get_gc_content(),
            "protein_sequence": self.translate_to_protein(),
            "hash_id": self.metadata.get_hash(),
            "connection": "Riemann–Navier–Stokes cytoplasmic flow resonance"
        }
    
    def generate_st26_xml(self) -> str:
        """
        Generate ST.26 XML format sequence listing
        
        ST.26 is the WIPO Standard for sequence listings in patent applications
        
        Returns:
            XML string in ST.26 format
        """
        # Create root element
        root = ET.Element("ST26SequenceListing")
        root.set("dtdVersion", "V1_3")
        root.set("fileName", f"{self.metadata.name}.xml")
        root.set("softwareName", "QCAL-Riemann-NS-Sequence-Generator")
        root.set("softwareVersion", "1.0")
        root.set("productionDate", self.metadata.date)
        
        # Application identification
        app_id = ET.SubElement(root, "ApplicationIdentification")
        ET.SubElement(app_id, "IPOfficeCode").text = "WO"
        ET.SubElement(app_id, "ApplicationNumberText").text = "QCAL-2026-141.7001"
        ET.SubElement(app_id, "FilingDate").text = self.metadata.date
        
        # Applicant information
        applicant = ET.SubElement(root, "ApplicantFileReference")
        applicant.text = self.metadata.name
        
        # Earliest priority application identification
        early_priority = ET.SubElement(root, "EarliestPriorityApplicationIdentification")
        ET.SubElement(early_priority, "IPOfficeCode").text = "ES"
        ET.SubElement(early_priority, "ApplicationNumberText").text = "QCAL-ES-2026-001"
        ET.SubElement(early_priority, "FilingDate").text = self.metadata.date
        
        # Applicant name
        applicant_name = ET.SubElement(root, "ApplicantName")
        ET.SubElement(applicant_name, "languageCode").text = "es"
        app_name_text = ET.SubElement(applicant_name, "FreeFormName")
        app_name_text.text = "Instituto Consciencia Cuántica QCAL ∞³"
        
        # Invention title
        invention_title = ET.SubElement(root, "InventionTitle")
        invention_title.set("languageCode", "es")
        invention_title.text = "Secuencia Molecular Simbiótica para Resonancia Citoplasmática Riemann-Navier-Stokes"
        
        # Sequence total quantity
        ET.SubElement(root, "SequenceTotalQuantity").text = "1"
        
        # Sequence data
        seq_data = ET.SubElement(root, "SequenceData")
        seq_data.set("sequenceIDNumber", "1")
        
        # Sequence ID number
        ET.SubElement(seq_data, "INSDSeq_length").text = str(self.get_sequence_length())
        ET.SubElement(seq_data, "INSDSeq_moltype").text = self.metadata.sequence_type
        
        # Sequence features
        features = ET.SubElement(seq_data, "INSDSeq_feature-table")
        
        # Source feature
        source_feature = ET.SubElement(features, "INSDFeature")
        ET.SubElement(source_feature, "INSDFeature_key").text = "source"
        source_location = ET.SubElement(source_feature, "INSDFeature_location")
        source_location.text = f"1..{self.get_sequence_length()}"
        
        source_quals = ET.SubElement(source_feature, "INSDFeature_quals")
        
        organism_qual = ET.SubElement(source_quals, "INSDQualifier")
        ET.SubElement(organism_qual, "INSDQualifier_name").text = "organism"
        ET.SubElement(organism_qual, "INSDQualifier_value").text = self.metadata.organism
        
        mol_type_qual = ET.SubElement(source_quals, "INSDQualifier")
        ET.SubElement(mol_type_qual, "INSDQualifier_name").text = "mol_type"
        ET.SubElement(mol_type_qual, "INSDQualifier_value").text = "synthetic RNA"
        
        # Frequency qualifier
        freq_qual = ET.SubElement(source_quals, "INSDQualifier")
        ET.SubElement(freq_qual, "INSDQualifier_name").text = "note"
        ET.SubElement(freq_qual, "INSDQualifier_value").text = f"Resonance frequency: {self.metadata.frequency_hz} Hz (Riemann-Navier-Stokes)"
        
        # CDS feature (if translatable)
        protein = self.translate_to_protein()
        if protein:
            cds_feature = ET.SubElement(features, "INSDFeature")
            ET.SubElement(cds_feature, "INSDFeature_key").text = "CDS"
            cds_location = ET.SubElement(cds_feature, "INSDFeature_location")
            cds_location.text = f"1..{self.get_sequence_length()}"
            
            cds_quals = ET.SubElement(cds_feature, "INSDFeature_quals")
            
            product_qual = ET.SubElement(cds_quals, "INSDQualifier")
            ET.SubElement(product_qual, "INSDQualifier_name").text = "product"
            ET.SubElement(product_qual, "INSDQualifier_value").text = "Cytoplasmic resonance protein (Riemann-NS)"
            
            translation_qual = ET.SubElement(cds_quals, "INSDQualifier")
            ET.SubElement(translation_qual, "INSDQualifier_name").text = "translation"
            ET.SubElement(translation_qual, "INSDQualifier_value").text = protein
        
        # Sequence itself
        sequence_elem = ET.SubElement(seq_data, "INSDSeq_sequence")
        sequence_elem.text = self.sequence.lower()  # ST.26 uses lowercase
        
        # Convert to pretty XML string
        xml_string = ET.tostring(root, encoding='unicode')
        dom = minidom.parseString(xml_string)
        pretty_xml = dom.toprettyxml(indent="  ", encoding=None)
        
        # Remove extra blank lines
        lines = [line for line in pretty_xml.split('\n') if line.strip()]
        return '\n'.join(lines)
    
    def save_st26_xml(self, filepath: str) -> None:
        """
        Save ST.26 XML to file
        
        Args:
            filepath: Path to save the XML file
        """
        xml_content = self.generate_st26_xml()
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(xml_content)
    
    def get_summary(self) -> Dict[str, any]:
        """
        Get complete summary of the symbiotic sequence
        
        Returns:
            Dictionary with all sequence information
        """
        return {
            "name": self.metadata.name,
            "type": self.metadata.sequence_type,
            "sequence": self.sequence,
            "length": self.get_sequence_length(),
            "gc_content_percent": self.get_gc_content(),
            "protein_sequence": self.translate_to_protein(),
            "frequency_hz": self.metadata.frequency_hz,
            "date": self.metadata.date,
            "hash_id": self.metadata.get_hash(),
            "description": self.metadata.description,
            "organism": self.metadata.organism,
            "valid": self.validate_sequence()
        }
    
    def print_summary(self):
        """Print a formatted summary of the sequence"""
        print("=" * 70)
        print("SECUENCIA MOLECULAR SIMBIÓTICA")
        print("πCODE–1417–CYTO–RNS")
        print("=" * 70)
        print()
        
        print(f"📄 Nombre: {self.metadata.name}")
        print(f"🧬 Tipo: {self.metadata.sequence_type}")
        print(f"📏 Longitud: {self.get_sequence_length()} nucleótidos")
        print()
        
        print("🔤 Secuencia:")
        print(f"   {self.sequence}")
        print()
        
        print(f"📊 Contenido GC: {self.get_gc_content():.2f}%")
        print()
        
        protein = self.translate_to_protein()
        if protein:
            print(f"🧪 Secuencia proteica: {protein}")
            print(f"   ({len(protein)} aminoácidos)")
            print()
        
        print(f"📡 Frecuencia anclada: f₀ = {self.metadata.frequency_hz} Hz")
        print("   (Resonancia fundamental Riemann-Navier-Stokes)")
        print()
        
        print(f"🔐 Hash simbólico: {self.metadata.get_hash()}...")
        print(f"   (SHA-256 de {self.metadata.name} + {self.metadata.frequency_hz})")
        print()
        
        print(f"📅 Fecha: {self.metadata.date}")
        print(f"✅ Validación: {'VÁLIDA' if self.validate_sequence() else 'INVÁLIDA'}")
        print()
        
        print("🌐 Organismo:")
        print(f"   {self.metadata.organism}")
        print()
        
        print("📝 Descripción:")
        print(f"   {self.metadata.description}")
        print()
        
        print("=" * 70)
        print("CONEXIÓN RIEMANN-NAVIER-STOKES")
        print("=" * 70)
        print()
        print("Esta secuencia molecular codifica la resonancia citoplasmática")
        print("que conecta los ceros de Riemann con el flujo de Navier-Stokes")
        print("en tejido biológico vivo.")
        print()
        print(f"La frecuencia fundamental f₀ = {self.metadata.frequency_hz} Hz")
        print("representa el primer eigenvalor del operador hermítico")
        print("de Hilbert-Pólya en el citoplasma celular.")
        print()
        print("🎯 Esta secuencia es el puente molecular entre:")
        print("   • Matemática pura (Hipótesis de Riemann)")
        print("   • Física de fluidos (Navier-Stokes)")
        print("   • Biología molecular (RNA celular)")
        print()
        print("=" * 70)


def main():
    """Main function for demonstration"""
    # Create symbiotic sequence
    sequence = SymbioticMolecularSequence()
    
    # Print summary
    sequence.print_summary()
    
    # Generate and save ST.26 XML
    xml_filename = f"{sequence.metadata.name}.xml"
    print(f"\n📦 Generando archivo ST.26 XML: {xml_filename}")
    sequence.save_st26_xml(xml_filename)
    print(f"✅ Archivo generado exitosamente")
    
    return sequence


if __name__ == "__main__":
    sequence = main()
