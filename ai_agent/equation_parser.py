"""
Equation Parser Module

Extracts mathematical equations and formulas from PDF documents
"""

import re
import json
from pathlib import Path
from typing import List, Dict, Optional, Set
import warnings


class EquationParser:
    """
    Parser for extracting mathematical equations from PDF documents
    and text files containing Navier-Stokes framework mathematics
    """
    
    def __init__(self):
        """Initialize the equation parser"""
        self.equations = []
        self.categories = {
            'navier_stokes': [],
            'vorticity': [],
            'besov_spaces': [],
            'riccati': [],
            'bkm_criterion': [],
            'energy_estimates': [],
            'constants': [],
            'inequalities': [],
            'other': []
        }
        
        # Common mathematical patterns
        self.patterns = {
            'equation': r'(?:[∂∇∫∑∏]|d/dt|\\frac|\\int|\\sum|\\prod)',
            'norm': r'‖[^‖]+‖(?:_[^\\s]+)?',
            'inequality': r'[≤≥<>]',
            'operators': r'[∂∇∫∑∏Δ∆]',
            'constants': r'(?:ν|γ|δ|α|β|ε|λ|C_[A-Za-z]+)',
            'spaces': r'(?:L[²³∞]|H[¹²³]|B[⁰¹²³]|Lₜ∞Lₓ³)',
        }
    
    def parse_pdf(self, pdf_path: str) -> Dict[str, any]:
        """
        Parse equations from a PDF file
        
        Args:
            pdf_path: Path to the PDF file
            
        Returns:
            Dictionary containing parsed equations and metadata
        """
        try:
            import PyPDF2
            
            pdf_path = Path(pdf_path)
            if not pdf_path.exists():
                raise FileNotFoundError(f"PDF file not found: {pdf_path}")
            
            text_content = ""
            with open(pdf_path, 'rb') as file:
                reader = PyPDF2.PdfReader(file)
                for page in reader.pages:
                    text_content += page.extract_text() + "\n"
            
            return self.parse_text(text_content, source=pdf_path.name)
            
        except ImportError:
            warnings.warn("PyPDF2 not installed. Using fallback text extraction.")
            return self._parse_pdf_fallback(pdf_path)
    
    def _parse_pdf_fallback(self, pdf_path: str) -> Dict[str, any]:
        """
        Fallback method to extract equations without PyPDF2
        Looks for documentation files with similar content
        """
        pdf_path = Path(pdf_path)
        
        # Look for associated text/markdown files
        doc_dir = pdf_path.parent / "Documentation"
        if doc_dir.exists():
            text_content = ""
            for md_file in doc_dir.glob("*.md"):
                with open(md_file, 'r', encoding='utf-8') as f:
                    text_content += f.read() + "\n"
            
            return self.parse_text(text_content, source=f"Documentation/*.md")
        
        return {
            'equations': [],
            'categories': self.categories,
            'source': pdf_path.name,
            'error': 'Unable to extract text from PDF'
        }
    
    def parse_text(self, text: str, source: str = "unknown") -> Dict[str, any]:
        """
        Parse mathematical equations from text content
        
        Args:
            text: Text content to parse
            source: Source identifier (filename, etc.)
            
        Returns:
            Dictionary containing parsed equations organized by category
        """
        equations = []
        
        # Extract lines that look like equations
        lines = text.split('\n')
        for i, line in enumerate(lines):
            line = line.strip()
            
            # Check if line contains mathematical notation
            if self._is_equation_line(line):
                equation_info = self._extract_equation_info(line, i)
                equations.append(equation_info)
                
                # Categorize the equation
                category = self._categorize_equation(equation_info)
                self.categories[category].append(equation_info)
        
        self.equations.extend(equations)
        
        return {
            'equations': equations,
            'categories': self.categories,
            'source': source,
            'total_equations': len(equations)
        }
    
    def _is_equation_line(self, line: str) -> bool:
        """
        Check if a line contains a mathematical equation
        
        Args:
            line: Text line to check
            
        Returns:
            True if line appears to contain an equation
        """
        if not line or len(line) < 3:
            return False
        
        # Check for mathematical operators and symbols
        for pattern_name, pattern in self.patterns.items():
            if re.search(pattern, line):
                return True
        
        # Check for common equation indicators
        equation_indicators = ['=', '≤', '≥', '∈', '→', '⇒', '⟨', '⟩']
        return any(indicator in line for indicator in equation_indicators)
    
    def _extract_equation_info(self, line: str, line_number: int) -> Dict:
        """
        Extract detailed information about an equation
        
        Args:
            line: Equation line
            line_number: Line number in source
            
        Returns:
            Dictionary with equation information
        """
        info = {
            'text': line,
            'line_number': line_number,
            'operators': [],
            'norms': [],
            'constants': [],
            'spaces': [],
            'has_inequality': False,
            'has_integral': False,
            'has_derivative': False,
        }
        
        # Extract operators
        operators = re.findall(self.patterns['operators'], line)
        info['operators'] = list(set(operators))
        
        # Extract norms
        norms = re.findall(self.patterns['norm'], line)
        info['norms'] = norms
        
        # Extract constants
        constants = re.findall(self.patterns['constants'], line)
        info['constants'] = list(set(constants))
        
        # Extract function spaces
        spaces = re.findall(self.patterns['spaces'], line)
        info['spaces'] = list(set(spaces))
        
        # Check for specific features
        info['has_inequality'] = bool(re.search(self.patterns['inequality'], line))
        info['has_integral'] = bool(re.search(r'[∫\\int]', line))
        info['has_derivative'] = bool(re.search(r'[∂∇d/dt\\frac]', line))
        
        return info
    
    def _categorize_equation(self, equation_info: Dict) -> str:
        """
        Categorize an equation based on its content
        
        Args:
            equation_info: Equation information dictionary
            
        Returns:
            Category name
        """
        text = equation_info['text'].lower()
        
        # Check for Navier-Stokes equations
        if any(term in text for term in ['navier-stokes', 'n-s', '∂u/∂t', 'momentum']):
            return 'navier_stokes'
        
        # Check for vorticity equations
        if 'ω' in equation_info['text'] or 'vorticity' in text or 'curl' in text:
            return 'vorticity'
        
        # Check for Besov space relations
        if any(space.startswith('B') for space in equation_info['spaces']) or 'besov' in text:
            return 'besov_spaces'
        
        # Check for Riccati inequalities
        if 'riccati' in text or ('d/dt' in text and equation_info['has_inequality']):
            return 'riccati'
        
        # Check for BKM criterion
        if 'bkm' in text or 'beale' in text or 'kato' in text or 'majda' in text:
            return 'bkm_criterion'
        
        # Check for energy estimates
        if 'energy' in text or any(norm.startswith('‖') and 'L²' in norm for norm in equation_info['norms']):
            return 'energy_estimates'
        
        # Check for constants
        if '=' in equation_info['text'] and equation_info['constants'] and not equation_info['has_derivative']:
            return 'constants'
        
        # Check for inequalities
        if equation_info['has_inequality']:
            return 'inequalities'
        
        return 'other'
    
    def get_equations_by_category(self, category: str) -> List[Dict]:
        """
        Get all equations in a specific category
        
        Args:
            category: Category name
            
        Returns:
            List of equations in that category
        """
        return self.categories.get(category, [])
    
    def search_equations(self, keyword: str) -> List[Dict]:
        """
        Search for equations containing a specific keyword
        
        Args:
            keyword: Keyword to search for
            
        Returns:
            List of matching equations
        """
        results = []
        for equation in self.equations:
            if keyword.lower() in equation['text'].lower():
                results.append(equation)
        return results
    
    def export_to_json(self, output_path: str):
        """
        Export parsed equations to JSON file
        
        Args:
            output_path: Path to output JSON file
        """
        data = {
            'total_equations': len(self.equations),
            'categories': {k: len(v) for k, v in self.categories.items()},
            'equations': self.equations,
            'detailed_categories': self.categories
        }
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
    
    def get_summary(self) -> Dict:
        """
        Get a summary of parsed equations
        
        Returns:
            Summary dictionary
        """
        return {
            'total_equations': len(self.equations),
            'by_category': {
                category: len(equations) 
                for category, equations in self.categories.items()
            },
            'unique_operators': list(set(
                op for eq in self.equations for op in eq['operators']
            )),
            'unique_constants': list(set(
                const for eq in self.equations for const in eq['constants']
            )),
            'unique_spaces': list(set(
                space for eq in self.equations for space in eq['spaces']
            ))
        }
