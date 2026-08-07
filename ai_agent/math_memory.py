"""
Mathematical Memory Module

Stores and organizes mathematical knowledge extracted from documents
"""

import json
from pathlib import Path
from typing import Dict, List, Optional, Set
from datetime import datetime


class MathematicalMemory:
    """
    Memory system for storing and retrieving mathematical equations,
    constants, and relationships from Navier-Stokes documents
    """
    
    def __init__(self, memory_file: Optional[str] = None):
        """
        Initialize mathematical memory
        
        Args:
            memory_file: Optional path to persistent memory file
        """
        self.memory_file = memory_file
        self.knowledge_base = {
            'equations': {},
            'constants': {},
            'theorems': {},
            'lemmas': {},
            'definitions': {},
            'relationships': [],
            'metadata': {
                'created': datetime.now().isoformat(),
                'last_updated': datetime.now().isoformat(),
                'sources': []
            }
        }
        
        # Load existing memory if file exists
        if memory_file and Path(memory_file).exists():
            self.load_from_file(memory_file)
        
        # Initialize domain-specific knowledge
        self._initialize_domain_knowledge()
    
    def _initialize_domain_knowledge(self):
        """Initialize known Navier-Stokes framework constants and equations"""
        
        # Key constants from the repository
        self.add_constant(
            name="ν",
            description="Kinematic viscosity",
            typical_value="1e-3",
            category="physical"
        )
        
        self.add_constant(
            name="C_BKM",
            description="Calderón-Zygmund operator norm / Besov constant",
            typical_value="2.0",
            category="mathematical"
        )
        
        self.add_constant(
            name="c_d",
            description="Bernstein constant (d=3)",
            typical_value="0.5",
            category="mathematical"
        )
        
        self.add_constant(
            name="δ*",
            description="Misalignment defect parameter",
            formula="a²c₀²/(4π²)",
            typical_value="1/(4π²) ≈ 0.0253",
            category="qcal"
        )
        
        self.add_constant(
            name="c⋆",
            description="Parabolic coercivity coefficient",
            typical_value="1/16",
            category="mathematical"
        )
        
        self.add_constant(
            name="C_str",
            description="Vorticity stretching constant",
            typical_value="32",
            category="mathematical"
        )
        
        self.add_constant(
            name="C_CZ",
            description="Calderón-Zygmund constant (optimized)",
            typical_value="1.5",
            category="mathematical"
        )
        
        # Key equations
        self.add_equation(
            name="Navier-Stokes",
            formula="∂u/∂t + (u·∇)u = -∇p + ν∆u + f",
            description="3D Navier-Stokes momentum equation",
            category="fundamental"
        )
        
        self.add_equation(
            name="Vorticity",
            formula="ω = ∇ × u",
            description="Vorticity definition",
            category="fundamental"
        )
        
        self.add_equation(
            name="BKM Criterion",
            formula="∫₀^T ‖ω(t)‖_{L∞} dt < ∞ ⇒ no blow-up",
            description="Beale-Kato-Majda criterion for global regularity",
            category="criterion"
        )
        
        self.add_equation(
            name="Riccati Inequality",
            formula="d/dt X(t) ≤ A - B X(t) log(e + βX(t))",
            description="Dyadic Riccati inequality for vorticity control",
            category="estimate"
        )
        
        self.add_equation(
            name="CZ-Besov Estimate",
            formula="‖∇u‖_{L∞} ≤ C_CZ‖ω‖_{B⁰_{∞,1}}",
            description="Calderón-Zygmund operator in Besov spaces",
            category="estimate"
        )
    
    def add_equation(self, name: str, formula: str, 
                    description: str = "", category: str = "general",
                    source: str = "", metadata: Dict = None):
        """
        Add an equation to memory
        
        Args:
            name: Equation name/identifier
            formula: Mathematical formula
            description: Description of the equation
            category: Category (fundamental, estimate, criterion, etc.)
            source: Source document/reference
            metadata: Additional metadata
        """
        equation_id = f"eq_{len(self.knowledge_base['equations']) + 1}"
        
        self.knowledge_base['equations'][equation_id] = {
            'name': name,
            'formula': formula,
            'description': description,
            'category': category,
            'source': source,
            'metadata': metadata or {},
            'added': datetime.now().isoformat()
        }
        
        self._update_timestamp()
    
    def add_constant(self, name: str, description: str = "",
                    typical_value: str = "", formula: str = "",
                    category: str = "general", source: str = ""):
        """
        Add a mathematical constant to memory
        
        Args:
            name: Constant name/symbol
            description: Description of the constant
            typical_value: Typical numerical value
            formula: Formula for computing the constant
            category: Category (physical, mathematical, qcal, etc.)
            source: Source document/reference
        """
        const_id = f"const_{len(self.knowledge_base['constants']) + 1}"
        
        self.knowledge_base['constants'][const_id] = {
            'name': name,
            'description': description,
            'typical_value': typical_value,
            'formula': formula,
            'category': category,
            'source': source,
            'added': datetime.now().isoformat()
        }
        
        self._update_timestamp()
    
    def add_theorem(self, name: str, statement: str,
                   proof_outline: str = "", category: str = "general",
                   source: str = "", related_equations: List[str] = None):
        """
        Add a theorem to memory
        
        Args:
            name: Theorem name
            statement: Theorem statement
            proof_outline: Brief proof outline
            category: Category
            source: Source reference
            related_equations: List of related equation IDs
        """
        theorem_id = f"thm_{len(self.knowledge_base['theorems']) + 1}"
        
        self.knowledge_base['theorems'][theorem_id] = {
            'name': name,
            'statement': statement,
            'proof_outline': proof_outline,
            'category': category,
            'source': source,
            'related_equations': related_equations or [],
            'added': datetime.now().isoformat()
        }
        
        self._update_timestamp()
    
    def add_relationship(self, from_entity: str, to_entity: str,
                        relationship_type: str, description: str = ""):
        """
        Add a relationship between mathematical entities
        
        Args:
            from_entity: Source entity ID
            to_entity: Target entity ID
            relationship_type: Type of relationship (implies, uses, derived_from, etc.)
            description: Description of the relationship
        """
        relationship = {
            'from': from_entity,
            'to': to_entity,
            'type': relationship_type,
            'description': description,
            'added': datetime.now().isoformat()
        }
        
        self.knowledge_base['relationships'].append(relationship)
        self._update_timestamp()
    
    def get_equation(self, query: str) -> Optional[Dict]:
        """
        Retrieve an equation by name or ID
        
        Args:
            query: Equation name or ID
            
        Returns:
            Equation dictionary or None
        """
        # Check by ID
        if query in self.knowledge_base['equations']:
            return self.knowledge_base['equations'][query]
        
        # Check by name
        for eq_id, eq_data in self.knowledge_base['equations'].items():
            if eq_data['name'].lower() == query.lower():
                return eq_data
        
        return None
    
    def get_constant(self, query: str) -> Optional[Dict]:
        """
        Retrieve a constant by name or ID
        
        Args:
            query: Constant name or ID
            
        Returns:
            Constant dictionary or None
        """
        # Check by ID
        if query in self.knowledge_base['constants']:
            return self.knowledge_base['constants'][query]
        
        # Check by name
        for const_id, const_data in self.knowledge_base['constants'].items():
            if const_data['name'] == query:
                return const_data
        
        return None
    
    def search(self, keyword: str, search_in: List[str] = None) -> Dict:
        """
        Search for keyword across knowledge base
        
        Args:
            keyword: Keyword to search for
            search_in: List of categories to search in (default: all)
            
        Returns:
            Dictionary of search results by category
        """
        if search_in is None:
            search_in = ['equations', 'constants', 'theorems', 'definitions']
        
        results = {}
        keyword_lower = keyword.lower()
        
        for category in search_in:
            if category not in self.knowledge_base:
                continue
            
            category_results = []
            for item_id, item_data in self.knowledge_base[category].items():
                # Search in all string fields
                for field, value in item_data.items():
                    if isinstance(value, str) and keyword_lower in value.lower():
                        category_results.append({
                            'id': item_id,
                            'data': item_data,
                            'matched_field': field
                        })
                        break
            
            if category_results:
                results[category] = category_results
        
        return results
    
    def get_by_category(self, entity_type: str, category: str) -> List[Dict]:
        """
        Get all entities of a type in a specific category
        
        Args:
            entity_type: Type of entity (equations, constants, theorems, etc.)
            category: Category to filter by
            
        Returns:
            List of entities in that category
        """
        if entity_type not in self.knowledge_base:
            return []
        
        results = []
        for item_id, item_data in self.knowledge_base[entity_type].items():
            if item_data.get('category') == category:
                results.append({'id': item_id, **item_data})
        
        return results
    
    def get_summary(self) -> Dict:
        """
        Get a summary of the knowledge base
        
        Returns:
            Summary dictionary with counts and statistics
        """
        return {
            'total_equations': len(self.knowledge_base['equations']),
            'total_constants': len(self.knowledge_base['constants']),
            'total_theorems': len(self.knowledge_base['theorems']),
            'total_relationships': len(self.knowledge_base['relationships']),
            'equations_by_category': self._count_by_category('equations'),
            'constants_by_category': self._count_by_category('constants'),
            'metadata': self.knowledge_base['metadata']
        }
    
    def _count_by_category(self, entity_type: str) -> Dict[str, int]:
        """Count entities by category"""
        counts = {}
        for item_data in self.knowledge_base[entity_type].values():
            category = item_data.get('category', 'unknown')
            counts[category] = counts.get(category, 0) + 1
        return counts
    
    def _update_timestamp(self):
        """Update the last_updated timestamp"""
        self.knowledge_base['metadata']['last_updated'] = datetime.now().isoformat()
    
    def save_to_file(self, filepath: str = None):
        """
        Save knowledge base to JSON file
        
        Args:
            filepath: Path to save file (uses self.memory_file if not provided)
        """
        filepath = filepath or self.memory_file
        if not filepath:
            raise ValueError("No filepath specified for saving")
        
        with open(filepath, 'w', encoding='utf-8') as f:
            json.dump(self.knowledge_base, f, indent=2, ensure_ascii=False)
    
    def load_from_file(self, filepath: str):
        """
        Load knowledge base from JSON file
        
        Args:
            filepath: Path to load file
        """
        with open(filepath, 'r', encoding='utf-8') as f:
            loaded_data = json.load(f)
            self.knowledge_base.update(loaded_data)
    
    def export_markdown(self, output_path: str):
        """
        Export knowledge base to a readable Markdown file
        
        Args:
            output_path: Path to output Markdown file
        """
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write("# Mathematical Knowledge Base\n\n")
            f.write(f"Generated: {datetime.now().isoformat()}\n\n")
            
            # Summary
            summary = self.get_summary()
            f.write("## Summary\n\n")
            f.write(f"- Total Equations: {summary['total_equations']}\n")
            f.write(f"- Total Constants: {summary['total_constants']}\n")
            f.write(f"- Total Theorems: {summary['total_theorems']}\n")
            f.write(f"- Total Relationships: {summary['total_relationships']}\n\n")
            
            # Constants
            f.write("## Constants\n\n")
            for const_id, const_data in self.knowledge_base['constants'].items():
                f.write(f"### {const_data['name']}\n")
                f.write(f"**Description:** {const_data['description']}\n\n")
                if const_data.get('formula'):
                    f.write(f"**Formula:** {const_data['formula']}\n\n")
                if const_data.get('typical_value'):
                    f.write(f"**Typical Value:** {const_data['typical_value']}\n\n")
                f.write(f"**Category:** {const_data['category']}\n\n")
                f.write("---\n\n")
            
            # Equations
            f.write("## Equations\n\n")
            for eq_id, eq_data in self.knowledge_base['equations'].items():
                f.write(f"### {eq_data['name']}\n")
                f.write(f"**Formula:** {eq_data['formula']}\n\n")
                f.write(f"**Description:** {eq_data['description']}\n\n")
                f.write(f"**Category:** {eq_data['category']}\n\n")
                f.write("---\n\n")
            
            # Theorems
            if self.knowledge_base['theorems']:
                f.write("## Theorems\n\n")
                for thm_id, thm_data in self.knowledge_base['theorems'].items():
                    f.write(f"### {thm_data['name']}\n")
                    f.write(f"**Statement:** {thm_data['statement']}\n\n")
                    if thm_data.get('proof_outline'):
                        f.write(f"**Proof Outline:** {thm_data['proof_outline']}\n\n")
                    f.write("---\n\n")
