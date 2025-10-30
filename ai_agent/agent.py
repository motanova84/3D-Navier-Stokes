"""
Main AI Agent Interface

Entry point for the AI agent that helps create scripts and visualize
mathematical content from Navier-Stokes documents
"""

from .equation_parser import EquationParser
from .math_memory import MathematicalMemory
from .script_generator import ScriptGenerator
from .visualizer import EquationVisualizer
from pathlib import Path
from typing import List, Optional


class NavierStokesAIAgent:
    """
    AI Agent for Navier-Stokes mathematical document analysis,
    equation extraction, visualization, and script generation
    """
    
    def __init__(self, workspace_dir: str = "ai_agent_workspace"):
        """
        Initialize the AI Agent
        
        Args:
            workspace_dir: Directory for agent workspace
        """
        self.workspace_dir = Path(workspace_dir)
        self.workspace_dir.mkdir(exist_ok=True, parents=True)
        
        # Initialize components
        self.parser = EquationParser()
        self.memory = MathematicalMemory(
            memory_file=str(self.workspace_dir / "knowledge_base.json")
        )
        self.generator = ScriptGenerator(
            output_dir=str(self.workspace_dir / "generated_scripts")
        )
        self.visualizer = EquationVisualizer(
            output_dir=str(self.workspace_dir / "visualizations")
        )
        
        print(f"AI Agent initialized. Workspace: {self.workspace_dir}")
    
    def process_pdf_document(self, pdf_path: str) -> dict:
        """
        Process a PDF document and extract mathematical content
        
        Args:
            pdf_path: Path to PDF file
            
        Returns:
            Dictionary with processing results
        """
        print(f"\n{'='*70}")
        print(f"Processing PDF document: {pdf_path}")
        print('='*70)
        
        # Parse equations from PDF
        parse_results = self.parser.parse_pdf(pdf_path)
        
        print(f"\nExtracted {parse_results['total_equations']} equations")
        
        # Add equations to memory
        for eq in parse_results['equations']:
            self.memory.add_equation(
                name=f"Equation_{eq['line_number']}",
                formula=eq['text'],
                description=f"Extracted from line {eq['line_number']}",
                category=self._map_category(eq),
                source=pdf_path
            )
        
        # Save memory
        self.memory.save_to_file()
        
        return parse_results
    
    def process_documentation(self, doc_dir: str = "Documentation") -> dict:
        """
        Process all documentation files in a directory
        
        Args:
            doc_dir: Directory containing documentation
            
        Returns:
            Dictionary with processing results
        """
        print(f"\n{'='*70}")
        print(f"Processing documentation directory: {doc_dir}")
        print('='*70)
        
        doc_path = Path(doc_dir)
        if not doc_path.exists():
            print(f"Warning: Directory not found: {doc_dir}")
            return {'total_equations': 0, 'files_processed': 0}
        
        total_equations = 0
        files_processed = 0
        
        # Process all markdown files
        for md_file in doc_path.glob("*.md"):
            print(f"\nProcessing: {md_file.name}")
            
            with open(md_file, 'r', encoding='utf-8') as f:
                content = f.read()
            
            parse_results = self.parser.parse_text(content, source=md_file.name)
            
            # Add to memory
            for eq in parse_results['equations']:
                self.memory.add_equation(
                    name=f"{md_file.stem}_{eq['line_number']}",
                    formula=eq['text'],
                    description=f"From {md_file.name}, line {eq['line_number']}",
                    category=self._map_category(eq),
                    source=str(md_file)
                )
            
            total_equations += parse_results['total_equations']
            files_processed += 1
        
        # Save memory
        self.memory.save_to_file()
        
        print(f"\n{'='*70}")
        print(f"Processed {files_processed} files")
        print(f"Total equations extracted: {total_equations}")
        print('='*70)
        
        return {
            'total_equations': total_equations,
            'files_processed': files_processed
        }
    
    def visualize_knowledge(self):
        """Generate visualizations of the mathematical knowledge base"""
        print(f"\n{'='*70}")
        print("Generating visualizations...")
        print('='*70)
        
        # Create various visualizations
        self.visualizer.visualize_equation_network(self.memory)
        self.visualizer.visualize_category_distribution(self.memory)
        self.visualizer.visualize_proof_structure(self.memory)
        self.visualizer.create_summary_report(self.memory)
        
        print("\nAll visualizations generated successfully!")
    
    def generate_scripts(self):
        """Generate Python scripts based on the knowledge base"""
        print(f"\n{'='*70}")
        print("Generating scripts...")
        print('='*70)
        
        # Get equations by category
        equations = [
            {'id': eq_id, **eq_data}
            for eq_id, eq_data in self.memory.knowledge_base['equations'].items()
        ]
        
        # Generate verification script
        self.generator.generate_verification_script(equations)
        
        # Generate simulation script
        constants = self.memory.knowledge_base['constants']
        self.generator.generate_simulation_script(constants)
        
        # Generate analysis script
        self.generator.generate_analysis_script(self.memory)
        
        # Generate visualization script
        self.generator.generate_visualization_script(self.memory)
        
        print("\nAll scripts generated successfully!")
    
    def export_knowledge_base(self, format: str = 'markdown'):
        """
        Export the knowledge base
        
        Args:
            format: Export format ('markdown', 'json')
        """
        print(f"\n{'='*70}")
        print(f"Exporting knowledge base as {format}...")
        print('='*70)
        
        if format == 'markdown':
            output_file = self.workspace_dir / "knowledge_base.md"
            self.memory.export_markdown(str(output_file))
            print(f"Exported to: {output_file}")
        
        elif format == 'json':
            output_file = self.workspace_dir / "knowledge_base.json"
            self.memory.save_to_file(str(output_file))
            print(f"Exported to: {output_file}")
        
        else:
            print(f"Unknown format: {format}")
    
    def search_knowledge(self, keyword: str):
        """
        Search the knowledge base for a keyword
        
        Args:
            keyword: Keyword to search for
        """
        print(f"\n{'='*70}")
        print(f"Searching for: '{keyword}'")
        print('='*70)
        
        results = self.memory.search(keyword)
        
        if not results:
            print("No results found.")
            return
        
        for category, items in results.items():
            print(f"\n{category.upper()}:")
            for item in items:
                print(f"  - {item['data'].get('name', item['id'])}")
                if 'formula' in item['data']:
                    print(f"    Formula: {item['data']['formula'][:80]}...")
    
    def get_summary(self):
        """Print a summary of the knowledge base"""
        print(f"\n{'='*70}")
        print("KNOWLEDGE BASE SUMMARY")
        print('='*70)
        
        summary = self.memory.get_summary()
        
        print(f"\nTotal Equations: {summary['total_equations']}")
        print(f"Total Constants: {summary['total_constants']}")
        print(f"Total Theorems: {summary['total_theorems']}")
        print(f"Total Relationships: {summary['total_relationships']}")
        
        print("\nEquations by Category:")
        for category, count in summary['equations_by_category'].items():
            print(f"  {category}: {count}")
        
        print("\nConstants by Category:")
        for category, count in summary['constants_by_category'].items():
            print(f"  {category}: {count}")
        
        if summary.get('unique_operators'):
            print(f"\nUnique Operators: {', '.join(summary['unique_operators'])}")
        
        if summary.get('unique_constants'):
            print(f"\nUnique Constants: {', '.join(summary['unique_constants'][:10])}")
        
        if summary.get('unique_spaces'):
            print(f"\nFunction Spaces: {', '.join(summary['unique_spaces'][:10])}")
        
        print('='*70)
    
    def _map_category(self, equation_info: dict) -> str:
        """
        Map internal category to memory category
        
        Args:
            equation_info: Equation information from parser
            
        Returns:
            Category name
        """
        text = equation_info['text'].lower()
        
        # Map to broader categories
        if 'navier-stokes' in text or 'momentum' in text:
            return 'fundamental'
        elif 'bkm' in text or 'criterion' in text:
            return 'criterion'
        elif 'riccati' in text or 'estimate' in text or 'inequality' in text:
            return 'estimate'
        elif any(const in text for const in ['ν', 'viscosity', 'reynolds']):
            return 'physical'
        else:
            return 'general'
    
    def run_full_pipeline(self, pdf_paths: Optional[List[str]] = None,
                         doc_dir: Optional[str] = None):
        """
        Run the full AI agent pipeline
        
        Args:
            pdf_paths: List of PDF files to process
            doc_dir: Documentation directory to process
        """
        print("\n" + "="*70)
        print("AI AGENT FULL PIPELINE")
        print("="*70)
        
        # Process PDFs if provided
        if pdf_paths:
            for pdf_path in pdf_paths:
                if Path(pdf_path).exists():
                    self.process_pdf_document(pdf_path)
        
        # Process documentation if provided
        if doc_dir and Path(doc_dir).exists():
            self.process_documentation(doc_dir)
        
        # Generate visualizations
        self.visualize_knowledge()
        
        # Generate scripts
        self.generate_scripts()
        
        # Export knowledge base
        self.export_knowledge_base('markdown')
        self.export_knowledge_base('json')
        
        # Show summary
        self.get_summary()
        
        print("\n" + "="*70)
        print("PIPELINE COMPLETE!")
        print("="*70)
        print(f"\nWorkspace: {self.workspace_dir}")
        print(f"  - Knowledge Base: {self.workspace_dir / 'knowledge_base.json'}")
        print(f"  - Visualizations: {self.workspace_dir / 'visualizations'}/")
        print(f"  - Generated Scripts: {self.workspace_dir / 'generated_scripts'}/")
        print("="*70)
