#!/usr/bin/env python3
"""
Example Usage: Navier-Stokes AI Agent

This script demonstrates how to use the AI agent to:
1. Parse equations from PDF documents
2. Memorize mathematical content
3. Generate visualizations
4. Create helper scripts

Usage:
    python run_ai_agent.py
"""

from ai_agent.agent import NavierStokesAIAgent
from pathlib import Path


def main():
    """
    Main function demonstrating AI agent capabilities
    """
    print("""
╔═══════════════════════════════════════════════════════════════════════╗
║                                                                       ║
║           NAVIER-STOKES AI AGENT - Mathematical Assistant            ║
║                                                                       ║
║  Helps create scripts and visualize mathematics from documents       ║
║                                                                       ║
╚═══════════════════════════════════════════════════════════════════════╝
    """)
    
    # Initialize the AI agent
    agent = NavierStokesAIAgent(workspace_dir="ai_agent_workspace")
    
    # Example 1: Process documentation files
    print("\n[EXAMPLE 1] Processing Documentation Files")
    print("-" * 70)
    
    doc_dir = Path("Documentation")
    if doc_dir.exists():
        agent.process_documentation(str(doc_dir))
    else:
        print("Documentation directory not found. Skipping...")
    
    # Example 2: Search for specific topics
    print("\n[EXAMPLE 2] Searching for Topics")
    print("-" * 70)
    
    topics = ["BKM", "vorticity", "Riccati", "Besov"]
    for topic in topics:
        agent.search_knowledge(topic)
    
    # Example 3: Get knowledge base summary
    print("\n[EXAMPLE 3] Knowledge Base Summary")
    print("-" * 70)
    agent.get_summary()
    
    # Example 4: Generate visualizations
    print("\n[EXAMPLE 4] Generating Visualizations")
    print("-" * 70)
    try:
        agent.visualize_knowledge()
    except Exception as e:
        print(f"Note: Visualization generation requires matplotlib: {e}")
        print("Install with: pip install matplotlib")
    
    # Example 5: Generate scripts
    print("\n[EXAMPLE 5] Generating Helper Scripts")
    print("-" * 70)
    agent.generate_scripts()
    
    # Example 6: Export knowledge base
    print("\n[EXAMPLE 6] Exporting Knowledge Base")
    print("-" * 70)
    agent.export_knowledge_base('markdown')
    agent.export_knowledge_base('json')
    
    # Final summary
    print("""
╔═══════════════════════════════════════════════════════════════════════╗
║                                                                       ║
║                        AI AGENT DEMO COMPLETE                         ║
║                                                                       ║
║  The agent has:                                                       ║
║  ✓ Processed and extracted equations from documents                  ║
║  ✓ Built a mathematical knowledge base                               ║
║  ✓ Generated visualizations of equations and relationships           ║
║  ✓ Created helper scripts for verification and simulation            ║
║  ✓ Exported knowledge base in multiple formats                       ║
║                                                                       ║
║  Check the 'ai_agent_workspace' directory for all outputs!           ║
║                                                                       ║
╚═══════════════════════════════════════════════════════════════════════╝
    """)
    
    # Show workspace contents
    workspace = Path("ai_agent_workspace")
    if workspace.exists():
        print("\nWorkspace Contents:")
        print("-" * 70)
        for item in workspace.rglob("*"):
            if item.is_file():
                print(f"  📄 {item.relative_to(workspace)}")
            elif item.is_dir() and item != workspace:
                print(f"  📁 {item.relative_to(workspace)}/")


def run_full_pipeline():
    """
    Run the complete AI agent pipeline with all available documents
    """
    print("\n[RUNNING FULL PIPELINE]")
    print("=" * 70)
    
    # Initialize agent
    agent = NavierStokesAIAgent()
    
    # Find all PDF documents in the root directory
    pdf_files = []
    root = Path(".")
    for pdf in root.glob("*.pdf"):
        pdf_files.append(str(pdf))
    
    # Run full pipeline
    agent.run_full_pipeline(
        pdf_paths=pdf_files if pdf_files else None,
        doc_dir="Documentation"
    )


if __name__ == "__main__":
    # Choose which mode to run
    import sys
    
    if len(sys.argv) > 1 and sys.argv[1] == "--full":
        # Run full pipeline with all documents
        run_full_pipeline()
    else:
        # Run examples
        main()
