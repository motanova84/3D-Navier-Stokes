#!/usr/bin/env python3
"""
Integration Demo: AI Agent + Verification Framework

This script demonstrates how the AI agent integrates with the
existing Navier-Stokes verification framework.
"""

from ai_agent import NavierStokesAIAgent
import sys


def demo_agent_features():
    """Demonstrate AI agent capabilities"""
    
    print("="*70)
    print("AI AGENT INTEGRATION DEMO")
    print("="*70)
    print()
    
    # Initialize agent
    print("[1/5] Initializing AI Agent...")
    agent = NavierStokesAIAgent(workspace_dir="demo_workspace")
    print("✓ Agent initialized")
    print()
    
    # Process documentation
    print("[2/5] Processing Documentation...")
    results = agent.process_documentation("Documentation")
    print(f"✓ Processed {results['files_processed']} files")
    print(f"✓ Extracted {results['total_equations']} equations")
    print()
    
    # Show knowledge summary
    print("[3/5] Knowledge Base Summary:")
    summary = agent.memory.get_summary()
    print(f"  - Total Equations: {summary['total_equations']}")
    print(f"  - Total Constants: {summary['total_constants']}")
    print(f"  - Total Theorems: {summary['total_theorems']}")
    print()
    
    # Search for specific topics
    print("[4/5] Searching for Key Topics:")
    
    topics = {
        "BKM": "Beale-Kato-Majda criterion",
        "Riccati": "Riccati inequalities",
        "ν": "Viscosity parameter",
        "vorticity": "Vorticity equations"
    }
    
    for keyword, description in topics.items():
        results = agent.memory.search(keyword)
        count = sum(len(items) for items in results.values())
        print(f"  - {description} ({keyword}): {count} results")
    print()
    
    # Generate scripts
    print("[5/5] Generating Helper Scripts...")
    agent.generate_scripts()
    print("✓ Scripts generated in demo_workspace/generated_scripts/")
    print()
    
    # Export knowledge base
    print("Exporting Knowledge Base...")
    agent.export_knowledge_base('markdown')
    agent.export_knowledge_base('json')
    print("✓ Knowledge base exported")
    print()
    
    # Show specific equations
    print("="*70)
    print("SAMPLE EQUATIONS FROM KNOWLEDGE BASE")
    print("="*70)
    print()
    
    # Get BKM criterion
    bkm = agent.memory.get_equation("BKM Criterion")
    if bkm:
        print("BKM Criterion (Beale-Kato-Majda):")
        print(f"  Formula: {bkm['formula']}")
        print(f"  Description: {bkm['description']}")
        print()
    
    # Get constants
    print("Key Constants:")
    for const_name in ["ν", "C_BKM", "δ*"]:
        const = agent.memory.get_constant(const_name)
        if const:
            print(f"  {const['name']}: {const['description']}")
            if const.get('typical_value'):
                print(f"    Typical value: {const['typical_value']}")
    print()
    
    # Integration example
    print("="*70)
    print("INTEGRATION WITH VERIFICATION FRAMEWORK")
    print("="*70)
    print()
    
    print("The AI agent can be integrated with the existing framework:")
    print()
    print("```python")
    print("from ai_agent import NavierStokesAIAgent")
    print("from verification_framework import FinalProof")
    print()
    print("# Extract constants using AI agent")
    print("agent = NavierStokesAIAgent()")
    print("agent.process_documentation('Documentation')")
    print()
    print("# Get viscosity constant")
    print("nu_const = agent.memory.get_constant('ν')")
    print("nu = float(nu_const['typical_value'].split()[0])")
    print()
    print("# Use in verification framework")
    print("proof = FinalProof(ν=nu)")
    print("results = proof.prove_global_regularity(")
    print("    T_max=100.0,")
    print("    X0=10.0,")
    print("    u0_L3_norm=1.0")
    print(")")
    print()
    print("print(f'Global regularity: {results[\"global_regularity\"]}')")
    print("```")
    print()
    
    # Show generated files
    print("="*70)
    print("GENERATED FILES")
    print("="*70)
    print()
    
    import os
    from pathlib import Path
    
    workspace = Path("demo_workspace")
    if workspace.exists():
        print("Files created in demo_workspace/:")
        for root, dirs, files in os.walk(workspace):
            level = root.replace(str(workspace), '').count(os.sep)
            indent = ' ' * 2 * level
            print(f"{indent}{os.path.basename(root)}/")
            subindent = ' ' * 2 * (level + 1)
            for file in files:
                filepath = Path(root) / file
                size = filepath.stat().st_size
                if size > 1024*1024:
                    size_str = f"{size/(1024*1024):.1f} MB"
                elif size > 1024:
                    size_str = f"{size/1024:.1f} KB"
                else:
                    size_str = f"{size} B"
                print(f"{subindent}{file} ({size_str})")
    print()
    
    print("="*70)
    print("DEMO COMPLETE!")
    print("="*70)
    print()
    print("Next steps:")
    print("1. Explore the generated scripts in demo_workspace/generated_scripts/")
    print("2. Review the knowledge base in demo_workspace/knowledge_base.md")
    print("3. Run the generated verification script:")
    print("   python demo_workspace/generated_scripts/verify_equations.py")
    print("4. Try the simulation script:")
    print("   python demo_workspace/generated_scripts/simulate_ns.py")
    print()


def demo_search_capabilities():
    """Demonstrate search capabilities"""
    
    print("="*70)
    print("SEARCH CAPABILITIES DEMO")
    print("="*70)
    print()
    
    agent = NavierStokesAIAgent(workspace_dir="demo_workspace")
    
    # If not already processed, process documentation
    summary = agent.memory.get_summary()
    if summary['total_equations'] < 100:
        print("Processing documentation first...")
        agent.process_documentation("Documentation")
        print()
    
    queries = [
        ("BKM", "BKM criterion and related concepts"),
        ("Riccati", "Riccati inequalities and differential equations"),
        ("Besov", "Besov spaces and norms"),
        ("energy", "Energy estimates and bounds"),
        ("viscosity", "Viscosity and damping"),
    ]
    
    for query, description in queries:
        print(f"Searching for: {description}")
        print(f"Query: '{query}'")
        print("-" * 70)
        
        results = agent.memory.search(query)
        
        if results:
            for category, items in results.items():
                if items:
                    print(f"\n  {category.upper()} ({len(items)} results):")
                    for item in items[:3]:  # Show first 3
                        name = item['data'].get('name', item['id'])
                        print(f"    • {name}")
                    
                    if len(items) > 3:
                        print(f"    ... and {len(items)-3} more")
        else:
            print("  No results found")
        
        print()
    
    print("="*70)


def demo_script_generation():
    """Demonstrate script generation"""
    
    print("="*70)
    print("SCRIPT GENERATION DEMO")
    print("="*70)
    print()
    
    agent = NavierStokesAIAgent(workspace_dir="demo_workspace")
    
    # Process some documentation if needed
    summary = agent.memory.get_summary()
    if summary['total_equations'] < 10:
        print("Loading knowledge base...")
        agent.process_documentation("Documentation")
        print()
    
    print("Generating specialized scripts...")
    print()
    
    # Generate all scripts
    agent.generate_scripts()
    
    print("Generated scripts:")
    print()
    
    scripts = [
        ("verify_equations.py", "Equation verification framework", 
         "Tests mathematical properties and inequalities"),
        ("simulate_ns.py", "3D Navier-Stokes simulator",
         "Pseudo-spectral DNS solver with QCAL framework"),
        ("analyze_results.py", "Results analysis tools",
         "Statistical analysis and BKM verification"),
        ("visualize_data.py", "Data visualization",
         "Plot velocity fields, vorticity, and energy spectra"),
    ]
    
    for filename, title, description in scripts:
        print(f"📄 {filename}")
        print(f"   Title: {title}")
        print(f"   Description: {description}")
        
        # Check file size
        filepath = Path("demo_workspace/generated_scripts") / filename
        if filepath.exists():
            size = filepath.stat().st_size
            if size > 1024:
                print(f"   Size: {size/1024:.1f} KB")
            else:
                print(f"   Size: {size} B")
        print()
    
    print("="*70)


def main():
    """Main function"""
    
    if len(sys.argv) > 1:
        if sys.argv[1] == "--search":
            demo_search_capabilities()
        elif sys.argv[1] == "--scripts":
            demo_script_generation()
        else:
            print(f"Unknown option: {sys.argv[1]}")
            print("Usage: python demo_integration.py [--search|--scripts]")
    else:
        # Run main demo
        demo_agent_features()


if __name__ == "__main__":
    main()
