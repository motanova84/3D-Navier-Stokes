#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════
    PARAMETRIC SWEEP MONITOR
    
    Monitors and reports progress across all simulation packages
    Generates visual progress reports
═══════════════════════════════════════════════════════════════
"""

import json
from pathlib import Path
from typing import Dict, List
from datetime import datetime


class ParametricSweepMonitor:
    """
    Monitors progress of parametric sweep execution
    """
    
    def __init__(self, package_dir: str = "parametric_sweep_packages"):
        self.package_dir = Path(package_dir)
        self.results_dir = self.package_dir / "results"
        
    def load_metadata(self) -> Dict:
        """Load package metadata"""
        metadata_file = self.package_dir / "metadata.json"
        
        if not metadata_file.exists():
            return None
        
        with open(metadata_file, 'r') as f:
            return json.load(f)
    
    def get_progress(self) -> Dict:
        """
        Get overall progress statistics
        
        Returns:
            Dictionary with progress information
        """
        metadata = self.load_metadata()
        
        if not metadata:
            return {
                'error': 'No packages found',
                'total_packages': 0,
                'completed': 0,
                'pending': 0
            }
        
        total_packages = metadata['total_packages']
        total_simulations = metadata['total_simulations']
        
        # Count completed packages and simulations
        completed_packages = 0
        completed_simulations = 0
        failed_simulations = 0
        
        progress_by_priority = {
            'HIGH': {'total': 0, 'completed': 0, 'pending': 0},
            'MEDIUM': {'total': 0, 'completed': 0, 'pending': 0},
            'LOW': {'total': 0, 'completed': 0, 'pending': 0}
        }
        
        for pkg_info in metadata['packages']:
            priority = pkg_info['priority']
            progress_by_priority[priority]['total'] += 1
            
            # Check if results exist
            results_file = self.results_dir / f"package_{pkg_info['package_id']:04d}_results.json"
            
            if results_file.exists():
                completed_packages += 1
                progress_by_priority[priority]['completed'] += 1
                
                # Load results to count simulations
                with open(results_file, 'r') as f:
                    results = json.load(f)
                    completed_simulations += results.get('completed', 0)
                    failed_simulations += results.get('failed', 0)
            else:
                progress_by_priority[priority]['pending'] += 1
        
        pending_packages = total_packages - completed_packages
        pending_simulations = total_simulations - completed_simulations - failed_simulations
        
        return {
            'total_packages': total_packages,
            'completed_packages': completed_packages,
            'pending_packages': pending_packages,
            'total_simulations': total_simulations,
            'completed_simulations': completed_simulations,
            'failed_simulations': failed_simulations,
            'pending_simulations': pending_simulations,
            'progress_by_priority': progress_by_priority,
            'completion_percentage': (completed_packages / total_packages * 100) if total_packages > 0 else 0
        }
    
    def get_package_status(self, package_id: int) -> Dict:
        """Get status of a specific package"""
        results_file = self.results_dir / f"package_{package_id:04d}_results.json"
        
        if not results_file.exists():
            return {'status': 'pending', 'package_id': package_id}
        
        with open(results_file, 'r') as f:
            return json.load(f)
    
    def print_progress_report(self):
        """Print a formatted progress report"""
        print("\n" + "═"*70)
        print("  PARAMETRIC SWEEP PROGRESS REPORT")
        print("═"*70 + "\n")
        
        progress = self.get_progress()
        
        if 'error' in progress:
            print(f"❌ {progress['error']}")
            return
        
        # Overall progress
        print("📊 OVERALL PROGRESS")
        print("-"*70)
        print(f"  Packages:    {progress['completed_packages']}/{progress['total_packages']} "
              f"({progress['completion_percentage']:.1f}% complete)")
        print(f"  Simulations: {progress['completed_simulations']}/{progress['total_simulations']} completed")
        
        if progress['failed_simulations'] > 0:
            print(f"  Failed:      {progress['failed_simulations']} simulations")
        
        # Progress bar
        bar_length = 50
        filled = int(bar_length * progress['completion_percentage'] / 100)
        bar = "█" * filled + "░" * (bar_length - filled)
        print(f"\n  [{bar}] {progress['completion_percentage']:.1f}%\n")
        
        # By priority
        print("🎯 PROGRESS BY PRIORITY")
        print("-"*70)
        
        for priority in ['HIGH', 'MEDIUM', 'LOW']:
            stats = progress['progress_by_priority'][priority]
            total = stats['total']
            completed = stats['completed']
            pending = stats['pending']
            
            if total > 0:
                pct = (completed / total * 100)
                bar_len = 30
                filled = int(bar_len * pct / 100)
                bar = "█" * filled + "░" * (bar_len - filled)
                
                print(f"  {priority:6s}: [{bar}] {completed}/{total} "
                      f"({pct:.0f}% complete, {pending} pending)")
        
        print("\n" + "═"*70 + "\n")
    
    def generate_detailed_report(self, output_file: str = None) -> str:
        """
        Generate detailed markdown report
        
        Args:
            output_file: Path to save report, or None for console
            
        Returns:
            Report as string
        """
        progress = self.get_progress()
        
        if 'error' in progress:
            return f"# Error\n\n{progress['error']}\n"
        
        # Build report
        report = []
        report.append("# Parametric Sweep Progress Report")
        report.append("")
        report.append(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        report.append("")
        
        # Summary
        report.append("## Summary")
        report.append("")
        report.append(f"- **Total Packages**: {progress['total_packages']}")
        report.append(f"- **Completed Packages**: {progress['completed_packages']}")
        report.append(f"- **Pending Packages**: {progress['pending_packages']}")
        report.append(f"- **Total Simulations**: {progress['total_simulations']}")
        report.append(f"- **Completed Simulations**: {progress['completed_simulations']}")
        report.append(f"- **Failed Simulations**: {progress['failed_simulations']}")
        report.append(f"- **Overall Progress**: {progress['completion_percentage']:.1f}%")
        report.append("")
        
        # By priority
        report.append("## Progress by Priority")
        report.append("")
        report.append("| Priority | Total | Completed | Pending | Progress |")
        report.append("|----------|-------|-----------|---------|----------|")
        
        for priority in ['HIGH', 'MEDIUM', 'LOW']:
            stats = progress['progress_by_priority'][priority]
            if stats['total'] > 0:
                pct = (stats['completed'] / stats['total'] * 100)
                report.append(f"| {priority} | {stats['total']} | "
                            f"{stats['completed']} | {stats['pending']} | "
                            f"{pct:.1f}% |")
        
        report.append("")
        
        # Package details
        report.append("## Package Details")
        report.append("")
        
        metadata = self.load_metadata()
        for pkg_info in metadata['packages']:
            pkg_id = pkg_info['package_id']
            priority = pkg_info['priority']
            
            results_file = self.results_dir / f"package_{pkg_id:04d}_results.json"
            
            if results_file.exists():
                with open(results_file, 'r') as f:
                    results = json.load(f)
                    status = f"✓ Completed ({results['completed']}/{results['total_simulations']} successful)"
            else:
                status = "⏳ Pending"
            
            report.append(f"- **Package {pkg_id:04d}** [{priority}]: {status}")
        
        report_text = "\n".join(report)
        
        # Save to file if requested
        if output_file:
            output_path = Path(output_file)
            output_path.parent.mkdir(exist_ok=True, parents=True)
            with open(output_path, 'w') as f:
                f.write(report_text)
            print(f"✓ Detailed report saved to: {output_file}")
        
        return report_text


def main():
    """Main entry point"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Monitor parametric sweep progress'
    )
    parser.add_argument(
        '--package-dir',
        type=str,
        default='parametric_sweep_packages',
        help='Package directory'
    )
    parser.add_argument(
        '--detailed',
        action='store_true',
        help='Generate detailed markdown report'
    )
    parser.add_argument(
        '--output',
        type=str,
        help='Output file for detailed report'
    )
    
    args = parser.parse_args()
    
    monitor = ParametricSweepMonitor(package_dir=args.package_dir)
    
    if args.detailed:
        output_file = args.output or str(monitor.package_dir / "progress_report.md")
        report = monitor.generate_detailed_report(output_file)
        if not args.output:
            print(report)
    else:
        monitor.print_progress_report()


if __name__ == "__main__":
    main()
