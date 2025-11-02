#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════
    INTELLIGENT EXECUTOR
    
    Smart execution modes:
    - Continuous: Run packages continuously for a specified duration
    - Opportunistic: Run when system resources are available
═══════════════════════════════════════════════════════════════
"""

import sys
import time
import subprocess
from pathlib import Path
from datetime import datetime, timedelta
import argparse


class IntelligentExecutor:
    """
    Intelligent package executor with multiple execution modes
    """
    
    def __init__(self, package_dir: str = "parametric_sweep_packages"):
        self.package_dir = Path(package_dir)
        
    def run_next_package(self, priority: str = None, dry_run: bool = False) -> bool:
        """
        Run the next pending package
        
        Returns:
            True if package was run, False if no packages pending
        """
        cmd = ['python3', 'run_package.py', '--next', 
               '--package-dir', str(self.package_dir)]
        
        if priority:
            cmd.extend(['--priority', priority])
        
        if dry_run:
            cmd.append('--dry-run')
        
        try:
            result = subprocess.run(cmd, check=True)
            return result.returncode == 0
        except subprocess.CalledProcessError:
            return False
    
    def continuous_mode(self, duration_hours: float = 24.0, 
                       priority: str = None, 
                       sleep_between: int = 60,
                       dry_run: bool = False):
        """
        Run packages continuously for a specified duration
        
        Args:
            duration_hours: How long to run (in hours)
            priority: Priority filter (HIGH, MEDIUM, LOW) or None
            sleep_between: Seconds to sleep between packages
            dry_run: Dry run mode
        """
        print("═"*70)
        print("  CONTINUOUS EXECUTION MODE")
        print("═"*70)
        print(f"\nDuration:    {duration_hours} hours")
        print(f"Priority:    {priority or 'ALL'}")
        print(f"Sleep time:  {sleep_between}s between packages")
        
        if dry_run:
            print("Mode:        DRY RUN")
        
        print("="*70 + "\n")
        
        start_time = datetime.now()
        end_time = start_time + timedelta(hours=duration_hours)
        packages_run = 0
        
        print(f"Started at:  {start_time.strftime('%Y-%m-%d %H:%M:%S')}")
        print(f"Will run until: {end_time.strftime('%Y-%m-%d %H:%M:%S')}")
        print()
        
        try:
            while datetime.now() < end_time:
                remaining = end_time - datetime.now()
                hours = remaining.total_seconds() / 3600
                
                print(f"\n⏰ Time remaining: {hours:.1f} hours")
                print(f"📦 Packages completed: {packages_run}")
                print()
                
                # Try to run next package
                if self.run_next_package(priority=priority, dry_run=dry_run):
                    packages_run += 1
                    print(f"\n✓ Package {packages_run} completed")
                    
                    # Sleep between packages
                    if datetime.now() < end_time:
                        print(f"💤 Sleeping for {sleep_between}s...")
                        time.sleep(sleep_between)
                else:
                    print("\n✓ No more pending packages")
                    break
            
            # Summary
            print("\n" + "═"*70)
            print("  CONTINUOUS EXECUTION COMPLETE")
            print("═"*70)
            print(f"\nTotal packages run: {packages_run}")
            print(f"Duration: {(datetime.now() - start_time).total_seconds() / 3600:.2f} hours")
            print()
            
        except KeyboardInterrupt:
            print("\n\n⚠️  Interrupted by user")
            print(f"Packages completed: {packages_run}")
            sys.exit(0)
    
    def opportunistic_mode(self, 
                          check_interval: int = 300,
                          priority: str = None,
                          dry_run: bool = False):
        """
        Run packages opportunistically when system is idle
        
        Args:
            check_interval: Seconds between checks
            priority: Priority filter
            dry_run: Dry run mode
        """
        print("═"*70)
        print("  OPPORTUNISTIC EXECUTION MODE")
        print("═"*70)
        print(f"\nCheck interval: {check_interval}s")
        print(f"Priority:       {priority or 'ALL'}")
        
        if dry_run:
            print("Mode:           DRY RUN")
        
        print("\n" + "="*70)
        print("\n⚠️  Running in background. Press Ctrl+C to stop.\n")
        
        packages_run = 0
        
        try:
            while True:
                print(f"[{datetime.now().strftime('%H:%M:%S')}] Checking for pending packages...")
                
                # Check system load (simplified - always run in this version)
                # In production, would check CPU/memory usage here
                can_run = True
                
                if can_run:
                    if self.run_next_package(priority=priority, dry_run=dry_run):
                        packages_run += 1
                        print(f"✓ Package {packages_run} completed")
                    else:
                        print("✓ No more pending packages. Monitoring continues...")
                else:
                    print("⏸️  System busy, waiting...")
                
                # Wait before next check
                print(f"💤 Sleeping for {check_interval}s...\n")
                time.sleep(check_interval)
                
        except KeyboardInterrupt:
            print("\n\n⚠️  Interrupted by user")
            print(f"Packages completed: {packages_run}")
            sys.exit(0)


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description='Intelligent executor for parametric sweeps'
    )
    
    # Execution mode
    mode_group = parser.add_mutually_exclusive_group(required=True)
    mode_group.add_argument(
        '--continuous',
        type=float,
        metavar='HOURS',
        help='Continuous mode: run for specified hours'
    )
    mode_group.add_argument(
        '--opportunistic',
        action='store_true',
        help='Opportunistic mode: run when system is idle'
    )
    
    # Common options
    parser.add_argument(
        '--priority',
        type=str,
        choices=['HIGH', 'MEDIUM', 'LOW'],
        help='Priority filter'
    )
    parser.add_argument(
        '--package-dir',
        type=str,
        default='parametric_sweep_packages',
        help='Package directory'
    )
    parser.add_argument(
        '--dry-run',
        action='store_true',
        help='Dry run mode'
    )
    
    # Mode-specific options
    parser.add_argument(
        '--sleep-between',
        type=int,
        default=60,
        help='Seconds to sleep between packages (continuous mode)'
    )
    parser.add_argument(
        '--check-interval',
        type=int,
        default=300,
        help='Seconds between checks (opportunistic mode)'
    )
    
    args = parser.parse_args()
    
    executor = IntelligentExecutor(package_dir=args.package_dir)
    
    if args.continuous:
        executor.continuous_mode(
            duration_hours=args.continuous,
            priority=args.priority,
            sleep_between=args.sleep_between,
            dry_run=args.dry_run
        )
    elif args.opportunistic:
        executor.opportunistic_mode(
            check_interval=args.check_interval,
            priority=args.priority,
            dry_run=args.dry_run
        )


if __name__ == "__main__":
    main()
