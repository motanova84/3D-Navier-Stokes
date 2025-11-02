#!/usr/bin/env python3
"""
Intelligent Executor
Smart execution system for parameter sweep packages with multiple modes
"""

import os
import sys
import json
import argparse
import time
import subprocess
import psutil
from datetime import datetime, timedelta
from typing import Dict, List, Any, Optional


class IntelligentExecutor:
    """Intelligent executor for parameter sweep packages"""
    
    def __init__(self, package_dir: str = "parametric_sweep_packages"):
        self.package_dir = package_dir
        self.results_dir = os.path.join(package_dir, "results")
        self.logs_dir = os.path.join(package_dir, "logs")
        os.makedirs(self.results_dir, exist_ok=True)
        os.makedirs(self.logs_dir, exist_ok=True)
    
    def get_pending_packages(self, priority: Optional[str] = None) -> List[Dict[str, Any]]:
        """Get list of pending packages, optionally filtered by priority"""
        packages = []
        
        for filename in sorted(os.listdir(self.package_dir)):
            if filename.startswith("package_") and filename.endswith(".json"):
                filepath = os.path.join(self.package_dir, filename)
                try:
                    with open(filepath, 'r') as f:
                        package = json.load(f)
                    
                    if package['status'] == 'pending':
                        if priority is None or package['priority'] == priority:
                            packages.append(package)
                except Exception as e:
                    print(f"Warning: Could not load {filename}: {e}")
        
        return packages
    
    def get_next_package(self) -> Optional[Dict[str, Any]]:
        """Get the next highest priority pending package"""
        # Try HIGH priority first
        packages = self.get_pending_packages(priority='HIGH')
        if packages:
            return packages[0]
        
        # Then MEDIUM
        packages = self.get_pending_packages(priority='MEDIUM')
        if packages:
            return packages[0]
        
        # Finally LOW
        packages = self.get_pending_packages(priority='LOW')
        if packages:
            return packages[0]
        
        return None
    
    def get_cpu_usage(self) -> float:
        """Get current CPU usage percentage"""
        return psutil.cpu_percent(interval=1)
    
    def run_package(self, package_id: int) -> bool:
        """Run a specific package"""
        try:
            result = subprocess.run(
                [sys.executable, "run_package.py", "--package-id", str(package_id)],
                capture_output=True,
                text=True,
                check=True
            )
            print(result.stdout)
            return True
        except subprocess.CalledProcessError as e:
            print(f"Error running package {package_id}: {e}")
            print(e.stdout)
            print(e.stderr)
            return False
    
    def mode_next(self) -> None:
        """Execute the next highest priority package"""
        print("╔═══════════════════════════════════════════════════════════════╗")
        print("║  MODE: NEXT - Execute Next Priority Package                  ║")
        print("╚═══════════════════════════════════════════════════════════════╝")
        print()
        
        package = self.get_next_package()
        
        if package is None:
            print("✅ No pending packages found!")
            return
        
        print(f"📦 Next package: ID {package['id']} (Priority: {package['priority']})")
        print(f"   Reynolds: {package['reynolds']}")
        print(f"   Grid Size: {package['grid_size']}³")
        print(f"   Estimated Time: {package['estimated_time_minutes']} minutes")
        print()
        
        self.run_package(package['id'])
    
    def mode_continuous(self, max_hours: float) -> None:
        """Continuously execute packages until time limit"""
        print("╔═══════════════════════════════════════════════════════════════╗")
        print("║  MODE: CONTINUOUS - Execute Until Time Limit                 ║")
        print("╚═══════════════════════════════════════════════════════════════╝")
        print()
        print(f"⏱️  Time Limit: {max_hours} hours")
        print()
        
        start_time = datetime.now()
        end_time = start_time + timedelta(hours=max_hours)
        packages_completed = 0
        packages_failed = 0
        
        while datetime.now() < end_time:
            package = self.get_next_package()
            
            if package is None:
                print("✅ All packages completed!")
                break
            
            elapsed = (datetime.now() - start_time).total_seconds() / 3600
            remaining = max_hours - elapsed
            
            print(f"\n⏱️  Elapsed: {elapsed:.2f}h / Remaining: {remaining:.2f}h")
            print(f"📦 Running package {package['id']} (Priority: {package['priority']})")
            
            if self.run_package(package['id']):
                packages_completed += 1
            else:
                packages_failed += 1
            
            # Check if we have time for another package
            if remaining < 0.1:  # Less than 6 minutes remaining
                print("\n⏰ Time limit approaching, stopping execution")
                break
        
        print("\n" + "="*70)
        print("CONTINUOUS EXECUTION SUMMARY")
        print("="*70)
        print(f"Total Time: {(datetime.now() - start_time).total_seconds() / 3600:.2f} hours")
        print(f"Packages Completed: {packages_completed}")
        print(f"Packages Failed: {packages_failed}")
        print("="*70)
    
    def mode_opportunistic(self, cpu_threshold: float) -> None:
        """Execute packages only when CPU usage is below threshold"""
        print("╔═══════════════════════════════════════════════════════════════╗")
        print("║  MODE: OPPORTUNISTIC - Execute When Resources Available      ║")
        print("╚═══════════════════════════════════════════════════════════════╝")
        print()
        print(f"🖥️  CPU Threshold: {cpu_threshold}%")
        print("📊 Monitoring system resources...")
        print()
        
        check_interval = 30  # seconds
        max_checks = 100  # Maximum number of checks before stopping
        checks = 0
        packages_completed = 0
        
        while checks < max_checks:
            cpu_usage = self.get_cpu_usage()
            print(f"CPU Usage: {cpu_usage:.1f}%", end="")
            
            if cpu_usage < cpu_threshold:
                print(" - ✅ Below threshold, executing package")
                
                package = self.get_next_package()
                if package is None:
                    print("✅ All packages completed!")
                    break
                
                print(f"📦 Running package {package['id']}")
                if self.run_package(package['id']):
                    packages_completed += 1
            else:
                print(f" - ⏳ Above threshold, waiting {check_interval}s...")
                time.sleep(check_interval)
            
            checks += 1
        
        print(f"\n✅ Opportunistic execution completed: {packages_completed} packages")
    
    def mode_status(self) -> None:
        """Display execution status"""
        print("╔═══════════════════════════════════════════════════════════════╗")
        print("║  EXECUTION STATUS                                             ║")
        print("╚═══════════════════════════════════════════════════════════════╝")
        print()
        
        status_counts = {'pending': 0, 'running': 0, 'completed': 0, 'failed': 0}
        priority_counts = {'HIGH': 0, 'MEDIUM': 0, 'LOW': 0}
        
        for filename in os.listdir(self.package_dir):
            if filename.startswith("package_") and filename.endswith(".json"):
                filepath = os.path.join(self.package_dir, filename)
                try:
                    with open(filepath, 'r') as f:
                        package = json.load(f)
                    status_counts[package['status']] = status_counts.get(package['status'], 0) + 1
                    if package['status'] == 'pending':
                        priority_counts[package['priority']] += 1
                except:
                    pass
        
        print("Status Summary:")
        print(f"  ⏳ Pending:   {status_counts['pending']}")
        print(f"  🔄 Running:   {status_counts['running']}")
        print(f"  ✅ Completed: {status_counts['completed']}")
        print(f"  ❌ Failed:    {status_counts['failed']}")
        print()
        print("Pending by Priority:")
        print(f"  🔴 HIGH:   {priority_counts['HIGH']}")
        print(f"  🟡 MEDIUM: {priority_counts['MEDIUM']}")
        print(f"  🟢 LOW:    {priority_counts['LOW']}")
        print()
        
        # Show next package
        next_pkg = self.get_next_package()
        if next_pkg:
            print("Next Package to Execute:")
            print(f"  ID: {next_pkg['id']}")
            print(f"  Priority: {next_pkg['priority']}")
            print(f"  Reynolds: {next_pkg['reynolds']}")
            print(f"  Grid: {next_pkg['grid_size']}³")
            print(f"  Est. Time: {next_pkg['estimated_time_minutes']} min")


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description="Intelligent executor for parameter sweep packages"
    )
    parser.add_argument(
        "--mode",
        type=str,
        choices=["next", "continuous", "opportunistic", "status"],
        default="next",
        help="Execution mode"
    )
    parser.add_argument(
        "--max-hours",
        type=float,
        default=1.0,
        help="Maximum hours for continuous mode"
    )
    parser.add_argument(
        "--cpu-threshold",
        type=float,
        default=50.0,
        help="CPU threshold percentage for opportunistic mode"
    )
    parser.add_argument(
        "--package-dir",
        type=str,
        default="parametric_sweep_packages",
        help="Package directory"
    )
    
    args = parser.parse_args()
    
    executor = IntelligentExecutor(package_dir=args.package_dir)
    
    if args.mode == "next":
        executor.mode_next()
    elif args.mode == "continuous":
        executor.mode_continuous(args.max_hours)
    elif args.mode == "opportunistic":
        executor.mode_opportunistic(args.cpu_threshold)
    elif args.mode == "status":
        executor.mode_status()


if __name__ == "__main__":
    main()
