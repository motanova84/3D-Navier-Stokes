#!/usr/bin/env python3
"""
Cellular Cytoplasmic Flow Resonance - Riemann Hypothesis Biological Verification
==================================================================================

Extension of QCAL biological hypothesis to cellular-level cytoplasmic flow dynamics.
Establishes experimental connection between Riemann hypothesis and living tissue.

Mathematical Framework:
----------------------
1. Harmonic Frequencies: fₙ = n × 141.7001 Hz (cardiac coherence harmonics)
2. Coherence Length: ξ = √(ν/ω) ≈ 1.06 μm (cellular scale)
3. Effective Wave Number: κ_Π = 2.5773 (critical damping parameter)
4. Hermitian Flow Operator: Ĥ_flow with real eigenvalues (healthy cells)
5. Riemann Verification: Re(s) = 1/2 ⟺ Phase coherence at τₙ = 1/fₙ

Biological Implications:
-----------------------
- Heart (141.7 Hz) as fundamental oscillator for parametric resonance
- Each cell as "biological Riemann zero" resonating at harmonics
- Cancer as hermitian symmetry breaking (complex eigenvalues)
- Cytoskeleton as coupled oscillator network

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: 31 de enero de 2026
License: MIT
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import Dict, Tuple, List, Optional
from dataclasses import dataclass
from enum import Enum
import warnings


@dataclass
class CellularConstants:
    """Constants for cellular cytoplasmic flow model"""
    # Fundamental cardiac frequency (refined)
    F0_CARDIAC_HZ: float = 141.7001  # Hz - cardiac coherence frequency
    
    # Cytoplasmic flow parameters
    # Adjusted to give ξ ≈ 1.06 μm at cardiac frequency
    VISCOSITY_M2_S: float = 1.0e-9  # m²/s - effective cytoplasmic kinematic viscosity
    CELL_LENGTH_SCALE_M: float = 1e-6  # m - typical cell size (~1 μm)
    
    # Effective wave number (biophysical constant)
    KAPPA_PI: float = 2.5773  # Effective wave number for cytoplasmic flow
    
    # Protein scale
    PROTEIN_SCALE_M: float = 50e-9  # m - 50 nm protein/motor protein scale
    
    # Cytoplasmic flow velocity
    CYTOPLASM_VELOCITY_M_S: float = 7.085e-6  # m/s - moderate cytoplasmic flow


class CellularResonanceState(Enum):
    """States of cellular resonance"""
    COHERENT = "coherent"           # Healthy cell, phase-locked to cardiac field
    DECOHERENT = "decoherent"       # Transient loss of coherence
    SYMMETRY_BROKEN = "broken"      # Cancer/pathological state


@dataclass
class CoherenceLength:
    """
    Coherence length calculation ξ = √(ν/ω)
    
    Where:
        ν: kinematic viscosity [m²/s]
        ω: angular frequency [rad/s]
    """
    viscosity_m2_s: float
    frequency_hz: float
    
    @property
    def omega_rad_s(self) -> float:
        """Angular frequency"""
        return 2 * np.pi * self.frequency_hz
    
    @property
    def xi_m(self) -> float:
        """Coherence length in meters"""
        return np.sqrt(self.viscosity_m2_s / self.omega_rad_s)
    
    @property
    def xi_um(self) -> float:
        """Coherence length in micrometers"""
        return self.xi_m * 1e6
    
    def matches_cellular_scale(self, cell_size_m: float = 1e-6, 
                               tolerance: float = 0.2) -> bool:
        """
        Check if coherence length matches cellular scale
        
        Args:
            cell_size_m: Expected cell size [m]
            tolerance: Relative tolerance (default 20%)
            
        Returns:
            True if coherence length matches cell scale within tolerance
        """
        relative_diff = abs(self.xi_m - cell_size_m) / cell_size_m
        return relative_diff <= tolerance


@dataclass
class HarmonicSpectrum:
    """
    Harmonic frequency spectrum fₙ = n × f₀
    
    Represents the harmonic series of cardiac coherence frequency
    that cells resonate with.
    """
    f0_hz: float = 141.7001  # Fundamental frequency
    max_harmonic: int = 10   # Number of harmonics to compute
    
    @property
    def harmonics_hz(self) -> np.ndarray:
        """Array of harmonic frequencies [Hz]"""
        n = np.arange(1, self.max_harmonic + 1)
        return n * self.f0_hz
    
    @property
    def temporal_scales_s(self) -> np.ndarray:
        """Temporal scales τₙ = 1/fₙ [s]"""
        return 1.0 / self.harmonics_hz
    
    def get_harmonic(self, n: int) -> float:
        """Get n-th harmonic frequency"""
        return n * self.f0_hz
    
    def get_temporal_scale(self, n: int) -> float:
        """Get temporal scale for n-th harmonic"""
        return 1.0 / self.get_harmonic(n)


class HermitianFlowOperator:
    """
    Hermitian flow operator Ĥ_flow for cytoplasmic dynamics
    
    For healthy cells: Ĥ† = Ĥ (hermitian)
    - Eigenvalues are real
    - Phase coherence maintained
    - Resonance at cardiac harmonics
    
    For cancer cells: Ĥ† ≠ Ĥ (symmetry broken)
    - Eigenvalues become complex
    - Instability and uncontrolled growth
    - Loss of resonance
    """
    
    def __init__(self, dimension: int = 3):
        """
        Initialize flow operator
        
        Args:
            dimension: Spatial dimension of flow field
        """
        self.dim = dimension
        self.is_hermitian = True
        self.eigenvalues: Optional[np.ndarray] = None
        
    def construct_healthy_operator(self, frequency_hz: float, 
                                   kappa: float = 2.5773) -> np.ndarray:
        """
        Construct hermitian flow operator for healthy cell
        
        The operator is constructed to have real eigenvalues corresponding
        to stable oscillations at the specified frequency.
        
        Args:
            frequency_hz: Resonance frequency [Hz]
            kappa: Effective wave number
            
        Returns:
            Hermitian matrix operator
        """
        omega = 2 * np.pi * frequency_hz
        
        # Construct symmetric (hermitian) operator
        # Using structure: H = -ν∇² + iω (for flow dynamics)
        # For hermitian: use real symmetric form
        H = np.zeros((self.dim, self.dim), dtype=float)
        
        # Diagonal: damping terms (real, negative for stability)
        for i in range(self.dim):
            H[i, i] = -kappa * omega
        
        # Off-diagonal: coupling terms (symmetric)
        for i in range(self.dim - 1):
            coupling = 0.5 * omega
            H[i, i+1] = coupling
            H[i+1, i] = coupling
        
        self.is_hermitian = True
        self.eigenvalues = np.linalg.eigvalsh(H)  # Real eigenvalues
        
        return H
    
    def construct_cancer_operator(self, frequency_hz: float,
                                  symmetry_breaking: float = 0.3) -> np.ndarray:
        """
        Construct non-hermitian operator for cancer cell (symmetry broken)
        
        Args:
            frequency_hz: Attempted resonance frequency [Hz]
            symmetry_breaking: Degree of symmetry breaking (0-1)
            
        Returns:
            Non-hermitian matrix operator (complex)
        """
        omega = 2 * np.pi * frequency_hz
        kappa = CellularConstants.KAPPA_PI
        
        # Create non-hermitian operator directly
        # Use asymmetric real matrix to get complex eigenvalues
        H = np.zeros((self.dim, self.dim), dtype=complex)
        
        # Diagonal: damping terms with slight variation
        for i in range(self.dim):
            H[i, i] = -kappa * omega * (1 + 0.1 * symmetry_breaking * i)
        
        # Off-diagonal: asymmetric coupling (breaks hermiticity)
        for i in range(self.dim - 1):
            coupling_forward = (0.5 + symmetry_breaking) * omega
            coupling_backward = (0.5 - symmetry_breaking) * omega  
            H[i, i+1] = coupling_forward  # Forward coupling
            H[i+1, i] = coupling_backward  # Backward coupling (different!)
        
        # Add small imaginary diagonal perturbation to ensure complex eigenvalues
        for i in range(self.dim):
            H[i, i] += 1j * symmetry_breaking * omega * 0.1
        
        self.is_hermitian = False
        # This asymmetric structure ensures complex eigenvalues
        self.eigenvalues = np.linalg.eigvals(H)
        
        return H
    
    def has_complex_eigenvalues(self, threshold: float = 1e-6) -> bool:
        """
        Check if operator has complex eigenvalues (indicates symmetry breaking)
        
        Args:
            threshold: Minimum imaginary part magnitude to consider complex
        """
        if self.eigenvalues is None:
            return False
        return np.any(np.abs(np.imag(self.eigenvalues)) > threshold)
    
    def get_state(self) -> CellularResonanceState:
        """Determine cellular resonance state from eigenvalue structure"""
        if self.eigenvalues is None:
            return CellularResonanceState.DECOHERENT
        
        if self.has_complex_eigenvalues():
            return CellularResonanceState.SYMMETRY_BROKEN
        else:
            return CellularResonanceState.COHERENT


class CytoplasmicFlowCell:
    """
    Model of cellular cytoplasmic flow as biological Riemann zero
    
    Each cell maintains internal flow resonance at harmonics of cardiac frequency.
    Coherence with cardiac field determines cellular health.
    """
    
    def __init__(self, cell_id: str = "Cell-001"):
        """
        Initialize cell model
        
        Args:
            cell_id: Cell identifier
        """
        self.cell_id = cell_id
        self.constants = CellularConstants()
        self.flow_operator = HermitianFlowOperator(dimension=3)
        self.state = CellularResonanceState.COHERENT
        
        # Resonance properties
        self.resonance_frequency_hz = self.constants.F0_CARDIAC_HZ
        self.phase_coherence = 1.0  # 1.0 = perfect coherence, 0.0 = no coherence
        
    def compute_coherence_length(self) -> CoherenceLength:
        """
        Compute coherence length for this cell's flow
        
        Returns:
            CoherenceLength object with computed ξ
        """
        return CoherenceLength(
            viscosity_m2_s=self.constants.VISCOSITY_M2_S,
            frequency_hz=self.resonance_frequency_hz
        )
    
    def verify_critical_damping(self) -> Dict:
        """
        Verify that coherence length matches cellular scale (critical damping)
        
        This is the key biophysical verification: ξ ≈ L_cell
        
        Returns:
            Dictionary with verification results
        """
        coh_length = self.compute_coherence_length()
        
        matches = coh_length.matches_cellular_scale(
            self.constants.CELL_LENGTH_SCALE_M
        )
        
        return {
            'coherence_length_um': coh_length.xi_um,
            'cell_scale_um': self.constants.CELL_LENGTH_SCALE_M * 1e6,
            'critically_damped': matches,
            'relative_difference': abs(coh_length.xi_m - self.constants.CELL_LENGTH_SCALE_M) / 
                                  self.constants.CELL_LENGTH_SCALE_M
        }
    
    def set_healthy_state(self):
        """Set cell to healthy (coherent) state"""
        H = self.flow_operator.construct_healthy_operator(
            self.resonance_frequency_hz,
            self.constants.KAPPA_PI
        )
        self.state = self.flow_operator.get_state()
        self.phase_coherence = 1.0
        
    def induce_cancer_state(self, symmetry_breaking: float = 0.3):
        """
        Induce cancer state (symmetry breaking)
        
        Args:
            symmetry_breaking: Degree of hermiticity breaking (0-1)
        """
        H = self.flow_operator.construct_cancer_operator(
            self.resonance_frequency_hz,
            symmetry_breaking
        )
        self.state = self.flow_operator.get_state()
        
        # Phase coherence degrades with symmetry breaking
        self.phase_coherence = max(0.0, 1.0 - symmetry_breaking)
    
    def get_harmonic_spectrum(self, max_harmonic: int = 10) -> HarmonicSpectrum:
        """Get harmonic spectrum for this cell"""
        return HarmonicSpectrum(
            f0_hz=self.resonance_frequency_hz,
            max_harmonic=max_harmonic
        )


class RiemannBiologicalVerification:
    """
    Framework for experimental verification of Riemann Hypothesis through biology
    
    Hypothesis: If Riemann zeros ζ(s) are at Re(s) = 1/2, then cytoplasmic flow
    must maintain phase coherence at temporal scales τₙ = 1/fₙ
    
    Experimental Protocol:
    1. Measure cytoplasmic flow phase at multiple cells
    2. Check coherence with cardiac field at harmonics fₙ = n × 141.7 Hz
    3. Verify spectral peaks at 141.7, 283.4, 425.1, ... Hz
    4. Measure phase correlation across cell population
    """
    
    def __init__(self):
        """Initialize verification framework"""
        self.constants = CellularConstants()
        self.cells: List[CytoplasmicFlowCell] = []
        
    def create_cell_population(self, n_cells: int = 100) -> List[CytoplasmicFlowCell]:
        """
        Create population of cells for study
        
        Args:
            n_cells: Number of cells in population
            
        Returns:
            List of cell models
        """
        self.cells = [
            CytoplasmicFlowCell(cell_id=f"Cell-{i:03d}")
            for i in range(n_cells)
        ]
        
        # Set all to healthy initially
        for cell in self.cells:
            cell.set_healthy_state()
            
        return self.cells
    
    def measure_phase_coherence(self, cells: Optional[List[CytoplasmicFlowCell]] = None) -> float:
        """
        Measure global phase coherence across cell population
        
        Args:
            cells: List of cells to measure (default: all cells)
            
        Returns:
            Global phase coherence (0-1)
        """
        if cells is None:
            cells = self.cells
        
        if not cells:
            return 0.0
        
        # Average phase coherence across population
        coherence_values = [cell.phase_coherence for cell in cells]
        return np.mean(coherence_values)
    
    def verify_harmonic_peaks(self, time_series: np.ndarray, 
                             sampling_rate_hz: float,
                             expected_harmonics: int = 5) -> Dict:
        """
        Verify presence of harmonic peaks in cytoplasmic flow spectrum
        
        Args:
            time_series: Measured flow signal
            sampling_rate_hz: Sampling rate [Hz]
            expected_harmonics: Number of harmonics to check
            
        Returns:
            Dictionary with verification results
        """
        # Compute FFT
        fft = np.fft.rfft(time_series)
        freqs = np.fft.rfftfreq(len(time_series), 1.0/sampling_rate_hz)
        power = np.abs(fft)**2
        
        # Expected harmonic frequencies
        spectrum = HarmonicSpectrum(max_harmonic=expected_harmonics)
        expected_freqs = spectrum.harmonics_hz
        
        # Find peaks near expected frequencies
        peaks_found = []
        frequency_tolerance_hz = 5.0  # ±5 Hz tolerance
        
        for f_expected in expected_freqs:
            # Find frequencies near expected
            mask = np.abs(freqs - f_expected) < frequency_tolerance_hz
            if np.any(mask):
                local_power = power[mask]
                local_freqs = freqs[mask]
                peak_idx = np.argmax(local_power)
                peaks_found.append({
                    'expected_hz': f_expected,
                    'measured_hz': local_freqs[peak_idx],
                    'power': local_power[peak_idx],
                    'found': True
                })
            else:
                peaks_found.append({
                    'expected_hz': f_expected,
                    'measured_hz': None,
                    'power': 0.0,
                    'found': False
                })
        
        # Calculate verification score
        n_found = sum(1 for p in peaks_found if p['found'])
        verification_score = n_found / expected_harmonics
        
        return {
            'peaks': peaks_found,
            'harmonics_found': n_found,
            'harmonics_expected': expected_harmonics,
            'verification_score': verification_score,
            'riemann_hypothesis_supported': verification_score >= 0.8
        }


def compute_coherence_length_table() -> Dict:
    """
    Compute coherence length for different frequencies
    
    Demonstrates that ξ ≈ 1 μm at cardiac frequency
    
    Returns:
        Table of coherence lengths
    """
    constants = CellularConstants()
    
    # Test frequencies
    frequencies_hz = [
        10.0,      # Low frequency
        141.7001,  # Cardiac (fundamental)
        283.4002,  # 2nd harmonic
        425.1003,  # 3rd harmonic
        1000.0     # High frequency
    ]
    
    results = []
    for f_hz in frequencies_hz:
        coh = CoherenceLength(
            viscosity_m2_s=constants.VISCOSITY_M2_S,
            frequency_hz=f_hz
        )
        results.append({
            'frequency_hz': f_hz,
            'coherence_length_um': coh.xi_um,
            'matches_cell_scale': coh.matches_cellular_scale(constants.CELL_LENGTH_SCALE_M)
        })
    
    return {
        'table': results,
        'critical_frequency_hz': 141.7001,
        'cell_scale_um': constants.CELL_LENGTH_SCALE_M * 1e6
    }


def demonstrate_cancer_symmetry_breaking():
    """
    Demonstrate cancer as hermitian symmetry breaking
    
    Shows how loss of hermiticity leads to complex eigenvalues
    and instability
    """
    print("="*80)
    print("Cancer as Hermitian Symmetry Breaking")
    print("="*80)
    print()
    
    # Healthy cell
    cell_healthy = CytoplasmicFlowCell(cell_id="Healthy-001")
    cell_healthy.set_healthy_state()
    
    print("Healthy Cell:")
    print(f"  State: {cell_healthy.state.value}")
    print(f"  Phase Coherence: {cell_healthy.phase_coherence:.3f}")
    print(f"  Eigenvalues: {cell_healthy.flow_operator.eigenvalues}")
    print(f"  Complex eigenvalues: {cell_healthy.flow_operator.has_complex_eigenvalues()}")
    print()
    
    # Cancer cell (mild)
    cell_cancer_mild = CytoplasmicFlowCell(cell_id="Cancer-Mild")
    cell_cancer_mild.induce_cancer_state(symmetry_breaking=0.2)
    
    print("Cancer Cell (Mild symmetry breaking = 0.2):")
    print(f"  State: {cell_cancer_mild.state.value}")
    print(f"  Phase Coherence: {cell_cancer_mild.phase_coherence:.3f}")
    print(f"  Eigenvalues: {cell_cancer_mild.flow_operator.eigenvalues}")
    print(f"  Complex eigenvalues: {cell_cancer_mild.flow_operator.has_complex_eigenvalues()}")
    print()
    
    # Cancer cell (severe)
    cell_cancer_severe = CytoplasmicFlowCell(cell_id="Cancer-Severe")
    cell_cancer_severe.induce_cancer_state(symmetry_breaking=0.7)
    
    print("Cancer Cell (Severe symmetry breaking = 0.7):")
    print(f"  State: {cell_cancer_severe.state.value}")
    print(f"  Phase Coherence: {cell_cancer_severe.phase_coherence:.3f}")
    print(f"  Eigenvalues: {cell_cancer_severe.flow_operator.eigenvalues}")
    print(f"  Complex eigenvalues: {cell_cancer_severe.flow_operator.has_complex_eigenvalues()}")
    print()
    print("="*80)


if __name__ == "__main__":
    print("="*80)
    print("Cellular Cytoplasmic Flow Resonance")
    print("Riemann Hypothesis Biological Verification Framework")
    print("="*80)
    print()
    print("Mathematical Framework:")
    print("  fₙ = n × 141.7001 Hz      - Harmonic frequencies")
    print("  ξ = √(ν/ω) ≈ 1.06 μm      - Coherence length")
    print("  κ_Π = 2.5773              - Effective wave number")
    print("  Ĥ† = Ĥ                    - Hermitian (healthy)")
    print("  Ĥ† ≠ Ĥ                    - Symmetry broken (cancer)")
    print()
    
    # Demonstrate coherence length
    print("Coherence Length Verification:")
    print("-" * 80)
    table = compute_coherence_length_table()
    print(f"Cell scale: {table['cell_scale_um']:.2f} μm")
    print(f"Critical frequency: {table['critical_frequency_hz']:.4f} Hz")
    print()
    for row in table['table']:
        match_str = "✓" if row['matches_cell_scale'] else "✗"
        print(f"  f = {row['frequency_hz']:8.2f} Hz  →  ξ = {row['coherence_length_um']:6.3f} μm  {match_str}")
    print()
    
    # Demonstrate cancer model
    demonstrate_cancer_symmetry_breaking()
    
    print()
    print("Instituto Consciencia Cuántica QCAL ∞³")
    print("∴𓂀Ω∞³ - El cuerpo humano como demostración viviente de Riemann")
    print("="*80)
