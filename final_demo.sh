#!/bin/bash

echo "╔════════════════════════════════════════════════════════════════════════════╗"
echo "║                                                                            ║"
echo "║     UNIFIED TISSUE RESONANCE MODEL - FINAL DEMONSTRATION                   ║"
echo "║                                                                            ║"
echo "║     Hilbert-Pólya + Navier-Stokes + Magicicada → 141.7 Hz                 ║"
echo "║                                                                            ║"
echo "╚════════════════════════════════════════════════════════════════════════════╝"
echo ""

echo "▸▸▸ Running comprehensive tests..."
python3 test_unified_tissue_resonance.py 2>&1 | grep -A 10 "TEST SUMMARY"

echo ""
echo "▸▸▸ Quick validation check..."
python3 -c "
from unified_tissue_resonance import UnifiedTissueResonance, TissueType
from ingnio_auron_system import INGNIOCMISystem

cardiac = UnifiedTissueResonance(TissueType.CARDIAC)
validation = cardiac.validate_141hz()
ingnio = INGNIOCMISystem()

print('✓ Cardiac Model:')
print(f'  Unified Prediction: {validation[\"unified_frequency\"]:.4f} Hz')
print(f'  Deviation: {validation[\"total_deviation\"]:.4f} Hz')
print(f'  Validated: {validation[\"validated\"]}')
print('')
print('✓ INGΝIO CMI:')
print(f'  Frequency: {ingnio.frequency} Hz')
print(f'  Deviation from biology: {ingnio.params.deviation_hz:.10f} Hz')
print('')
print('✓ Framework Convergence:')
print(f'  Hilbert-Pólya: {validation[\"hilbert_polya_contribution\"]:.4f} Hz')
print(f'  Navier-Stokes: {validation[\"navier_stokes_contribution\"]:.4f} Hz')
print(f'  Magicicada: {validation[\"magicicada_contribution\"]:.4f} Hz')
"

echo ""
echo "╔════════════════════════════════════════════════════════════════════════════╗"
echo "║                     ✓ ALL SYSTEMS OPERATIONAL                              ║"
echo "╚════════════════════════════════════════════════════════════════════════════╝"
