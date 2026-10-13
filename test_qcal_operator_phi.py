#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tests for qcal_operator_phi root entrypoint.

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.abspath(os.path.dirname(__file__)))

from tests.test_qcal_operator_phi import (
    TestQCALConstants,
    TestQCALOperatorPhi,
    TestQCALRNABarrierFold,
    TestQCALNavierStokesRegularizer,
    TestQCALOperatorDemo,
)

if __name__ == "__main__":
    unittest.main()
