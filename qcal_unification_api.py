#!/usr/bin/env python3
"""
QCAL Unification API - REST API for QCAL Unified Framework

This module provides a REST API for exploring and verifying the QCAL
unified framework. It allows users to:
- Query universal constants
- Execute spectral operators
- Verify problem connections
- Run cross-verification protocols

Note: This is an optional component. Install FastAPI to use:
    pip install fastapi uvicorn pydantic
"""

try:
    from fastapi import FastAPI, HTTPException
    from fastapi.responses import JSONResponse
    from pydantic import BaseModel
    from typing import Dict, List, Any, Optional
    import uvicorn
    FASTAPI_AVAILABLE = True
except ImportError:
    FASTAPI_AVAILABLE = False
    print("⚠️  FastAPI not installed. Install with: pip install fastapi uvicorn pydantic")
    print("   This is an optional component for the QCAL API.")

from qcal_unified_framework import QCALUnifiedFramework
from cross_verification_protocol import CrossVerificationProtocol
import numpy as np


# Request/Response Models
class ProblemRequest(BaseModel):
    """Request model for problem unification"""
    problem_name: str
    parameters: Optional[Dict[str, Any]] = {}


class OperatorRequest(BaseModel):
    """Request model for operator execution"""
    operator_name: str
    parameters: Dict[str, Any]


class UnifiedResponse(BaseModel):
    """Response model for unified problem analysis"""
    qcal_operator: str
    universal_constant: float
    verification_result: Dict[str, Any]
    connected_problems: List[str]
    eigenvalue: float
    interpretation: str


if FASTAPI_AVAILABLE:
    # Initialize FastAPI app
    app = FastAPI(
        title="QCAL Unified Framework API",
        description="REST API for exploring the QCAL unified framework connecting Millennium Prize Problems",
        version="1.0.0"
    )
    
    # Initialize framework
    framework = QCALUnifiedFramework()
    verification_protocol = CrossVerificationProtocol()
    
    
    @app.get("/")
    async def root():
        """Root endpoint with API information"""
        return {
            "message": "QCAL Unified Framework API",
            "version": "1.0.0",
            "endpoints": {
                "constants": "/constants",
                "problems": "/problems",
                "unify": "/unify",
                "operator": "/operator",
                "connections": "/connections",
                "verify": "/verify",
                "coherence": "/coherence"
            }
        }
    
    
    @app.get("/constants")
    async def get_constants():
        """Get all universal constants"""
        constants = framework.constants
        
        return {
            "constants": {
                "kappa_pi": constants.kappa_pi,
                "f0": constants.f0,
                "critical_line": constants.critical_line,
                "ramsey_ratio": constants.ramsey_ratio,
                "navier_stokes_epsilon": constants.navier_stokes_epsilon,
                "bsd_delta": constants.bsd_delta
            },
            "coherence": constants.verify_coherence(),
            "relationships": constants.constant_relationships()
        }
    
    
    @app.get("/problems")
    async def get_problems():
        """Get all millennium problems in the framework"""
        problems = {}
        
        for key, problem in framework.problems.items():
            problems[key] = {
                "name": problem.name,
                "statement": problem.problem_statement,
                "operator": problem.qcal_operator_name,
                "constant": problem.universal_constant,
                "verification_protocol": problem.verification_protocol
            }
        
        return {
            "problems": problems,
            "count": len(problems)
        }
    
    
    @app.get("/problems/{problem_name}")
    async def get_problem(problem_name: str):
        """Get details about a specific problem"""
        if problem_name not in framework.problems:
            raise HTTPException(status_code=404, detail=f"Problem '{problem_name}' not found")
        
        problem = framework.problems[problem_name]
        
        # Get operator result
        operator_result = framework.operators[problem_name](framework.constants.__dict__)
        
        # Get connections
        connections = framework.find_connections(problem_name)
        
        # Get verification
        verification = framework.verify_problem(problem_name)
        
        return {
            "problem": {
                "name": problem.name,
                "statement": problem.problem_statement,
                "operator": problem.qcal_operator_name,
                "constant": problem.universal_constant,
                "verification_protocol": problem.verification_protocol
            },
            "operator_result": operator_result,
            "connected_to": connections,
            "verification": verification
        }
    
    
    @app.post("/unify")
    async def unify_problem(request: ProblemRequest):
        """Unify a millennium problem through QCAL framework"""
        if request.problem_name not in framework.problems:
            raise HTTPException(
                status_code=404, 
                detail=f"Problem '{request.problem_name}' not found. Available: {list(framework.problems.keys())}"
            )
        
        problem = framework.problems[request.problem_name]
        
        # Execute operator with parameters
        params = {**framework.constants.__dict__, **request.parameters}
        operator_result = framework.operators[request.problem_name](params)
        
        # Get connections
        connections = framework.find_connections(request.problem_name)
        
        # Verify problem
        verification = framework.verify_problem(request.problem_name)
        
        return {
            "qcal_operator": operator_result['operator'],
            "universal_constant": problem.universal_constant,
            "verification_result": verification,
            "connected_problems": connections,
            "eigenvalue": operator_result['eigenvalue'],
            "interpretation": operator_result['interpretation']
        }
    
    
    @app.post("/operator")
    async def execute_operator(request: OperatorRequest):
        """Execute a specific QCAL operator with custom parameters"""
        if request.operator_name not in framework.operators:
            raise HTTPException(
                status_code=404,
                detail=f"Operator '{request.operator_name}' not found. Available: {list(framework.operators.keys())}"
            )
        
        operator = framework.operators[request.operator_name]
        result = operator(request.parameters)
        
        return result
    
    
    @app.get("/connections")
    async def get_problem_connections():
        """Get all connections between problems via QCAL"""
        connections = framework.get_problem_connections()
        coherence_score = framework.calculate_coherence()
        verification_status = framework.get_verification_status()
        
        return {
            "connections": connections,
            "coherence_score": coherence_score,
            "verification_status": verification_status
        }
    
    
    @app.get("/verify")
    async def run_verification():
        """Run complete cross-verification protocol"""
        # Run verification (capture without printing)
        results = {}
        for problem, verifier in verification_protocol.problem_solutions.items():
            result = verifier()
            results[problem] = {
                "test_name": result.test_name,
                "passed": result.passed,
                "confidence": result.confidence,
                "details": result.details
            }
        
        # Build consistency matrix
        verification_results = {
            k: verification_protocol.problem_solutions[k]() 
            for k in verification_protocol.problem_solutions.keys()
        }
        consistency_matrix = verification_protocol.build_consistency_matrix(verification_results)
        
        # Get coherence
        qcal_coherence = verification_protocol.verify_qcal_coherence(consistency_matrix)
        
        # Check unified status
        all_passed = all(r['passed'] for r in results.values())
        unified_status = all_passed and qcal_coherence['all_constants_coherent']
        
        return {
            "individual_results": results,
            "consistency_matrix": {
                "shape": consistency_matrix.shape,
                "mean": float(np.mean(consistency_matrix)),
                "min": float(np.min(consistency_matrix[consistency_matrix > 0])),
                "max": float(np.max(consistency_matrix))
            },
            "qcal_coherence": {
                "constant_coherence": qcal_coherence['constant_coherence'],
                "matrix_coherence": qcal_coherence['matrix_coherence'],
                "overall_coherence": qcal_coherence['overall_coherence'],
                "all_constants_coherent": qcal_coherence['all_constants_coherent']
            },
            "unified_status": unified_status
        }
    
    
    @app.get("/coherence")
    async def get_coherence():
        """Get overall framework coherence metrics"""
        constant_coherence = framework.constants.verify_coherence()
        overall_coherence = framework.calculate_coherence()
        relationships = framework.constants.constant_relationships()
        
        return {
            "constant_checks": constant_coherence,
            "overall_coherence": overall_coherence,
            "constant_relationships": relationships,
            "status": "coherent" if overall_coherence > 0.95 else "needs_review"
        }
    
    
    @app.get("/summary")
    async def get_summary():
        """Get complete framework summary"""
        summary = framework.generate_summary()
        
        return {
            "summary_text": summary,
            "constants": {
                "kappa_pi": framework.constants.kappa_pi,
                "f0": framework.constants.f0,
                "critical_line": framework.constants.critical_line,
                "ramsey_ratio": framework.constants.ramsey_ratio,
                "navier_stokes_epsilon": framework.constants.navier_stokes_epsilon,
                "bsd_delta": framework.constants.bsd_delta
            },
            "problems_count": len(framework.problems),
            "coherence": framework.calculate_coherence()
        }


def main():
    """Run the API server"""
    if not FASTAPI_AVAILABLE:
        print("❌ Cannot start API server - FastAPI not installed")
        print("   Install with: pip install fastapi uvicorn pydantic")
        return 1
    
    print("🚀 Starting QCAL Unified Framework API...")
    print("📚 Documentation available at: http://localhost:8000/docs")
    print("🔍 Interactive API explorer at: http://localhost:8000/redoc")
    print("")
    
    uvicorn.run(app, host="0.0.0.0", port=8000)
    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main())
