#!/usr/bin/env bash
# Validate GitHub Actions workflow files
# Checks YAML syntax and workflow structure

set -euo pipefail

echo "================================================"
echo "GitHub Actions Workflow Validation"
echo "================================================"
echo ""

# Check if Python is available
if ! command -v python3 &> /dev/null; then
    echo "❌ Python3 not found. Cannot validate YAML."
    exit 1
fi

# Install PyYAML if not available
python3 -c "import yaml" 2>/dev/null || {
    echo "Installing PyYAML..."
    pip install --user PyYAML -q
}

WORKFLOW_DIR=".github/workflows"
VALID=0
INVALID=0

echo "Checking workflows in $WORKFLOW_DIR..."
echo ""

for workflow in "$WORKFLOW_DIR"/*.yml "$WORKFLOW_DIR"/*.yaml; do
    if [ ! -f "$workflow" ]; then
        continue
    fi
    
    echo "Validating: $workflow"
    
    # Check YAML syntax
    if python3 -c "import yaml; yaml.safe_load(open('$workflow'))" 2>/dev/null; then
        echo "  ✅ YAML syntax valid"
        
        # Check required fields
        if python3 << EOF
import yaml
with open('$workflow') as f:
    wf = yaml.safe_load(f)
    has_name = 'name' in wf
    has_on = ('on' in wf) or (True in wf)  # YAML may parse 'on' as boolean True
    has_jobs = 'jobs' in wf
    print(f"  {'✅' if has_name else '❌'} Has 'name' field")
    print(f"  {'✅' if has_on else '❌'} Has 'on' (triggers) field")
    print(f"  {'✅' if has_jobs else '❌'} Has 'jobs' field")
    exit(0 if (has_name and has_on and has_jobs) else 1)
EOF
        then
            echo "  ✅ Workflow structure valid"
            VALID=$((VALID + 1))
        else
            echo "  ❌ Workflow structure invalid"
            INVALID=$((INVALID + 1))
        fi
    else
        echo "  ❌ YAML syntax invalid"
        INVALID=$((INVALID + 1))
    fi
    echo ""
done

echo "================================================"
echo "Validation Summary"
echo "================================================"
echo "Valid workflows: $VALID"
echo "Invalid workflows: $INVALID"
echo ""

if [ $INVALID -gt 0 ]; then
    echo "❌ Some workflows are invalid"
    exit 1
else
    echo "✅ All workflows are valid"
    exit 0
fi
