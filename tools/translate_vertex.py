import json
import os
import sys
import numpy as np

def translate_vertex(json_path):
    if not os.path.exists(json_path):
        print(f"Error: File not found: {json_path}")
        sys.exit(1)

    with open(json_path, 'r') as f:
        data = json.load(f)

    # Extract data
    num_basis = data['numBasis']
    # basisS comes as a list of 2x2 matrices
    basis_s = np.array(data['basisS']) 
    centers = np.array(data['centers'])
    coeffs_a = np.array(data['a'])
    
    # Active constraints
    # constraints is a list of objects with "L", "B", "params"
    # params = {x0, v, t0, tau}
    constraints = data['constraints']

    print(f"Loaded Vertex Data:")
    print(f"  Basis Size: {num_basis}")
    print(f"  Coefficients: {coeffs_a}")
    print(f"  Number of Active Constraints: {len(constraints)}")

    for i, c in enumerate(constraints):
        params = c['params']
        print(f"  Constraint {i+1}: x0={params[0]:.2f}, v={params[1]:.2f}, t0={params[2]:.2f}, tau={params[3]:.2f}")

    # TODO: Generate Lean code
    
if __name__ == "__main__":
    if len(sys.argv) < 2:
        # Default path
        default_path = "mathematica/results/vertex.json"
        translate_vertex(default_path)
    else:
        translate_vertex(sys.argv[1])
