import json
import numpy as np
import sys

def generate_lean(json_path, output_path):
    with open(json_path, 'r') as f:
        data = json.load(f)

    basis_s = data['basisS']
    centers = data['centers']
    coeffs_a = data['a'] # list
    
    constraints = data['constraints']
    active_indices = data['activeIndices']

    with open(output_path, 'w') as f:
        f.write("import Std\n\n")
        f.write("/- \n")
        f.write("  AQEI_Generated_Data.lean\n")
        f.write("  Auto-generated from Phase 2 Optimization (Mathematica -> Python).\n")
        f.write("  Contains the concrete basis, vertex coefficients, and active constraints.\n")
        f.write("-/\n\n")
        
        f.write("namespace AQEIGenerated\n\n")
        
        # 1. Basis Centers
        f.write("/-- Centers of the Gaussian basis functions (t, x) -/\n")
        f.write("def basis_centers : List (Float × Float) := [\n")
        for c in centers:
            f.write(f"  ({c[0]}, {c[1]}),\n")
        f.write("]\n\n")
        
        # 2. Basis Matrices
        f.write("/-- Spin-2 polarization matrices for the basis -/\n")
        f.write("def basis_matrices : List (List (List Float)) := [\n")
        for m in basis_s:
            row0 = f"[{m[0][0]}, {m[0][1]}]"
            row1 = f"[{m[1][0]}, {m[1][1]}]"
            f.write(f"  [{row0}, {row1}],\n")
        f.write("]\n\n")
        
        # 3. Coefficients
        f.write("/-- Vertex coefficients 'a' found by Linear Programming -/\n")
        f.write("def coefficients : List Float := [\n")
        for a in coeffs_a:
            f.write(f"  {a},\n")
        f.write("]\n\n")
        
        # 4. Active Constraint Indices
        f.write("/-- Indices of active constraints (1-based from Mathematica) -/\n")
        f.write("def active_indices : List Nat := " + str(active_indices).replace('[', '[').replace(']', ']') + "\n\n")
        
        # 5. Active Constraints Data
        f.write("structure ConstraintData where\n")
        f.write("  x0 : Float\n")
        f.write("  v : Float\n")
        f.write("  t0 : Float\n")
        f.write("  tau : Float\n")
        f.write("deriving Repr\n\n")
        
        f.write("/-- Parameters for the active constraints -/\n")
        f.write("def active_constraints : List ConstraintData := [\n")
        for c in constraints:
            p = c['params'] # x0, v, t0, tau
            f.write(f"  {{ x0 := {p[0]}, v := {p[1]}, t0 := {p[2]}, tau := {p[3]} }},\n")
        f.write("]\n\n")

        # 6. Active Constraint Vectors (L) and Bounds (B)
        f.write("/-- The normal vectors L for the active constraints -/\n")
        f.write("def active_L : List (List Float) := [\n")
        for c in constraints:
            # Mathematica might output integers or floats. Ensure standard formatting.
            L_vec = c['L']
            f.write("  " + str(list(L_vec)).replace('[', '[').replace(']', ']') + ",\n")
        f.write("]\n\n")

        f.write("/-- The bounds B for the active constraints (inequality is L.a >= -B) -/\n")
        f.write("def active_B : List Float := [\n")
        for c in constraints:
            B_val = c['B']
            f.write("  " + str(float(B_val)) + ",\n")
        f.write("]\n\n")
            
        f.write("end AQEIGenerated\n\n")
        
        # Add axiom checks
        f.write("#print axioms AQEIGenerated.basis_centers\n")
        f.write("#print axioms AQEIGenerated.basis_matrices\n")
        f.write("#print axioms AQEIGenerated.coefficients\n")

    print(f"Generated {output_path}")

if __name__ == "__main__":
    json_p = "mathematica/results/vertex.json"
    out_p = "lean/src/AQEI_Generated_Data.lean"
    generate_lean(json_p, out_p)
