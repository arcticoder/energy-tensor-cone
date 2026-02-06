import json
import numpy as np
from scipy.integrate import quad
import sys

# Parameters mirroring Mathematica
SIGMA = 0.5
DOMAIN = 5.0

def phi(t, x, tc, xc):
    """Correlation function/Gaussian basis element"""
    return np.exp( -((t - tc)**2 + (x - xc)**2) / (2 * SIGMA**2) )

def g_gaussian(t, t0, tau):
    """Sampling function"""
    return np.exp( -(t - t0)**2 / (2 * tau**2) )

def normalize_velocity(v):
    # u = (1, v)
    # Norm^2 = | -1*(1)^2 + 1*(v)^2 | = | v^2 - 1 | = 1 - v^2 (since |v| < 1)
    norm = np.sqrt(1 - v**2)
    return np.array([1.0/norm, v/norm])

def compute_L_component(i, a_val, basis_s_i, center_i, params):
    """
    Computes L_i * a_i (single component contribution)
    But wait, L is a vector of integrals.
    L_i = Integral[ u . S_i . u * phi_i(gamma(t)) * g(t) dt ]
    """
    x0, v, t0, tau = params
    u = normalize_velocity(v)
    
    # S_i is 2x2 matrix
    S_i = np.array(basis_s_i)
    # contraction u . S . u
    contraction = u @ S_i @ u
    
    tc, xc = center_i
    
    def integrand(t):
        pos_t = t
        pos_x = x0 + v * t
        
        # phi_val = phi(t, x, tc, xc)
        phi_val = np.exp( -((pos_t - tc)**2 + (pos_x - xc)**2) / (2 * SIGMA**2) )
        g_val = np.exp( -(pos_t - t0)**2 / (2 * tau**2) )
        
        return contraction * phi_val * g_val

    # Integrate
    val, err = quad(integrand, -DOMAIN, DOMAIN)
    return val

def compute_B_val(params):
    x0, v, t0, tau = params
    
    def integrand_g2(t):
        g_val = np.exp( -(t - t0)**2 / (2 * tau**2) )
        return g_val**2
        
    integral, err = quad(integrand_g2, -DOMAIN, DOMAIN)
    return 0.1 * np.sqrt(integral)

def verify_vertex(json_path):
    with open(json_path, 'r') as f:
        data = json.load(f)

    basis_s = data['basisS']
    centers = data['centers']
    coeffs_a = np.array(data['a'])
    
    # Active constraints only
    constraints = data['constraints']
    active_indices = data['activeIndices']
    
    print(f"Verifying {len(constraints)} active constraints...")
    
    all_passed = True
    
    for k, constraint in enumerate(constraints):
        params = constraint['params'] # x0, v, t0, tau
        
        # Compute L . a
        L_dot_a = 0.0
        for i in range(len(coeffs_a)):
            L_i = compute_L_component(i, coeffs_a[i], basis_s[i], centers[i], params)
            L_dot_a += L_i * coeffs_a[i]
            
        # Compute B
        B_val = compute_B_val(params)
        
        # Check inequality: L.a >= -B
        # Check tightness: L.a + B approx 0
        residue = L_dot_a + B_val
        
        print(f"Constraint {active_indices[k]}: L.a = {L_dot_a:.6f}, -B = {-B_val:.6f}, Residue = {residue:.6e}")
        
        if residue < -1e-4:
            print("  [FAIL] Violation!")
            all_passed = False
        elif abs(residue) > 1e-4:
            print("  [WARN] Not tight (maybe numerical error or this wasn't the tightest binding)")
        else:
            print("  [PASS] Satisfied and Tight")

    return all_passed

if __name__ == "__main__":
    path = "mathematica/results/vertex.json"
    if len(sys.argv) > 1:
        path = sys.argv[1]
    
    if verify_vertex(path):
        print("\nVerification Successful.")
        sys.exit(0)
    else:
        print("\nVerification Failed.")
        sys.exit(1)
