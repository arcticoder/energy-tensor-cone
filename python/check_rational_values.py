
import sympy
from sympy import Rational

def check_rational_values():
    print("Verifying exact rational values from Lean formalization...")
    
    # Candidate Vertex v from FinalTheorems.lean
    #   0 => (-201930050 : Rat) / 188548783
    #   1 => 100
    #   2 => 100
    #   3 => (-697114919 : Rat) / 954338471
    #   4 => (271445287 : Rat) / 543764461
    #   5 => 100
    v = [
        Rational(-201930050, 188548783),
        Rational(100, 1),
        Rational(100, 1),
        Rational(-697114919, 954338471),
        Rational(271445287, 543764461),
        Rational(100, 1)
    ]
    
    # Active Constraints (L) from VertexVerificationRat.lean / AQEI_Generated_Data_Rat.lean
    # Row 0:
    #   0 => 18242171 / 185310433
    #   3 => 1686499 / 783101748
    # Row 1:
    #   0 => -61 / 489973282
    #   2 => -33857 / 815586094
    #   3 => -7864737 / 141838453
    #   4 => -110132019 / 383795849
    # Row 2:
    #   0 => -29649869 / 504524770
    #   3 => -188681736 / 836755073
    #   4 => -178 / 269582495
    #   5 => -320317 / 94761543
    
    # We construct the full 6x6 matrix (including box constraints)
    # Box constraints active are x1=100, x2=100, x5=100.
    # In VertexVerificationRat.lean box_rows are indices 1, 2, 5 with value 1 on diag.
    
    # CAUTION: The indices in Lean (Fin 6) map to 0..5.
    
    L_matrix = [
        [Rational(0) for _ in range(6)] for _ in range(6)
    ]
    
    # Fill Row 0
    L_matrix[0][0] = Rational(18242171, 185310433)
    L_matrix[0][3] = Rational(1686499, 783101748)
    
    # Fill Row 1
    L_matrix[1][0] = Rational(-61, 489973282)
    L_matrix[1][2] = Rational(-33857, 815586094)
    L_matrix[1][3] = Rational(-7864737, 141838453)
    L_matrix[1][4] = Rational(-110132019, 383795849)
    
    # Fill Row 2
    L_matrix[2][0] = Rational(-29649869, 504524770)
    L_matrix[2][3] = Rational(-188681736, 836755073)
    L_matrix[2][4] = Rational(-178, 269582495)
    L_matrix[2][5] = Rational(-320317, 94761543)
    
    # Fill Row 3 (Box constraint for x1 -> index 1)
    L_matrix[3][1] = Rational(1, 1)
    
    # Fill Row 4 (Box constraint for x2 -> index 2)
    L_matrix[4][2] = Rational(1, 1)
    
    # Fill Row 5 (Box constraint for x5 -> index 5)
    L_matrix[5][5] = Rational(1, 1)
    
    # B values (RHS bound values) from FinalTheorems.lean
    # Lean says: L_poly i candidate_v = -B_poly i
    # So we check L * v
    
    # From FinalTheorems.lean:
    # 0 => 36286065376054059506337885986767 / 339120078382890596879902371141156
    # 1 => 56881163208213718514020808481935025194233775134029935638377 / 532124755520295182874251714890874438355108028311061855673287
    # 2 => 237683910384684634846040317252027915796047109138197689971 / 2153503410892270359210740429201985008222235476670837870345
    # 3, 4, 5 (Box) => 100
    
    # NOTE: The rows in FinalTheorems.lean are indexed 0..5.
    # Rows 0,1,2 correspond to our L_matrix rows 0,1,2.
    # Rows 3,4,5 correspond to our L_matrix rows 3,4,5 (the box constraints).
    # But wait, FinalTheorems says:
    # "For i >= 3 (Box constraints x_j <= 100), the inequality is -x_j >= -100."
    # "So the functional L is -e_j, and the bound -B is -100."
    # "The verification_matrix stores +e_j."
    # My L_matrix above stores +e_j for rows 3,4,5.
    # So for rows 3,4,5, L * v should be 100.
    
    expected_L_dot_v = [
         -Rational(36286065376054059506337885986767, 339120078382890596879902371141156),
         -Rational(56881163208213718514020808481935025194233775134029935638377, 532124755520295182874251714890874438355108028311061855673287),
         -Rational(237683910384684634846040317252027915796047109138197689971, 2153503410892270359210740429201985008222235476670837870345),
         Rational(100, 1),
         Rational(100, 1),
         Rational(100, 1)
    ]

    print("\n--- Checking L * v == RHS ---")
    for i in range(6):
        row = L_matrix[i]
        dot_prod = sum([row[j] * v[j] for j in range(6)])
        
        expected = expected_L_dot_v[i]
        diff = dot_prod - expected
        
        print(f"Row {i}:")
        print(f"  Computed: {dot_prod}")
        print(f"  Expected: {expected}")
        
        if diff == 0:
            print("  Result: PASS")
        else:
            print(f"  Result: FAIL (Diff: {diff})")
            exit(1)

    # Check Determinant of the 6x6 matrix
    print("\n--- Checking Determinant != 0 ---")
    M = sympy.Matrix(L_matrix)
    det = M.det()
    print(f"Determinant: {det}")
    if det != 0:
        print("  Result: PASS (Non-singular)")
    else:
        print("  Result: FAIL (Singular)")
        exit(1)

    print("\nAll Rational Value Checks PASSED.")

if __name__ == "__main__":
    check_rational_values()
