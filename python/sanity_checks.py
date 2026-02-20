import os
import sys

def check_files_exist(root_dir, files):
    print("\n--- Checking Critical Files ---")
    missing = []
    for f in files:
        path = os.path.join(root_dir, f)
        if not os.path.exists(path):
            missing.append(f)
            print(f"[FAIL] Missing: {f}")
        else:
            print(f"[OK] Found: {f}")
    
    if missing:
        return False
    return True

def check_empty_files(root_dir, extensions=['.lean', '.py', '.tex']):
    print("\n--- Checking for Empty Files ---")
    empty = []
    for root, dirs, filenames in os.walk(root_dir):
        if 'lake-packages' in root or '__pycache__' in root or '.git' in root:
            continue
        for f in filenames:
            if any(f.endswith(ext) for ext in extensions):
                path = os.path.join(root, f)
                if os.path.getsize(path) == 0:
                    empty.append(path)
                    print(f"[FAIL] Empty file: {path}")
    
    if empty:
        return False
    print("[OK] No empty source files found.")
    return True

def check_todos(root_dir, extensions=['.lean', '.py']):
    print("\n--- Checking for TODOs ---")
    found_todos = False
    for root, dirs, filenames in os.walk(root_dir):
        if 'lake-packages' in root or '__pycache__' in root or '.git' in root:
            continue
        for f in filenames:
            if any(f.endswith(ext) for ext in extensions):
                path = os.path.join(root, f)
                try:
                    with open(path, 'r', encoding='utf-8') as file:
                        for i, line in enumerate(file):
                            if "TODO" in line:
                                print(f"[WARN] TODO found in {f}:{i+1}: {line.strip()}")
                                found_todos = True
                except Exception as e:
                    print(f"[WARN] Could not read {path}: {e}")
    
    if not found_todos:
        print("[OK] No TODOs found.")
    else:
        print("[INFO] TODOs exist. This is a warning, not a failure.")
    return True

def main():
    # Assume script is in python/ subdirectory
    script_dir = os.path.dirname(os.path.abspath(__file__))
    root_dir = os.path.dirname(script_dir) # Parent of python/ is root
    
    print(f"Running Sanity Checks on Workspace: {root_dir}")
    
    critical_files = [
        "lean/lakefile.lean",
        "lean/src/FinalTheorems.lean",
        "lean/src/VertexVerificationRat.lean",
        "python/analyze_results.py",
        "python/check_rational_values.py",
        "papers/aqei-cone-formalization-body.tex"
    ]
    
    files_ok = check_files_exist(root_dir, critical_files)
    empty_ok = check_empty_files(root_dir)
    todos_checked = check_todos(root_dir)
    
    if not files_ok or not empty_ok:
        print("\n[FAILURE] Sanity Checks Failed!")
        sys.exit(1)
    
    print("\n[SUCCESS] Sanity Checks Passed!")
    sys.exit(0)

if __name__ == "__main__":
    main()
