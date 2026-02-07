# Terminal Crash Fix (2026-02-06)

## Problem
Terminals were crashing/freezing during test runs, especially when running Lean builds.

## Root Cause
The **Lean 4 VSCode extension** (`leanprover.lean4`) was installed and automatically starting a Lean Language Server whenever it detected `.lean` files in the workspace. This background process was:
- Consuming system resources
- Interfering with terminal processes
- Potentially conflicting with manual `lake build` commands run from CLI

## Solution
Disabled the Lean 4 extension's automatic language server across the workspace while preserving the ability to manually build Lean projects via CLI (`lake build`):

### 1. Workspace-level settings
Updated `~/Code/asciimath/energy/energy.code-workspace` to disable Lean extension features:
```json
"lean4.enabled": false,
"lean4.serverLogging.enabled": false,
"lean4.elaborationDelay": 0,
```

### 2. Project-level settings  
Created `.vscode/settings.json` in the `energy-tensor-cone` project with the same Lean disablement and additional file watcher exclusions for build artifacts.

### 3. File watcher optimizations
Excluded Lean build directories from VSCode's file watcher to reduce resource usage:
- `**/.lake/**`
- `**/lake-packages/**`
- `**/mathematica/results/**`

## Verification
After applying these changes:
- ✅ Terminals remain stable during test runs
- ✅ Full test suite (`./run_tests.sh`) completes without crashes
- ✅ Lean CLI tools (`lake build`) still work perfectly
- ✅ No background Lean processes interfering with terminal

## Impact
- **Lean IDE features** (syntax highlighting, go-to-definition, error checking in editor) are disabled
- **Lean CLI functionality** is fully preserved and we continue to build via `lake build` in tests
- **Terminal stability** is restored

## Alternative Approach (if IDE features needed)
If you need the Lean extension's IDE features in the future, you can:
1. Re-enable it: set `"lean4.enabled": true` in workspace settings
2. Use the extension's built-in restart command when terminals become unstable
3. Consider upgrading to a more powerful machine or allocating more resources to WSL

For this project, manual CLI-based Lean builds are preferred and sufficient.
