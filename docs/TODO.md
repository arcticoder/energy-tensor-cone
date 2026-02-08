**# TODO.md – energy-tensor-cone (DawsonInstitute org)**

**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI, combining Lean formalization, computational searches, and verification against known bounds.

**Current Status (February 8, 2026)**: Repo moved to https://github.com/DawsonInstitute/energy-tensor-cone. Paper archived at Zenodo (https://zenodo.org/records/18522457), LaTeX draft ready in `papers/aqei-cone-formalization.tex` with Zotero bib, Lean proofs advancing (some `sorry` remain for extensions), pipeline functional. Switch journal to Classical and Quantum Gravity (CQG).

### Priority Tasks (Do These First)

**1. Switch Target Journal to Classical and Quantum Gravity (CQG) (Today)**  
- Downloaded CQG LaTeX template from IOP (https://publishingsupport.iopscience.iop.org/journals/classical-and-quantum-gravity/ can be found under ~/Code/asciimath/energy/docs/journals/CQG
- Convert `papers/aqei-cone-formalization.tex` to use the IOP class (`\documentclass[12pt]{iopart}` or equivalent).  
- Update bibliography style to IOP (usually `iopart-num` or similar).  
- Adjust affiliation/email, abstract, keywords, and sections to match CQG guidelines.  
- Keep the data availability statement and file-structure description (shortened to appendix + GitHub link).  
Commit: "Convert LaTeX to CQG (IOP) template"


**2. Answer Remaining Questions & Verification Tasks (Today–Tomorrow)**  
- **README.md line 29 ("skeleton" with `sorry`)**: This is perfectly acceptable for publication in CQG (or PRD). Many formal-methods papers in physics journals publish partial formalizations with clear statements of what is proven vs. future work. Update README to: "The Lean development provides mechanized proofs of core properties (convexity, extreme-ray candidates in finite models); some extensions remain as `sorry` placeholders." Add Zenodo badge and CQG submission note.  
- **Dimensionality (1+1 vs 3+1)**: We do **not** need to extend to 3+1 for publishability. Most foundational AQEI results (Fewster, Ford, etc.) begin in 1+1 or 2+1; our finite-basis computational + formal approach is a valuable proof-of-concept. It does **not** unfairly burden the next researcher — it invites follow-up, which is standard. Mention this explicitly in the "Limitations and Outlook" section.  
- **Infinite-dimensional QFT connection**: No, completing the full infinite-dim link is not required (and realistically beyond a single paper). Our finite ansatz is the methodological innovation; discuss the approximation and extrapolation to QFT in the discussion.  
- **Comparisons with analytic bounds**: Add a dedicated subsection in "Verification and Limitations" comparing our near-miss candidates against known Fewster bounds for the free scalar field (or other solvable cases). papers/related/fewster*.tex to extract key formulas if needed.  

**5. Final Polish & Submission Readiness (This Week)**  
- Update all repo references (README, tex, websites) to DawsonInstitute/energy-tensor-cone.  
- Add data statement and limitations section to `aqei-cone-formalization.tex`.  
- Run full pipeline (`run_tests.sh`) and include latest statistics in the paper.  
- Prepare supplements zip (lean/src, mathematica, python, tests, results).  
- Submit to CQG.

**6. Journal Submission Notes**  
- Proceed with CQG submission once LaTeX is converted and cover letter is ready.
