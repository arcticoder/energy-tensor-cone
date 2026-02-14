**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI, combining Lean formalization, computational searches, and verification against known bounds.

**Current Status (February 12, 2026)**: Repo at https://github.com/DawsonInstitute/energy-tensor-cone. Anonymized repo at https://anonymous.4open.science/r/aqei-convex-cone-5789/. Zenodo restricted. CQG desk rejection received (ref: CQG-115023) due to insufficient standards in scientific reporting/references. Shift to revision and resubmission.

### Priority Tasks (Do These First -- note additional details after Pre-Submission Checklist)

**1. Analyze CQG Desk Rejection and Plan Revisions (Today)**
- Rejection reason: Insufficient "highest standard" presentation and "comprehensive overview of related research through the reference list" (common for desk rejections per CQG's 38% rate; aligns with general causes like incomplete lit review).
- Revise `papers/aqei-cone-formalization.tex`: Expand introduction/discussion with broader QFT/AQEI context (e.g., implications for wormholes, exotic matter, GR stability). Add 10-15 more references (e.g., Ford-Roman series, Fewster's full oeuvre, recent hep-th on energy conditions). 
- Improve reporting: Add detailed methodology section, more figures (e.g., bound comparisons), and explicit links to analytic results.
- Commit: "Revise tex with expanded lit review and references post-CQG rejection"

**2. Switch Target Journal to Physical Review D (PRD) (COMPLETED)**
- Added a REVTeX 4.2 PRD wrapper at `papers/aqei-cone-formalization-prd.tex`.
- Confirmed clean build via `pdflatex → bibtex → pdflatex ×2` using `apsrev4-2`.
- Updated the Zotero-exported BibTeX entry `kontou2024` with explicit arXiv metadata so `apsrev4-2.bst` runs without errors.

**3. Update Anonymization and Supplements for PRD**
- Remove anonymized tex/PDF; PRD doesn't allow optional anonymous review.
- Supplements-anon.tar.gz: Remove.
- Commit with appropriate commit message.

**4. Refactor LaTeX for Multi-Version Maintenance (Ongoing)**
- Proceed with shared inputs (common-preamble.tex, etc.) as prior; add PRD-specific wrapper.
- For revisions: Use version control branches (e.g., git branch prd-revision) to manage changes without duplicating code.
- PRD will get full non-anon files.
- Commit: "Further refactor LaTeX with shared components"

**5. Additional Verification & Polish**
- Expand "Verification and Limitations": Include detailed analytic bound comparisons (Fewster scalar fields); note 1+1D as proof-of-concept (no need for 3+1D now – publishable as is).
- Run pipeline; add results to paper.
- Commit: "Enhance verification section with bound comparisons"

### Final Pre-Submission Checklist (to PRD)
- Revised PDF clean.
- Submit to PRD (parallel arXiv if endorsed; no wait needed).
- Update READMEs/sites (~/Code/asciimath/www/index.html, ~/Code/asciimath/.github/profile/README.md, ~/Code/asciimath/energy-tensor-cone/README.md) with PRD status once submitted.

**Additional details for 5 pre-submission tasks**
The references we're adding (or expanding upon) are primarily to address the CQG desk rejection's feedback on insufficient comprehensive overview of related research. Based on the project's focus (AQEI cones, formal verification, computational approximations), prioritize expanding the literature review in `papers/aqei-cone-formalization.tex` with 10-15 more citations for depth in QFT energy inequalities, convexity in cones, and formal methods. I'll list them below, grouped by category, with BibTeX entries (already added to `aqei-cone-formalization.bib`). These build on our existing ones (e.g., Fewster 2012, Ford 1995) and target gaps like analytic bounds, historical context, and related cones in GR/QFT.

Of these, **only a subset need to utilize LaTeX source** for our verification work (e.g., to cross-check math proofs, extract equations for our comparisons, or validate our Lean formalizations). We can use BibTeX + abstracts for basic citation, and then for deep math verification (as in our "Verification and Limitations" section), full .tex is useful. These will be noted below.

### References to Add/Expand
Add these to ensure a "comprehensive overview". I've selected recent + foundational ones; cite them in intro/discussion (e.g., "Building on [fewster2000], we formalize...").

#### Core AQEI/QEI Papers (Add 5-7 for bounds/comparisons)
These are critical for our verification section (compare to Fewster's scalar bounds).
- Fewster, Christopher J. “A General Worldline Quantum Inequality.” Classical and Quantum Gravity 17, no. 9 (2000): 1897. https://doi.org/10.1088/0264-9381/17/9/302.
  - **Use LaTeX? Yes, from papers/related/fewster2000.tex** – For extracting worldline integral bounds to compare our Gaussian results.

- Fewster, Christopher J., and Eleni-Alexandra Kontou. “Quantum Strong Energy Inequalities.” Physical Review D: Particles and Fields 99, no. 4 (2019): 045001. https://doi.org/10.1103/PhysRevD.99.045001.
  - **Use LaTeX? Yes, from papers/related/fewster2019.tex** – Strong inequalities for verification.

- Ford, L. H., and Thomas A. Roman. “Quantum Field Theory Constrains Traversable Wormhole Geometries.” Physical Review D: Particles and Fields 53, no. 10 (1996): 5496–507. https://doi.org/10.1103/PhysRevD.53.5496.
  - **LaTeX available in papers/related/fewster2019.tex** – Useful for wormhole implications. Use source as needed if/when comparing geometries.

- Fewster, Christopher J., and Jacob Thompson. “Quantum Energy Inequalities along Stationary Worldlines.” Classical and Quantum Gravity 40, no. 17 (2023): 175008. https://doi.org/10.1088/1361-6382/ace233.
  - **Use LaTeX? Yes, from papers/related/fewster2023.tex** – For small-curvature bounds comparison.

#### Convexity/Cones in GR/QFT (Add 3-4 for mathematical depth)
- Ziegler, Günter M. Lectures on Polytopes. Vol. 152. Graduate Texts in Mathematics. Springer New York, 1995. https://doi.org/10.1007/978-1-4613-8431-1.
  - **Needs full LaTeX? No** – General cone theory; flag as TODO if latex needed for polyhedral sections.

- Rockafellar, Ralph Tyrell. Convex Analysis. Princeton University Press, 1970. https://doi.org/10.1515/9781400873173.
  - **Full LaTeX available from papers/related/rockafellar_convex_analysis_1970.md ** – For extreme ray defs and key theorems.

#### Formal Methods/Lean in Physics (Add 2-3 for novelty)
- Moura, Leonardo de, and Sebastian Ullrich. “The Lean 4 Theorem Prover and Programming Language.” Automated Deduction – CADE 28: 28th International Conference on Automated Deduction, Virtual Event, July 12–15, 2021, Proceedings (Berlin, Heidelberg), 2021, 625–35. https://doi.org/10.1007/978-3-030-79876-5_37.
  - **Needs full LaTeX? No** – Already cited; source available but not essential.

- Buzzard, Kevin, Johan Commelin, and Patrick Massot. “Formalising Perfectoid Spaces.” Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs, January 20, 2020, 299–312. https://doi.org/10.1145/3372885.3373830.
  - **Needs full LaTeX? No** – Example of Lean in math; optional for context.

This strengthens the lit review for resubmission (e.g., to PRD).

### Expanded List of Additional References

Here's an expanded set of **13 additional references**. These focus on recent (2020-2024) developments in QEIs/AQEIs, integrable models, wormhole constraints, and local covariance – directly relevant for strengthening our "overview of related research." I've prioritized ones with analytic bounds for our verification section comparisons (e.g., to our Gaussian basis results).

Added to `aqei-cone-formalization.bib` already. Cite in the intro/discussion (e.g., "Recent numerical extensions [mandrysch2024] build on analytic QEIs [fewster2000], informing our finite-basis approach...").

#### New Additions (5 More for Recent Work)
These are from 2020-2024, emphasizing multi-particle/integrable models and applications.

- Mandrysch, Jan. “Numerical Results on Quantum Energy Inequalities in Integrable Models at the Two-Particle Level.” Physical Review D 109, no. 8 (2024): 085022. https://doi.org/10.1103/PhysRevD.109.085022.
  - **Needs full LaTeX? Yes, available in papers/related/mandrysch2024.tex** – For numerical multi-particle bounds to compare our searches.

- Bostelmann, Henning, Daniela Cadamuro, and Jan Mandrysch. “Quantum Energy Inequalities in Integrable Models with Several Particle Species and Bound States.” Annales Henri Poincaré 25, no. 10 (2024): 4497–542. https://doi.org/10.1007/s00023-023-01409-8.
  - **Needs full LaTeX? Yes, available in papers/related/bostelmann2024.tex** – Integrable models with bound states; key for our finite approximations.

- Kontou, Eleni-Alexandra. Wormhole Restrictions from Quantum Energy Inequalities. Version 2. 2024. https://doi.org/10.48550/ARXIV.2405.05963.
  - **full LaTeX available in papers/related/kontou2024.tex** – Applications to wormholes; useful for implications section.

- Fewster, Christopher J., and Jacob Thompson. “Quantum Energy Inequalities along Stationary Worldlines.” Classical and Quantum Gravity 40, no. 17 (2023): 175008. https://doi.org/10.1088/1361-6382/ace233.
  - **Needs full LaTeX? Yes available in papers/related/fewster2023.tex** – Stationary worldlines QEIs; for bound comparisons; arXiv source.

- Hovhannisyan, Karen V., and Alberto Imparato. “Energy Conservation and Fluctuation Theorem Are Incompatible for Quantum Work.” Quantum 8 (May 2024): 1336. https://doi.org/10.22331/q-2024-05-06-1336.
  - **Needs full LaTeX? No** – Related fluctuation theorems; bib sufficient for context.

Update you lit section accordingly!

20 references should be sufficient for a submission to Physical Review D (PRD), especially for a focused, interdisciplinary paper like ours on AQEI cones with formal verification and computational elements. PRD articles (particularly in quantum field theory or general relativity sections) typically range from 15-40 citations, with shorter or more specialized works often landing on the lower end. Our count provides a solid, comprehensive overview without overwhelming the manuscript—addressing the CQG rejection's concern about the reference list—while leaving room for reviewer-suggested additions.

That said, to optimize for PRD's standards (rigorous, physics-oriented with strong ties to established theory), double-check balance:
- **Core AQEI/QEI (8-10)**: Ensure foundational (Ford, Fewster) and recent (Kontou, Mandrysch) are well-represented for bounds comparisons.
- **Mathematical/Convexity (4-6)**: Ziegler, Rockafellar for cone properties.
- **Formal Methods/Lean (2-4)**: Moura, Buzzard to highlight novelty.
- **Applications (e.g., wormholes, GR) (4-6)**: To show broader impact.

If our lit review feels sparse in any section (e.g., recent hep-th crossovers), flag as needed to add 2-3 more targeted ones, but 20 is already in the sweet spot for acceptance potential. Focus on weaving them tightly into the narrative rather than quantity.