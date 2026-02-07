# TODO.md: Final Push to Submission-Ready Manuscript
**Project**: Convex Cone of Energy Tensors under AQEI: Formal Verification and Computational Exploration  
**Status as of 7 Feb 2026**: All Verification Items 1–4 from previous TODO completed (Lean theorems verified, literature cross-checks done, recent updates tested, paper draft.tex and history.md updated).  
**Next goal**: Produce a clean, bibliographically correct, reproducible LaTeX manuscript ready for arXiv + journal submission.

## 1. Integrate Zotero-exported bibliography (immediate)
- `papers/draft.bib` is currently being auto-exported by Zotero/Better BibTeX from collection “Convex Cone of Energy Tensors under AQEI”.
- `draft.tex` currently uses a manual `\begin{thebibliography}{9}` environment and ignores `draft.bib`.
- Action:
  1. In `draft.tex` replace the entire manual bibliography block with:
     ```latex
     \bibliographystyle{unsrt}  % or plain, alpha, etc.; pick one you like
     \bibliography{draft}
     ```
  2. Place `\bibliography{draft}` immediately before `\end{document}`.
  3. Compile twice (`pdflatex draft.tex && bibtex draft && pdflatex draft.tex && pdflatex draft.tex`).
  4. Verify all 4 existing entries (Lean library, Fewster 2012, Lean 4 paper, Ziegler polytopes) appear correctly.
- Commit: “Switch to external draft.bib + integrate Zotero export”

## 2. `git mv` draft.tex to a permanent filename (immediate)
Current name “draft.tex” is temporary and will become confusing once the paper is on arXiv.
Suggested name (unique, descriptive, matches title):  
**`aqei-cone-formalization.tex`**

Alternative short options:
- `energy-tensor-cone.tex`
- `convex-cone-aqei.tex`

Action:
```bash
cd papers
git mv draft.tex aqei-cone-formalization.tex
# Then update any internal references if they exist (none currently)
git commit -m "Rename draft.tex → aqei-cone-formalization.tex (permanent filename)"
```
Update `README.md` and `history.md` to point to the new name.

## 3. Add essential additional citations (today)
Zotero collection already contains the core Fewster 2012 lectures. These high-impact, directly relevant references have been auto-exported by zotero into the .bib file:

- Quantum Energy Inequalities along stationary worldlines (papers/draft.bib:31-42; downloaded preprint version from arxiv to papers/related/fewster2023.tex)
- Averaged Energy Conditions and Quantum Inequalities (papers/draft.bib:44-55; downloaded preprint version from arxiv to papers/related/ford1995.tex)
- Quantum strong energy inequalities (papers/draft.bib:18-29; downloaded preprint version from arxiv to papers/related/fewster2019.tex)
```

Cite them in the Introduction/Discussion (e.g., “The modern formulation of AQEI originates with... and was ... developed by ...”).

## 4. Citations for verification work
The full `papers/draft.bib` plus these arXiv .tex files (downloaded to `papers/related/`):
- AEI2012_arXiv.tex  (Fewster 2012 lectures – the standard reference)
- QEIs_v4.tex  (Fewster–Verch review)

Use only these references for any claim about AQEI bounds or definitions. Do not invent new citations.

## 5. Journal choice
**Communications in Mathematical Physics** (CMP) – top choice for rigorous mathematical physics. Prepare the submission package once the LaTeX is final.

## 6. arXiv categories
Primary: **math-ph** (Mathematical Physics)  
Secondary
- gr-qc (General Relativity and Quantum Cosmology)
- hep-th (High Energy Physics – Theory)

## 7. Remaining tasks before submission
- [ ] Integrate `draft.bib` and add the 4 new entries above (done in step 1+3)
- [ ] Rename `draft.tex` (step 2)
- [ ] Final Lean build + run `run_tests.sh` (ensure no `sorry` left in `FinalTheorems.lean`)
- [ ] Add one sentence in Discussion citing the new Fewster 2023 paper
- [ ] Generate final PDF, check for compilation warnings, run `pdflatex` + `bibtex` twice
- [ ] Update `README.md` with: “Manuscript `aqei-cone-formalization.tex` ready for arXiv (math-ph, gr-qc, hep-th)”
- [ ] Write short arXiv abstract (copy from title + first paragraph of abstract)
- [ ] Upload to arXiv first (gets DOI, lets you cite your own work, gives community feedback)
- [ ] After arXiv acceptance (1–2 days), submit CMP

Once these are done the manuscript is submission-ready. You have already completed the hard verification work; this is just polishing and bibliography housekeeping.

Commit frequently with clear messages. When everything is green, the paper is ready for arXiv moderators and journal referee.