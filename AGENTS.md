# Exact Liouville comparison

Archon owns the proof work. Read docs/objective.md and the unchanged manuscript at docs/reference/exact_liouville_comparison.tex.

Use native Mathlib manifolds, tangent spaces, forms, exterior derivatives, and flows, and reuse the pinned FsFltz interfaces when appropriate. Check the actual definition and prove any needed bridge. A Liouville manifold ALWAYS has an actual complete Liouville flow for all real times, with convention i_Z d lambda = lambda. Use separate exact-symplectic terminology for the more general theorem without completeness hypotheses.

Write a clear compilable statement and an independently reviewed definition crosswalk before substantive proof work. The reference metric g and all dual/operator norms must be explicit. Preserve the manuscript's assumptions and conclusion; no circular fields, assumed Moser flows, sorry, admit, custom axioms, or replacement of actual geometry by arbitrary operations. A target proposition is not a proof.

Prioritize Lean first. GitHub upload is the FINAL step after full Lean acceptance and final documentation; do not upload any intermediate files to GitHub. Follow the standalone layout of the previous cluster-skeleton project: Lean library, statement and proof guides/PDFs with editable LaTeX, verification receipts, axiom audit, reproducible scripts and CI. Keep status truthful. Only propext, Classical.choice, and Quot.sound may occur in the transitive axiom audit. Do not edit the authoritative manuscript, old project, or upstream dependencies. New sessions for this objective use Astra/high.
