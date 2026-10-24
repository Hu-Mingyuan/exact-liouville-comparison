# Exact comparison of Liouville forms under weak taming

## User mandate

Archon owns statement design, decomposition, implementation, proofs, review, integration, and the matching mathematical exposition. The operator supplies the source, the mathematical goal, and acceptance requirements; do not ask the operator to write the proofs. Build a standalone project matching the structure and verification quality of Hu-Mingyuan/cluster-skeleton. New sessions for this objective use gpt-6-astra with reasoning_effort high (not xhigh). Preserve other projects and their settings.

## Authoritative source

The complete user manuscript is supplied unchanged at docs/reference/exact_liouville_comparison.tex in the initial repositories. Record its SHA-256 in docs/sources.json. Treat that copy as a read-only source snapshot. This task concerns that entire note: Theorem thm:main, its supporting results, and cor:liouville, cor:stein, cor:two. No application to multiplicative hypertoric varieties or categorical HMS is requested.

## Mathematical target

On a finite-dimensional smooth real manifold X without boundary, let beta be a smooth one-form with Omega = d beta symplectic, J an Omega-compatible smooth almost complex structure, and g(v,w) = Omega(v,Jw). Assume a smooth proper R : X -> [1,infinity), constants c > 0 and rstar > 1, and outside {R <= rstar}:

    beta = -c dR composed with J,
    a = c |dR|_(g dual)^2 <= R.

Let lambda be a smooth real one-form, omega = d lambda symplectic, and omega(v,Jv) >= 0 for every tangent vector. Let B : [1,infinity) -> (0,infinity) be smooth with B(r) >= r and integral_1^infinity r/B(r)^2 dr = infinity. Assume ||(omega flat)^(-1)||_(g dual -> g) <= C B(R), C > 0, outside a compact subset.

Prove that there is an actual smooth diffeomorphism F : X -> X, smoothly isotopic to the identity, and an actual smooth h : X -> R, such that

    F* lambda = beta + dh,
    F* omega = Omega.

Retain weak (nonstrict) taming, every admissible B, unrestricted primitive growth, and the compact-core exception. Neither completeness of the metric nor completeness of the Liouville vector fields is an extra hypothesis of this GENERAL exact-symplectic theorem. Prove the finite-type reference, properly embedded Stein reference, and common-reference corollaries with the scopes actually stated. Distinguish any partial intermediate result from completion of this theorem.

## Mandatory definition and statement policy

The user requires: whenever an object is called a Liouville manifold, its Liouville vector field is complete for ALL REAL TIMES, in both directions. Forward completeness, a semigroup, or a merely local flow is insufficient. Use the positive convention i_Z d lambda = lambda. General exact symplectic structures without this assumption must be named ExactSymplecticStructure or equivalent, never silently called LiouvilleManifold. A comparison between two objects called Liouville manifolds must carry their complete-primitive data. Separate this complete specialization from the more general manuscript theorem. An exact gauge change by dh does not on its own establish completeness of the given primitives or conjugacy of their Liouville fields.

Reuse suitable definitions rather than inventing disconnected substitutes. The old project was checked at cluster-skeleton commit 2c239b0c03922a1549f18ee3a45a8e0ca25bb28c. Its GeometryTarget.lean LiouvilleData uses FsFltz.Geometry.CompleteLiouvilleFlow literally; its conversion to CompleteLiouvilleManifold preserves the same manifold, primitive, field, and flow. Both use d lambda(Z,v) = lambda(v). The fixed public dependency is:

- fs-fltz-minimal: 1a3d387cfacc746e25aad31e5b27b1803103e7cb
- Mathlib: d13f23b723b8a846827a245b89c10fc7d3f11612
- Lean: leanprover/lean4:v4.34.1

At that pin, FsFltz/Geometry/Liouville.lean defines CompleteLiouvilleFlow using Flow R M.Point, jointly smooth action, and the actual chart ODE for every t : R. CompleteLiouvilleManifold includes that flow, without a finite-type assumption. FixedAmbient.lean provides CompletePrimitive M lambda with the actual fixed primitive, and a separate FiniteTypePrimitive. Smooth.lean supplies native Mathlib manifolds, tangent spaces, differential forms, exterior derivative, and diffeomorphisms.

Before substantive proof work, write and independently review a compilable statement module and a definition crosswalk at the pinned sources. Verify actual types, quantifiers, signs, differentiability, pullback and ODE meanings, not only names. Fix the statement and explain its exact correspondence with the note. Keep definitions, target propositions, constructions, and proved theorems distinct. Do not require another user approval unless a real mathematical ambiguity cannot be resolved without changing the requested theorem.

The paper's g = d beta(.,J.) and its induced tangent, dual, and operator norms must be explicit. The existing default/chart norm on Lean tangent spaces is not automatically this g. The inverse-form norm is the norm of the inverse contraction map from the g-dual to g. Smoothness on [1,infinity), the divergent improper integral, properness of R, and smooth isotopy must use genuine mathematical notions. The main conclusion allows +dh; primitive-preserving InclusionMarking is not a substitute. Reuse lower-level FsFltz/Mathlib structures and add the needed radial/metric wrappers and bridges with proofs.

## Proof acceptance

Archon chooses its own proof organization. The final theorem must construct the diffeomorphism and isotopy from the stated assumptions. Global Moser flows, their smooth dependence, both time directions, Cartan/exactness identities, or the comparison conclusion may not be assumed as unproved fields. A structure that packages these conclusions, an affine-space-only proof, or a theorem conditional on the desired global flows is only partial progress. Do not strengthen assumptions or weaken the conclusion to obtain compilation.

No sorry, admit, sorryAx, custom axioms, opaque unverified proof imports, or circular assumptions. Only the standard foundational axioms propext, Classical.choice, and Quot.sound are allowed transitively. Require independent mathematical statement review, reproducible build of the exact committed final library, transitive axiom audit of the actual final theorem and relevant declarations, source/dependency hashes, and consumers demonstrating the advertised interfaces. An execution marked Succeeded is not mathematical acceptance. Keep the goal open and state the precise blocker if the full proof remains incomplete.

## Final standalone project

Target GitHub repository: https://github.com/Hu-Mingyuan/exact-liouville-comparison (private empty shell, already created by the operator; no files uploaded). LATEST USER ORDER: complete the Lean work FIRST; uploading GitHub is the FINAL step. Do not push drafts, statements, intermediate proofs, documentation or other project files to GitHub during this run. Development remains in this objective's dedicated private local Forgejo repositories. Do not modify the old cluster project, source manuscript, ChatGPT sources directory, or upstream dependency. After complete Lean acceptance and matching final documentation, provide an exact commit and publication-ready tree for the operator's final GitHub upload. Do not claim publication without a verified remote readback.

Match the old project's useful layout:

- ExactLiouvilleComparison.lean and ExactLiouvilleComparison/ for the actual Lean library.
- Pinned lean-toolchain, lakefile.toml, and lake-manifest.json.
- README.md clearly linking the theorem, status, documentation, and verification instructions.
- docs/target-theorem.md, docs/proof-blueprint.md, docs/sources.json, and a definition-comparison document.
- docs/tex/ editable LaTeX and root target-theorem.pdf and proof-blueprint.pdf, rewritten to match the actual final statements and proofs.
- verification/ with statement review, transitive axiom audit, exact-source receipts, and interface consumers.
- scripts/ for reproducible builds/audits and .github/workflows/lean.yml for CI.

Prioritize Lean formalization now. Final packaging, rewritten PDFs, and GitHub publication come after the complete formal result. The final PDFs must explain complete Liouville terminology, the general exact-symplectic theorem, hypotheses and quantifiers, proof-to-code correspondence, and any remaining limitations. Compile and visually check them; do not issue a misleading completed-proof PDF while the formal theorem is open. Preserve accurate attribution and upstream licensing. Do not add a website, GitHub Pages, or unrelated applications.

## Resources and operation

Reuse existing installed Lean toolchains and managed dependency caches. Do not perform large fresh toolchain/dependency downloads or increase paid-provider/resource capacity without reporting the need. Ordinary lightweight project text, private Git transfers, compilation outputs, and this authorized formalization are in scope. Existing native worker capacity is three primary slots; use the previous conservative split of two work and one maintenance/review. Do not alter another run or global model default. Keep ownership and recovery inside this objective, and report evidence rather than self-certifying completion.
