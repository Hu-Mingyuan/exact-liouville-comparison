# Definition crosswalk and statement gate

Base: private repository fe83a2bb-5147-4bfd-b750-19b11c583d74, exact commit
1ec91645f801288f06b158a050c098f5511b9071. Binding
3fb80f88-28ed-4083-a923-74b7d0b3f32a, verified publication
e1c33fe7-6765-48b9-84ad-9c3931eb054b. The prepared Git HEAD is a stale skeleton;
source was reconstructed by authenticated exact-commit repository-file reads.

The existing independent statement gate is retained without redefinition:
`verification/first-path-flow/statement-review.md`, final additional prerequisite
assessment; statement SHA256
d1f8ad17b89f7acea0a9c757319bcfc027666df264c9471ba01d0c03164598f1.
The statement and parent scalar/open-neighborhood bridges remain byte-identical.
The versioned roadmap was read from e579622a-2cef-4703-be0b-345f68e1f0e7 at
c040da49e1af1954f49bb954c267dc1f7043f211:docs/objective.md and compared with
local bytes. The authoritative manuscript remains unchanged.

| Object | Actual definition and proof bridge |
| --- | --- |
| M | Pinned `SmoothManifold d`, a Hausdorff second-countable native boundaryless finite-dimensional smooth manifold. |
| Tangent field | `(t : ℝ) → (x : M.Point) → TangentSpace 𝓘(ℝ, Model d) x`. |
| Smooth domain | Actual open Ω in ℝ × M.Point containing Icc 0 1 × univ; native tangent-bundle-valued `ContMDiffOn ∞`. |
| Scalar control | Smooth P, `IsProperMap P`, `BddBelow (range P)`, and `abs (mfderiv P x (Z t x)) ≤ D` only for t in Icc 0 1. |
| Compact sublevel | Unchanged `ODE.compact_sublevel`; inverse image of a compact real interval using a global lower bound. |
| Bounded cutoff | Native Mathlib `exists_contMDiff_support_eq_eq_one_iff`; retains its range [0,1] conclusion, open region where χ=1, compact closed support inside Ω. |
| Section extension | Lift Z to native product section `(0,Z)`, multiply by χ using `ContMDiffOn.smul_section_of_tsupport`, then project via `equivTangentBundleProd`. Zero time here is only the section-extension proof, not the ODE suspension. |
| Auxiliary existence | Actual `CollarFlow.exists_global_solution`; its ODE suspension is `(1,W)` and its proof identifies the time coordinate. The auxiliary field is proved smooth and compactly supported. |
| Confinement | Unchanged `ODE.scalar_displacement` applied to W on Icc 0 1; absolute displacement handles every s and both time directions. |
| Output derivative | Full native `HasMFDerivAt`, linear map r ↦ r • Z(t,γ(t)), obtained by χ=1 pointwise from the full auxiliary equation. No weakening to within derivatives at endpoints. |
| Metrics and norms | No metric appears in the generic target. No chart norm is substituted for the explicit parent reference metric g or its induced dual/operator norms. |

No extra hypothesis, assumed solution, flow, or continuation field is added to
the exact target. The cutoff theorem itself is a proved construction. This is
finite-interval exact-symplectic infrastructure; it defines no Liouville manifold.
