# Independent bounded proof and fidelity review

Date: 2026-10-23. Mission: `509d5a0f-ce2f-4fe5-9a4c-2365ff3cf96b`.
Reviewer: delegated native proof reviewer, independent of implementation and build ownership.

**Verdict: pass this bounded source-level proof/fidelity review.** No correctness,
statement-fidelity, circularity, or concrete maintainability blocker was found in
the four modules below. This is not mission acceptance. Final transitive axiom
audit remains a separate required check, and finite existence from the two-barrier
hypotheses remains the separate parent work item (`c88064ba`, assignment
`33e55321`). This bridge does not prove the full two-barrier theorem or the
manuscript comparison theorem by itself.

## Exact source identity and scope

Reviewed checkout:
`/home/no_body/.local/share/archon-horizon/fast-runtime/provider-scratch/ccc1d5f5-2295-4090-a2de-3e5286db723f/smooth`.
The task identifies private baseline `70cb5f533db3755922378f2324a928398ac4b3a2`;
the checkout HEAD observed during review was
`5022b07efef2fab159e53504bba6dd1a7c3afb56`. The review is bound to these file
hashes, computed before the full read and checked again after the supplied final
build:

| Module under `ExactLiouvilleComparison/` | SHA-256 |
| --- | --- |
| `ODETwoBarrierLocalization.lean` | `ef7d37a76a994e2be21424a7f52e81b11b5f856160c3c16bfa278ebf8593daba` |
| `ODETwoBarrierLocalizationPatch.lean` | `5cdc67126ed2028ec672ced1dcd0539c51d825c7ae480c8a45c6ce20106776e5` |
| `ODETwoBarrierSmoothAssembly.lean` | `bd707273547418472904e8260c0d1a3e03f14ae1951fb85e309f6b79e20a7138` |
| `ODETwoBarrierSmooth.lean` | `41edf8838dc5a99744e252a76b498b7f98d448da1415e07b203bbbcc80c1bf87` |

All 433 source lines of these modules were read. Dependencies were inspected to
understand the actual statements and reused proofs, without modifying them. The
accepted `verification/radial-interpolation-flow/crosswalk.md` and
`statement-review.md` were read and their statement gate was not repeated. The
objective and unchanged manuscript were read from the primary workspace because
those documentation files are absent from this isolated checkout. The inspected
manuscript hash is
`8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576`.
The manifest pins FsFltz `1a3d387cfacc746e25aad31e5b27b1803103e7cb` and
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Literal statement and fidelity

The main declaration is
`ExactLiouvilleComparison.ODE.evolution_of_finite_existence`.
Its only geometric parameters are arbitrary `d`, native FsFltz `M : SmoothManifold d`,
and the dependent tangent field `Z : ℝ → (x : M.Point) → M.Tangent x`.
Its explicit assumptions are an open spacetime set `Ω` containing
`parameterInterval ×ˢ univ`, native `ContMDiffOn` of the actual tangent-bundle
section on `Ω`, and the specified finite existence premise. For every
`s : Parameter` and every `x`, that premise supplies a real-domain curve with
`γ s.val = x` and the actual `HasMFDerivAt` velocity equation at every real
`t ∈ parameterInterval`. It assumes neither smooth dependence nor any evolution,
composition, inverse, or all-real solution equation.

`Parameter` and `parameterInterval` are literally `Icc 0 1`. FsFltz's manifold
uses native Mathlib charts on finite-dimensional Euclidean space, with Hausdorff,
second-countable, boundaryless smooth structure; `Tangent` is native
`TangentSpace`, and `SmoothEquiv` is native `Diffeomorph` at order infinity.
There is no extra nonempty-manifold, compact-manifold, metric-completeness, proper
function, or scalar bound assumption in the final bridge. Completeness of the
finite-dimensional model in reused local analysis is not completeness of a
Riemannian metric on `M`.

The conclusion is literally `Nonempty (FirstPathFlow.Evolution (fun t => Z t.val))`.
The unchanged contract file has hash
`2c698398955a83619d3324db968796982952449a0aa4c1987ecb96730c721217`, matching the
accepted statement review. Every field is constructed: native diffeomorphisms,
a real double-time extension on an actual open neighborhood of the entire closed
strip, initial identity, native and chart equations, closed unordered-interval
uniqueness, composition, inverse, and smooth isotopy including its inverse family.
No metric or symplectic operation is replaced here; this is a general ODE bridge.
No Liouville manifold or complete original field is asserted.

## Proof groups and library reuse

1. **Compact localization.** `smoothEvolution_of_compact_support` uses the pinned
   `CollarFlow.exists_global_solution` for a smooth field with compact spacetime
   support. Its inspected implementation constructs solutions by suspended native
   integral-curve continuation. `eq_of_hasMFDerivAt` supplies composition and
   inverses, and `contMDiff_joint_of_hasMFDerivAt` supplies joint regularity only
   after those auxiliary all-real trajectories have been constructed. It has no
   assumed smoothness of the chosen trajectory family. Actual slice smoothness
   gives the two directions of a native diffeomorphism.
   `compact_field_localization` constructs a scalar cutoff equal to one on an
   open neighborhood of a compact set, with compact support, and multiplies the
   actual field by it. The reused `contMDiff_cutoff_field` uses native product
   tangent-bundle equivalences and smooth section multiplication.
   `eqOn_closed_of_hasMFDerivWithinAt` localizes around the union of the two compact
   spacetime traces and applies `SmoothEvolution.unique_closed` to both curves.
   The latter's inspected proof handles a singleton separately, otherwise joins
   the curve to auxiliary trajectories on both sides and proves matching native
   derivatives at the joins before applying native uniqueness.

2. **Open patches.** A finite trajectory has compact spacetime trace by its native
   differentiability and continuity. The localized auxiliary evolution agrees
   with it on the closed interval by the existing closed uniqueness theorem.
   `enlarged_interval` extends an open time set containing `[0,1]` to a slightly
   larger closed interval. Compactness of that larger interval and continuity of
   the auxiliary evolution give an open set of initial data whose entire traces
   stay where the fields agree. Thus `evolutionPatch_of_finite_curve` constructs
   all `EvolutionPatch` fields; the structure is output data, not a circular
   certificate in the final assumptions. `EvolutionPatch.agree` invokes the
   pinned open-interval uniqueness theorem on the intersection of both patches'
   time intervals. Both the initial and terminal times are proved to lie there.

3. **Assembly.** `evolutionDomain` is the union of open patch domains. Classical
   choice defines `localEvolution`, and agreement of patches proves equality with
   each local smooth representative. This yields native joint smoothness and
   the actual ODE by neighborhood equality. The arbitrary fallback outside this
   domain is the input point; no regularity or ODE claim is made there. Finite
   existence proves coverage of every pair of closed time parameters and every
   point. Although the union is expressed using all valid patches, coverage is
   established by the constructed finite-curve patches, and uniqueness proves
   independence of the choice; there is no existential assumption hidden here.

4. **Final consumer.** `evolution_of_finite_existence_global` derives closed
   uniqueness, composition, and inverse from the assembled actual solutions.
   Both directions of each diffeomorphism are smooth slices of the same open
   double-time extension. `chart_hasDerivWithinAt` transports the native ODE
   through the actual chart differential. For isotopy, the clamped parameter
   supplies diffeomorphisms for every real isotopy parameter; on `[0,1]` it is
   exactly `u*t`. Forward and inverse families are proved smooth on that closed
   interval using the smooth expressions `Φ 0 (u*t)` and `Φ (u*t) 0`.
   No global smoothness of the clamp is asserted or needed by the unchanged
   isotopy contract. Finally, the inspected `extend_strip_field` constructs a
   globally smooth auxiliary field using a separating smooth cutoff supported
   inside `Ω`, equal to one on the closed strip. Its support need not be compact,
   and no completeness of this extension is inferred. Pointwise equality on the
   entire closed strip transports the finite premise and the final `Evolution`
   back to the original `Z`.

This is a direct reliable route with the pinned interfaces: compact cutoffs
supply the all-real trajectories required by the existing smooth-dependence
result, and uniqueness glues their local representatives. The necessary bridges
(open initial-data neighborhoods, double-time gluing, and transport from the
open strip) are actually proved. The small amount of repeated evolution assembly
is structurally straightforward; no concrete maintenance consequence warrants a
blocking refactor. The local transparency option affects elaboration and is not
an added mathematical axiom.

## Edge cases, trust, and evidence limits

Endpoints are included in both the finite premise and the conclusion; each
constructed patch has strict time margins past zero and one. Reversed time
segments use `uIcc`; singleton uniqueness reduces to identity in the reused
closed-uniqueness proof. Empty manifolds are not excluded: constructions are
pointwise and neither introduce a chosen global point nor require `Nonempty M`.
Open neighborhoods may shrink with the spatial point; there is no unjustified
uniform exterior time strip at spatial infinity. Inverse isotopy regularity is
proved explicitly, including the closed endpoints.

I performed source inspection, hash checks, and a textual check of the four
modules for admissions/custom axioms/unsafe implementations, finding none. I did
not run Lean, any build, or an axiom audit, as required by the review assignment.
I read the supplied `../final-build.json`: after an out-of-date cache diagnostic,
it records successful rebuild of all four modules, return code zero,
`snapshot_verified: true`, Lean 4.34.1, and source key
`fe000d07640d1c6888744ae2cb10031d557e6db72c95eefbb2588bc22927e36b`.
This is build-owner evidence, not an independent execution by this reviewer.

The transitive axiom audit was pending when this report was written. Neither
successful compilation nor textual absence of `sorry` proves that audit. The
integration owner must retain exact-source evidence that the relevant declarations
use only `propext`, `Classical.choice`, and `Quot.sound` transitively. This report
reviews the bounded bridge and selected dependency proofs, not every upstream
proof, the separate finite-existence implementation, or final manuscript theorem
acceptance. No source or dependency was edited, and this report is the only file
written by the reviewer.
