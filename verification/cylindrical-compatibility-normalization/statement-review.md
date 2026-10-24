# Independent normalization statement review

Mission: `50754190-03fe-44b3-830e-5b109eca0470`.
Reviewer: independent `normalization_statement_review` agent.
Scope: supplied-metric normalization only; this does not repeat the parent
cylindrical statement review or accept any normalization proof.

## Final decision: ACCEPT repaired statement and crosswalk

Accepted source SHA-256:
`a100611cd3ccc7a9076e318f3b4fc8e376f1dd9e1fc304004e4adec270ec2fc3`.
Accepted crosswalk SHA-256:
`3c009a3a5bbd22219fff51ac1b6e3ed5140d057b9e3c48d95c74e0a1f8ab906c`.
The rebuilt authoritative receipt in `statement-build.txt` passes with
`snapshot_verified=true`, source key
`d94192df4bbe81390dee7fd7a86a662c7fd9c64bcb555878c7045381097db1eb`,
and Lean 4.34.1.

The repaired declaration explicitly binds `[IsManifold IB ∞ B]`,
`[FiniteDimensional ℝ F]`, and `[ContMDiffVectorBundle ∞ F E IB]`.
Independent reinspection of source and a second successful managed temporary
`#print` confirm that all three now occur in the elaborated target type.
The temporary probe again has `snapshot_verified=false` and is only diagnostic;
exact-source build evidence is the authoritative receipt above. The crosswalk
now correctly distinguishes the more general `SymplecticForm` record from the
finite-rank smooth normalization target. R1 is resolved.

This accepts the contract for substantive proof work. There are no remaining
statement-level repair requests. Native smooth normalization, recovery, all
required transport/consumer bridges, and the eventual proof axiom audit remain
to be proved and reviewed. No existence theorem is accepted here.

## Revision 1 decision: REPAIR REQUIRED

Reviewed source SHA-256:
`d99285124e926ada0f946880b2db951d50ec030e5395a102c6b2460a45c4c1d1`.
Reviewed crosswalk SHA-256:
`bc1546bc1c518bf6cae8742e235425556a34b77c0a29ad151b4a9cb2489040c8`.
The statement build passed with `snapshot_verified=true` and source key
`0a62eabf4ad751419d18f7e68f3bd7d4cabd7b13e740bbba556ae05e4f47d433`.
Compilation does not detect the specification defect below.

**R1 — actual declaration closure omits intended hypotheses.** The three
section variables `[FiniteDimensional ℝ F]`, `[IsManifold IB ∞ B]`, and
`[ContMDiffVectorBundle ∞ F E IB]` do not occur in the elaborated
`NormalizationTarget` type. Lean removes these unused section variables.
Consequently revision 1's actual target is not restricted to the advertised
finite-rank smooth bundle over a smooth manifold. In particular, finite-rank
normalization cannot be justified by citing a finite-dimensional section
variable that does not survive into the declaration.

A temporary managed diagnostic compiled the exact statement text followed by
`#print SymplecticForm`, `#print NormalizationTarget`, and `#print axioms
NormalizationTarget`. The printed target retains normed model/fibers,
`FiberBundle`, and `VectorBundle`, but none of the three intended hypotheses.
The temporary-project receipt had `snapshot_verified=false`; this diagnostic
is not represented as an exact-source acceptance receipt. Its declaration
closure agrees with inspection of the source. The printed target-definition
axioms were only `propext`, `Classical.choice`, and `Quot.sound`; this is not a
proof-theorem axiom audit.

Required repair: put the three hypotheses explicitly in the target declaration
(or another binder mechanism that demonstrably retains them), then rebuild and
inspect the elaborated type. `SymplecticForm` may retain its more general carrier
assumptions; the crosswalk must distinguish those from the normalization
contract's finite-rank smooth hypotheses.

## Definition and mathematical findings

The following findings are favorable independently of R1.

- `FiberBundle` supplies genuine local trivializations covering each point and
  an inducing inclusion of each fiber into the total space. `VectorBundle`
  requires those trivializations to be linear and their coordinate changes
  continuous. At a covered point,
  `Bundle.Trivialization.continuousLinearEquivAt` is an actual continuous linear
  equivalence from `E x` to `F`. Thus retained finite dimensionality of `F`
  implies finite dimensionality of the actual fibers; an additional fiber-rank
  assumption is unnecessary. `ContMDiffVectorBundle` requires the actual
  coordinate changes to be smooth, rather than furnishing a substitute
  smoothness operation.
- `SymplecticForm.form` is an actual curried continuous bilinear map on each
  fiber. Diagonal vanishing gives skew-symmetry over ℝ by bilinearity.
  Nondegeneracy is the vanishing-left-kernel condition, exactly matching the
  tangent-form nondegeneracy convention after currying. No isomorphism or
  inverse contraction is assumed. In finite rank the required inverse must be
  constructed from nondegeneracy.
- Both smoothness clauses use native `ContMDiff` into the actual iterated Hom
  bundle or endomorphism bundle. Mathlib's `hom_chart` and
  `contMDiffAt_hom_bundle` identify these with smooth transported local
  coefficients; `continuousLinearMapCoordChange` uses the genuine source and
  target coordinate changes through `arrowCongrSL`. This is not smoothness of
  a raw family in a globally identified model fiber.
- The metric is literally `Bundle.ContMDiffRiemannianMetric`: its fields are
  continuous bilinear `inner`, symmetry, strict positivity off zero,
  `IsVonNBounded` unit sublevel sets, and the native smooth section. Its
  `toRiemannianMetric` preserves these inner products. Existing fiber norms
  are only topology-bearing norms here. Metric adjoints or square roots must
  use the supplied inner products, with explicit transport if existing norm
  instances are replaced. No reference-metric or dual-norm estimate is hidden
  in this auxiliary statement.
- `Compatible` demands `J²=-id`, form invariance, and the positive convention
  `omega(v,Jv)>0`. It is the required compatibility condition, not merely
  taming. The proposal `h(Av,w)=omega(v,w)` has the correct sign: when
  `h=omega(.,J₀.)`, invariance gives `A=J₀`. Then `-A²=id`, so the proposed
  positive polar normalization recovers `J₀`. This calculation checks the
  proposed formula; it is not a formal construction or smoothness proof.
- The existential output J precedes all recovery quantifiers. Recovery is
  pointwise for every compatible `J₀ : E x →L[ℝ] E x` whose induced metric
  equals h at that fiber. It requires neither a globally defined J₀ nor its
  extension or smoothness. Uniqueness on a recovery fiber follows from
  nondegeneracy, so simultaneous recovery clauses are consistent. No global
  compatible J, square-root operator, spectral regularity, normalization map,
  or Moser flow is an input field.
- There is no positive-rank, nonempty-base, connectedness, compactness,
  completeness, or parity hypothesis. Rank zero is retained: every vector
  vanishes, `-id=0`, and off-zero positivity is vacuous exactly as it should be.
  An empty base has the empty section. Odd positive rank with a nondegenerate
  alternating form is excluded by the actual form assumptions, not by a
  hidden domain restriction. Supplied h avoids any need for a paracompactness
  or partition-of-unity assumption in this auxiliary normalization theorem.
- No closedness assumption is needed for an alternating form on a general
  vector bundle. This terminology does not claim a symplectic base manifold.
  Allowing base corners does not alter the boundaryless comparison theorem.

## Consumer and proof boundaries

The unchanged manuscript's equation `eq:cylJ` and the subsequent extension
assertion prescribe a compatible structure on the cylindrical end. Normalizing
a glued metric h can preserve it exactly because the recovery clause applies
at every end fiber where h equals the prescribed compatible metric. Gluing h
and constructing the contact/cylindrical data remain parent obligations.

For the native tangent-bundle consumer, set `IB=𝓘(ℝ, Model d)`, `B=M.Point`,
`F=Model d`, and `E=M.Tangent`. The output smoothness clause is then precisely
`ExactLiouvilleComparison.SmoothEndomorphism M J`. The original
`CompatibleStructure` still requires a native smooth metric
`g(v,w)=evalTwo (d beta) v (J w)`. From normalization's compatibility this
metric can be constructed, but it is not an output field already proved here.
In particular the integration must prove:

1. Currying the actual alternating form `d beta` produces this contract's
   `SymplecticForm`, including its native Hom-section smoothness. FsFltz
   `IsSmoothForm` is chart-based, so that bridge must be proved, not identified
   by name or treated as definitional equality.
2. The induced positive symmetric form `omega(.,J.)` is a native smooth
   Riemannian metric, including the bounded-unit-ball field, and packages the
   unchanged `CompatibleStructure`.
3. A local matrix normalization obeys the appropriate transport/naturality
   identities and its square root/inverse depends smoothly on the input.
   Smooth chart coefficients alone do not justify assembling inconsistent
   local choices. An intrinsic construction must still prove native section
   smoothness.

The inspected FsFltz `CompatibleComplexPath` requires two compatible endpoints;
its path construction does not discharge existence. `CompatibleComplexExtension`
constructs coframe-conjugated complex structures and does not supply the required
symplectic compatibility normalization. These APIs do not remove the stated
proof obligations.

## Sources checked

The unchanged manuscript SHA-256 is
`8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576`.
Dependency checkouts were inspected at actual HEADs:
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`,
FsFltz `1a3d387cfacc746e25aad31e5b27b1803103e7cb`; toolchain is
`leanprover/lean4:v4.34.1`.
Read definitions include Mathlib `Topology/FiberBundle/Basic.lean`,
`Topology/VectorBundle/Basic.lean`, `Topology/VectorBundle/Hom.lean`,
`Topology/VectorBundle/Riemannian.lean`,
`Geometry/Manifold/VectorBundle/Basic.lean`,
`Geometry/Manifold/VectorBundle/Hom.lean`, and
`Geometry/Manifold/VectorBundle/Riemannian.lean`; FsFltz
`Geometry/Smooth.lean`, `CompatibleComplexPath.lean`, and
`CompatibleComplexExtension.lean`; and the local `Geometry.lean` consumer.

`NormalizationTarget` is a specification, not an existence theorem. No
normalization proof, cylindrical extension proof, or full-objective acceptance
is certified by this review.
