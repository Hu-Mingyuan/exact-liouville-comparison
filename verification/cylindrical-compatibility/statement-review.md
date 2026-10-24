# Independent pre-proof statement and definition review

Mission: `deee4e3c-9772-491a-b842-98913f062983`.
Reviewer: independent statement-review agent `/root/statement_review`.
Date: 2026-10-24.

**Verdict: ACCEPT the statement and definition crosswalk as specifications
only.** I found no exhibited weakening, circular input, wrong sign, lost
quantifier, or incompatible native definition in the reviewed targets. This is
acceptance of the specifications, not of any existence or extension proof. All
four new target propositions remain unproved construction obligations.

**Scope supersession:** after this review was undertaken, the parent relayed
operator scope notice `235b0caa-465a-43e8-a65f-5540545fca5a`: stop expanding this
existence mission; the chosen cylindrical J is the intended comparison
assumption, and independent existence/extension is not a release prerequisite.
This mission is therefore discontinued by that scope clarification. The review
is preserved as bounded evidence only; it neither commissions substantive proof
work nor treats the optional unproved targets as release blockers. Release
assessment belongs to the integration owner under the clarified scope.

I read the statement-fidelity reviewer descriptor and independently compared
the new module with the manuscript's `eq:cylJ` and extension assertion (lines
376–392), the following finite-type corollary, the source's metric/inverse-norm
conventions, `docs/objective.md`, and the coverage ruling. I inspected constructor
fields and underlying definitions in the actual pinned dependency sources,
including `Smooth.lean`, `Liouville.lean`, `ExteriorDerivative.lean`, and Mathlib's
`VectorBundle/Riemannian.lean`, rather than relying on their names. I also read
the existing Geometry, Statement, and FiniteTypeComparison modules.

## Exact statement groups and quantifiers

The new namespace is `ExactLiouvilleComparison.CylindricalCompatibility`.
The complete explicit target binders and conclusions inspected are:

```lean
ExistenceTarget : Prop :=
  ∀ (d : ℕ) (D : LiouvilleDomain d) (C : Completion D),
    ∃ A : CompatibleStructure (completionReference C),
      Nonempty (CylindricalStructure C A)

ExtensionTarget : Prop :=
  ∀ (d : ℕ) (D : LiouvilleDomain d) (C : Completion D)
    (P : ContactData D),
    ∃ A : CompatibleStructure (completionReference C), Extends C P A

ContactExistenceTarget : Prop :=
  ∀ (d : ℕ) (D : LiouvilleDomain d) (C : Completion D),
    Nonempty (ContactData D)

ConsumerTarget : Prop :=
  ∀ (d : ℕ) (D : LiouvilleDomain d) (C : Completion D),
    ∃ A : CompatibleStructure (completionReference C),
      Nonempty (CylindricalStructure C A) ∧
      ∀ T : ExactSymplecticStructure C.ambient.manifold,
        WeaklyTames A T →
        (∃ B : AdmissibleGrowth 1, ∃ C₀ : ℝ, 0 < C₀ ∧
          ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ y t, t₀ ≤ t →
            A.inverseNorm T (C.endMap (y, t)) ≤ C₀ * B.B (Real.exp t)) →
        ExactComparison C.ambient.manifold T.primitive C.ambient.primitive
```

These are source declarations inspected with their dependencies, not a fresh
reviewer-generated `#print` dump. The parent-supplied managed build establishes
their elaboration; I performed no build or source edit.

There are no additional hidden universe-polymorphic manifold instances or
nonemptiness/positive-dimension hypotheses in these declarations: native
instances come from the explicitly quantified `SmoothManifold` packages.
`ContactExistenceTarget` deliberately retains the completion binder even though
its result only mentions D. This is the commissioned completed-domain scope;
it is not a proof of unconditional existence for domains without completions.

Existence does not take A, a cylindrical witness, a global Moser flow, or a
comparison as input. Extension takes arbitrary prescribed P and returns A.
Separate contact existence prevents extension from standing in for an existence
claim by vacuity. The consumer chooses A before quantifying T and reproduces
the existing `FiniteTypeTarget` premises literally. T need only have a smooth
primitive with symplectic exterior derivative, weak nonnegative taming, and the
stated eventual end bound. No primitive growth, metric completeness, or complete
Liouville flow for T is added. The universal existing comparison theorem also
permits consumption of the A produced for any prescribed P, once its
cylindrical witness has been constructed.

## Contact representation and native geometric crosswalk

`alpha D` is the literal pullback of `D.liouville.primitive` by the smooth
boundary inclusion. Its derivative is the actual chartwise Mathlib `extDeriv`
transported by `mfderiv`. Pinned `exteriorDerivative_pullback` proves naturality;
no arbitrary differential or naturality callback is supplied as an input.
Tangent fibers are native `TangentSpace`, forms are continuous alternating maps,
and the end formula uses the actual differential of `C.endMap`.

The `ContactData` representation is mathematically faithful. Write R for its
Reeb field and π(v) = v − α(v)R. Normalization gives π² = π and image π = ker α.
Its horizontal and Reeb-annihilation fields say Jπ = J and πJ = J. Its square
field says J² = −π. Consequently restriction to ker α squares to −id;
invariance and strict positivity restrict to ordinary dα-compatibility. Reeb
annihilation by dα makes invariance on *all* boundary tangent vectors equivalent
to invariance on the kernel; it is not a stronger symplectic requirement on the
odd-dimensional full tangent space.

Conversely, given the smooth kernel subbundle, its compatible smooth j, and the
actual smooth Reeb field, J = inclusion ∘ j ∘ π has exactly the specified
identities and vanishes on the Reeb line. The ambient endomorphism-section
smoothness in `SmoothEndomorphism` is the native Hom-bundle notion; it is not
smoothness in an assumed global frame. Reeb smoothness uses the pinned chartwise
vector-field definition. This argument identifies the necessary Lean bridge;
the bridge is not proved merely by the structure declaration or by this review.

`Extends` quantifies every y, every real t with 0 ≤ t, every boundary tangent v,
and every real s. It imposes

    J_X Dend(v,s) = Dend(Jv + s R, −α(v)).

At (v,s) = (0,1) this gives J_X(∂t) = R; at (R,0) it gives
J_X(R) = −∂t; on ker α it is the prescribed radius-independent j. Since
r = exp t, ∂t = r∂r. These are exactly the manuscript's positive convention.
The formula fixes the boundary t = 0 as well as every later time; eventual
agreement after a cutoff would not prove this target. To check the compatibility
sign, the actual end form is exp(t)(dt ∧ α + dα), so its value on
((v,s),(Jv+sR,−α(v))) is exp(t)(dα(v,Jv)+s²+α(v)²), which is positive for
nonzero (v,s). Establishing this identity and smooth transport in Lean remains
part of the construction.

The output's `CompatibleStructure` requires smooth native J, J² = −id,
symplectic invariance, and a native `Bundle.ContMDiffRiemannianMetric` whose
inner product is exactly dβ(v,Jw). I checked that the metric constructor includes
symmetry, strict positivity, bounded unit balls, and smoothness. `MetricTangent`
installs its norm; `covector` transports the unchanged functional to that norm;
`inverseContraction` is constructed from actual nondegeneracy and finite
dimension; `inverseNorm` is its operator norm from that g-dual to g. Thus the
consumer uses the manuscript's norm, not a hidden chart norm.

The completion ambient is literally `CompleteLiouvilleManifold`: its specified
field satisfies dβ(Z,v) = β(v), and its `CompleteLiouvilleFlow` contains a native
`Flow ℝ`, jointly smooth action, and chart ODE for every real time. This is
legitimate reference geometry already in the source setting; it is not an
assumed Moser flow for the comparison. The new output has no such circular flow
field. The comparison conclusion is an actual native diffeomorphism, smooth
identity isotopy (including smooth inverse family), smooth h, literal +dh
identity, and exterior-form identity.

## Boundary cases and indispensable proof obligations

No parity or nonemptiness restriction is imposed. If d = 0,
`CompactDomain.zero_boundary` makes the boundary empty; P and the end formula
then have empty boundary quantifiers, but A on the ambient still must be
constructed. The zero-dimensional tangent metric and zero J satisfy the usual
definitions; no spurious strict positivity on the zero vector is demanded. If
the ambient or domain is empty in other dimensions, the pointwise statements
are appropriately vacuous. If a boundary point exists, the dimension and
invertible end-differential facts must follow from geometry; they are not new
hypotheses. There is no assumption of a globally trivial contact bundle.

If the optional existence/extension targets are resumed in a future separately
authorized scope, the following would be their indispensable proof obligations;
acceptance here does not discharge them or require them for the clarified
comparison release:

1. Construct the actual smooth Reeb field and compatible contact data from the
   Liouville domain/completion geometry, including contact nondegeneracy.
2. Construct the native smooth ker(α) subbundle presentation and prove both
   restriction and zero-extension bridges, with the smoothness equivalence.
3. Prove native pullback/end identities and construct a smooth compatible J
   globally that fixes the entire specified closed end. Local or pointwise
   linear algebra alone, or a result starting from an assumed global J, is
   insufficient. The seam at t = 0 must be addressed.
4. Construct the required smooth metric with the exact `metric_eq`, including
   its finite-dimensional boundedness field.
5. Convert P plus `Extends` to the unchanged `CylindricalStructure`, derive
   existence without vacuity, and consume the already universal
   `FiniteTypeComparison.finiteTypeTarget` with its exact T premises.

Minor nonblocking documentation precision, corrected by the parent before the
final crosswalk hash below: `FiniteTypeRadialMetric.end_derivative_surjective`
delegates to upstream `C.endMap_isLocalDiffeomorph`; it does not itself perform
the positive-dimension count. The statement's surjectivity type was unaffected.

## Build evidence and exact source bindings

The settled `statement-build.txt` records `passed`, `ok=true`, return code 0,
and `snapshot_verified=true` for
`lake build ExactLiouvilleComparison.CylindricalCompatibilityStatement`, source
key `980e83fbcee8f4b64651cd8a14ff271fd8d0e1e3bc349ff9d6c0a62ba5bf3c5c`.
It reports Lean 4.34.1 and only the unused C-binder linter warning. I checked the
receipt after the parent replaced an earlier source-changed/deferred log; the
earlier deferred log is not acceptance evidence. This is a statement build,
not a final proof build, proof review, or transitive axiom audit.

Pinned dependency HEADs independently read:
`fsfltz` = `1a3d387cfacc746e25aad31e5b27b1803103e7cb`;
`mathlib` = `d13f23b723b8a846827a245b89c10fc7d3f11612`.

SHA-256 bindings at review:

| File | SHA-256 |
| --- | --- |
| `ExactLiouvilleComparison/CylindricalCompatibilityStatement.lean` | `9e48006f6407c3405ca4a4f438c8f535c806e888b293e9aef5eaf60261151ff9` |
| `docs/cylindrical-compatibility-crosswalk.md` | `f4735f7bf4a980b2aabafa5100d393d4d0a6cc52a8ac4623e8bddedd863d0664` |
| `docs/reference/exact_liouville_comparison.tex` | `8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576` |
| `docs/objective.md` | `0f7ca4a2449cca3d400e7afda913364582be71f858fe31475fa60665502ce5e8` |
| `docs/manuscript-coverage-decision.md` | `ca6b9f9fd4bbff200baea465861a366db784410c684c3408d2ab04c61f6d45e2` |
| `ExactLiouvilleComparison/Geometry.lean` | `2b30f2be23bb8f1338b72ed0fdfd26f67ee8fef1cf70f4f5f4a5e7430a307326` |
| `ExactLiouvilleComparison/Statement.lean` | `ff7798a4a5c0adc5b27b27766bddc7b123a6923d0c9063983b7a04eb5daa07b7` |
| `ExactLiouvilleComparison/FiniteTypeComparison.lean` | `68910a4ecf2f6a6fe1750abb097bc6e47ef24ce849ee8c16f2f9fb82f0ff36d5` |
| `.lake/packages/fsfltz/FsFltz/Geometry/Smooth.lean` | `57b89da972058e0f3e2b963d9c291ca8dfcdc60f3b5c5904c8e3ae6f9e6cecbd` |
| `.lake/packages/fsfltz/FsFltz/Geometry/Liouville.lean` | `d51b04337e39b31ab1b1d3b20093ba5956b8ea0b04456e141ef4c827268b335e` |
| `.lake/packages/fsfltz/FsFltz/Geometry/ExteriorDerivative.lean` | `498095c7bfa18204b0bb1bfba2943c42e3c257d27a74efe85e85df74077962ad` |
| `.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean` | `044b397c80cc85430415afd4f976195943dd0015170cd0388d445dc09098c979` |
| `lake-manifest.json` | `2790d3bafa974c7cbdd6e9ca85ac8e33d1caf801ab00d645ceebaea8aa65ba83` |
| `verification/cylindrical-compatibility/statement-build.txt` | `869ed797fe312bbdcec1a723650ecd9288d97cf72bff43ebadff49fec8e7fcdf` |

Only this review file was written by this reviewer. The manuscript, shared
Lean sources, existing proofs, and dependency sources were not modified.
