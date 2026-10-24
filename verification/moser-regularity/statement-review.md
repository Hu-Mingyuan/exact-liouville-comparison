# Independent bounded statement and definition review

Reviewer: native helper `/root/statement_review`, 2026-10-23. Scope: mission 60ad47b3 revision 1, the compiled `MoserRegularityStatement` specifications and their definition crosswalk, before substantive proof implementation. This is a bounded mathematical assessment, not formal PR approval, mission acceptance, a proof review, or acceptance of the main comparison theorem.

**Assessment: no blocking semantic or statement-fidelity defect found in this scope.** The specified inverse-contraction regularity and compact bounds are faithful intermediate claims. They remain unproved specifications. Globalization, trajectories, complete Moser flows, and exact comparison are subsequent obligations, not consequences supplied by compiling this module.

## Sources and checks

Read `docs/objective.md`, the authoritative manuscript's Moser convention and radial interpolation lemma (lines 153–208) and first-path proof (lines 280–303), the statement module, crosswalk, inputs manifest, and managed build/type receipts. Inspected the actual definitions in `Geometry`, `Statement`, `RadialCoefficient`, `RadialInterpolationCoefficient`, `FirstPathVector`, `RadialInterpolationGeometry`, and `RadialInterpolationEstimates`, plus the representative `FirstPathChecks` and `RadialInterpolationChecks` consumers. Inspected the pinned FsFltz `Smooth`, `Family`, `SmoothLiouville`, `FamilyLiouville`, and `FamilyLiouvilleNeighborhood` definitions/proofs, and Mathlib's inverse differentiability API and `ContDiffAt` definition. Read the supplied definitions and statement-fidelity reviewer descriptors.

The dependency checkout HEADs are exactly FsFltz `1a3d387cfacc746e25aad31e5b27b1803103e7cb` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; `lean-toolchain` specifies `leanprover/lean4:v4.34.1`. Every file SHA-256 in `verification/moser-regularity/inputs.json` matched the current file. The Geometry/Statement hashes below match that manifest's unchanged accepted semantic baseline.

No builds or API mutations were performed by this reviewer. The supplied managed statement-build receipt reports `ok: true`, `snapshot_verified: true`, source key `1d6a2a831210662822f62c666c01800bdbc8650a143114d38792919c4894eae0`. The initial out-of-date diagnostic is followed by an actual successful rebuild. The elaborated-type receipt separately reports success with source key `9b78a6003531db776e48cce81e7c1853490bc898b5fad93d4f5981c1a283188c`. This review does not independently certify transitive axiom closure; final implemented producers and consumers still require the prescribed audit.

## Definition and source correspondence

1. **Native geometry and generality.** `M : SmoothManifold d` contains native Mathlib charts and smooth-manifold instances, Hausdorffness and second countability, for arbitrary finite dimension. Its tangent fibers are `TangentSpace`, forms are fiberwise continuous alternating maps, chart transport uses actual `mfderiv`, and exterior differentiation uses Mathlib `extDeriv`. No affine-space restriction is introduced. `NativeJoint` uses the genuine tangent-bundle model for the section `(t,x) ↦ (x,Z_t(x))`, not smoothness of an unrelated scalar or arbitrary operation.

2. **Interval endpoints and locality.** `Parameter` is the subtype `[0,1]`, and `parameterInterval` is the same closed interval. The one extension in `NativeJoint` agrees with all interval slices, and ambient `ContMDiffAt` is required at every interval-space point, including both endpoints. There is no uniform strip assumption and no hypothesis of nondegeneracy outside the interval. `IsSmoothFormFamily` supplies actual jointly smooth chart coefficients on open neighborhoods of the closed interval times chart targets. The pinned open invertibility theorem and native chart-section bridge provide an appropriate route to a producer.

   Precise future consumer caveat: `ContMDiffAt ∞` is pointwise infinite differentiability; its Euclidean counterpart quantifies over finite orders. The specification does not itself package a single open set on which the extension is `ContMDiffOn ∞`. If a later flow API requires that stronger open-set package, prove or retain it from the smooth inverse construction. Do not claim it merely by unfolding `NativeJoint`. This is not a defect in the presently stated compact-bound targets.

3. **Inverse bridge and signs.** `InverseBridgeTarget` universally quantifies over independent smooth two-form and covector families. Its only algebraic hypothesis is pointwise nondegeneracy at interval times. It requests an actual solution and proves uniqueness through equality with every solution. The equation is positive contraction `omega(Z,w)=alpha(w)`. Thus the Moser applications use `alpha=-k(R) beta` and `alpha=-delta(R) beta`, exactly as the manuscript. FsFltz's existing Liouville contraction theorem specializes the two-form to the differential of its RHS primitive, so the proposed independent-form bridge is a justified generalization. No smooth inverse or flow is an input field.

4. **Metric identity is preserved.** `CompatibleStructure.g.inner` is explicitly equal to `d beta(v,Jw)`. `MetricTangent` selects this metric's norm; `Dual`, `covector`, and `dualNorm` select its dual norm; `inverseNorm` is the continuous inverse contraction norm from this dual to this tangent norm. Existing inverse contraction is constructed by finite-dimensional linear algebra. An auxiliary Euclidean chart identification used in the new producer must be identified with it by the intrinsic contraction equation and uniqueness. No norm estimate in the target silently uses a chart norm.

5. **First-path target.** `firstField` is literally the accepted `FirstPath.X`, and its nonnegative-time proof includes `t=0`. Existing `X_equation`, `X_unique`, and `X_zero` identify its equation and the initial slice `W`. `FirstTarget` asks for joint native smoothness and one nonnegative absolute derivative bound for every compact spatial set, uniformly over all interval times. `scalarDerivative` is the actual manifold derivative of `exhaustion = log(S(R))`. This is the manuscript's compact-set regularity step. The absence of an inverse-growth hypothesis here is legitimate: that hypothesis is needed for the exterior estimate, not for smoothness or compact boundedness. Later globalization must retain the arbitrary compact exception already present in `FirstPath.exterior_estimate`/`growth_consumer`.

6. **Interpolation target.** `interpolationField` is the accepted pointwise inverse for the convex coefficient and `delta=q1.rho-q0.rho`. `WeakDifferential` allows degenerate `d sigma`, including the checked zero case. The coefficient framework handles `R=1` using half-line smoothness and the actual within derivative; composition smoothness and derivative lemmas have already been proved. `barrierRate` is the actual spatial derivative of `Q_u(R)` plus `delta(R)*R`; `Q_parameter_derivative` proves that this latter term is the actual time derivative. The requested signs `XR ≤ C0` and `-C1 ≤ barrierRate` match the manuscript. The constants are simultaneous and uniform in time on the entire closed core `R ≤ rstar`, which is compact by properness and `R ≥ 1`.

   Neither coefficient ordering nor divergence is needed for these compact-core bounds. Their omission is therefore a valid generalization, not a lost hypothesis. They must be restored when invoking exterior `radial`/`Q_directional` and `uniform_exhaustion` to deduce global bounds and reverse-time control. These targets do not assert those global conclusions.

No complete-Liouville object is introduced or weakened. These are exact-symplectic intermediate claims and do not establish completeness of either original primitive. No circular conclusion-bearing data, assumed Moser flow, `sorry`, `admit`, or custom axiom occurs in the reviewed statement source.

## Exact reviewed hashes

SHA-256:

| File | Hash |
|---|---|
| `ExactLiouvilleComparison/MoserRegularityStatement.lean` | `fecaeb5bfe5e16df859c8805915e525cca0ddbbe084f0c0649dc9532e6c9eb0b` |
| `verification/moser-regularity/crosswalk.md` | `181207fb6387a7ad7eebf43e2071ede701776be086f776dfca20efaea06a78f6` |
| `verification/moser-regularity/inputs.json` | `2e3ff03002d9dd4b0a5bdca6f0282d5ee728b2735694836081d38f3e8b6876fa` |
| `verification/moser-regularity/statement-build.log` | `6990335795270028ab2a544b1d389674dac75f58e02ef61c97faa53ed11bdf1f` |
| `verification/moser-regularity/statement-types.log` | `cb434430803fed954714ac915b93bfa11a40e9b821b9c37ccb579589fa6b044c` |
| `docs/objective.md` | `0f7ca4a2449cca3d400e7afda913364582be71f858fe31475fa60665502ce5e8` |
| `docs/reference/exact_liouville_comparison.tex` | `8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576` |
| `ExactLiouvilleComparison/Geometry.lean` | `2b30f2be23bb8f1338b72ed0fdfd26f67ee8fef1cf70f4f5f4a5e7430a307326` |
| `ExactLiouvilleComparison/Statement.lean` | `ff7798a4a5c0adc5b27b27766bddc7b123a6923d0c9063983b7a04eb5daa07b7` |
| FsFltz `Geometry/Smooth.lean` | `57b89da972058e0f3e2b963d9c291ca8dfcdc60f3b5c5904c8e3ae6f9e6cecbd` |
| FsFltz `Geometry/Family.lean` | `6bf8ca0e50ad10402bd465491cf26bd177f0319da019d57d77b2e7134f6a0098` |
| FsFltz `Geometry/SmoothLiouville.lean` | `87001a87f6b54001cce44c43b21d8f0ffb2b69af8c538e2bc9a81f9f84d5e51a` |
| FsFltz `Geometry/FamilyLiouville.lean` | `1074e0847e613315a996874688c753057cd92b01b5f2998bdedec9fa06344f16` |
| FsFltz `Geometry/FamilyLiouvilleNeighborhood.lean` | `d8545f145609c777e8a7b414671f9223ca656198a4c654c119c508038fe8b9d1` |

The crosswalk's cluster-archive reuse history was not independently re-audited here; none of the reviewed specifications depends on a cluster-specific flow theorem. Parent owns implementation, integration, global consumers, and subsequent acceptance evidence.
