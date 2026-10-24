# Cylindrical end derivative and exact metric calculation

Import `ExactLiouvilleComparison.FiniteTypeRadialMetric`.
`ExactLiouvilleComparison.FiniteTypeRadialMetric.target` proves the unchanged,
independently reviewed `Target`. It is a local end theorem for a supplied smooth
`R` satisfying `EndRadius`, not a construction of `R` or `RadialReference`, and
not a proof of `FiniteTypeTarget` or `MainTarget`.

The proof keeps the original `C`, primitive, `A.J`, `A.g`, and native tangents.

1. `end_derivative_surjective` uses the continuous linear equivalence furnished
   by FsFltz `Completion.endMap_isLocalDiffeomorph`. Its upstream proof uses the
   native immersion and finite-dimensional rank, treating dimension zero via
   the empty boundary. No positive-dimensional hypothesis is added.
2. `radius_end_derivative` differentiates `R o endMap = exp o snd` on a genuine
   open neighborhood of `(y,t)` for `t > log 2`. Mathlib's `HasMFDerivAt.comp`,
   `hasMFDerivAt_snd`, `mfderiv_comp`, and `EventuallyEq.mfderiv_eq` give
   `dR(d endMap(v,s)) = exp(t) s`.
3. `end_time_derivative` composes the native derivative of `s ↦ (y,s)` with
   `endMap`. FsFltz `CompleteLiouvilleFlow.isMIntegralCurve` proves the native
   manifold ODE from the actual all-chart ODE; `Completion.end_flow` identifies
   the curve with that all-real-time flow. Hence `d endMap(0,1) = Z`.
4. `primitive_identity` uses tangent surjectivity, the given cylindrical `J`
   equation, and `Completion.end_primitive` to obtain `beta = -dR o J` on all
   ambient tangent vectors.
5. `field_inner` uses the prescribed `g = d beta(.,J.)`, positive contraction,
   the primitive identity evaluated on `Jw`, and `J²=-1`. Thus `g(Z,w)=dR(w)`.
6. `radius_dualNorm_sq` identifies the transferred native covector with the
   Mathlib Riesz image of `Z`. The isometry and `inner_self` identity give
   `dualNorm(dR)^2 = g(Z,Z) = dR(Z) = exp(t) = R` exactly.

The consumers use both `exp(t)>2` and the parent's literal `c=1` radial-field
notation, retaining the equality before taking the bound. They require no
parent draft module and do not introduce a radius reference as a hypothesis.

## Reuse and trust

Mathlib supplies the native manifold chain/product/germ derivative rules,
local-diffeomorphism derivative equivalence and Riesz isometry. FsFltz is used
for the pinned completion, its proved local diffeomorphism, and the proved
bridge from its complete flow's chart ODE to the native integral curve.
The existing unchanged project `LinearAlgebra.metricInnerProductSpace` equips
the already defined metric norm with the exact same inner-product core;
`metric_inner_eq` is literally `A.metric_eq`.

The prior cluster source at commit
`2c239b0c03922a1549f18ee3a45a8e0ca25bb28c` was inspected in
`ClusterSkeleton/GeometryTarget.lean` and `GeometryNativeBridge.lean`.
Its `LiouvilleData` uses `CompleteLiouvilleFlow`, but it supplies no cylindrical
radius/dual-norm calculation needed here. No prior project or dependency is
modified or newly imported.

Run `python scripts/verify-finite-type-radial-metric.py` with the existing
`HORIZON_LEAN_BUILD` policy. It checks the consumer, then serially emits full
elaborated types and audits every declaration under the owned namespace with
`Lean.collectAxioms`. It verifies the pinned dependency revisions, unchanged
reviewed semantics and manuscript hashes, a stable source snapshot, complete
inventory, and only `propext`, `Classical.choice`, `Quot.sound` transitively.
`verification/finite-type-radial-metric/receipt.json` binds the source and
relevant dependency hashes to the three managed check receipts. Concatenate
`inventory-001.txt`, `inventory-002.txt`, and subsequent numbered parts in order
to recover the full UTF-8 declaration inventory; the receipt gives its aggregate
and per-part hashes. Splitting preserves every byte, including all explicit types.

The parent mission `9329795b-7d27-46a3-adb3-79b3711aaf56` retains radius
construction, compactness, growth conversion and integration. This delivery
adds only metric-mission paths. No criterion was removed or weakened, and no
mission correction was required. Final acceptance is subject to independent
source-bound final review; no GitHub upload or final PDF belongs to this mission.
