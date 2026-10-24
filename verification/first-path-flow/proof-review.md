# Independent review of first-path flow prerequisites

Reviewer: delegated independent agent `flow_statement_review`, 2026-10-23.

**Bounded assessment: PASS.** The three reviewed modules prove the advertised
native open-neighborhood bridge, scalar estimates for existing curves, and
first-path input packages. No concrete mathematical or definition defect was
found. They do not construct a trajectory or an `Evolution`; the first-path
flow and manuscript comparison targets remain open.

## Exact scope and evidence

| Reviewed input | SHA-256 |
| --- | --- |
| `ExactLiouvilleComparison/ODEIntervalRegularity.lean` | `644643d6a1b33f6fe816e49b83fedccbeda377bb7a2ff23d8e5117a34d944bf7` |
| `ExactLiouvilleComparison/ODEScalarConfinement.lean` | `0b07b6c8765cb2cbe1a81407ec1f051f80fd9d3f5003fe711a99e2c708083fa8` |
| `ExactLiouvilleComparison/FirstPathFlowInputs.lean` | `7560d937b516b0a30b35151491af5d349496b2883255cd1a23f57d1ad629daa0` |
| `ExactLiouvilleComparison/FirstPathFlowStatement.lean` | `2c698398955a83619d3324db968796982952449a0aa4c1987ecb96730c721217` |
| `ExactLiouvilleComparison/ODEContinuationStatement.lean` | `d1f8ad17b89f7acea0a9c757319bcfc027666df264c9471ba01d0c03164598f1` |
| `verification/first-path-flow/crosswalk.md` | `d674b0bf9332be07bade8575f2940d2fc4db8679fa59e540f9a3207b07a17d75` |
| Supplied build receipt `/tmp/first-flow-proofs-check.json` | `0648c5b6af3bc59b4992bc0b858502f018964db35e692d80532ad1eca56343dd` |
| Pinned FsFltz `Geometry/Family.lean` | `6bf8ca0e50ad10402bd465491cf26bd177f0319da019d57d77b2e7134f6a0098` |
| Pinned FsFltz `Geometry/FamilyLiouvilleNeighborhood.lean` | `d8545f145609c777e8a7b414671f9223ca656198a4c654c119c508038fe8b9d1` |
| Pinned Mathlib `Analysis/Calculus/MeanValue.lean` | `7e1e6f097fe92a2493ea5b4bc9a1896c850514604f26f863f812906fb500b856` |

The supplied managed receipt reports successful compilation of
`FirstPathFlowInputs` and `ODEScalarConfinement`, including the imported
`ODEIntervalRegularity`, with `snapshot_verified: true`, Lean 4.34.1, and source
key `3ac98e31b5d712eaa87e7ca506bbe3113bfaba75f067e0eb44c23a875070df4c`.
This reviewer inspected the declaration bodies, actual imported definitions and
the relevant mean-value theorem. No new build, API operation, or source change
was performed. Previously accepted first-path estimates were treated as inputs
and were not re-reviewed. This report does not itself run a transitive axiom
audit; no `sorry`, `admit`, custom `axiom`, or opaque declaration occurs in the
three reviewed source modules.

## Native open-neighborhood bridge

`native_open_of_chart_family` unfolds the actual coefficient-family hypothesis
and chooses its open neighborhoods `U a` together with `ContDiffOn ℝ ∞` on each.
It constructs

`V a = (univ × chartSource a) ∩ (time, chart a) ⁻¹' U a`.

The chart map is only used as continuous on its actual source; the proof of
openness correctly uses `ContinuousOn.isOpen_inter_preimage`. Each point of
`[0,1] × M.Point` lies in `V x` for its own centered chart. The output is the
open union of all these sets, not a set merely containing pointwise smooth
germs on the strip.

At every point of that union the proof retains membership in one `U a`, uses
its openness to obtain a full coefficient `ContDiffAt ∞`, and applies the
actual `contMDiffAt_familySection_of_chart`. Thus the tangent section is smooth
at every point of the open union, including points outside `[0,1]`. This
resolves exactly the gap that `NativeJoint` alone could not resolve. The same
global real-indexed section `Z` is used in every chart; no unrelated local
fields or unjustified gluing equations are introduced.

`native_open_of_interval_family` preserves the single extension supplied by
`IsSmoothIntervalVectorFieldFamily` and its function equality at every
`Parameter`. This includes both endpoints. No uniform larger time interval or
extra off-interval nondegeneracy hypothesis is required.

`chart_hasDerivWithinAt` composes the actual manifold derivative of a valid
chart with the native solution derivative. The conversion to a real
one-variable derivative evaluates the resulting linear map at 1; `one_smul`
gives precisely `chartTangentMap a (γ t) (Z t (γ t))`. The chart-source premise
and interval-time witness are explicit. Endpoints retain their within-set
derivative meaning, rather than silently becoming interior points.

## Scalar estimates and compact confinement

`compact_sublevel` uses the actual global lower bound `b` to identify
`{x | P x ≤ A}` with `P ⁻¹' Icc b A`, then applies properness to that compact
real interval. This gives compactness in the original manifold topology and
uses no metric completeness assumption.

`scalar_hasDerivWithinAt` is the native chain rule for `P ∘ γ`. Its derivative
is literally `M.scalarDerivative P (γ t) (Z t (γ t))`, with no surrogate
operation. The proof again evaluates the composed linear derivative at 1.

`scalar_displacement` uses the actual real-valued derivative along the curve
on the convex set `J`. The auxiliary `rate` is defined outside `J` by zero only
to make it a total function; both the derivative and norm hypotheses of the
pinned `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` are used only on
`J`. The explicit inclusion `J ⊆ [0,1]` ensures all field values are defined
and all interval derivative hypotheses apply. The resulting bound is

`|P (γ t) - P (γ s)| ≤ D * |t - s|`.

It therefore handles both time directions, closed endpoints, open or half-open
trial intervals, and singleton intervals. It assumes an existing solution and
does not claim to produce one. No separate `D ≥ 0` is needed for this lemma:
at a point of a nonempty trial curve its absolute-derivative bound already
forces that inequality.

`compact_confinement` chooses the compact set
`{y | P y ≤ P x + D * A}` before quantifying over trial curves and their time
sets. It then uses the displacement bound and `D ≥ 0` to handle every time
distance at most `A`. For the entire unit time interval one may take `A = 1`.
The statement allows negative `A`, in which case the time-distance premise is
unattainable; this does not weaken the useful nonnegative-horizon assertion.
The compact set depends on the initial point and horizon, not on the trial
curve. This is the compact confinement needed for continuation, but the
continuation step itself is absent.

## Exact first-path consumers

`first_native_data` keeps arbitrary `G : AdmissibleGrowth 1`, the original
positive `C`, arbitrary compact `K`, and the original inverse-norm bound
outside `K`. It invokes the accepted `first_global` without strengthening that
bound. It independently invokes `first_intervalSmooth` with the same `G`, then
uses the new open-neighborhood bridge. Its equation identifies the output
extension literally with `FirstPath.X P G T hw x t.val t.property.1`.

`first_growth_data` invokes the accepted `first_growth_consumer` to choose its
`G`, scalar exhaustion, properness, lower bound, and uniform derivative bound.
It discards only that consumer's weaker `NativeJoint` conclusion and replaces
it with the proved stronger open-neighborhood output for the same field and
same growth witness. It does not choose a second unrelated coefficient.

In both declarations the scalar bound is transferred through exact extension
equality at every real `t ∈ parameterInterval`. It includes 0 and 1, and never
asserts a derivative bound for the extension off the interval. The exhaustion
is the accepted smooth proper bounded-below `FirstPath.exhaustion P G`.
These outputs have the types needed by the reviewed
`ODE.FiniteIntervalExistenceTarget`; they do not assume an inhabitant of it.

## Remaining obligations

The compiled prerequisites now prove the open-neighborhood and scalar-input
parts that the statement crosswalk listed as planned bridges. That crosswalk
remains accurate as a record of the statement gate; final delivery status
should identify these parts as proved while keeping flow construction open.

No trajectory existence, uniqueness, global solution family, joint smooth
dependence of solutions, inverse evolution, isotopy, or exact Moser pullback
identity is supplied by these three modules. The independently assigned generic
existence work and the parent's subsequent evolution assembly remain separate
obligations. Acceptance here is limited to the exact prerequisites above.
