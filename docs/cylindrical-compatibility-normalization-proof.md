# Smooth compatible normalization from a supplied metric

Mission `50754190-03fe-44b3-830e-5b109eca0470`. Integration owner:
`1f45f2d4-0edc-4d6b-8646-2c1212915b09`.

The proved endpoint is
`ExactLiouvilleComparison.CylindricalCompatibility.Normalization.normalization`
in `CylindricalCompatibilityNormalizationBundle.lean`. It inhabits the unchanged,
independently reviewed `NormalizationTarget IB F E omega h`. Its only geometric
inputs are a native smooth finite-dimensional real vector bundle, a smooth
fiberwise alternating nondegenerate bilinear form, and the supplied native
smooth positive metric. No compatible global complex structure is an input.

## Proof chain

1. In a continuous frame, the actual bilinear coefficients are `matrixIn e h`
   and `matrixIn e omega`. `form_matrixIn` proves their evaluation equals the
   supplied fiber form evaluated on inverse-frame vectors. Positivity,
   alternation and nondegeneracy transport to matrix positive definiteness,
   skew transpose and invertibility.
2. Write these matrices as G and W. Put H = sqrt(G), K = -H⁻¹ W H⁻¹,
   Q = sqrt(-K²), and J = H⁻¹ K Q⁻¹ H. All operations are the literal matrix
   operations and Mathlib continuous functional calculus. The algebra child
   proves -K² positive definite, J² = -1 and WJ = HQH positive definite.
   Alternation then gives J-transpose W J = W and omega(v,Jv) > 0.
3. Smoothness of square root on positive-definite families is proved using
   the inverse function theorem for squaring. The Sylvester derivative
   L ↦ QL + LQ is invertible by the spectral theorem and positive eigenvalues.
   Cone-relative continuity identifies the local inverse with CFC.sqrt.
   The proof never claims ambient smoothness of CFC.sqrt outside its positive
   locus. Matrix inverse smoothness gives inverse-root smoothness.
4. `contMDiffWithinAt_normalize` composes those proved analytic results with
   native manifold maps. All positive-root hypotheses are discharged from the
   metric and symplectic hypotheses; no square-root field or smoothness oracle
   is assumed.
5. For an arbitrary invertible change of frame P, the algebra proof shows
   normalization(P-transpose G P, P-transpose W P) = P⁻¹ J P. Its proof reduces
   through orthogonal whitening, rather than treating arbitrary P as a star
   algebra equivalence. `normalizeIn_frame_independent` transports this exact
   identity to equality of native fiber continuous linear maps.
6. `normalizedEndomorphism` uses a covering trivialization and the finite basis
   of the model fiber to choose a frame at each base point. Frame independence
   identifies this pointwise definition, near any point x, with the formula in
   the fixed chart at x. `bilinearCoordinates_apply` proves that the native
   nested Hom-bundle chart is the actual transported bilinear form.
   `contMDiffAt_hom_bundle` and the proved local matrix smoothness then show
   that the global endomorphism section is natively smooth.
7. If h(v,w) = omega(v,J₀w) and J₀² = -id in a fiber, the algebra recovery theorem
   gives J = J₀. The public contract uses the stronger compatible-J₀ hypothesis,
   and therefore yields recovery at every specified fiber. Neither smoothness
   nor a global extension of J₀ is needed.

All original fiber topologies and linear structures are retained. Matrices use
Mathlib's L2 operator-norm instance. The supplied metric is explicit and is
never silently substituted for the chart norm. No operator-norm estimates are
asserted in this prerequisite.

## Dimensions and native consumers

No proof assumes a nonzero rank or a nonempty base. The general formula and
naturality apply to `Fin 0` as well. The earlier independently reviewed native
zero-section proofs also remain available in `NormalizationDegenerate`.

`tangent_normalization` in `CylindricalCompatibilityNormalizationConsumers.lean`
(in the same Normalization namespace) instantiates the result on the pinned FsFltz manifold's actual
Mathlib tangent bundle and returns the project's `SmoothEndomorphism` plus
square, invariance, positivity and fiberwise recovery. Local tangent normed
instances are the model norm through Mathlib's definition of `TangentSpace`;
these local auxiliary chart norms preserve its native topology and module and
are not asserted to be a canonical metric or the reference metric g. The second consumer proves
recovery on an arbitrary set when the supplied metric already matches the
prescribed compatible endomorphisms there. It constructs no relative metric.
The algebra plane consumer checks the positive sign explicitly, and its
rank-zero consumer retains the empty matrix case.

## Reuse, provenance and verification

The pre-proof crosswalk and its independently accepted statement remain
unchanged. Mathlib was searched first, pinned FsFltz second, and the mandatory
cluster third. The retained crosswalk records why the existing compatible-path
and extension APIs did not prove existence. The missing analytic and algebraic
results were delegated as distinct durable missions:

| Result | Mission | Exact delivered private source | Verified publication |
| --- | --- | --- | --- |
| Smooth matrix square-root composition | `226d751b-2331-4986-a5b5-fbbc2f95df01` | `f67f524a8a32162b7faf16f9987ce4bbe941729e` | `7c0ca2c6-4afa-4d0f-ba55-04b7b29e9885` |
| Normalization algebra, recovery, GL naturality | `30bfbe32-1f63-42e8-8279-88f994bffb09` | `59832b30dff0014b87360ccb725261d55aaed16d` | `b3bd1ba1-6a27-4807-ada4-3b4f8cbd4dbb` |

Their imported source hashes match their independent final reviews. The bundle
owner composes and integrates these results; the children do not accept the
parent mission. Reproduce the full managed build, native consumer compilation,
unabridged declaration inventory and transitive axiom audit using
`python3 scripts/verify-cylindrical-compatibility-normalization.py`. The script
checks dependency pins, the unchanged accepted statement and manuscript,
source stability throughout all checks, equal verified source keys, complete
declaration coverage, and the allowed-only axiom set. Logs, receipt, declaration
types and audit are in `verification/cylindrical-compatibility-normalization/`.
The unabridged inventory is published as `types.txt.gz.base64` to fit the upload
limit; decode base64 and gzip to recover `types.txt`. Its uncompressed SHA-256
and byte count are recorded in the receipt. The reproduction script regenerates
both forms and checks exact round-trip equality. The independent final report
is `final-review.md` in that directory.

This delivers normalization only. The original cylindrical owner
`9997dc64-3871-4296-b839-1a516314042b` retains the actual form-to-Hom bridge,
relative metric construction/gluing, construction of the output metric
omega(.,J.), and cylindrical/contact extension. No claim of the whole
cylindrical theorem, final objective acceptance, GitHub upload or final packaging
is made here.
