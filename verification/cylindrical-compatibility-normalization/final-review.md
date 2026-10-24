# Independent final review: native supplied-metric normalization

Mission: `50754190-03fe-44b3-830e-5b109eca0470`.
Reviewer: independent `normalization_final_review` agent, 2026-10-24.

**Verdict: ACCEPT the completed smooth bundle normalization prerequisite.**
No blocking mathematical, statement-fidelity, native-interface, consumer, or
axiom-closure defect remains in the exact source snapshot identified below.
This is a proof acceptance of the unchanged `NormalizationTarget`, not merely
acceptance of a target proposition or a successful build.

The result constructs a native smooth compatible endomorphism from the actual
supplied metric and alternating nondegenerate fiber form, with fiberwise
recovery. It does not accept relative metric gluing, the actual differential-form
to Hom-bundle bridge, the induced output metric, cylindrical extension, or the
full Liouville comparison theorem. Those remain the parent's obligations.

## Review scope and preserved contract

I read all normalization Lean source files: the statement, degenerate cases and
checks; the square-root statement, Sylvester and regularity proof; the algebra
statement, algebra, recovery, naturality, native bridges and consumers; and the
new Regularity, Coordinates, Frames, BundleCoordinates, Bundle and Consumers
modules. I read the pre-proof crosswalk and review, both dependency proof reviews,
the final proof/progress guides, verification script, declaration inventory and
axiom programs, managed logs, receipt and relevant elaborated endpoint types.

I independently recomputed all 36 source hashes and all three published generated
artifact hashes in the final receipt; every hash matched. I checked the retained
Sqrt and Algebra sources against the hashes in their prior independent reviews;
all match. The statement, crosswalk and authoritative manuscript retain their
accepted hashes. This review introduces no replacement contract.

The elaborated `normalization` type retains finite-dimensional model fiber,
`IsManifold IB ∞ B`, and `ContMDiffVectorBundle ∞ F E IB`, and its conclusion is
literally the reviewed `NormalizationTarget IB F E omega h`. No global compatible
J, square-root certificate, assumed regularity, positivity-rank condition,
nonempty-base assumption, completeness assumption, or desired normalization
conclusion is an input. Smoothness and recovery are actual proved consequences.

## Mathematical proof findings

**The supplied metric is used, with the correct sign.** `matrixIn` contains the
actual coefficients of the continuous bilinear form in an actual continuous
linear frame, and `form_matrixIn` proves its evaluation law. Metric symmetry and
strict positivity yield native matrix `PosDef`; alternation and the left-kernel
nondegeneracy condition yield skew transpose and invertibility. The second kernel
condition needed by the matrix nondegeneracy API is proved using alternation.
No arbitrary inverse pairing or replacement form operation is introduced.

The literal formula is H = sqrt(G), K = -H⁻¹ W H⁻¹,
Q = sqrt(-K²), and J = H⁻¹ K Q⁻¹ H. Its negative sign agrees with
h(Av,w) = omega(v,w), whose matrix is A = -G⁻¹W. The algebra proves
-K² positive definite, J² = -1, and WJ = HQH positive definite; symmetry then
gives invariance. The transported theorem therefore gives exactly
omega(v,Jv) > 0 for every nonzero v. The canonical-plane consumer independently
exhibits the prescribed positive convention.

**Smoothness is proved for the actual native formula.** The square-root dependency
proves the full Sylvester operator invertible using spectral coordinates and
positive eigenvalue sums, then applies the inverse function theorem to squaring.
Continuity relative to the positive cone identifies that local inverse with
native CFC.sqrt. Matrix inverse smoothness is used only after proving the root
is a unit. The integration's manifold composition theorems use those proved
within-set results, and discharge positivity of the polar square using the
metric and symplectic hypotheses. There is no assumed square-root field,
smoothness oracle, or invalid claim of ambient smoothness for totalized CFC.sqrt.

**Arbitrary frame changes are handled before gluing smoothness.** Both G and W
transform by congruence. The algebra naturality proof reduces arbitrary
invertible P to an orthogonal whitening transition and proves
N(PᵀGP,PᵀWP) = P⁻¹N(G,W)P. `frameChange`, `matrixIn_frameChange` and
`normalizeIn_frame_independent` transport this identity to equality of actual
fiber continuous linear maps. No orientation, orthogonality or determinant-sign
restriction is imposed on the original frame change.

`normalizedEndomorphism` may choose a covering frame separately at each point;
it does not assert those choices themselves vary smoothly. At each fixed base
point its values on the covering neighborhood agree with the formula in that
one fixed local trivialization. `bilinearCoordinates_apply` proves that nested
native Hom coordinates transport both bilinear arguments by the inverse frame.
`endomorphismIn_coordinates` proves the corresponding endomorphism-coordinate
identity. The local smooth coefficient formula and native
`contMDiffAt_hom_bundle` then prove the actual total-space section smooth.
This proves chart compatibility rather than assuming a chartwise certificate.

**Recovery has the advertised quantifiers.** At a single fiber, h(v,w) =
omega(v,J₀w) and J₀² = -id imply recovery by the algebra theorem. The public
contract legitimately specializes this stronger fact to compatible J₀.
The output J is fixed before quantifying over all recovery fibers and J₀.
No smoothness or extension of a prescribed J₀ is needed. The subset consumer
recovers any supplied J₀ on any set where the supplied metric matches it.
It does not hide the parent's separate task of constructing that metric.

**All finite ranks and empty bases remain covered.** The frame construction uses
`Fin (finrank ℝ F)` without a nonempty-index hypothesis. The matrix algebra and
regularity dependencies include zero rank; the unique matrix is a unit there.
The positivity assertion quantifies only nonzero vectors, so the zero-rank
case is correct. The earlier native zero-section proofs remain available,
including transport of model subsingletonness through actual trivializations.
On an empty base all pointwise constructions and assertions are vacuous.
No positive-rank, parity, connectedness or base nonemptiness assumption was added.

## Native interface and metric check

I checked the pinned definitions of Mathlib `ContMDiffRiemannianMetric`,
`contMDiffAt_hom_bundle`, nested `inCoordinates_apply_eq₂`, and `TangentSpace`,
and the local project's `Geometry.SmoothEndomorphism`. The bilinear smoothness
criterion and output smoothness are literally native Hom-bundle smoothness.
The input metric is the native record containing its actual bilinear inner
product, symmetry, positivity, bounded unit sublevel set and smooth section.

The tangent consumer initially needed local normed instances because Mathlib's
native `TangentSpace` intentionally registers only its topology and linear
structure. The final local instances reuse the model norm through its defining
type synonym. Its derived topology, additive group and module agree, and the
native tangent total-space topology and atlas remain the ones used in the
consumer. This norm is an auxiliary chart norm; it is not identified with h or
the reference metric g. The normalization formula uses h.inner explicitly,
and no metric operator-norm estimate occurs in this prerequisite.

The compiled `tangent_normalization` returns the project's actual
`SmoothEndomorphism M J` together with square, invariance, strict positivity
and fiberwise recovery. The second native consumer gives subset recovery for
the literal `normalizedEndomorphism`. Their elaborated types use the supplied
native tangent metric/form and do not require a compatible global J.

## Verification and reproduction evidence

The final receipt records three successful managed checks with return code zero
and `snapshot_verified=true`, all with source key
`19e5815b49e1915d49ca23dd41011ecfa863462c939cd0564b219cb9b14df972`:

1. Build of `CylindricalCompatibilityNormalizationConsumers` and its imports.
2. Execution of the complete declaration inventory program.
3. Execution of the transitive axiom audit program.

The toolchain is Lean 4.34.1. Mathlib is pinned at
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and FsFltz at
`1a3d387cfacc746e25aad31e5b27b1803103e7cb`.
I compared the three log receipt records to `final-receipt.json`; they agree.
I did not run a competing Lean build. Compilation evidence comes from the
inspected managed runs; source, mathematics and artifact consistency were
reviewed independently.

The inventory, audit and receipt have equal sets of 344 elaborated declaration
names, with no duplicate inventory names. They cover all 148 explicitly named
source declarations and the generated helpers/instances, including both local
tangent normed instances and the actual main theorem and consumers.
`Lean.collectAxioms` is transitive. Every recorded set is contained in
`{propext, Classical.choice, Quot.sound}`, and the union is exactly those three.
There is no source admission, custom axiom or unverified proof substitute in
the reviewed implementation.

The reproduction script checks pinned dependency HEADs, immutable statement,
crosswalk and manuscript hashes, imported prerequisite source identities,
source stability before/after all checks, a shared verified source key, named
source coverage, unabridged type output and the axiom allowlist. Its compressed
inventory representation uses deterministic gzip time and checks a lossless
base64/gzip round trip. I independently decoded it and obtained exactly the
18,774,671-byte raw inventory with the recorded hash. I checked that the full
inventory has no omission marker. The script requires the configured managed
`horizon-lean-check` environment; no fresh rebuild of all pinned dependencies
is claimed.

## Exact source and artifact identity

The following new source files are under `ExactLiouvilleComparison/`; the common
filename prefix is `CylindricalCompatibilityNormalization`.

| Suffix | SHA-256 |
| --- | --- |
| `Regularity.lean` | `8b03aea572f0bace8424a99f2355b34b5849a55ec8fd6c9fff8f90c99d571326` |
| `Coordinates.lean` | `c09c5d1fb367e4839be2046380003ad29363d1057789fabe66211d780b8c2f21` |
| `Frames.lean` | `bb9f33d44a4d81e1e0e63e83bbf6d5acf1435e861e0ebbad0fbac602c49be6e9` |
| `BundleCoordinates.lean` | `e3ad9a4ee3183b1e2c440b57865821969613780296b503628fa7a6d5eb2dfc33` |
| `Bundle.lean` | `8f1c86bddf64304a1a4148a0a7d5511770787a3c54a45f6a5a0b73d1999bf32b` |
| `Consumers.lean` | `72a56a7c46785639af2a161367c1de469722205df7d1d48f2c9dc8b595dabf84` |

Additional exact bindings:

| Artifact | SHA-256 |
| --- | --- |
| Accepted `NormalizationStatement.lean` | `a100611cd3ccc7a9076e318f3b4fc8e376f1dd9e1fc304004e4adec270ec2fc3` |
| Accepted crosswalk | `3c009a3a5bbd22219fff51ac1b6e3ed5140d057b9e3c48d95c74e0a1f8ab906c` |
| Final proof guide | `a1d802b074ab5db6ed8540d56da0f511fad30e06dcacb7c43f26df515b723ec3` |
| Final progress record | `f1981f26d0c03b10c77a5767814c37a56b6cb6fbb13ce93dde6673929549a757` |
| Verification script | `5c06319c2d11526d3d13a453d452fdb572a092b284fae7cf4fc47e268976f330` |
| `final-receipt.json` | `8a64ed23599148769afc2e8b418ddbb55841b292af405d67d920a98396f02fc8` |
| Raw inventory `types.txt` | `b1f91b4faedd4af2c036811df9fff8c9bec0ab43840ae9b1bef1e3e63dd090f9` |
| Published `types.txt.gz.base64` | `7d97d630bf7a7b29a1b611170a2755257b1374a787cd12ed5fea33367cec3a63` |
| `types.txt.names` | `feda920bea48e2dea892ad40543b05e42776c4059d6acdf280b266685f7880a6` |
| `axioms.tsv` | `17eb9beb27401edf6182267fa5dea62d9ae6c2da925ed10fc0cf3198755d3a97` |

The complete binding of older normalization sources, native Geometry,
documentation, pins and audit programs is in the hashed final receipt.

This acceptance is bound to the source hashes and verified snapshot above.
It may carry forward to an evidence-only private publication that preserves
those bytes; exact publication identity still requires a separate readback.
This report does not itself assert a private commit exists or that its remote
contents have been checked. No GitHub upload, full-objective acceptance or final
project packaging is authorized or certified by this bounded review.
