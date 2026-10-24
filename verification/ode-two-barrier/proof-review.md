# Independent bounded integration review: full two-barrier evolution

Date: 2026-10-23. Reviewer: delegated independent proof reviewer; no implementation edits, Lean builds, or axiom audits performed.

**Verdict: pass for the source-level integration of the generic ODE target. No defect found.** The theorem `ExactLiouvilleComparison.ODE.twoBarrierEvolution` composes the reviewed finite-existence producer with the reviewed finite-existence-to-evolution bridge and concludes the literal unchanged `ODE.TwoBarrierEvolutionTarget`. Exact-source compilation and transitive axiom acceptance remain separate build-owner obligations. This report does not accept radial applicability, any comparison theorem, the entire objective, or publication.

## Scope and source binding

Inspected tree: `/home/no_body/.local/share/archon-horizon/fast-runtime/provider-scratch/b6688f87-bebd-4b49-8f64-beb706227741/two-barrier`. Observed checkout HEAD: `ad07637b5d37a57be0f47a52f21d3e4f1bb882f7`; the wrapper and some integrated component files are untracked in this review checkout. The review therefore binds to the actual file hashes below, not to a claim that checkout HEAD contains them.

The assignment identifies the finite component's private source as `161487be39fee21c4ff64e660b32d120d9a4a77e` and the smooth bridge's private source as `e6b264151f8e1eed8e42f4b52e91e853fc0ff860`. The checkout does not resolve the former object, so this review does not independently certify those commit-to-tree bindings. It does independently verify that all six reviewed component module hashes match the supplied independent component reports exactly. Retaining exact private-source provenance is the integration owner's obligation.

I also read the supplied `../child-binding.json` (identified by the owner as artifact `d1abbd57-bcc4-4776-84ca-30d952fd46f2`). Its four published smooth-component Lean hashes and proof-review hash match the inspected files. It records private commit `e6b264151f8e1eed8e42f4b52e91e853fc0ff860` and a `git_tree_delta` publication receipt. The owner reports fetching the files through the exact-commit repository API and separately retaining the finite source's readback receipt as artifact `88a5a7b6-ee9f-4065-baa5-2f47ec32399f`. These are supplied provenance records, not an independently repeated remote readback by this reviewer. The actual source compatibility checked here has no mismatch.

| Artifact relative to the inspected tree | SHA-256 |
| --- | --- |
| `ExactLiouvilleComparison/ODETwoBarrier.lean` | `86fb566e2a61507e33d4168a6dede320111d59fed5891da2680ad259231c8aa0` |
| `ExactLiouvilleComparison/ODETwoBarrierStatement.lean` | `81b206239999b41a479672cc5a73673115a5c09f3393d0438674bf2df794eb17` |
| `ExactLiouvilleComparison/FirstPathFlowStatement.lean` | `2c698398955a83619d3324db968796982952449a0aa4c1987ecb96730c721217` |
| `ExactLiouvilleComparison/ODETwoBarrierConfinement.lean` | `bd10ac404e00c985b50091701882400f08576e77758ebd85eeffdbd419501959` |
| `ExactLiouvilleComparison/ODETwoBarrierExistence.lean` | `fc2efd63070a58bf63b84ce143cbc850dddd9aace5b4e93ca9d580a85507a8df` |
| `ExactLiouvilleComparison/ODETwoBarrierLocalization.lean` | `ef7d37a76a994e2be21424a7f52e81b11b5f856160c3c16bfa278ebf8593daba` |
| `ExactLiouvilleComparison/ODETwoBarrierLocalizationPatch.lean` | `5cdc67126ed2028ec672ced1dcd0539c51d825c7ae480c8a45c6ce20106776e5` |
| `ExactLiouvilleComparison/ODETwoBarrierSmoothAssembly.lean` | `bd707273547418472904e8260c0d1a3e03f14ae1951fb85e309f6b79e20a7138` |
| `ExactLiouvilleComparison/ODETwoBarrierSmooth.lean` | `41edf8838dc5a99744e252a76b498b7f98d448da1415e07b203bbbcc80c1bf87` |
| `verification/ode-two-barrier/finite-proof-review.md` | `59bcd899521bead5db3376a3dda54baa05b07d69be015e6887edc596425f7333` |
| `verification/ode-two-barrier-smooth/proof-review.md` | `c42323ae26cbf84422261713d3cdb352ef4e180dc0a617a4b380a94477556c63` |

The target and `Evolution` hashes also match the independent statement review. The inspected definition crosswalk hash is `54ed4154d99265fbbbb29d6e63c2506fee66f59c7a1cca58d7f574068c87b732`; its statement review hash is `540e299db4d8835212bf708e1dcac3a0fc73e83229e55b0805ed521342e0f9eb`. The checked finite-component dependency hashes (`ODEContinuationCutoff`, `ODEScalarConfinement`, pinned `CollarEvolution`, and Mathlib `MFDeriv/SpecificFunctions`) likewise match its existing independent report. The manifest retains FsFltz `1a3d387cfacc746e25aad31e5b27b1803103e7cb` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

I read the objective and manuscript, the wrapper, literal target, literal `Evolution` and `IsSolution`, both consumed theorem declarations and their containing proof modules, the prior independent component reports, and the statement crosswalk/review. Prior component proof coverage is reused; the localization and confinement proofs are not independently re-proved in this bounded integration review. The unchanged manuscript was read from the primary workspace and has SHA-256 `8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576`.

## Quantifiers and composition

1. The new theorem at `ODETwoBarrier.lean:13` has precisely `TwoBarrierEvolutionTarget (M := M)` as its conclusion, with arbitrary natural dimension and native `M : SmoothManifold d`. There are no extra section assumptions. Line 14 introduces all and only the target's arguments: the dependent tangent field, open spacetime neighborhood and containment of the closed strip, native bundle smoothness there, smooth proper lower-bounded R, globally jointly smooth Q, its uniform coercivity implication, nonnegative C0 and C1, and the three one-sided derivative bounds. No new compactness, metric completeness, absolute rate estimate, trajectory, or evolution assumption appears.
2. `twoBarrier_finiteIntervalExistence` receives those arguments in exactly the target's order and with the same field, domain, functions, constants, and proof witnesses. Leaving its final `s : Parameter` and `x : M.Point` arguments unapplied supplies the universally quantified premise required by the bridge: for every initial time and point there is a curve on real time, initialized at that point, satisfying full native `HasMFDerivAt` at every time in `parameterInterval`. The curve need not solve the original field outside that interval. It is a constructed output of finite existence, not a new hypothesis.
3. `evolution_of_finite_existence Z hΩ hstrip hZ` uses the same open neighborhood and native bundle section and consumes precisely that finite-existence premise. Its result is literally `Nonempty (FirstPathFlow.Evolution (fun t : Parameter => Z t.val))`, exactly the target's result. There is no field substitution, loss of initial times, endpoint restriction, changed derivative notion, or conditional flow premise at this composition boundary.
4. Reading the actual consumed bridge confirms its globally smooth extension is constructed internally and equals Z on the entire closed strip. Its finite-existence premise is transported to that extension, and the resulting evolution is transported back by equality of the restricted fields. No global smoothness or all-real completeness of the original field is assumed by the integration.

## Every output field retained

The integrated theorem returns the entire unchanged structure, without projecting a weaker consequence. The bridge's record construction explicitly supplies each field:

| `Evolution` field | Actual retained obligation |
| --- | --- |
| `map` | Native smooth diffeomorphism for every pair of initial and terminal parameters. |
| `extension`, `agrees` | Real double-time extension agreeing with those maps on the closed square. |
| `smooth` | Native joint smoothness on an actual open subset of real double-time spacetime containing the full closed square times the manifold. No uniform exterior time margin is asserted. |
| `initial` | Identity for every initial time and every point. |
| `solves` | Explicit continuity and native manifold ODE on all of `[0,1]`, with within derivatives at both endpoints. The finite premise used in construction has full derivatives there. |
| `chart_solves` | Actual chart equation using the native chart differential at the evolved point, whenever it belongs to the chart source. |
| `unique` | Every continuous native solution on `uIcc s t` has the prescribed terminal value; both time directions and equal times are included. |
| `compose` | Evolution composition for arbitrary r, s, and t in the interval. |
| `inverse` | The inverse diffeomorphism is the reversed-time map. |
| `isotopy` | Each map from time zero is smoothly isotopic to identity, including joint smoothness of the inverse family on the closed isotopy interval. |

`parameterInterval` and `Parameter` are literally `Icc 0 1` in pinned `Family.lean`. I checked `SmoothlyIsotopicToIdentity` in `Geometry.lean`: it requires an actual family of native diffeomorphisms, the two endpoint identities, and joint `ContMDiffOn` for both forward and inverse families. The bridge's clamped family agrees on the closed interval with smooth double-time expressions for each direction, as already reviewed. Nothing here asserts smoothness of the clamp outside that interval. The open smooth extension of the evolution itself is the stronger separate `smooth` field.

## Geometry and noncircularity

Pinned `Smooth.lean` was checked directly: `SmoothManifold` installs native Mathlib finite-dimensional boundaryless charts, Hausdorff and second-countable structure; `M.Tangent` is native `TangentSpace`; `M.SmoothEquiv` is native `Diffeomorph` at order infinity; `M.scalarDerivative f x v` is actual `mfderiv` applied to v. The ODE is expressed using native manifold derivatives and the continuous linear velocity map `a ↦ a • Z`, not arbitrary operations. The checked `Smooth.lean` hash is `57b89da972058e0f3e2b963d9c291ca8dfcdc60f3b5c5904c8e3ae6f9e6cecbd` and `Family.lean` hash is `6bf8ca0e50ad10402bd465491cf26bd177f0319da019d57d77b2e7134f6a0098`.

This generic ODE target has no symplectic, metric, dual-norm, or operator-norm assumptions to reinterpret. It introduces no replacement for those quantities and does not establish their radial applicability. It does not call its finite-interval evolution a complete Liouville flow or assert an all-real flow of Z. Completeness required elsewhere for objects called Liouville manifolds is unaffected.

The finite component constructs solutions by cutoff and confinement; the smooth component constructs the required smooth dependence, diffeomorphisms, and identities from finite solutions. The integration discharges the latter's existence premise with the former's theorem. Consequently an assumption that was intentionally intermediate in the bridge is no longer an input of the full generic theorem. The new wrapper is an actual proof term, not merely a target definition. Textual inspection of the wrapper and consumed modules found no `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration; prior reports cover the other component modules. This textual check does not replace a transitive axiom audit.

## Acceptance boundary

Accept the bounded source-level integration review for the exact bytes listed above. The integration owner must separately retain a successful build of the exact integrated source and a transitive audit of the actual final generic theorem allowing only `propext`, `Classical.choice`, and `Quot.sound`, as well as private-source provenance and mission accounting. I ran no Lean command and certify no build or audit outcome. No implementation, manuscript, dependency, GitHub content, or PDF was changed. This report is the only file written by this reviewer.
