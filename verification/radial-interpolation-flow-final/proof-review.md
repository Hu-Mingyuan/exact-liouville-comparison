# Independent final radial interpolation flow review

Date: 2026-10-23. Mission: `49efc076`. Reviewer: delegated independent source reviewer, separate from implementation and serial managed build ownership.

**Verdict: pass the bounded source-level proof and fidelity review. No defect found.** `RadialInterpolationFlow.radialInterpolationFlow` proves the literal unchanged `RadialInterpolationFlow.Target`, with the actual two-barrier theorem discharging the former analytic premise. The new consumers retain the advertised geometry and endpoints. This verdict is conditional on the separately required exact-source Lean build and transitive axiom audit; this reviewer ran neither. It does not accept the entire comparison theorem, the remaining manuscript results, or publication.

## Scope and source identity

Reviewed workspace: `/home/no_body/.local/share/archon-horizon/fast-runtime/workspaces/exact-liouville-comparison`.
The parent identifies the delivered generic ODE source as private commit `7afe8014aae719630d0969d0bcfc28f29e9ab3b7` and the prior radial inputs as `a5bccccea792f4e81f1f2c917d02f1c542a06f21`, and reports verifying all 74 delivered file hashes. I performed no remote readback and make no independent commit-to-tree claim. This report binds to the actual local SHA-256 values below.

I read `AGENTS.md`, `docs/objective.md`, manuscript `lem:bridge` and its proof, the radial statement/crosswalk and prior input review, both new modules in full, the adapter and coefficient/equal modules in full, the literal generic target and wrapper, its finite-existence and smooth-evolution producers, and the existing generic/component reviews. I checked the actual native definitions and radial geometric producers listed below. Prior independently reviewed confinement/localization proofs are reused; this bounded integration review does not re-prove every transitive dependency. I also read the subsequently supplied `docs/radial-interpolation-flow-final.md`: its mathematical description and bounded scope agree with the inspected source. Its reproducible-script claims and eventual receipt outcomes remain build-owner verification obligations, not independently executed checks here.

The five resolvable bindings in the prior statement review, six in the input review, and eleven in the generic integration review match the local sources with no mismatch. In particular, the two targets, evolution contract, manuscript, prior radial inputs, all six ODE component modules and generic wrapper retain their reviewed bytes. The manifest retains FsFltz `1a3d387cfacc746e25aad31e5b27b1803103e7cb`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, and Lean `v4.34.1`.

## Mathematical findings

1. **Unchanged manuscript assumptions and actual geometry.** The target quantifies arbitrary native `M : SmoothManifold d`, a `RadialReference`, two `RadialCoefficient` values, their order on `Ici 1`, divergence of `r * rho0 r`, a smooth one-form sigma and only weak differential taming. `RadialReference` retains proper smooth `R >= 1`, positive c, `rstar > 1`, and its radial identity/bound only outside the core. Coefficients are positive and genuinely smooth on the closed ray, constant on the whole core, with `rho + r * derivWithin rho (Ici 1) r > 0`. There is no upper coefficient or primitive growth bound, metric completeness, Liouville completeness, strict taming, nondegeneracy of d sigma, or supplied flow assumption.

   Pinned FsFltz uses native Mathlib finite-dimensional boundaryless manifolds, `TangentSpace`, continuous alternating forms, chart-transported native `extDeriv`, native `mfderiv` for scalar derivatives, and native `Diffeomorph`. `CompatibleStructure.g.inner` equals `d beta(v,Jw)`; `MetricTangent`, `Dual`, `covector` and `inverseNorm` retain the g tangent, dual and operator norms. Inverse contraction is constructed from nondegeneracy and finite dimension. No chart norm is substituted for g in this integration. No finite-interval Moser evolution is called an all-real complete Liouville flow; the unchanged complete interface uses actual `Flow R` and positive contraction.

2. **Literal Moser field and symplecticity.** `interpolationField` unfolds to the precise `RadialInterpolation.vector` occurring in `Target`, with the accepted interpolated coefficient and delta. The inspected `primitive_parameter_derivative` gives `delta(R) beta`, and `vector_equation` gives its negative under positive contraction, so the Moser sign is correct. `exactStructure` and `RadialInterpolationChecks.constructed` already prove symplecticity of the interpolated differential and unique pointwise solution from weak taming. The final flow target need not redundantly include that existing theorem as another conjunct. It neither replaces the vector with an arbitrary field nor assumes its defining equation as a new hypothesis.

3. **Actual one-sided applicability.** `of_twoBarrier` constructs an open native smooth extension of this exact field using the previously proved interval-regularity bridge, with equality at every closed parameter. It passes the actual proper R with lower bound 1 and `Q(t,x) = R(x) * ((1-t)*rho0(R(x)) + t*rho1(R(x)))`. Joint smoothness is proved globally in real time by smooth composition with R, including R=1. The ordinary partial derivative is `delta(R)*R >= 0`; the two global constants come from `interpolation_global`, using compact-core smooth bounds and exterior estimates. The reverse input is the native total Q derivative, not an absolute scalar estimate. Uniform sublevel control correctly invokes exhaustion at `L+1` and excludes the equality gap. Exact interval field agreement transports both inequalities and the entire result. These are precisely the actual `TwoBarrierEvolutionTarget` arguments, with no extra growth or regularity hypothesis.

4. **The former premise is discharged.** The final theorem is the proof term `of_twoBarrier ODE.twoBarrierEvolution`, under only dimension/manifold implicit parameters. The generic theorem constructs finite trajectories using `twoBarrier_finiteIntervalExistence`, then supplies those to `evolution_of_finite_existence`. The inspected producer constructs cutoff trajectories and proves confinement before recovering the original field; the inspected assembly constructs native diffeomorphisms and their smooth dependence. Thus the intermediate bridge's trajectory premise is no longer a final assumption. `evolution` merely chooses from the theorem's proved `Nonempty`, which is legitimate classical choice, not an additional existence postulate.

5. **Every evolution obligation survives.** `Parameter` is literally `Icc 0 1`. The result supplies maps for every source/target parameter pair and every point, native diffeomorphisms, an extension jointly smooth on an actual open neighborhood of the entire closed double-time strip, initial identity, native and chart ODEs on the full closed interval, uniqueness for continuous solutions on `uIcc s t`, composition, inverse, and smooth isotopy with smooth inverse family. The finite producer even supplies full derivatives at interval endpoints; the advertised structure uses within derivatives there. Equal times and reversed times are retained. No uniform open time margin at spatial infinity is silently assumed. `native_ode` uses that extension and its agreement/initial fields to exhibit the actual initialized literal-vector trajectory, including both endpoints. `endpoint_inverse_isotopy` projects the same chosen evolution's genuine inverse and isotopy fields.

6. **Specialized consumers.** `sigma_zero` proves existence with the literal zero form and the proved weak-zero witness. `unit_start` proves divergence from `r*1 = r` and allows arbitrary ordered upper coefficient and weak sigma. `second_path` obtains order/divergence from the delivered literal k and A and the original weak taming of lambda; it adds no inverse-form growth or primitive-growth premise. `fourth_path` constructs the forward beta-to-A beta evolution with zero sigma and literal lower coefficient 1; reversing its endpoint gives the manuscript's fourth arrow. The pre-existing `second_rho`/`fourth_rho` identify the precise affine coefficients, and A's within derivative is bridged at radius 1 as well. No substitute coefficient is introduced.

7. **Identity and stationary points.** `fixes_of_zero` proves the constant curve is a continuous native solution on each unordered closed interval and applies the evolution's uniqueness. It needs no nontrivial-time assumption. `equal_identity` uses the already constructed equal-coefficient evolution and the actual zero-delta vector theorem, proving identity at every pair and point without a divergence hypothesis. `critical_fixed` applies the same uniqueness argument to the selected general evolution. It correctly retains `rstar < R x` and native `mfderiv R x = 0`; the radial primitive identity forces the covector and vector to vanish there. It does not extend the exterior radial identity to the compact core.

## Trust and remaining acceptance obligations

Textual inspection of the radial-flow and two-barrier modules found no `sorry`, `admit`, `sorryAx`, custom `axiom`, `opaque`, or `unsafe` declaration. This is not a transitive axiom audit. The parent must retain a successful serial managed build of the exact final source, compiled consumers of the full target and edge cases, and a transitive audit of `radialInterpolationFlow`, `evolution`, the new checks and relevant imported producers permitting only `propext`, `Classical.choice`, and `Quot.sound`. Source/dependency receipt and final documentation must agree with that accepted source. Before report finalization, the parent reported a successful managed Checks build, `snapshot_verified: true`, source key `74068849cd4292917e04f56c87d68db4d020a0661266dff7612b320f82741f79`. This is supplied evidence, not an independent rerun. The final frozen-source serial build/types/audit remains pending with the parent. The parent confirmed both new Lean modules stable, and their hashes were rechecked unchanged.

The bounded radial-flow result does not prove Cartan pullback/exactness identities, the third path, final comparison assembly, or all manuscript corollaries. Those remain outside this review. Historical prior reports correctly describe what was open at their own source snapshots; the present wrapper closes their two-barrier/radial-flow dependency gap at source level. No implementation, manuscript, upstream dependency, old project, or remote content was changed. This report is the only file written by this reviewer.

## SHA-256 source bindings

| File | SHA-256 |
| --- | --- |
| `ExactLiouvilleComparison/RadialInterpolationFlow.lean` | `70f7a368a8e0d54ca041976073dbbe73dbfea64734c5a61d0977917ae4e47ce1` |
| `ExactLiouvilleComparison/RadialInterpolationFlowChecks.lean` | `c207524ac2e3f12436e69262d51f3ac36b2f96378d3f3c545fac0fbbed54d67b` |
| `ExactLiouvilleComparison/RadialInterpolationFlowStatement.lean` | `a9e8a8f144f240846f4b3e85ab26f78877aa063a2fbf2a478b78bf4c90c7d123` |
| `ExactLiouvilleComparison/RadialInterpolationFlowInputs.lean` | `9d90c3b0cf7bf4260edad41f785a07eca9a6bbe5dc6370fe5925fd212e4e54da` |
| `ExactLiouvilleComparison/RadialInterpolationFlowCoefficients.lean` | `c494e751fd75f7ad95a72e271ea4ca945c7ebfa947ff5c18a91459674a50806c` |
| `ExactLiouvilleComparison/RadialInterpolationFlowEqual.lean` | `97b2ba6eaafb09a8041726a295507cdab218f5424a12d8415bc84eb06c8a9462` |
| `ExactLiouvilleComparison/FirstPathFlowStatement.lean` | `2c698398955a83619d3324db968796982952449a0aa4c1987ecb96730c721217` |
| `ExactLiouvilleComparison/ODETwoBarrier.lean` | `86fb566e2a61507e33d4168a6dede320111d59fed5891da2680ad259231c8aa0` |
| `ExactLiouvilleComparison/ODETwoBarrierStatement.lean` | `81b206239999b41a479672cc5a73673115a5c09f3393d0438674bf2df794eb17` |
| `ExactLiouvilleComparison/ODETwoBarrierConfinement.lean` | `bd10ac404e00c985b50091701882400f08576e77758ebd85eeffdbd419501959` |
| `ExactLiouvilleComparison/ODETwoBarrierExistence.lean` | `fc2efd63070a58bf63b84ce143cbc850dddd9aace5b4e93ca9d580a85507a8df` |
| `ExactLiouvilleComparison/ODETwoBarrierLocalization.lean` | `ef7d37a76a994e2be21424a7f52e81b11b5f856160c3c16bfa278ebf8593daba` |
| `ExactLiouvilleComparison/ODETwoBarrierLocalizationPatch.lean` | `5cdc67126ed2028ec672ced1dcd0539c51d825c7ae480c8a45c6ce20106776e5` |
| `ExactLiouvilleComparison/ODETwoBarrierSmoothAssembly.lean` | `bd707273547418472904e8260c0d1a3e03f14ae1951fb85e309f6b79e20a7138` |
| `ExactLiouvilleComparison/ODETwoBarrierSmooth.lean` | `41edf8838dc5a99744e252a76b498b7f98d448da1415e07b203bbbcc80c1bf87` |
| `ExactLiouvilleComparison/Geometry.lean` | `2b30f2be23bb8f1338b72ed0fdfd26f67ee8fef1cf70f4f5f4a5e7430a307326` |
| `ExactLiouvilleComparison/Statement.lean` | `ff7798a4a5c0adc5b27b27766bddc7b123a6923d0c9063983b7a04eb5daa07b7` |
| `ExactLiouvilleComparison/RadialCoefficient.lean` | `a639d4dbd9c8b16186466e2a9d3c3f4ac729736b7e08134a16c7df002aeb082a` |
| `ExactLiouvilleComparison/RadialInterpolationCoefficient.lean` | `e2f53289c602bab2da2c428ca61adcd215b158aad24b373b897539c1f1431801` |
| `ExactLiouvilleComparison/RadialInterpolationGeometry.lean` | `746160c876499357ea9031263b40e116c652084143e0a800d55ab4361c8e82d4` |
| `ExactLiouvilleComparison/RadialInterpolationChecks.lean` | `d27a407be7a5fc50d92daa867794cc52ba97191f98eb4807694433f4805af9e1` |
| `ExactLiouvilleComparison/MoserRegularityStatement.lean` | `fecaeb5bfe5e16df859c8805915e525cca0ddbbe084f0c0649dc9532e6c9eb0b` |
| `ExactLiouvilleComparison/MoserRegularityGlobal.lean` | `81c7ee5fc61973bd82ad60c7cc5566e1ad28d0213753e91ec9cb9f2a8f0c30a7` |
| `docs/reference/exact_liouville_comparison.tex` | `8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576` |
| `verification/radial-interpolation-flow/statement-review.md` | `540e299db4d8835212bf708e1dcac3a0fc73e83229e55b0805ed521342e0f9eb` |
| `verification/radial-interpolation-flow/input-proof-review.md` | `1fcb67e4575b235a85663d3521fb6f2b24a7e901fc9876e3344575339e7739c3` |
| `verification/radial-interpolation-flow/crosswalk.md` | `54ed4154d99265fbbbb29d6e63c2506fee66f59c7a1cca58d7f574068c87b732` |
| `verification/ode-two-barrier/proof-review.md` | `7ff69c35ddf1343b97e8b5c2ee7ae754ba7a317c283bd158101286765c77e81e` |
| `verification/ode-two-barrier/finite-proof-review.md` | `59bcd899521bead5db3376a3dda54baa05b07d69be015e6887edc596425f7333` |
| `verification/ode-two-barrier-smooth/proof-review.md` | `c42323ae26cbf84422261713d3cdb352ef4e180dc0a617a4b380a94477556c63` |
| `.lake/packages/fsfltz/FsFltz/Geometry/Smooth.lean` | `57b89da972058e0f3e2b963d9c291ca8dfcdc60f3b5c5904c8e3ae6f9e6cecbd` |
| `.lake/packages/fsfltz/FsFltz/Geometry/Family.lean` | `6bf8ca0e50ad10402bd465491cf26bd177f0319da019d57d77b2e7134f6a0098` |
| `.lake/packages/fsfltz/FsFltz/Geometry/Liouville.lean` | `d51b04337e39b31ab1b1d3b20093ba5956b8ea0b04456e141ef4c827268b335e` |
| `docs/radial-interpolation-flow-final.md` | `b6d0b33095fe7e95efd9a70314d427f5b014b73759abb2d98bbc0f510769969b` |
