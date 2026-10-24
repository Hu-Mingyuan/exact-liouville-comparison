# Independent pre-proof statement and definition review

Mission: `2cde2f71-9a68-4bf2-86cd-cfc13d8268cb`. Reviewer: independent `presentation_review` agent. Verdict: **accepted for substantive proof of this bounded constructed-quotient adapter**. This is statement acceptance, not proof acceptance, full-objective acceptance, or publication authorization.

The reviewer read `docs/objective.md`, the authoritative manuscript's finite-type section and corollary, the complete new statement and crosswalk, and the actual pinned definitions and construction in `IntrinsicLiouvilleForms`, `IntrinsicExteriorDerivative`, `IntrinsicLiouvilleCoefficients`, `IntrinsicCompletionLiouville`, `IntrinsicCompletionDomain`, `IntrinsicCompletion`, and `Liouville`. The existing `Statement`, `FiniteTypeComparisonStatement`, and `FiniteTypeComparison` consumer interfaces were also inspected. No build was launched by the reviewer.

## Exact reviewed artifacts and compilation evidence

| Artifact | SHA-256 independently read from the workspace |
| --- | --- |
| `ExactLiouvilleComparison/FiniteTypePresentationStatement.lean` | `1c0a143611518562a99d2de11002165cc19905ca25e10cb873aaf7b7691cbc0d` |
| `docs/finite-type-presentation-crosswalk.md` | `bb974415f900333d6f185342b3febfb638cef1aabfa427b43519be36988cc092` |

The reviewer inspected `verification/finite-type-presentation/statement-build.json`: the command is `lake build ExactLiouvilleComparison.FiniteTypePresentationStatement`, status `passed`, return code `0`, `snapshot_verified: true`, Lean version `4.34.1`, and source key `9db0311918739f50e7a3eb7df4dfebd4700e4a1132f40e8ca6d844b9d0121e20`. The only elaboration adjustment after initial semantic review was opening `Topology`; the additional attached-end equality was separately reviewed before this acceptance.

The independently read private publication receipt binds this statement stage to commit `d3523f6f68fa8e68424190bdb982331a800467dd`, publication `e58ca64f-c9eb-4abb-80e5-d8579d13a92b`, repository `31e09b7d-6080-4383-8e4e-92b14780690a`, branch `horizon/changes/edc05214-0197-447a-9e61-3011f12888f6`. Its verification is `git_tree_delta`; compilation evidence is the separate build receipt above. This is private development publication, not GitHub publication.

## Mathematical fidelity

1. The native source is compact, Hausdorff, second countable and smooth with the actual Mathlib half-space model. The dimension is `k+1`; the crosswalk correctly limits this adapter to the positive-dimensional upstream constructor and makes no new zero-dimensional construction claim. Empty manifolds are not excluded.
2. The primitive is an actual alternating form on every full native tangent fiber, including boundary points. `IsLocallyExtendibleForm` supplies local open smooth coefficient extensions agreeing on half-space germs, not a globally supplied extension manifold, field, collar, or flow. The crosswalk does not claim an unproved equivalence with a different smoothness predicate.
3. The exterior derivative is the actual native within-chart exterior derivative, with the pinned covariance theorem. Nondegeneracy is a trivial contraction kernel. The primitive determines the Liouville field, and the checked contraction lemma has the positive convention `dα(Z,v)=α(v)`.
4. `LocalOutward` matches the pinned native constructor's local defining-function premise: local nonpositivity, zero value at the boundary point, nonzero derivative, a smooth ambient chart germ, and strictly positive derivative along the native Liouville field. It does not add a global defining function or completeness premise.
5. `NativeTarget` constructs `QuotientData` as an existential output. Its collar, primitive, nondegeneracy, and preservation fields are obligations to be proved from the native hypotheses, not assumptions handed to the final theorem. They match available lower-level outputs of `exists_liouvilleStructure_from_native`.
6. `domain`, `completed`, and `nativeIn` are the literal pinned compact domain, complete completion, and original map into its half-infinite quotient. Reusing this lower-level construction keeps the native boundary definitionally visible; the higher-level existential completion theorem hides that identification. There is no substitute manifold or arbitrary geometric operation.
7. `Identifications` requires smooth closed embedding, bijective native derivative at every point, exact carrier/frontier, identity completion inclusion, full primitive pullback, native field pushforward, the literal native boundary inclusion, and equality with the native boundary restriction form. Thus preservation is not reduced to tangential/contact values alone.
8. The explicit end equality holds on `-width<t`, exactly the domain of the pinned orbit-versus-attached-end theorem. This contains the seam and every nonnegative logarithmic radius. The exponential primitive identity holds for every real time. The `Completion` itself supplies a genuine all-real jointly smooth Liouville flow solving the actual ODE, end immersion, nonnegative-end embedding, coverage and overlap. No claim of an embedded all-negative end is made.
9. The manuscript radius is `r=exp(t)`. The resulting exponential boundary primitive is precisely the manuscript's `r α_boundary`. The source-domain primitive and its boundary restriction are distinguished correctly.
10. The quotient is fixed before the universal choice of compatible `A`, cylindrical data, target exact primitive, and estimates. `ComparisonFor` keeps exactly that `A`, hence its `J`, explicit metric `g=dλ₀(.,J.)`, metric dual norm, and inverse-contraction operator norm. It requires the accepted weak, nonstrict taming and the original arbitrary admissible `B`, positive constant, and eventual uniform end estimate using `B(exp(t))`.
11. No target-primitive completeness, metric completeness, primitive-growth condition, Moser-flow assumption, radial exhaustion input, or comparison hypothesis is introduced. The native conclusion contains an actual diffeomorphism, smooth identity-start isotopy and smooth inverse family, smooth exact gauge, primitive equality, and exterior-form equality.

## Scope and proof obligations

This is sufficient for the authorized source adapter on the actually constructed quotient. It does not identify an independently supplied completed manifold, prove uniqueness of completion, transport an arbitrary chosen manifold's `J` or metric, or construct/extend a cylindrical compatible structure. Those omissions are explicit and do not weaken this bounded target. The selected cylindrical structure remains a legitimate supplied premise, as in the accepted finite-type comparison interface.

Substantive proof should construct every `QuotientData` field from the existing native constructor, establish the identification conjunction with pinned bridge lemmas, and apply the already proved finite-type comparison while retaining the selected `A`. Final proof review must inspect those bodies and the exact compiled consumer and transitive axiom audit. This pre-proof gate does not itself establish `NativeTarget`.
