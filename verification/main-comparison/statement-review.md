# Independent statement and definition fidelity review

Verdict: **ACCEPT for bounded statement freeze and subsequent assembly proof work.**
No blocking semantic correction is required. This is not acceptance of a proof of
`MainTarget`, of the application corollaries, or of the final transitive axiom audit.

Mission: `92dedb29-ffc9-40f9-8d8c-07db9fc6ffbe`, revision 1.
Reviewer: independent native reviewer `/root/statement_review`, 2026-10-24.
Baseline identified by the assembly owner: `f8b5b6bcb56a18c0094d15fed4619ff100327e30`.
Applied rubric: `$HORIZON_SKILLS_DIR/subagents/reviewers/statement-fidelity.md`,
“The Mathematical Skeptic”; this was a source-bound mathematical review, not a PR review.
No semantic source was modified and no build was run by this reviewer.

## Evidence binding

I recomputed all five hashes in `statement-hashes.json`, and all 203 file bindings
in `import-manifest.json`: all matched the local bytes. The import manifest binds
deliveries to commits a7d1220ce86078b4c57df64447ce7743bd39a040,
c1773eba6457e4e3331cee126a6da07fc62333ac and
7389b2f8b1b85a87eb83cb245cd3f3855c721dd5. This review verifies those local bindings;
it does not independently repeat remote authentication or the whole baseline diff.

I read the recorded statement build. Its final result is `ok: true`,
`status: passed`, `snapshot_verified: true`, source key
`5bfe02dcdf028fc1478917ee845c49a10a4d34cafca56035984fe1e82ccd76a9`.
The earlier out-of-date diagnostics are followed by successful rebuilding and
successful completion of `ExactLiouvilleComparison.MainComparisonStatement`.

Exact SHA-256 bindings for the principal semantic files, inspected public
interfaces, and evidence receipts follow:

| File | SHA-256 |
| --- | --- |
| `ExactLiouvilleComparison/MainComparisonStatement.lean` | `050e0fda5b0d0c65a92b5c33ff7383f6022bd607ca19f759d57865c533a548cd` |
| `docs/main-comparison-crosswalk.md` | `0ec21662271a54cd98e8a28611fc27150dceb3f035296f39fa3a35754debfe5d` |
| `ExactLiouvilleComparison/Geometry.lean` | `2b30f2be23bb8f1338b72ed0fdfd26f67ee8fef1cf70f4f5f4a5e7430a307326` |
| `ExactLiouvilleComparison/Statement.lean` | `ff7798a4a5c0adc5b27b27766bddc7b123a6923d0c9063983b7a04eb5daa07b7` |
| `docs/reference/exact_liouville_comparison.tex` | `8e5ae225e12eb1adcc4f3851e5e5e026e0de2b9436ba0e6e1301e8771ca90576` |
| `ExactLiouvilleComparison/MoserExactness.lean` | `34ceac4c53f36bfadb8c12d483b5d660519c3894eddd64e23ffdc23a9363af86` |
| `ExactLiouvilleComparison/MoserExactnessStatement.lean` | `13e919fbf803aab75c3758a0c8ab3045fb284dbe3628db19274c9fa4cad3ff88` |
| `ExactLiouvilleComparison/FirstPathExactness.lean` | `7d48df3426e4861cdcd455ee015e7486ebc07cb5aca352f41dcf944d0dfbb47e` |
| `ExactLiouvilleComparison/FirstPathFlowStatement.lean` | `2c698398955a83619d3324db968796982952449a0aa4c1987ecb96730c721217` |
| `ExactLiouvilleComparison/ThirdPathFlow.lean` | `33b3574e5805832587874c33c67b3d025e6f5f6d2cc4c380f7d3092b6f2c6a08` |
| `ExactLiouvilleComparison/RadialInterpolationFlow.lean` | `70f7a368a8e0d54ca041976073dbbe73dbfea64734c5a61d0977917ae4e47ce1` |
| `ExactLiouvilleComparison/RadialInterpolationFlowCoefficients.lean` | `c494e751fd75f7ad95a72e271ea4ca945c7ebfa947ff5c18a91459674a50806c` |
| `ExactLiouvilleComparison/ExactComparisonAlgebra.lean` | `c15c5b615805b3c62c760c54d49c2a363c8c0c43e338c24cfa90f71248568e14` |
| `verification/main-comparison/statement-hashes.json` | `3fb92022f583db84f81b635d6d58b7ff208b5f3929250d2024184a1d4a9e198c` |
| `verification/main-comparison/import-manifest.json` | `cb3f47f95fd7bc627c4a984ebae4865ffed81bba750f57e450699b4b8615c95e` |
| `verification/main-comparison/statement-build.txt` | `79e8f975b9486b18e321af75197273a4130951119d2d0de142e9b4e3d3150019` |

## Principal quantifiers and native geometry

The complete target type after unfolding `MainComparison.Target` is exactly:

```lean
∀ (d : ℕ) (M : SmoothManifold d) (P : RadialReference M)
  (T : ExactSymplecticStructure M),
  WeaklyTames P.compatible T →
  GrowthAtInfinity P.compatible T P.R 1 →
  ExactComparison M T.primitive P.exactStructure.primitive
```

I inspected the actual definitions in `Geometry.lean`, `Statement.lean` and the
pinned FsFltz `Smooth.lean`, `Family.lean`, `Liouville.lean` and `FixedAmbient.lean`.
The source locator is manuscript Section 1, `eq:radialsetup`, `eq:inversenorm`,
`thm:main`, `eq:weak`, `eq:growth`, `eq:conclusion` and `rem:scope`.

`SmoothManifold d` is a Hausdorff, second-countable boundaryless native smooth
manifold modeled on finite-dimensional real Euclidean space; arbitrary d is
quantified. Zero dimension and the empty manifold are not excluded. Forms are
continuous alternating maps on actual Mathlib tangent spaces. Exterior derivative
is `extDeriv` in charts transported by actual `mfderiv`; pullback uses actual
`mfderiv`, and `SmoothEquiv` is `Diffeomorph`. Symplecticity explicitly includes
smoothness, closedness and nondegeneracy. No arbitrary geometry operations are
supplied by the theorem's caller.

The metric is a native smooth Riemannian metric with the equation
`g.inner x v w = dβ(v,Jw)`. The metric tangent synonym installs this metric's
norm. `tangent_norm_eq` identifies it with `sqrt(dβ(v,Jv))`. Covectors retain the
same linear function via `covector_apply`, with continuity obtained in finite
dimension. Positive contraction is constructed from the actual two-form;
`inverseContraction_equation` proves its inverse equation. Consequently
`inverseNorm` is precisely the g-dual-to-g operator norm, not a chart norm.
The positivity of g, J² = −id and invariance are the compatible-J assumptions,
not an extra completeness assumption.

The smooth proper real function R has R≥1; properness as a real-valued map is
appropriate for its closed-ray-valued counterpart. The radial identity and bound
are required only on R>rstar, with c>0 and rstar>1. Weak taming is ≥0 with
nondegeneracy supplied separately. Growth is an existential arbitrary admissible B,
a positive C and an arbitrary compact exceptional K. B is smooth within the
closed ray, positive, dominates r, and its literal interval-integral primitive
tends to infinity. There is no monotonicity or primitive-growth assumption.
No metric or Liouville-field completeness premise appears in this theorem.

`ExactComparison` returns an actual smooth diffeomorphism, an actual smooth
function h, pointwise `F*λ = β + dh`, and equality of the exterior derivatives.
The isotopy uses actual diffeomorphisms with jointly smooth forward and inverse
families on [0,1], identity at 0 and F at 1. There is no compact-support condition.
Complete Liouville terminology remains separate: the pinned definition uses
`Flow ℝ`, joint smoothness and the actual ODE at every real time, with
`dλ(Z,v)=λ(v)`. Neither an exact gauge nor a finite-interval Moser evolution is
being used to assert all-real completeness of the original primitives.

## Four paths, regularity and noncircular outputs

The complete remaining-path type quantifies arbitrary P, G, T and only the
original `hw : WeaklyTames P.compatible T`, and demands a conjunction of
`MoserExactness.Endpoint` for the second, third and fourth literal primitives and
their named delivered evolutions. No free evolution or exactness hypothesis is
present. The omission of inverse-growth bounds for these three paths is a valid
stronger intermediate statement: only path one needs that bound.

The paths agree with the manuscript's first through fourth path subsections:
λ+t k(R)β; λ+((1−u)k(R)+uA(R))β; A(R)β+sλ; and
(1+v(A(R)−1))β. The chosen k and A are the delivered coefficient definitions.
`second_applicable` and `fourth_applicable` prove the radial interpolation
premises; they do not pass them to the caller. `ThirdPath.evolution_exists` and
`RadialInterpolationFlow.radialInterpolationFlow` construct existence before
`Classical.choice` selects their evolution. `FirstPathExactness.exactComparison`
retains the original positive C, compact K and bound. The inspected output
contracts are not circular input certificates.

`Evolution.map s t` is ordered initial time then final time and is an actual
diffeomorphism. Its extension has joint smoothness on an open neighborhood of
the whole closed two-time strip. Its ODE is actual `HasMFDerivWithinAt`, and its
chart ODE, uniqueness, identity, composition and inverse laws refer to that map.
The pinned family definitions demand open joint extensions, including at time
endpoints. This is stronger than separately smooth slices and is supplied by
the inspected construction interfaces.

`MoserExactness.Equation` reads `i_Z dμ = −∂t μ`, where the derivative fixes x,v.
`Endpoint` uses the literal gauge ∫₀¹ μ_t(Z_t)(E(0,t,x)) dt, requires its global
smoothness, and asserts `E(0,1)*μ₁ = μ₀ + dH` and the corresponding two-form
identity. The if-expression extending the integrand outside [0,1] does not alter
this integral. The theorem `moserExactness` supplies these conclusions together
with its derivative identity from smoothness, the equation and actual evolution.
This matches manuscript `eq:moser` and `eq:exactness`, with the correct signs.

Assembly still must prove the literal affine-family equalities and parameter
derivatives for paths two and four, and match the third derivative to its existing
field equation. These are explicit proof obligations, not statement defects.
The source crosswalk records them accurately.

## Endpoint order and final scope

Let the four forward endpoints be G1,...,G4. Their witness directions are:
λ+kβ → λ, λ+Aβ → λ+kβ, λ+Aβ → Aβ, and Aβ → β,
where source → target means pullback of source equals target plus an exact form.
Inverting the fourth and third and composing with second and first therefore gives
Ψ=G4⁻¹∘G3⁻¹∘G2∘G1 and Ψ*β=λ+df. Inverting once more gives exactly
F=Ψ⁻¹ and h=−f∘F, with F*λ=β+dh.

I checked `Witness.comp` against native `Diffeomorph.trans`: its map is F∘G
(`G.trans F`) and its gauge is k+h∘G. `Witness.symm` uses −h∘F⁻¹. The
existential-witness equivalence is proved in both directions without extra
hypotheses. Pointwise composition of the supplied forward and inverse isotopies
satisfies the unchanged smooth-isotopy conclusion. This differs from the
manuscript's concatenation proof technique, but does not alter its theorem.
The additional smoothly varying intermediate primitives mentioned after the
manuscript proof are not an extra conclusion of `thm:main`.

No concrete counterexample, vacuous premise, missing quantifier, hidden
completeness hypothesis or altered conclusion was found in this bounded target.
A lexical scan of project Lean sources found no sorry, admit, custom axiom or
sorryAx token. That scan is not a replacement for the required final transitive
kernel axiom audit. Acceptance is restricted to these exact semantic bytes and
the bounded statement gate. The main theorem still needs its assembly proof,
exact-source final review, consumers and allowed-only audit; the application
corollaries remain outside this review's scope.
