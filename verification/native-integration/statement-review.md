# Independent statement review: native integration

Mission `27db12fe-bb36-4bbe-b5c8-8c46236e3da2`; reviewer `/root/integration_review`; 2026-10-24.

**Verdict: mathematical statement and definition crosswalk accepted.** No correction is required before the bounded composition proof. This verdict is a source-level statement review; managed compilation of this exact statement remains a separate prerequisite before substantive proof work. The root is diagnosing the inherited dependency cache, and I have not started a competing Lean build. This is not final proof, root-objective, publication, or release acceptance.

## Source and reuse boundary

I read AGENTS.md, docs/objective.md, the mathematical-fidelity reviewer descriptor, and the unchanged manuscript's finite-type setup, cylindrical extension assertion and cor:liouville (lines 374–412). I read both new integration files, the accepted adapter statement/implementation/consumers, cylindrical statement/export/consumers, actual metric and comparison definitions, and the pinned complete-flow and complete-primitive definitions. I reuse the independently accepted component reviews at `verification/cylindrical-compatibility/construction/final-review.md` and `verification/finite-type-presentation/final-review.md`. I do not reopen their solved contact, normalization, extension, quotient, radial, or Moser proofs.

I independently recomputed all 191 local file SHA-256 and Git blob OID pairs in `preservation.json`; every pair matches. Exactly 122 entries belong to both input commits. The manifest contains no conflicts. The parent reports exact remote readback; this review independently verifies local preservation against that supplied record, not a second remote fetch.

| New reviewed input | SHA-256 |
| --- | --- |
| `ExactLiouvilleComparison/NativeIntegrationStatement.lean` | `2bcef00d926618d82c787c8d2693ebbaa04da58a6fcfd1963adadef2b77cdfa7` |
| `docs/native-integration-crosswalk.md` | `1c3d21571a01a89370f5581c7413427a7931f668cd0a7aded00ad58a22f10f4a` |
| `verification/native-integration/preservation.json` | `8cfb3926e07d3e9c4654041a51d6c50aa3d813d6c14262f64124477becec62b7` |

## Actual statement and quantifiers

`ConstructedComparison` starts with the accepted native compact smooth half-space source of dimension `k+1`, its locally extendible one-form, nondegenerate actual exterior derivative and local outwardness. `fromNative` chooses the quotient using only these source data. The definition then fixes `Q := P.completed hα`, concludes `P.Identifications hα`, and existentially chooses a compatible `A` and cylindrical witness before universally quantifying the exact-symplectic target `T`. Thus neither the quotient nor the chosen reference depends on the comparison primitive. The source identifications are conclusions of the accepted adapter, not supplied premises.

The prospective composition is literal: cylindrical existence applies to `P.domain` and this very `P.completed hα`; `P.comparisonFor hα` accepts the resulting `A` and cylindrical witness on that same completion. No manifold transport, assumed completion equivalence, assumed global Moser flow, or circular comparison input occurs.

`WeaklyTames` is precisely the nonstrict inequality `0 ≤ dλ(v,Jv)` for every point and tangent vector. Growth keeps the original existential admissible `B`, positive constant, nonnegative eventual logarithmic-time cutoff, and uniform estimate at every end point using `B(exp t)`. There is no primitive growth, target completeness or metric completeness hypothesis. `NativeConclusion` expands to the actual smooth diffeomorphism, smooth real gauge, identity-start isotopy with smooth forward and inverse families, `F*λ = β + dh`, and the actual exterior-derivative pullback identity. Its primitive orientation matches cor:liouville.

`PrescribedExtension` quantifies every accepted `ContactData` on the same source domain. `Extends` uses the actual differential of `Q.endMap` and the full formula `(v,s) ↦ (K.J v+s K.reeb,−α(v))` for every `t ≥ 0`, including the seam `t=0`. This is extension of arbitrary prescribed smooth contact data, not only existence of some end structure. The previously proved native-kernel endpoint remains imported unchanged.

## Metric, native geometry and completeness

`CompatibleStructure.g` is an actual native smooth Riemannian metric and its `metric_eq` requires `g(v,w)=dβ(v,Jw)`. `MetricTangent` installs this metric's core; `Dual` is its continuous dual, `covector` preserves the underlying linear functional, and `dualNorm` takes its operator norm. `inverseContraction` is constructed by inverting the actual alternating-form contraction using nondegeneracy and finite dimension. `inverseNorm` is its norm from the g-dual to the g-tangent fiber. The integration expression `A.inverseNorm T` therefore has exactly the required meaning, and the accepted radial consumer's metric and norm equalities preserve that same `A` definitionally.

The pinned `Completion.ambient` is a `CompleteLiouvilleManifold` with positive contraction `dβ(Z,v)=β(v)`. Its `CompleteLiouvilleFlow` contains `Flow ℝ`, jointly smooth action and the actual chart ODE quantified over every real time. `P.completed hα` constructs this datum through the accepted native adapter. Exact-symplectic target terminology is appropriate because `ExactSymplecticStructure` has no flow field. The separately imported complete specialization takes `CompletePrimitive` for both prescribed primitives; that structure preserves the actual all-real flow. A gauge equality does not manufacture completeness.

## Scope and later acceptance

The new native-source composition deliberately retains the independently approved positive-dimensional `k+1` adapter convention; it makes no zero-dimensional native-source construction or arbitrary independently supplied completion identification claim. The imported original cylindrical existence, arbitrary extension and comparison endpoints still quantify all natural dimensions. Their explicit `d=0` and empty-boundary consumers remain unchanged. The crosswalk accurately distinguishes these scopes.

The file currently defines the two new propositions; it does not claim they have been proved. Final narrow review must inspect their actual integration proofs and consumers, exact-source managed compilation, and transitive audits of the new exported endpoints, with all axiom sets contained in `{propext, Classical.choice, Quot.sound}`. Re-exporting the general manuscript and complete-specialization theorems must remain direct use of the already accepted endpoints. No new proof or axiom acceptance is inferred from this statement verdict.
