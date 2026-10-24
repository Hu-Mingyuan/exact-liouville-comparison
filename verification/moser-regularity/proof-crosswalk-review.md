# Independent bounded proof-to-definition assessment

Reviewer: native helper `/root/statement_review`, 2026-10-23. Follow-up to `statement-review.md` for mission 60ad47b3. Scope: source-level fidelity and definition correspondence of `MoserRegularityInverse`, `MoserRegularityFields`, `MoserRegularityCompact`, and `MoserRegularityGlobal` to the independently reviewed statement. No builds, API mutations, or unrelated edits were performed.

**No concrete definition or fidelity blocker found in the inspected sources.** Actual theorem bodies now implement the previously specified inverse bridge and two compact regularity targets, and add the advertised global derivative bounds. This assessment is not compilation acceptance, a transitive axiom audit, final consumer acceptance, phase acceptance, or a flow/comparison theorem claim. Parent owns those checks. Global was undergoing a local elaboration repair when review began; this assessment binds to the source hash below rather than asserting its build status.

## Inspected correspondence

- `solve` uses a total continuous-linear-map inverse in the native fiber, with no assumed inverse data. `solve_equation` proves positive contraction from finite-dimensional nondegeneracy; `solution_unique` uses that same nondegeneracy. `solve_eq_inverseContraction` proves equality with `CompatibleStructure.inverseContraction` for every compatible reference and covector representing the same one-form. Thus the auxiliary Euclidean identification is only a construction device. The unchanged reference metric, dual norm, and inverse operator norm keep their accepted meanings.

- `contraction_chart` transports the actual equation using the inverse-chart differential and the chart/inverse-chart derivative identity. `solve_chart` then identifies the transported section with the inverse of the transported contraction operator. This supplies the substantive intrinsic-to-chart bridge; regularity is not asserted merely because the raw tangent fiber is definitionally the model vector space.

- `solve_smoothFamily` unfolds the pinned chart-family notion. For each chart it constructs `W = ((U ∩ V) ∩ (univ × chart.target)) ∩ A⁻¹'{T | T.IsInvertible}`. Openness is proved from coefficient continuity and openness of invertibility. Interval inclusion uses only nondegeneracy on `[0,1]`. On `W`, native inverse differentiability and `solve_chart` prove joint chart smoothness. No uniform time strip and no off-interval nondegeneracy hypothesis is introduced.

- `nativeJoint_of_smoothFamily` invokes the pinned native tangent-bundle chart bridge. Both `nativeJoint_of_equation` and `intervalSmooth_of_equation` identify any supplied interval solution with the constructed extension by uniqueness. The supplied solution has no regularity hypothesis. `inverse_bridge` supplies the reviewed `InverseBridgeTarget`, including its existence equation and explicit uniqueness conclusion.

- `first_joint` and `first_intervalSmooth` apply these producers to the actual `FirstPath.form` and RHS `-q.primitive = -k(R) beta`. Their equation consumer is the existing `FirstPath.X_equation`, so the output concerns exactly `FirstPath.X`. All parameters include `0` and `1`; nondegeneracy consumes `t.property.1`, without requiring `t>0`. `W_smooth` restricts the native section to `t=0` and uses `FirstPath.X_zero`, proving smoothness of the existing `W` rather than defining a replacement.

- `interpolationForm_eq` proves equality between the affine family of two-forms and the actual exterior derivative of the coefficient primitive. Its proof uses genuine exterior-derivative additivity and constant scalar linearity, after an equality of the actual one-forms. `interpolation_joint` and `interpolation_intervalSmooth` then use RHS `q0.primitive-q1.primitive = -delta(R) beta` and the existing `RadialInterpolation.vector_equation`. The original weak differential hypothesis remains nonstrict and does not require nondegeneracy of `d sigma`.

- The stronger `first_intervalSmooth` and `interpolation_intervalSmooth` outputs unfold to one actual real-parameter extension, pinned `IsSmoothVectorFieldFamily` regularity, and exact agreement with every interval slice. These preserve the open chart neighborhoods that `NativeJoint` alone did not package. They resolve the previous review's producer-side caveat without altering `NativeJoint`. Conversion to any particular future open-set native flow interface remains a separate downstream task; no such flow interface is claimed here.

- In `Compact`, continuity of scalar derivative evaluation is derived through the native tangent map of the scalar function, composed with the actual continuous tangent section. `compact_abs_bound` uses compactness of the entire parameter subtype times the supplied compact set, with a nonnegative bound also valid for an empty set. `first_compact` therefore proves the exact reviewed `FirstTarget`. For interpolation, `barrierRate_linear` proves an equality of actual scalar derivatives; its continuity follows from the two fixed smooth `radialQ` functions. Properness of `R` and `R≥1` prove compactness of the full closed core. `interpolation_compact` delivers exactly the reviewed upper radial and lower barrier bounds, uniformly in both parameters and points of that core.

- `first_global` takes the original arbitrary compact exception `K`, its compactness proof, the positive constant, and the inverse-norm inequality outside `K`. These are passed unchanged to `FirstPath.exterior_estimate`. The compact bound is then applied to its enlarged compact set `L`, and a maximum combines the bounds. `first_growth_consumer` destructs the accepted `GrowthAtInfinity` proposition and retains arbitrary admissible growth; it does not replace the compact exception by a global inverse bound or add metric completeness.

- `Q_scalarDerivative` uses the actual half-line derivative chain rule and the range condition `R≥1`, so it includes `R=1`. `barrierRate_eq` identifies the actual derivative expression with the accepted algebraic one. `interpolation_global` restores the ordering hypothesis, then combines core bounds with `radial` and `Q_directional` on the strict exterior. Signs agree with the manuscript: an upper bound for `XR` and lower bound for the time-plus-space `Q` rate. Divergence of `r*rho0(r)` is not needed for these bounds; it remains necessary when a later reverse-time compactness argument uses uniform exhaustion.

No trajectory, global flow, completeness, diffeomorphism, or exact comparison is assumed or constructed by these modules. No complete-Liouville definition is altered. A lexical check of these four proof sources found no `sorry`, `admit`, custom `axiom`, or `opaque` declaration; this is not a substitute for the parent's transitive kernel axiom audit.

## Source binding

The statement hash remains exactly the previously reviewed hash. All files listed in `verification/moser-regularity/inputs.json` still matched their recorded SHA-256 values at this follow-up inspection. Inspected new sources:

| File | SHA-256 |
|---|---|
| `ExactLiouvilleComparison/MoserRegularityStatement.lean` | `fecaeb5bfe5e16df859c8805915e525cca0ddbbe084f0c0649dc9532e6c9eb0b` |
| `ExactLiouvilleComparison/MoserRegularityInverse.lean` | `60ba290c2101e743af3cf2fdb3ee80fddd22b34c47f988d34c00a00d20cb8f07` |
| `ExactLiouvilleComparison/MoserRegularityFields.lean` | `8ef90c4df28f103792ee415afa2ad21b3a398a9c3ad8cb3675b83da371146370` |
| `ExactLiouvilleComparison/MoserRegularityCompact.lean` | `77204133bd37ef23206c1d43d53db3853e69bc6470252268011b6c73409ab826` |
| `ExactLiouvilleComparison/MoserRegularityGlobal.lean` | `81c7ee5fc61973bd82ad60c7cc5566e1ad28d0213753e91ec9cb9f2a8f0c30a7` |

Final exact-source build receipts, elaborated output types, compiled interface consumers, and axiom closure are deliberately left to the owner and are not certified by this bounded assessment.
