# Third-path construction

Import `ExactLiouvilleComparison.ThirdPathFlowConsumers`. The proved theorem
`ExactLiouvilleComparison.ThirdPath.thirdPathFlow` inhabits the independently
reviewed `ThirdPath.Target`; `construction P T hw` returns the actual output.
Inputs are the accepted arbitrary native radial reference `P`, an exact
symplectic primitive `T`, and weak taming `hw`. No primitive or metric
completeness is used. The delivered `LargeCoefficient.A P T.primitive` occurs
literally in the primitive and all estimates.

| Proof group | Declarations and mechanism |
| --- | --- |
| Primitive and symplecticity | `differential_eq` identifies the actual exterior derivative with the affine family; `energy_lower` uses the radial g estimate and weak taming; `nondegenerate` and `symplectic` follow. |
| Actual field | `field` applies the proved inverse contraction to `-lambda`. `field_equation` and `field_unique` give the required sign and uniqueness on native tangents. |
| Regularity | `field_joint` and `field_intervalSmooth` instantiate the existing inverse regularity theorem with the actual family, nondegeneracy and equation. |
| Norm estimate | `field_norm_bound` applies the field equation at `J X`, uses the g isometry of J and the actual dual operator norm, then cancels the positive tangent norm. `ratio_le_one` uses the delivered A domination theorem. |
| Scalar control | `exhaustion_smooth`, `exhaustion_proper`, and `exhaustion_lower` establish the native properties of sqrt(R). `exhaustion_derivative` proves the chain rule. The exterior bound uses the given radial dual estimate; the core bound uses compactness and native joint regularity. |
| Full evolution | `evolution_exists` constructs a native open extension via exact equality, discharges the scalar continuation hypotheses, and invokes the already proved `FirstPathFlow.evolution_of_scalar_bound`. `evolution` chooses this proved output; `construction` fills every reviewed field. |
| Direct consumers | `flow`, `trajectory`, and `full_interval_solution` supply actual maps and solutions. `trajectory_smooth`, `trajectory_solves`, `trajectory_chart_solves`, `flow_unique`, `flow_compose`, and `flow_inverse` cover every pair of interval parameters, including reversed order and endpoints. |
| Endpoint | `inverseEndpoint_direction` identifies the literal primitives at 1 and 0 and the inverse of the forward endpoint. `inverseEndpoint_isotopy` supplies a smooth identity-start isotopy with smooth inverse family. |

The scalar child's helper norm and joint-regularity premises are discharged by
the parent field proofs. The smooth open extension is an output, and no
trajectory, inverse field or evolution is an input. The reference g norms are
explicit `P.compatible.MetricTangent` and `P.compatible.dualNorm`, not chart norms.
The compact-core exception is preserved throughout.

Run `python3 scripts/verify-third-path.py` from this checkout. In the managed
environment it runs `horizon-lean-check` serially; otherwise it uses the pinned
Lake installation. The script verifies all preserved baseline Lean, manuscript
and pin hashes, builds the final consumer, inventories elaborated types of all
new namespace constants (including generated structure declarations), and
computes each constant's transitive axioms with `Lean.collectAxioms`.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Its output files
are written after all checks, to avoid modifying a managed source snapshot.
See `verification/third-path/receipt.json`, `final-elaborated-types.txt`,
`environment-declarations.json`, and `axiom-audit.json`.

The statement/crosswalk review is in `verification/third-path/statement-review.md`.
The scalar child provenance and standalone verification are retained in
`verification/third-path-exhaustion/`. This bounded construction excludes
Cartan exactness, a pullback identity, four-stage comparison, corollaries,
final PDFs and final global acceptance. Those remain owned by the existing
root mission and its scheduler successor.
