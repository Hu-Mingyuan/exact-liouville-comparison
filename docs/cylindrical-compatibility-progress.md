# Cylindrical compatibility: retained proof progress

Original mission `deee4e3c-9772-491a-b842-98913f062983` was reopened at revision 3
under explicit continuation notice `3c37481e-986a-42b4-b55f-0f4e2ebddf2c`.
The cancellation prose in the preserved disposition and statement review is
historical and superseded. All original acceptance criteria remain open.

## Reused statement gate

Recovered exact statement, crosswalk, independent review and managed statement
receipt from private archive `24b8ee9589e80d6e415cf978e895cc33338deeb3`, verified
publication `c647518f-c8cc-4b4c-8df5-cfc236c0f33d`. Every reviewed Lean definition,
dependency, manuscript and objective hash matches this workspace. The historical
coverage note was recovered from the original author's preserved workspace.
No semantic statement change was made, so the existing independent statement
review applies. It certifies specifications only, not their existence proofs.

## Proved prerequisites

All names below are under `ExactLiouvilleComparison.CylindricalCompatibility`.

- `ContactData.endJ` is a continuous linear operator on the actual boundary
  tangent times the real time direction. `endJ_square`, `endJ_time`,
  `endJ_reeb`, `endPairing_invariant`, `endPairing_energy` and
  `endPairing_positive` prove the full end algebra and positive sign.
- `end_twoForm` identifies `exp(t)(d alpha + dt wedge alpha)` with the actual
  completion exterior derivative under the actual end differential. Its proof
  uses exterior-derivative naturality on fixed-time boundary slices, the
  primitive end law, and the positive Liouville contraction equation. It holds
  for every real time and arbitrary dimension.
- `endTangentJ` transports the operator through the proved native differential
  equivalence. Its square, invariance and strict positivity are proved on actual
  ambient tangent fibers. This is pointwise construction, not yet a smooth
  global section or compatible core extension.
- `RelativeSection.exists_relative_section` uses Mathlib's native smooth
  partition of unity to glue local sections in convex fibers, fixing prescribed
  values on a closed subset of an open neighborhood. `RelativeMetric.convex_SPD`
  proves convexity of symmetric strictly positive continuous bilinear forms.
  The local-section premise is explicit and still needs the metric construction.
- `Extends.cylindrical` preserves the prescribed Reeb/contact data literally.
  `comparison_of_extends` uses the accepted `FiniteTypeComparison.finiteTypeTarget`
  with exactly the original weak-taming and existential end-growth premises.
  `existence_of_contact_and_extension` and `consumer_of_existence` are assembly
  implications whose construction premises remain explicit and unproved here.

The native consumer module prints the literal end formula and exercises the
assembly implications. These results do not establish `ExistenceTarget`,
`ExtensionTarget`, `ContactExistenceTarget`, or unconditional `ConsumerTarget`.
No shared `Statement.lean`, `Geometry.lean`, manuscript, upstream dependency or
old project was edited. The independent presentation adapter remains untouched.

## Remaining construction and ownership

| Outcome | Owner |
| --- | --- |
| Smooth compatible normalization of a native symplectic vector bundle with metric, including recovery on compatible fibers | Child mission `50754190-03fe-44b3-830e-5b109eca0470`, assignment `1f45f2d4-0edc-4d6b-8646-2c1212915b09` |
| Smooth Reeb/contact data, native kernel restriction and zero-extension bridges | Child mission `39265fb2-8bea-40d8-a0da-7ae1ba7f9018`, assignment `f9c486a4-ea65-4432-9f68-baa0abb33692` |
| Smooth end transport, relative metric construction, prescribed global extension, integration, consumers, final independent review and repair | Original mission; retained assignment `9997dc64-3871-4296-b839-1a516314042b` |

The split isolates genuine prerequisites: the pinned compatible-path theorem
assumes both compatible endpoints, and pointwise symplectic bases do not produce
smooth fields. It changes no mathematical criterion. Root mission
`91f6a7c7-1eb9-4e2c-bb7e-39389d62ea18` retains combined final acceptance.

The native relative-gluing helper was collected. Its exact route is now
implemented in `CylindricalCompatibilityRelativeSection.lean`. Remaining metric
work: construct local chart pullback inner products; prove their native section
smoothness and the bounded-unit-ball field; apply relative convex gluing, then
the child's compatible normalization with its recovery property. The prescribed
end is closed (`Completion.isClosed_endMap_image_Ici`), and its all-real range is
open with a proved smooth inverse (`Completion.endDiffeomorph`), so the full
closed nonnegative end, including time zero, can be fixed. Native smoothness of
the transported end operator and metric still needs proof.

Reuse checks: Mathlib `exists_contMDiffSection_forall_mem_convex_of_local`;
FsFltz `MarkedHorizontalGluing.exists_smooth_marked_affine_lift`,
`CompletionCollar`, `CompletionIntervalMapFamily`, `BoundarySmooth`,
`ExteriorDerivative`, `FormScalarDerivative`, and `VectorFieldBridge`;
mandatory cluster snapshot `2c239b0c03922a1549f18ee3a45a8e0ca25bb28c`, whose
`LocalFormGluing.existsUnique_smooth_gluing` requires overlap agreement and does
not replace positive-metric averaging. Existing project
`SteinReferenceMetric.pullback_unitBall_bounded` can supply local metric
boundedness. No general smooth normalization was found in the inspected pins.

## Verification boundary

Run `python scripts/verify-cylindrical-compatibility.py`. It verifies the unchanged
accepted source and statement bindings, uses managed builds, audits every owned
declaration and relevant interface transitively, and records the full imported
source closure, elaborated types and definition bodies in
`verification/cylindrical-compatibility/progress/`. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed. The receipt is explicitly partial;
it is not final independent proof review or mission acceptance. No final PDFs,
packaging or GitHub upload is included.
