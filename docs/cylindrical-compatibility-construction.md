# Cylindrical compatible structures and prescribed extension

The supporting assertion immediately before `cor:liouville` is implemented in
`ExactLiouvilleComparison/CylindricalCompatibility.lean`. The unchanged reviewed
contract is `CylindricalCompatibilityStatement.lean`; its original crosswalk and
independent statement review remain authoritative. No comparison hypothesis or
shared geometry interface has changed.

The actual proofs are `extensionTarget`, `existenceTarget` and `consumerTarget`.
The first extends every prescribed `ContactData`; the second constructs some
such data and hence some cylindrical compatible structure. The additional
`extension_of_prescribed_kernel` starts directly with a native smooth section
on the constructed contact-kernel bundle and literal restricted-d-alpha
compatibility. `FinalChecks.native_consumer` obtains the native diffeomorphism,
smooth isotopy and exact primitive conclusion from the constructed choice.

The product operator is `(v,s) ↦ (j(v)+sR,-alpha(v))`. The actual end derivative
transports it to the open escaping basin, with native Hom-bundle smoothness.
The two-form calculation identifies compatibility with the actual ambient
d beta, including its exp(t) factor. The entire image of t≥0 is closed and lies
in the open basin. Relative positive-metric gluing therefore fixes the induced
pairing on this whole set, including t=0. Supplied-metric normalization constructs
a global smooth compatible J and recovers the prescribed operator wherever the
auxiliary metric agrees. The output metric is separately constructed as the
literal d beta(.,J.), not identified with the auxiliary metric globally.

Every dimension and empty case allowed by the original structures is retained.
The contact construction proves applicable low-dimensional boundary emptiness;
the end, relative metric and normalization constructions require no extra
nonemptiness, positive-rank, parity or dimension hypothesis. Native consumers
include d=0 and an empty boundary.

The chosen A precedes the arbitrary exact symplectic target T. Its hypotheses
remain weak taming and existence of the original admissible B and end bound.
There is no primitive-growth or completeness assumption on T. The already
accepted conditional comparison and separate presentation adapter are reused.

## Exact prerequisite evidence

- Normalization: private source `f032d42f86fe749897233b4343fe02df41194293`, publication
  `e6bf0dcd-ffc5-4809-910d-7a211091e61b`; 344 allowed-only audits.
- Relative metric: source `7c9b105a42bf756c4a6ac5931fa6d42bbebd4334`, publication
  `40c2fff1-931a-4862-b447-afba383424d7`; 129 allowed-only audits.
- Contact existence and smooth kernel bridges: source
  `a95be5ac0e3843b255b6f751983f15b1596a7441`, publication
  `91e9a7fd-8939-4e19-bc13-741536acb94e`; 747 allowed-only audits.

Each input has independent statement/proof review. Exact import bindings are
under `verification/cylindrical-compatibility/continuation/`. The contact
companion archive is bound by artifact `2c6f6d19-5a16-4336-a28c-231876d5fb11`.
Its large metadata expression was recovered from the verified archive and
matched to the exact Git blob because the contents API omitted that large body.

## Reproduction and acceptance boundary

Run `python3 scripts/verify-cylindrical-compatibility-construction.py` using the
existing managed Lean environment. It checks preserved source/statement and
pins, builds the final native consumers, audits all mathematical cylindrical
modules by module origin (including private/generated declarations), and binds
the complete imported source closure. New construction/interface types and
computational definitions have lossless native-expression exports. Metadata
fallbacks retain all metadata; readable source is not substituted for this export.
Previously accepted prerequisite inventories are retained through exact bindings.

The receipt and independent final review under
`verification/cylindrical-compatibility/construction/` determine source-bound
acceptance. This guide alone is not an acceptance claim. Root retains combined
integration and final acceptance. No final PDFs, GitHub upload or global-phase
closure is performed by this bounded mission.
