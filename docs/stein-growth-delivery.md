# Bounded growth delivery

Mission 0a2bd945-f938-49ba-885b-b4961c95a760 revision 1.
Source repository: 31e09b7d-6080-4383-8e4e-92b14780690a (private Forgejo).
Exact implementation commit: `86e390a8db9ac75e61a64a64b6d709c35e9e8e50`.
Base: `f8b5b6bcb56a18c0094d15fed4619ff100327e30`.
Source branch: `horizon/changes/89981c30-5d67-42ea-9ce3-9d586281a5e3`.
The final delivery adds the independent review and publication evidence only;
it does not change the checked implementation.

## Public entry points

Import `ExactLiouvilleComparison.SteinGrowthConsumers`. In namespace
`ExactLiouvilleComparison.SteinGrowth`:

- `extend` constructs `AdmissibleGrowth 1` from every `AdmissibleGrowth (Real.exp 1)`.
- `extend_eq` gives equality for r>=e+2; `extend_eventuallyEq` gives eventual equality.
- `primitive_eq_add_constant` proves the literal finite integral correction.
- `growthAtInfinity` preserves A, T, R, C and the exact g-induced inverseNorm,
  using explicit properness and lower bound and enlarging the compact exception.
- `steinRadius_growth` consumes the literal Stein radius once its separately
  owned properness and lower-bound facts are supplied.
- `scalarTarget`, `witnessTarget`, `growthTarget`, `steinConsumerTarget` are actual
  proof terms for all four independently reviewed bounded specifications.

## Evidence

`python scripts/verify-stein-growth.py` passed two serial managed checks with
snapshot verification and shared source key
`c402614422cd765958bc9bc463ce8764e615829ec988119d89843d139ea347c6`.
The inventory covers 30 source declarations and 35 elaborated declarations,
including generated declarations. Every transitive axiom set is contained in
{propext, Classical.choice, Quot.sound}. See `verification/stein-growth/receipt.json`,
`elaborated-types.txt`, `axiom-audit.json`, `statement-review.md` and `final-review.md`.
`source-publication.json` binds the verified private Git tree delta to the exact
uploaded source hashes. The transport receipt does not substitute for Lean checks.

## Integration and remaining ownership

Integrate only the SteinGrowth modules and dedicated docs, verification and script
paths from this delivery. They import unchanged Statement/Geometry and native
pinned Mathlib; they do not import independently owned SteinRadial, SteinReference,
MoserExactness or FirstPathExactness implementations. Existing source and dependency
pins are preserved. The reproducible script checks both required preserved files
and, when present, unrelated snapshot-only files recorded in the initial workspace.

This closes the bounded extension/compact-exception implementation obligation,
subject to maintainer acceptance of the delivered evidence. It does not prove
MainTarget, SteinTarget or any comparison theorem. Root mission
91f6a7c7-1eb9-4e2c-bb7e-39389d62ea18 retains application to Stein geometry,
remaining exactness/comparison, other corollaries and final packaging through its
existing successor. Radial owner 1d193a92-1a8f-43a3-915d-9b3e2d6d80de and exactness
owner 1f6c4a8d-7d2b-4696-9a6f-2d9ac61c120b remain unchanged. No mission correction,
criterion removal, new planner, GitHub upload or final PDF was made.
