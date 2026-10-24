# Finite trajectories to smooth evolution

`ExactLiouvilleComparison.ODE.evolution_of_finite_existence` proves the generic
localization bridge at private baseline
`70cb5f533db3755922378f2324a928398ac4b3a2`.

For any native `SmoothManifold d`, assume an actual time-dependent tangent field
`Z` is `ContMDiffOn` on an open neighborhood of `[0,1] × M`. For each initial
parameter `s : Parameter` and point `x`, assume a curve `γ : ℝ → M.Point` with
`γ s.val = x` and the actual `HasMFDerivAt` equation at every `t ∈ [0,1]`.
No equation outside that interval and no jointly regular family of curves is
assumed. The result is the unchanged `Nonempty (FirstPathFlow.Evolution
(fun t : Parameter => Z t.val))`.

This is a bridge theorem. Parent mission `c88064ba-ac8f-4ffe-b3aa-85315df3b9bf`,
assignment `33e55321-24f6-43f9-b5eb-4d5ed623cd68`, owns finite existence from the
two scalar barriers, final two-barrier theorem assembly, integration and recovery.
This package does not claim that finite existence has been discharged, that
`TwoBarrierEvolutionTarget` is proved, or that the full comparison is accepted.

## Proof correspondence

1. `smoothEvolution_of_compact_support` constructs all-real auxiliary curves
   with FsFltz `CollarFlow.exists_global_solution`. Its uniqueness and native
   smooth-dependence theorem then produce actual smooth diffeomorphisms.
2. `compact_field_localization` applies the existing bounded smooth cutoff to
   a compact set of spacetime points. `eqOn_closed_of_hasMFDerivWithinAt`
   localizes around the two compact curve traces and reuses the proved closed
   uniqueness for the auxiliary evolution. It includes singleton and reversed
   intervals and does not assume completeness of the original field.
3. `evolutionPatch_of_finite_curve` cuts off around the given finite trajectory.
   Closed uniqueness identifies it with the auxiliary evolution on `[0,1]`.
   Continuity enlarges the time interval across both endpoints. Compactness
   gives an open neighborhood of initial data for which every auxiliary
   trajectory remains where the cutoff equals one. Thus each patch solves
   the original equation on an actual open time interval.
4. `EvolutionPatch.agree` compares patches on the intersection of their open
   time intervals using native nonautonomous uniqueness. `localEvolution`
   chooses their common value. `evolutionDomain` is their open union and
   contains the entire closed double-time strip. Local equality to a smooth
   patch proves `ContMDiffAt` there; no uniform exterior strip is asserted.
5. `evolution_of_finite_existence_global` constructs smooth time slices and
   their smooth inverses, native and chart equations, closed uniqueness,
   composition and inverse identities. The isotopy uses real-valued extension
   maps to prove smoothness within `[0,1]` of both the diffeomorphisms and their
   inverses. The clamped parameter is used only to supply diffeomorphisms at
   irrelevant exterior parameter values; it is not asserted to be smooth there.
6. `evolution_of_finite_existence` first uses the proved `extend_strip_field`.
   Its globally smooth extension agrees with `Z` on the strip but is not
   assumed complete. The finite premise transports literally along this
   equality, and the resulting full Evolution transports back.

## Definitions and verification

The accepted statement/crosswalk review at the baseline remains authoritative:
`verification/radial-interpolation-flow/{crosswalk,statement-review}.md`.
Native manifold, tangent, derivative and diffeomorphism definitions are retained.
No metric estimate or norm enters this generic bridge, so it introduces no
replacement for the reference metric or its dual/operator norms. No object
constructed here is asserted to be a Liouville manifold.

Only the new `ODETwoBarrierLocalization*` and `ODETwoBarrierSmooth*` modules,
this document, the matching script, and `verification/ode-two-barrier-smooth/`
are delivered. Existing sources, the aggregate module, manuscript, dependencies,
and radial modules remain unchanged. There is no GitHub upload or PDF.

Run `python3 scripts/verify-ode-two-barrier-smooth.py`. It checks preserved
baseline hashes and pinned dependency revisions, inventories the new explicit
declarations, serially builds the endpoint and checks declaration types and
transitive axioms. It requires only `propext`, `Classical.choice`, and
`Quot.sound`; managed checks require exact-source receipts. Logs, source hashes,
and the independent proof review are in `verification/ode-two-barrier-smooth/`.
Private publication and source binding are reported separately so no source
commit is falsely self-embedded in its own tree.
