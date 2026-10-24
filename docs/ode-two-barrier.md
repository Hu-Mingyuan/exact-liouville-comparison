# Two-barrier evolution infrastructure

`ODE.twoBarrierEvolution` proves the full unchanged
`ODE.TwoBarrierEvolutionTarget`. Import `ExactLiouvilleComparison.ODETwoBarrier`.
The statement at private baseline `70cb5f533db3755922378f2324a928398ac4b3a2`
and its accepted definition crosswalk are unchanged. The final theorem has
exactly the reviewed hypotheses; it assumes neither trajectories nor flows.

## Finite existence

`ODETwoBarrierConfinement.lean` proves the cutoff algebra, actual native chain
rules, one-sided scalar displacement estimates, and compact confinement.
`ODETwoBarrierExistence.twoBarrier_finiteIntervalExistence` constructs a curve
through every initial parameter and native point with the actual native ODE
on the whole closed interval. Its endpoint derivatives are full
`HasMFDerivAt`, stronger than derivatives only within the interval. No global
trajectory, completeness or absolute scalar-rate bound is an input.

For initial data `(s,x)`, uniform control of R by Q sublevels gives a threshold
A at level `Q(s,x)+C₁`. Choose the compact set
`K = {y | R(y) ≤ max (R(x)+C₀) A}`. It is fixed before choosing a cutoff or
trial curve. Properness and the lower bound on R prove compactness.

A smooth spacetime cutoff χ with values in `[0,1]` equals one on a neighborhood
of `[0,1] × K` and has compact support inside the field's open smooth domain.
The existing native cutoff bridge makes `W=χZ` globally smooth. The pinned
FsFltz compact-support theorem constructs an actual all-real solution for W.
The cutoff preserves `WR ≤ C₀`. Its total Q rate is
`χ(∂t Q+ZQ)+(1-χ)∂t Q ≥ -C₁`, using the nonnegative partial time derivative.

Along this solution, forward time gives
`R(γ(t)) ≤ R(x)+C₀(t-s) ≤ R(x)+C₀`.
Reverse time gives
`Q(t,γ(t)) ≤ Q(s,x)+C₁(s-t) ≤ Q(s,x)+C₁`, hence `R(γ(t)) ≤ A`.
The entire trajectory stays in K. Therefore χ is one along it and its actual
ODE is the original Z equation, including at both endpoints. This supplies
finite continuation directly by a complete auxiliary field.

The chain rule is proved using Mathlib `mfderiv_prod_eq_add_apply` and native
derivative composition. The time contribution is the ordinary real `deriv`;
the spatial contribution is the existing `SmoothManifold.scalarDerivative`.
No surrogate differentiation or geometry is introduced.

## Reuse and evidence

Sources inspected in order: pinned Mathlib native `IntegralCurve/ExistUnique`
and `MFDeriv/SpecificFunctions`, real mean-value bounds; pinned FsFltz
`CollarSmoothEvolution` and the compact-support existence interface imported
by `FamilyLiouvilleLocalFlow`; recorded cluster-skeleton
`2c239b0c03922a1549f18ee3a45a8e0ca25bb28c:ClusterSkeleton/NativeCompleteFlow.lean`.
The latter's compact-confinement/continuation proof is specialized to a cluster
seed field. The existing generic compact-support construction applies here.
No dependency, old-project or authoritative manuscript source was edited.

Run `python scripts/verify-ode-two-barrier.py` for serial managed build,
complete declaration/type inventory and transitive axiom audit of all 28 explicit declarations, including the final theorem. Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
Source hashes and baseline provenance are in
`verification/ode-two-barrier/source-binding.json`. This result is generic ODE infrastructure; the radial application and global
comparison theorem remain separate work.

## Smooth evolution and integration

`ODETwoBarrierLocalization.lean` constructs globally smooth evolutions for
compactly supported auxiliary fields and proves closed-segment native uniqueness
by localizing around compact trajectory traces. The original field need not
have an all-real flow.

`ODETwoBarrierLocalizationPatch.lean` localizes each finite trajectory. A compact
trace lies in an open set where the auxiliary and original fields agree.
Continuity and compactness enlarge the time interval beyond both endpoints and
give an open neighborhood of the initial time and point with the same property.
These are constructed smooth representatives, not extra input assumptions.

`ODETwoBarrierSmoothAssembly.lean` uses native uniqueness to identify the
representatives on overlaps. Their open domains form an actual open
neighborhood of the entire closed double-time strip. The selected evolution
is jointly smooth on this domain and solves the native ODE there.

`ODETwoBarrierSmooth.lean` constructs every field of the unchanged `Evolution`:
actual native diffeomorphisms with smooth inverse slices; full strip coverage;
initial identity; native and chart equations; closed unordered-interval
uniqueness; composition and inverse laws; and identity-start smooth isotopy,
including the inverse family. A globally smooth extension of the original
open-domain field is used only after proving equality on the closed strip;
no completeness of that extension is asserted.

Finally, `ODETwoBarrier.twoBarrierEvolution` supplies the finite-existence
premise of `evolution_of_finite_existence` using
`twoBarrier_finiteIntervalExistence`. Thus no trajectory assumption remains.

The source-bound independent component reviews are retained in
`verification/ode-two-barrier/finite-proof-review.md` and
`verification/ode-two-barrier-smooth/proof-review.md`. The final integration
review is `verification/ode-two-barrier/proof-review.md`. The two components
were privately delivered at `161487be39fee21c4ff64e660b32d120d9a4a77e`
and `e6b264151f8e1eed8e42f4b52e91e853fc0ff860`; the latter's four Lean modules
are integrated without changing their reviewed bytes. Final receipts bind the
combined source and full theorem.

Mission `c88064ba-ac8f-4ffe-b3aa-85315df3b9bf` owns this generic result.
Child mission `509d5a0f-ce2f-4fe5-9a4c-2365ff3cf96b` delivered the localization
bridge and is reconciled through this integration. Parent mission
`49efc076-e2c9-4fa3-bcb9-a88475037526` retains radial applicability,
specializations, consumers and flow integration; root `040e593e` retains
comparison. The split addressed the actual all-real hypotheses of the pinned
smooth-dependence interface and changed no required criterion. No complete
Liouville structure is claimed for the auxiliary fields. No GitHub upload
or final PDF belongs to this delivery.
