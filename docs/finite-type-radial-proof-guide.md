# Finite-type radial proof guide

Status: the bounded construction, original metric identities and growth bridge
are implemented. The distinct cylindrical metric child
0b5b2f0c-3dfa-4741-ac55-30976cabd107 delivered independently reviewed source
9716da2fdab7d268cfea6fbc3808a40cf3a47546, integrated without changes. This is
not FiniteTypeTarget or MainTarget, and no comparison is assumed. Final combined
checks and independent review are recorded in verification/finite-type-radial/.

The independent statement gate is verification/finite-type-radial/statement-review.md.
Semantic source assumptions remain unchanged.

## Radius and compactness

`profile r = 1 + smoothTransition (2*r-3)*(r-1)` is smooth, at least one,
identically one below 3/2, equal to r from 2, and at most two below 2.
`radius C` uses this profile of exp(t) on the actual escaping basin and one
outside it. `radius_end` proves the formula for every real end time from the
pinned end inverse; `radius_end_eq` gives the manuscript equality.

`radius_smooth` uses the proved native local diffeomorphism of the end map
at basin points. Outside the basin it is locally constant, because the end
ray starting at log(3/2) is closed. The latter is the pinned theorem
Completion.isClosed_endMap_image_Ici, proved by the actual full flow and
compact-domain/end topology. This imports CompletionIntervalMapFamily only
for that proved closed-ray fact; no map family, Moser flow, or comparison is
an assumption. All branches use actual ContMDiff and eventual equalities.

`compact_farEnd_compl` proves compactness of the complement of every strict
end cutoff a. That complement is closed by native openness of endMap, and
coverage places it in the compact domain image union the image of
boundary×[0,a]. Compactness of the native boundary is the pinned
CompactDomain.isCompact_boundary, derived from its embedded compact frontier.
The argument works even for negative a and for empty boundary.

`radius_sublevel_compact` contains the closed sublevel R≤b in the compact
complement of t>log(max(2,b)). On that tail R=exp(t)>b. Native
isProperMap_iff_isCompact_preimage and compact real sets being bounded above
then give `radius_proper`. `radius_core_bound` proves R≤2 off t>log(2).
No metric completeness or chosen exhaustion is used.

## Growth and packing

`growth_witness Q` sets K to the complement of the strict end above
max(t₀,log(2)). The proved compact truncation makes K compact. Outside K,
R=exp(t), so the original bound transfers with exactly the original B and C₀.
The stronger intermediate proof needs neither positivity of C₀ nor t₀≥0;
`growthWitnessTarget` reinstates those exact source premises. `growth` packages
the unchanged existential witnesses into GrowthAtInfinity.

`radius_primitive` and `radius_dual_sq` apply the metric child's proved
identities to `radius C`, discharging its native smoothness and end-equality
premises by radius_smooth and radius_end_eq. The compact-core bound proves that
every point with R>2 lies at an end time greater than log(2). These are literal
identities in the original metric, not estimates in chart norms.

`constructedRadius` constructs every Radius field from C, A and the original
CylindricalStructure. `reference` then uses `Radius.toReference` to construct
the actual RadialReference with exactly completionReference C, A, c=1 and
rstar=2. The actual theorems `constructionTarget` and `consumerTarget` prove
the independently reviewed specifications without further hypotheses.

The metric child uses the native chain rule and equality on an open end
neighborhood for dR(d endMap(v,s))=exp(t)*s. The original complete flow's native
integral-curve theorem identifies d endMap(0,1) with its original field Z.
Cylindrical J and derivative surjectivity give β=−dR∘J on every ambient vector.
Positive contraction and g(v,w)=dβ(v,Jw) then give g(Z,w)=dR(w). The native Riesz
isometry identifies the SAME covector on the g-tangent; consequently its dual
norm square is g(Z,Z)=dR(Z)=exp(t)=R. No pullback/exterior-derivative operator
is assumed, and no calculation treats chart norms as g.

FiniteTypeRadialConsumers exposes reflexive equalities preserving the exact
structure, compatible structure, primitive, J, g, radius, c and rstar; it also
exposes the native end derivative at the constructed reference and the original
B/C₀ witness conversion. `checked_construction`, `checked_growth` and
`checked_consumer` check all three advertised specification proofs.

Run `python scripts/verify-finite-type-radial.py` for the current bounded proof
scope, full elaborated type inventory and transitive audit. Final proof and
source-bound review claims must cite their exact final receipts.

The published full inventories are losslessly gzip-compressed to fit the private
artifact transport limit. `elaborated-types-full.txt.gz` contains fully explicit
types with proofs and deep terms displayed, with no elision; its decompressed
SHA-256 and byte length are recorded in receipt.json. The accompanying
elaborated-types.txt is readable. `statement-inventory.types.gz` reconstructs
exactly the statement-inventory.types bytes bound by the statement review.
The earlier specification inventory used default proof display; the final
expanded audit supersedes it for full type coverage without changing semantics.
