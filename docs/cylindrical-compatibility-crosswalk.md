# Cylindrical compatible structures: statement crosswalk

Mission deee4e3c-9772-491a-b842-98913f062983, revision 1. This is the
pre-proof specification of a supporting assertion, not a completed construction.
Authoritative source: unchanged `docs/reference/exact_liouville_comparison.tex`,
lines 376–392, especially equation `eq:cylJ` and the following extension sentence.
Coverage ruling: FINAL artifact ae0f8bb3-2396-4e53-82c4-3e6fc4afdf77;
evidence d1e7b976-d2d6-4498-ac32-463cb21d7e02. The accepted four comparison
proofs and complete specialization remain unchanged.

## Quantifiers and native meaning

`CylindricalCompatibilityStatement.lean` imports the accepted Statement directly.
`ExistenceTarget` quantifies every natural d, LiouvilleDomain D, and Completion C,
and outputs a CompatibleStructure A together with Nonempty (CylindricalStructure C A).
Neither A nor its cylindrical witness is an input. `ExtensionTarget` additionally
accepts arbitrary prescribed ContactData D and outputs A agreeing with them on
the entire closed nonnegative end. These are separate obligations.
`ContactExistenceTarget` explicitly requires constructing the contact input;
proving extension alone cannot establish existence by a vacuous argument.

FsFltz SmoothManifold uses native Mathlib ChartedSpace, IsManifold and TangentSpace,
with Hausdorff second-countable finite-dimensional real model. Forms are actual
continuous alternating maps on those tangent spaces. The boundary form alpha is
the pullback of the domain primitive through its actual smooth boundary inclusion.
The exterior derivative is the pinned native-chart exterior derivative, not an
arbitrary operation. Completion includes the actual complete Liouville flow for
all real times and uses the positive convention d beta(Z,v)=beta(v).

ContactData presents a complex structure on ker(alpha) as a boundary tangent
endomorphism J that vanishes on the Reeb line. It supplies native smoothness of
both that endomorphism section and the Reeb vector field; alpha(Reeb)=1 and
d alpha(Reeb,v)=0; alpha(Jv)=0; J Reeb=0;
J(Jv)=-v+alpha(v) Reeb; invariance of d alpha; and strict positivity
d alpha(v,Jv)>0 for nonzero v in ker(alpha). The split
v=(v-alpha(v) Reeb)+alpha(v) Reeb explains the representation. Restriction to
the kernel has square -id, is symplectic and positive. Conversely the zero
extension of prescribed smooth kernel data is the intended encoding. A native
kernel restriction/zero-extension bridge remains proof work; no topological
trivialization of the contact bundle is assumed. Reeb data are characterized by
their actual equations and do not contain a global extension conclusion.

The end parameter is t with r=exp(t). Thus the time vector is r partial_r.
`Extends C P A` is the complete formula

    J_X d(endMap)(v,s) = d(endMap)(P.J v+s P.reeb, -alpha(v))

for every boundary point, every t>=0 (including t=0), every v and every s.
It simultaneously gives J(r partial_r)=Reeb, J Reeb=-r partial_r and the
prescribed t-independent contact restriction. It does not merely assert agreement
eventually or outside a larger compact set. Turning this identity into the
existing CylindricalStructure requires only its named fields, not a changed
accepted interface.

The output CompatibleStructure contains native SmoothEndomorphism, square=-id,
symplectic invariance, and a Bundle.ContMDiffRiemannianMetric with the exact
identity g(v,w)=d beta(v,Jw). This metric must be constructed, including its
smoothness and positivity. MetricTangent, covector, dualNorm and inverseNorm in
Geometry.lean then use its actual tangent/dual/operator norms; no ambient chart
norm is silently substituted. No completeness of this metric is assumed.

`ConsumerTarget` chooses A before quantifying T. T is any exact symplectic
structure on the same completion. Its only analytic premises are the unchanged
WeaklyTames A T and existential admissible B, positive C0, nonnegative t0, and
the inverse-norm bound at every y,t with t>=t0. Applying the already proved
FiniteTypeComparison.finiteTypeTarget to a constructed A and cylindrical witness
will give the original exact diffeomorphism, isotopy and +dh conclusion.
There is no primitive-growth or completeness premise on T.

## Boundary cases

No positivity, parity or nonemptiness restriction is imposed on d or the
manifolds. CompactDomain.zero_boundary makes the boundary empty when d=0.
The zero-dimensional ambient still needs a compatible metric and zero J; the
empty contact input and its extension formula are vacuous only on that boundary.
In other dimensions any dimension consequences used in a proof must be derived.
Existing FiniteTypeRadialMetric.end_derivative_surjective delegates to
Completion.endMap_isLocalDiffeomorph, whose upstream proof handles the
positive-dimension consequence needed for its dimension count.

## Reuse checks and unresolved construction

Mathlib: Geometry/Manifold/VectorBundle/Riemannian.lean defines the required
smooth metric with explicit inner, symmetry, positivity, bounded unit ball and
native section smoothness. Geometry/Manifold/PartitionOfUnity.lean provides
exists_contMDiffSection_forall_mem_convex_of_local for gluing sections in convex
fiber sets. These do not by themselves construct compatible J. LinearAlgebra/
SymplecticGroup concerns standard symplectic matrices, not the requested relative
smooth bundle construction.

FsFltz: Geometry/Liouville.lean supplies the actual domain/completion interfaces.
CompatibleComplexPath.lean constructs compatible paths from two already given
compatible structures, with polynomial intertwiners and smooth inverses. It may
serve for relative gluing, but cannot be cited as unconditional existence.
CanonicalBundle.exists_smooth_local_complexCoframe starts from an already supplied
J and therefore does not construct the missing J. Reuse must respect that input.

Mandatory cluster inspection: the read-only cluster-skeleton snapshot at
2c239b0c03922a1549f18ee3a45a8e0ca25bb28c has GeometryTarget.LiouvilleData and its
complete-flow conversion. It preserves native primitive/flow data and does not
supply the supporting cylindrical-J existence theorem. A separate bounded
reuse audit checks further construction candidates before new infrastructure.

Remaining mathematical work: construct compatible contact data, extend prescribed
data smoothly over the core while fixing every t>=0, construct the native metric,
and instantiate the existing comparison. Definitions of the targets discharge
none of these obligations. No shared Statement/Geometry change is proposed.
