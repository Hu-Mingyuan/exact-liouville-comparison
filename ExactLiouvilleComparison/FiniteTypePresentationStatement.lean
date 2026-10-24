import FsFltz.Geometry.IntrinsicCompletion
import ExactLiouvilleComparison.FiniteTypeComparison

/-! Native source-domain presentation of the finite-type corollary.
The quotient data below are OUTPUTS of `NativeTarget`, never source assumptions.
No independently specified completed manifold is transported by this interface. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology FsFltz.Geometry FsFltz.Geometry.SmoothManifold
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace ExactLiouvilleComparison.FiniteTypePresentation

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Local smooth defining functions, nonpositive locally on the domain, with positive
derivative along the primitive-determined field. This is exactly the pinned
native completion theorem's outwardness convention. -/
def LocalOutward (α : IntrinsicLiouville.Form k M 1) : Prop :=
  ∀ x : IntrinsicBoundary.Point k M,
    ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
      rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
      ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
      beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
        ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
        (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
      0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
        (IntrinsicLiouville.liouvilleVector α (IntrinsicLiouville.exteriorDerivative α) x.val))

/-- Witnesses produced by the existing native gluing theorem. In particular,
the global primitive and its laws are constructed, not input to `NativeTarget`. -/
structure QuotientData (α : IntrinsicLiouville.Form k M 1) where
  collar : ℝ × IntrinsicBoundary.Point k M → M
  width : ℝ
  positive : 0 < width
  embedding : IsOpenEmbedding (fun p : Half width (IntrinsicBoundary.Point k M) => collar p.val)
  smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ collar
    (Half width (IntrinsicBoundary.Point k M))
  boundary : ∀ p : Half width (IntrinsicBoundary.Point k M),
    (𝓡∂ (k + 1)).IsBoundaryPoint (collar p.val) ↔ p.val.1 = 0
  inverse : ∀ p ∈ Half width (IntrinsicBoundary.Point k M),
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (collar p) ∧
        ∀ᶠ q in 𝓝[Half width (IntrinsicBoundary.Point k M)] p, g (collar q) = q
  zero : ∀ b : IntrinsicBoundary.Point k M, collar (0, b) = b.val
  liouville : LiouvilleStructure (compactDomain positive collar embedding smooth boundary inverse zero)
  native_primitive : letI := completionChartedSpace positive collar embedding boundary zero
    (fun x => (liouville.primitive (original
      (fun p : Half width (IntrinsicBoundary.Point k M) => collar p.val) x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (original (fun p : Half width (IntrinsicBoundary.Point k M) => collar p.val)) x)) = α
  cylinder_primitive : (bandManifold width (IntrinsicBoundary.smoothManifold k M)).pullback
    (completionManifold positive collar embedding smooth boundary inverse zero)
    (cylinder (fun p : Half width (IntrinsicBoundary.Point k M) => collar p.val)) liouville.primitive =
      cylinderPrimitive width α
  nondegenerate : ∀ x, (completionManifold positive collar embedding smooth boundary inverse zero).Nondegenerate
    ((completionManifold positive collar embedding smooth boundary inverse zero).exteriorDerivative liouville.primitive) x
  canonical_field : liouville.field =
    (completionManifold positive collar embedding smooth boundary inverse zero).liouvilleVector liouville.primitive
  native_field : letI := completionChartedSpace positive collar embedding boundary zero
    ∀ x, liouville.field (original
      (fun p : Half width (IntrinsicBoundary.Point k M) => collar p.val) x) =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (original (fun p : Half width (IntrinsicBoundary.Point k M) => collar p.val)) x
        (IntrinsicLiouville.liouvilleVector α (IntrinsicLiouville.exteriorDerivative α) x)

namespace QuotientData
variable {α : IntrinsicLiouville.Form k M 1} (P : QuotientData α)

def domain : LiouvilleDomain (k + 1) :=
  ⟨compactDomain P.positive P.collar P.embedding P.smooth P.boundary P.inverse P.zero, P.liouville⟩

def completed (hα : IntrinsicLiouville.IsLocallyExtendibleForm α) : Completion P.domain :=
  completion P.positive P.collar P.embedding P.smooth P.boundary P.inverse P.zero
    α hα P.liouville P.nondegenerate P.cylinder_primitive

def nativeIn : M → P.domain.domain.extension.Point :=
  original (fun p : Half P.width (IntrinsicBoundary.Point k M) => P.collar p.val)

/-- All preservation clauses refer to the literal original map into this quotient.
The end parameter t is logarithmic: the manuscript radius is exp t. -/
def Identifications (hα : IntrinsicLiouville.IsLocallyExtendibleForm α) : Prop :=
  let Q := P.completed hα
  ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ P.nativeIn ∧
  IsClosedEmbedding P.nativeIn ∧
  (∀ x, Function.Bijective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) P.nativeIn x)) ∧
  range P.nativeIn = P.domain.domain.carrier ∧
  frontier P.domain.domain.carrier = P.nativeIn '' (𝓡∂ (k + 1)).boundary M ∧
  (∀ x, Q.inclusion.map x = x) ∧
  (∀ x, (Q.ambient.primitive (P.nativeIn x)).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) P.nativeIn x) = α x) ∧
  (∀ x, Q.ambient.field (P.nativeIn x) =
    mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) P.nativeIn x
      (IntrinsicLiouville.liouvilleVector α (IntrinsicLiouville.exteriorDerivative α) x)) ∧
  (∀ b : IntrinsicBoundary.Point k M, P.domain.domain.boundaryInclusion.map b = P.nativeIn b.val) ∧
  P.domain.domain.boundaryForm P.domain.liouville.primitive = IntrinsicBoundary.restrictForm α ∧
  (∀ (b : IntrinsicBoundary.Point k M) (t : ℝ), -P.width < t →
    Q.endMap (b, t) = outwardEndMap P.positive P.collar (b, t)) ∧
  (∀ (b : IntrinsicBoundary.Point k M) (t : ℝ) (v : Model k) (s : ℝ),
    evalOne Q.ambient.primitive (Q.endMap (b, t))
      (mfderiv (𝓘(ℝ, Model k).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model (k + 1)) Q.endMap (b, t) (v, s)) =
      Real.exp t * evalOne (M := IntrinsicBoundary.smoothManifold k M)
        (IntrinsicBoundary.restrictForm α) b v)

/-- Same chosen J, metric g, dual and inverse operator norm as the accepted
corollary, all on the actual quotient. No completion or flow is a new premise. -/
def ComparisonFor (hα : IntrinsicLiouville.IsLocallyExtendibleForm α) : Prop :=
  let Q := P.completed hα
  ∀ (A : CompatibleStructure (completionReference Q)), CylindricalStructure Q A →
    ∀ (T : ExactSymplecticStructure Q.ambient.manifold), WeaklyTames A T →
    (∃ B : AdmissibleGrowth 1, ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ t₀ : ℝ, 0 ≤ t₀ ∧
      ∀ y t, t₀ ≤ t → A.inverseNorm T (Q.endMap (y, t)) ≤ C₀ * B.B (Real.exp t)) →
    FiniteTypeComparison.NativeConclusion Q.ambient.manifold T.primitive Q.ambient.primitive

end QuotientData

/-- Bounded source-level statement. It constructs one quotient before choosing
J or the comparison primitive; it does not assert uniqueness or given-X transport. -/
def NativeTarget (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α) : Prop :=
  (∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative α) x) →
  LocalOutward α → ∃ P : QuotientData α, P.Identifications hα ∧ P.ComparisonFor hα

end ExactLiouvilleComparison.FiniteTypePresentation
