import ExactLiouvilleComparison.MoserRegularityGlobal

/-! Bounded first-path flow contract. No existence assertion is proved by this file. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.FirstPathFlow
variable {d : ℕ} {M : SmoothManifold d}

/-- Native nonautonomous ODE on a real parameter set; endpoint derivatives are within
that set. Continuity is explicit, including for singleton parameter sets. -/
def IsSolution (Z : Parameter → (x : M.Point) → M.Tangent x)
    (γ : ℝ → M.Point) (J : Set ℝ) : Prop :=
  ContinuousOn γ J ∧ ∀ t ∈ J, ∀ ht : t ∈ parameterInterval,
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ J t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z ⟨t, ht⟩ (γ t)))

/-- Output data, never an input to the first-path existence target. The ordering
is initial time, terminal time, initial point. Smoothness has an actual open
extension around both closed time parameters, with no uniform exterior strip. -/
structure Evolution (Z : Parameter → (x : M.Point) → M.Tangent x) where
  map : Parameter → Parameter → M.SmoothEquiv M
  extension : ℝ → ℝ → M.Point → M.Point
  agrees : ∀ s t : Parameter, extension s.val t.val = map s t
  smooth : ∃ U : Set (ℝ × (ℝ × M.Point)), IsOpen U ∧
    parameterInterval ×ˢ (parameterInterval ×ˢ univ) ⊆ U ∧
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
      𝓘(ℝ, Model d) ∞ (fun p => extension p.1 p.2.1 p.2.2) U
  initial : ∀ s x, map s s x = x
  solves : ∀ (s : Parameter) x, IsSolution Z (fun t => extension s.val t x) parameterInterval
  chart_solves : ∀ (s t : Parameter) (x a : M.Point),
    map s t x ∈ (chartAt (Model d) a).source →
    HasDerivWithinAt (fun u => chartAt (Model d) a (extension s.val u x))
      (M.chartTangentMap a (map s t x) (Z t (map s t x))) parameterInterval t.val
  unique : ∀ (s t : Parameter) (γ : ℝ → M.Point),
    IsSolution Z γ (uIcc s.val t.val) →
    γ t.val = map s t (γ s.val)
  compose : ∀ r s t x, map s t (map r s x) = map r t x
  inverse : ∀ s t, (map s t).symm = map t s
  isotopy : ∀ t, SmoothlyIsotopicToIdentity M (map parameterZero t)

/-- The arbitrary admissible growth function and original compact exception remain
explicit. In particular this statement neither assumes a flow nor metric completeness. -/
def Target : Prop :=
  ∀ (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    (C : ℝ), 0 < C → ∀ K : Set M.Point, IsCompact K →
    (∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * G.B (P.R x)) →
    Nonempty (Evolution (MoserRegularity.firstField P G T hw))

/-- Original manuscript input consumer; the chosen coefficient is tied to its
admissible growth witness, and the field is the literal accepted first path. -/
def GrowthTarget : Prop :=
  ∀ (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T), GrowthAtInfinity P.compatible T P.R 1 →
    ∃ G : AdmissibleGrowth 1,
      Nonempty (Evolution (fun t x => FirstPath.X P G T hw x t.val t.property.1))
end ExactLiouvilleComparison.FirstPathFlow
