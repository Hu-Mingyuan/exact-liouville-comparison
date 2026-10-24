import ExactLiouvilleComparison.Geometry

/-! Bounded structural statement gate. These propositions are specifications,
not proofs of comparison existence from radial hypotheses. -/
noncomputable section
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.ExactComparisonAlgebra

variable {d : ℕ} (M : SmoothManifold d)

/-- The explicit witnesses in the existing `ExactComparison` conclusion.
This is a predicate on supplied maps and gauges, not additional geometric data. -/
def Witness (source target : M.Form 1) (F : M.SmoothEquiv M)
    (h : M.Point → ℝ) : Prop :=
  SmoothlyIsotopicToIdentity M F ∧
  ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ h ∧
  (∀ x v, evalOne (M.pullback M F source) x v =
    evalOne target x v + M.scalarDerivative h x v) ∧
  M.pullback M F (M.exteriorDerivative source) = M.exteriorDerivative target

def IdentityStatement : Prop :=
  ∀ source : M.Form 1,
    Witness M source source (Diffeomorph.refl _ _ ∞) (fun _ => 0)

def InversionStatement : Prop :=
  ∀ (source target : M.Form 1) (F : M.SmoothEquiv M) (h : M.Point → ℝ),
    Witness M source target F h →
    Witness M target source F.symm (fun x => -h (F.symm x))

def CompositionStatement : Prop :=
  ∀ (source middle target : M.Form 1) (F G : M.SmoothEquiv M)
    (h k : M.Point → ℝ),
    Witness M source middle F h → Witness M middle target G k →
    Witness M source target (G.trans F) (fun x => k x + h (G x))

def CommonReferenceStatement : Prop :=
  ∀ (source₁ source₂ reference : M.Form 1) (F₁ F₂ : M.SmoothEquiv M)
    (h₁ h₂ : M.Point → ℝ),
    Witness M source₁ reference F₁ h₁ → Witness M source₂ reference F₂ h₂ →
    Witness M source₁ source₂ (F₂.symm.trans F₁)
      (fun x => (h₁ - h₂) (F₂.symm x))

def IsotopyLawsStatement : Prop :=
  SmoothlyIsotopicToIdentity M (Diffeomorph.refl _ _ ∞) ∧
  (∀ F : M.SmoothEquiv M, SmoothlyIsotopicToIdentity M F →
    SmoothlyIsotopicToIdentity M F.symm) ∧
  (∀ F G : M.SmoothEquiv M, SmoothlyIsotopicToIdentity M F →
    SmoothlyIsotopicToIdentity M G → SmoothlyIsotopicToIdentity M (G.trans F))

end ExactLiouvilleComparison.ExactComparisonAlgebra
