import ExactLiouvilleComparison.ExactComparisonAlgebraIsotopy

/-! Exact-comparison algebra with explicit native diffeomorphism and gauge
witnesses. These structural laws do not construct Moser endpoints. -/
noncomputable section
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set

namespace ExactLiouvilleComparison
namespace ExactComparisonAlgebra
variable {d : ℕ} {M : SmoothManifold d}

/-- Evaluation of the literal native pullback. -/
theorem evalOne_pullback (F : M.Point → M.Point) (source : M.Form 1)
    (x : M.Point) (v : M.Tangent x) :
    evalOne (M.pullback M F source) x v =
      evalOne source (F x) (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) F x v) := rfl

/-- Scalar chain rule for the literal `scalarDerivative` interface. -/
theorem scalarDerivative_comp {h : M.Point → ℝ}
    (hh : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ h)
    (F : M.SmoothEquiv M) (x : M.Point) (v : M.Tangent x) :
    M.scalarDerivative (fun x => h (F x)) x v =
      M.scalarDerivative h (F x)
        (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) F x v) := by
  exact congrArg (fun L : M.Tangent x →L[ℝ] ℝ => L v)
    (mfderiv_comp x (hh.mdifferentiable (by simp) (F x))
      (F.mdifferentiable (by simp) x))

/-- Gauge addition uses the native derivative addition theorem. -/
theorem scalarDerivative_add {h k : M.Point → ℝ}
    (hh : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ h)
    (hk : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ k)
    (x : M.Point) (v : M.Tangent x) :
    M.scalarDerivative (fun x => h x + k x) x v =
      M.scalarDerivative h x v + M.scalarDerivative k x v := by
  exact congrArg (fun L : M.Tangent x →L[ℝ] ℝ => L v)
    (mfderiv_add (hh.mdifferentiable (by simp) x) (hk.mdifferentiable (by simp) x))

/-- Gauge negation preserves the literal derivative sign. -/
theorem scalarDerivative_neg (h : M.Point → ℝ) (x : M.Point) (v : M.Tangent x) :
    M.scalarDerivative (fun x => -h x) x v = -M.scalarDerivative h x v := by
  exact congrArg (fun L : M.Tangent x →L[ℝ] ℝ => L v)
    (mfderiv_neg (I := 𝓘(ℝ, Model d)) (f := h) (x := x))

/-- Merely regroup the existential witnesses of the unchanged definition. -/
theorem exactComparison_iff_exists_witness (source target : M.Form 1) :
    ExactComparison M source target ↔
      ∃ (F : M.SmoothEquiv M) (h : M.Point → ℝ), Witness M source target F h := by
  constructor
  · rintro ⟨F, hF, h, hh, hp, hd⟩
    exact ⟨F, h, hF, hh, hp, hd⟩
  · rintro ⟨F, h, hF, hh, hp, hd⟩
    exact ⟨F, hF, h, hh, hp, hd⟩

namespace Witness

/-- Forget the specified witnesses to recover the existing comparison. -/
theorem exactComparison {source target : M.Form 1} {F : M.SmoothEquiv M}
    {h : M.Point → ℝ} (w : Witness M source target F h) :
    ExactComparison M source target :=
  (exactComparison_iff_exists_witness source target).mpr ⟨F, h, w⟩

/-- Identity comparison with the zero gauge. -/
theorem refl (source : M.Form 1) :
    Witness M source source (Diffeomorph.refl _ _ ∞) (fun _ => 0) := by
  refine ⟨SmoothlyIsotopicToIdentity.refl M, contMDiff_const, ?_, ?_⟩
  · intro x v
    simp only [Diffeomorph.coe_refl, M.pullback_id, scalarDerivative, mfderiv_const]
    exact (add_zero _).symm
  · exact M.pullback_id _

/-- Compose F*source = middle + dh and G*middle = target + dk.
The actual map is F ∘ G and the actual gauge is k + h ∘ G. -/
theorem comp {source middle target : M.Form 1} {F G : M.SmoothEquiv M}
    {h k : M.Point → ℝ} (wF : Witness M source middle F h)
    (wG : Witness M middle target G k) :
    Witness M source target (G.trans F) (fun x => k x + h (G x)) := by
  obtain ⟨hiF, hh, hpF, hdF⟩ := wF
  obtain ⟨hiG, hk, hpG, hdG⟩ := wG
  refine ⟨hiG.trans hiF, hk.add (hh.comp G.contMDiff), ?_, ?_⟩
  · intro x v
    rw [Diffeomorph.coe_trans, M.pullback_comp M M
      (G.mdifferentiable (by simp)) (F.mdifferentiable (by simp))]
    rw [evalOne_pullback, hpF]
    rw [← evalOne_pullback G middle, hpG]
    rw [scalarDerivative_add (k := fun x => h (G x)) hk (hh.comp G.contMDiff),
      scalarDerivative_comp hh G]
    ring
  · rw [Diffeomorph.coe_trans, M.pullback_comp M M
      (G.mdifferentiable (by simp)) (F.mdifferentiable (by simp)), hdF, hdG]

/-- Invert the comparison, using the gauge −h ∘ F⁻¹. -/
theorem symm {source target : M.Form 1} {F : M.SmoothEquiv M}
    {h : M.Point → ℝ} (w : Witness M source target F h) :
    Witness M target source F.symm (fun x => -h (F.symm x)) := by
  obtain ⟨hi, hh, hp, hd⟩ := w
  refine ⟨hi.symm, contDiff_neg.comp_contMDiff (hh.comp F.symm.contMDiff), ?_, ?_⟩
  · intro x v
    have hc := congrArg (fun eta : M.Form 1 => evalOne eta x v)
      (M.pullback_symm_pullback M F source)
    rw [evalOne_pullback, hp] at hc
    rw [evalOne_pullback, scalarDerivative_neg,
      scalarDerivative_comp hh F.symm]
    linarith
  · rw [← hd]
    exact M.pullback_symm_pullback M F _

/-- The manuscript's explicit common-reference map and difference gauge.
Both input comparisons must already have been proved. -/
theorem commonReference {source₁ source₂ reference : M.Form 1}
    {F₁ F₂ : M.SmoothEquiv M} {h₁ h₂ : M.Point → ℝ}
    (w₁ : Witness M source₁ reference F₁ h₁)
    (w₂ : Witness M source₂ reference F₂ h₂) :
    Witness M source₁ source₂ (F₂.symm.trans F₁)
      (fun x => (h₁ - h₂) (F₂.symm x)) := by
  have w := w₁.comp w₂.symm
  have hg : (fun x => -h₂ (F₂.symm x) + h₁ (F₂.symm x)) =
      (fun x => (h₁ - h₂) (F₂.symm x)) := by
    funext x
    simp only [Pi.sub_apply]
    ring
  rw [hg] at w
  exact w

end Witness

/-- Proof of the reviewed identity specification. -/
theorem identity (M : SmoothManifold d) : IdentityStatement M := Witness.refl

/-- Proof of the reviewed inversion specification. -/
theorem inversion (M : SmoothManifold d) : InversionStatement M :=
  fun _ _ _ _ w => w.symm

/-- Proof of the reviewed composition specification. -/
theorem composition (M : SmoothManifold d) : CompositionStatement M :=
  fun _ _ _ _ _ _ _ wF wG => wF.comp wG

/-- Proof of the reviewed common-reference specification. -/
theorem commonReference (M : SmoothManifold d) : CommonReferenceStatement M :=
  fun _ _ _ _ _ _ _ w₁ w₂ => w₁.commonReference w₂

end ExactComparisonAlgebra

namespace ExactComparison
open ExactComparisonAlgebra
variable {d : ℕ} {M : SmoothManifold d}

/-- The existing exact-comparison relation is reflexive. -/
theorem refl (source : M.Form 1) : ExactComparison M source source :=
  (Witness.refl source).exactComparison

/-- The existing exact-comparison relation is symmetric. -/
theorem symm {source target : M.Form 1} (w : ExactComparison M source target) :
    ExactComparison M target source := by
  obtain ⟨F, h, hw⟩ := (exactComparison_iff_exists_witness source target).mp w
  exact hw.symm.exactComparison

/-- The existing exact-comparison relation is transitive. -/
theorem trans {source middle target : M.Form 1}
    (w₁ : ExactComparison M source middle) (w₂ : ExactComparison M middle target) :
    ExactComparison M source target := by
  obtain ⟨F, h, hwF⟩ := (exactComparison_iff_exists_witness source middle).mp w₁
  obtain ⟨G, k, hwG⟩ := (exactComparison_iff_exists_witness middle target).mp w₂
  exact (hwF.comp hwG).exactComparison

/-- Conditional common-reference combination; no radial existence is asserted. -/
theorem commonReference {source₁ source₂ reference : M.Form 1}
    (w₁ : ExactComparison M source₁ reference) (w₂ : ExactComparison M source₂ reference) :
    ExactComparison M source₁ source₂ := w₁.trans w₂.symm

end ExactComparison
end ExactLiouvilleComparison
