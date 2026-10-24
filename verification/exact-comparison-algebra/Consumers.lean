import ExactLiouvilleComparison.ExactComparisonAlgebra

noncomputable section
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
open ExactLiouvilleComparison ExactLiouvilleComparison.ExactComparisonAlgebra

namespace ExactComparisonAlgebraConsumers
variable {d : ℕ} {M : SmoothManifold d}

/-- The composition consumer spells out the function composition and gauge. -/
theorem composition_sign {a b c : M.Form 1} {F G : M.SmoothEquiv M}
    {h k : M.Point → ℝ} (wF : Witness M a b F h) (wG : Witness M b c G k) :
    (∀ x v, evalOne (M.pullback M (fun y => F (G y)) a) x v =
      evalOne c x v + M.scalarDerivative (fun y => k y + h (G y)) x v) ∧
    M.pullback M (fun y => F (G y)) (M.exteriorDerivative a) = M.exteriorDerivative c :=
  (wF.comp wG).2.2

/-- The inverse consumer exposes the minus sign inside the actual scalar derivative. -/
theorem inversion_sign {a b : M.Form 1} {F : M.SmoothEquiv M}
    {h : M.Point → ℝ} (w : Witness M a b F h) :
    (∀ x v, evalOne (M.pullback M F.symm b) x v =
      evalOne a x v + M.scalarDerivative (fun y => -h (F.symm y)) x v) ∧
    M.pullback M F.symm (M.exteriorDerivative b) = M.exteriorDerivative a :=
  w.symm.2.2

/-- Composition with the inverse cancels the actual gauge as well as the map. -/
theorem round_trip {a b : M.Form 1} {F : M.SmoothEquiv M}
    {h : M.Point → ℝ} (w : Witness M a b F h) :
    Witness M a a (Diffeomorph.refl _ _ ∞) (fun _ => 0) := by
  have hw := w.comp w.symm
  simpa only [Diffeomorph.symm_trans_self, neg_add_cancel] using hw

/-- Explicit witnesses and both identities for the manuscript's common-reference formula. -/
theorem common_reference_explicit {a b reference : M.Form 1}
    {F₁ F₂ : M.SmoothEquiv M} {h₁ h₂ : M.Point → ℝ}
    (w₁ : Witness M a reference F₁ h₁) (w₂ : Witness M b reference F₂ h₂) :
    ∃ (Phi : M.SmoothEquiv M) (q : M.Point → ℝ),
      (∀ x, Phi x = F₁ (F₂.symm x)) ∧
      (∀ x, q x = h₁ (F₂.symm x) - h₂ (F₂.symm x)) ∧
      SmoothlyIsotopicToIdentity M Phi ∧
      ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ q ∧
      (∀ x v, evalOne (M.pullback M Phi a) x v =
        evalOne b x v + M.scalarDerivative q x v) ∧
      M.pullback M Phi (M.exteriorDerivative a) = M.exteriorDerivative b := by
  exact ⟨F₂.symm.trans F₁, (fun x => (h₁ - h₂) (F₂.symm x)),
    fun _ => rfl, fun _ => rfl, w₁.commonReference w₂⟩

/-- A consumer of both smooth isotopy directions, including the closed endpoints. -/
theorem common_reference_isotopy {a b reference : M.Form 1}
    {F₁ F₂ : M.SmoothEquiv M} {h₁ h₂ : M.Point → ℝ}
    (w₁ : Witness M a reference F₁ h₁) (w₂ : Witness M b reference F₂ h₂) :
    ∃ H : ℝ → M.SmoothEquiv M,
      (∀ x, H 0 x = x) ∧ (∀ x, H 1 x = F₁ (F₂.symm x)) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model d))) (𝓘(ℝ, Model d)) ∞
        (fun p : ℝ × M.Point => H p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model d))) (𝓘(ℝ, Model d)) ∞
        (fun p : ℝ × M.Point => (H p.1).symm p.2) (Icc (0 : ℝ) 1 ×ˢ univ) :=
  (w₁.commonReference w₂).1

/-- The unchanged relation supports a common reference without extra geometric premises. -/
theorem relation_consumer {a b reference : M.Form 1}
    (wa : ExactComparison M a reference) (wb : ExactComparison M b reference) :
    ExactComparison M a b ∧ ExactComparison M b a :=
  ⟨wa.commonReference wb, (wa.commonReference wb).symm⟩

end ExactComparisonAlgebraConsumers

#check ExactComparisonAlgebraConsumers.composition_sign
#check ExactComparisonAlgebraConsumers.inversion_sign
#check ExactComparisonAlgebraConsumers.round_trip
#check ExactComparisonAlgebraConsumers.common_reference_explicit
#check ExactComparisonAlgebraConsumers.common_reference_isotopy
#check ExactComparisonAlgebraConsumers.relation_consumer
#print axioms ExactComparisonAlgebraConsumers.composition_sign
#print axioms ExactComparisonAlgebraConsumers.inversion_sign
#print axioms ExactComparisonAlgebraConsumers.round_trip
#print axioms ExactComparisonAlgebraConsumers.common_reference_explicit
#print axioms ExactComparisonAlgebraConsumers.common_reference_isotopy
#print axioms ExactComparisonAlgebraConsumers.relation_consumer
#eval IO.println "EXACT_COMPARISON_CONSUMERS_COMPLETE"
