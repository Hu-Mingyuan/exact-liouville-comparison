import ExactLiouvilleComparison.FirstPathFlowStatement
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.ODE
variable {d : ℕ} {M : SmoothManifold d}

/-- Properness and boundedness below give compact scalar sublevels. -/
theorem compact_sublevel (P : M.Point → ℝ) (hp : IsProperMap P)
    (hl : BddBelow (range P)) (A : ℝ) : IsCompact {x | P x ≤ A} := by
  obtain ⟨b, hb⟩ := hl
  have heq : {x | P x ≤ A} = P ⁻¹' Icc b A := by
    ext x
    exact ⟨fun h => ⟨hb (mem_range_self x), h⟩, fun h => h.2⟩
  rw [heq]
  exact hp.isCompact_preimage isCompact_Icc

/-- The derivative bound concerns the actual scalar along the actual native curve. -/
theorem scalar_hasDerivWithinAt
    (Z : Parameter → (x : M.Point) → M.Tangent x)
    (P : M.Point → ℝ) (hP : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ P)
    {γ : ℝ → M.Point} {J : Set ℝ} (hγ : FirstPathFlow.IsSolution Z γ J)
    {t : ℝ} (ht : t ∈ J) (hi : t ∈ parameterInterval) :
    HasDerivWithinAt (fun u => P (γ u))
      (M.scalarDerivative P (γ t) (Z ⟨t, hi⟩ (γ t))) J t := by
  have hd := ((hP.mdifferentiable (by simp) (γ t)).hasMFDerivAt.comp_hasMFDerivWithinAt t
    (hγ.2 t ht hi))
  have hr := (hasMFDerivWithinAt_iff_hasFDerivWithinAt.mp hd).hasDerivWithinAt
  apply hr.congr_deriv
  change M.scalarDerivative P (γ t) ((1 : ℝ) • Z ⟨t, hi⟩ (γ t)) = _
  rw [one_smul]

/-- Uniform scalar control confines any existing solution in both time directions.
This is an a priori estimate, not an existence theorem. -/
theorem scalar_displacement
    (Z : Parameter → (x : M.Point) → M.Tangent x)
    (P : M.Point → ℝ) (hP : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ P)
    {D : ℝ} (hb : ∀ t : Parameter, ∀ x, |M.scalarDerivative P x (Z t x)| ≤ D)
    {γ : ℝ → M.Point} {J : Set ℝ} (hγ : FirstPathFlow.IsSolution Z γ J)
    (hJ : J ⊆ parameterInterval) (hc : Convex ℝ J)
    {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    |P (γ t) - P (γ s)| ≤ D * |t - s| := by
  classical
  let rate : ℝ → ℝ := fun u => if hu : u ∈ J then
    M.scalarDerivative P (γ u) (Z ⟨u, hJ hu⟩ (γ u)) else 0
  have hd : ∀ u ∈ J, HasDerivWithinAt (fun r => P (γ r)) (rate u) J u := by
    intro u hu
    simpa only [rate, dite_eq_left hu] using scalar_hasDerivWithinAt Z P hP hγ hu (hJ hu)
  have hr : ∀ u ∈ J, ‖rate u‖ ≤ D := by
    intro u hu
    simpa only [rate, dite_eq_left hu, Real.norm_eq_abs] using hb ⟨u, hJ hu⟩ (γ u)
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hr hc hs ht

/-- A compact set chosen before the trial solution confines it for a bounded horizon. -/
theorem compact_confinement
    (Z : Parameter → (x : M.Point) → M.Tangent x)
    (P : M.Point → ℝ) (hP : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ P)
    (hp : IsProperMap P) (hl : BddBelow (range P))
    {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ t : Parameter, ∀ x, |M.scalarDerivative P x (Z t x)| ≤ D)
    (x : M.Point) (A : ℝ) :
    ∃ K : Set M.Point, IsCompact K ∧
      ∀ (γ : ℝ → M.Point) (J : Set ℝ), FirstPathFlow.IsSolution Z γ J →
      J ⊆ parameterInterval → Convex ℝ J → ∀ s ∈ J, γ s = x →
      ∀ t ∈ J, |t - s| ≤ A → γ t ∈ K := by
  refine ⟨{y | P y ≤ P x + D * A}, compact_sublevel P hp hl _, ?_⟩
  intro γ J hγ hJ hc s hs hx t ht htime
  have h := scalar_displacement Z P hP hb hγ hJ hc hs ht
  rw [hx] at h
  have hh := (le_abs_self (P (γ t) - P x)).trans (h.trans (mul_le_mul_of_nonneg_left htime hD))
  change P (γ t) ≤ P x + D * A
  linarith
end ExactLiouvilleComparison.ODE
