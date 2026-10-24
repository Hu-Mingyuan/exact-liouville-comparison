import ExactLiouvilleComparison.ODETwoBarrierConfinement
import ExactLiouvilleComparison.ODEContinuationCutoff

/-! Actual finite-interval trajectories constructed using two different one-sided barriers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.ODE
variable {d : ℕ} {M : SmoothManifold d}

/-- From the unchanged two-barrier hypotheses, construct a native solution through
every initial time and point on the entire closed interval. Full derivatives at
both endpoints come from the constructed compactly supported auxiliary field.
This theorem is the existence component, not yet the full smooth evolution. -/
theorem twoBarrier_finiteIntervalExistence
    (Z : ℝ → (x : M.Point) → M.Tangent x)
    (Ω : Set (ℝ × M.Point)) (hΩ : IsOpen Ω) (hstrip : parameterInterval ×ˢ univ ⊆ Ω)
    (hZ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ :
        TangentBundle 𝓘(ℝ, Model d) M.Point)) Ω)
    (R : M.Point → ℝ) (hR : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ R)
    (hp : IsProperMap R) (hl : BddBelow (range R))
    (Q : ℝ → M.Point → ℝ)
    (hQ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M.Point => Q p.1 p.2))
    (hcontrol : ∀ L : ℝ, ∃ A : ℝ, ∀ t ∈ parameterInterval, ∀ x, Q t x ≤ L → R x ≤ A)
    (C₀ C₁ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hforward : ∀ t ∈ parameterInterval, ∀ x, M.scalarDerivative R x (Z t x) ≤ C₀)
    (hpartial : ∀ t ∈ parameterInterval, ∀ x, 0 ≤ deriv (fun u => Q u x) t)
    (hreverse : ∀ t ∈ parameterInterval, ∀ x,
      -C₁ ≤ deriv (fun u => Q u x) t + M.scalarDerivative (Q t) x (Z t x))
    (s : Parameter) (x : M.Point) :
    ∃ γ : ℝ → M.Point, γ s.val = x ∧
      ∀ t ∈ parameterInterval, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t))) := by
  obtain ⟨K, hK, hconf⟩ := twoBarrier_compact_confinement R hR hp hl Q hQ hcontrol hC₀ hC₁ s x
  let : LocallyCompactSpace (ModelProd ℝ (Model d)) :=
    inferInstanceAs (LocallyCompactSpace (ℝ × Model d))
  obtain ⟨χ, V, hχ, hrange, hKV, hone, hsupport, hsuppΩ⟩ :=
    exists_bounded_smooth_compact_cutoff (I := (𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((show IsCompact parameterInterval from isCompact_Icc).prod hK) hΩ
      (fun p hp => hstrip ⟨hp.1, mem_univ _⟩)
  let W : ℝ → (y : M.Point) → M.Tangent y := fun t y => χ (t, y) • Z t y
  have hW := contMDiff_cutoff_field Z hΩ hZ χ hχ hsuppΩ
  obtain ⟨γ, hinit, hγ⟩ := CollarFlow.exists_global_solution (F := Model d) (Z := W) hW hsupport
    (fun p hp => by simp only [W, image_eq_zero_of_notMem_tsupport hp, zero_smul]) s.val x
  have hRbound : ∀ t ∈ parameterInterval, ∀ y, M.scalarDerivative R y (W t y) ≤ C₀ := by
    intro t ht y
    exact twoBarrier_forward_cutoff R y (Z t y) (hrange (t, y)) hC₀ (hforward t ht y)
  have hQbound : ∀ t ∈ parameterInterval, ∀ y,
      -C₁ ≤ deriv (fun u => Q u y) t + M.scalarDerivative (Q t) y (W t y) := by
    intro t ht y
    exact twoBarrier_reverse_cutoff Q t y (Z t y) (hrange (t, y)) hC₁
      (hpartial t ht y) (hreverse t ht y)
  have hstay := hconf W hRbound hQbound γ hinit (fun t _ => hγ t)
  refine ⟨γ, hinit, ?_⟩
  intro t ht
  have hχone := hone (t, γ t) (hKV ⟨ht, hstay t ht⟩)
  simpa only [W, hχone, one_smul] using hγ t

end ExactLiouvilleComparison.ODE
