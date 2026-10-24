import ExactLiouvilleComparison.ODEContinuationStatement
import ExactLiouvilleComparison.ODEContinuationCutoff
import ExactLiouvilleComparison.ODEScalarConfinement

/-! Native finite-interval existence from proper scalar control. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.ODE
variable {d : ℕ} {M : SmoothManifold d}

/-- A bounded cutoff preserves the actual scalar derivative bound on the strip. -/
theorem scalar_bound_cutoff
    (Z : ℝ → (x : M.Point) → M.Tangent x) (P : M.Point → ℝ)
    (χ : ℝ × M.Point → ℝ) (hχ : ∀ p, χ p ∈ Icc (0 : ℝ) 1)
    {D : ℝ} (hb : ∀ t ∈ parameterInterval, ∀ x,
      |M.scalarDerivative P x (Z t x)| ≤ D) :
    ∀ t ∈ parameterInterval, ∀ x,
      |M.scalarDerivative P x (χ (t, x) • Z t x)| ≤ D := by
  intro t ht x
  simp only [scalarDerivative, map_smul, smul_eq_mul, abs_mul]
  rw [abs_of_nonneg (hχ (t, x)).1]
  exact (mul_le_of_le_one_left (abs_nonneg _) (hχ (t, x)).2).trans (hb t ht x)

/-- Actual native curves through every initial parameter, with full derivatives
at both endpoints. Only the auxiliary cutoff field is extended to an all-real
complete system; the original field and scalar bound are used on the given strip. -/
theorem finiteIntervalExistence : FiniteIntervalExistenceTarget (M := M) := by
  intro Z Ω hΩ hstrip hZ P hP hp hl D hD hb s x
  let K : Set M.Point := {y | P y ≤ P x + D}
  have hK : IsCompact K := compact_sublevel P hp hl _
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
  have hsol : FirstPathFlow.IsSolution (fun t => W t.val) γ parameterInterval := by
    refine ⟨?_, fun t _ _ => (hγ t).hasMFDerivWithinAt⟩
    exact (continuous_iff_continuousAt.mpr (fun t => (hγ t).continuousAt)).continuousOn
  have hbound : ∀ t : Parameter, ∀ y, |M.scalarDerivative P y (W t.val y)| ≤ D :=
    fun t => scalar_bound_cutoff Z P χ hrange hb t.val t.property
  have hconf : ∀ t ∈ parameterInterval, γ t ∈ K := by
    intro t ht
    have hdisp := scalar_displacement (fun u => W u.val) P hP hbound hsol
      (Subset.refl _) (convex_Icc _ _) s.property ht
    rw [hinit] at hdisp
    have htime : |t - s.val| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith [ht.1, ht.2, s.property.1, s.property.2]
    have hle := (le_abs_self (P (γ t) - P x)).trans
      (hdisp.trans (mul_le_mul_of_nonneg_left htime hD))
    change P (γ t) ≤ P x + D
    linarith
  refine ⟨γ, hinit, ?_⟩
  intro t ht
  have hχone := hone (t, γ t) (hKV ⟨ht, hconf t ht⟩)
  simpa only [W, hχone, one_smul] using hγ t

end ExactLiouvilleComparison.ODE
