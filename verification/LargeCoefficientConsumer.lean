import ExactLiouvilleComparison.LargeCoefficient

noncomputable section
open Set
open scoped ContDiff Manifold
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold
open ExactLiouvilleComparison
namespace ExactLiouvilleComparison.LargeCoefficientChecks

/-- A downstream caller supplies only the accepted reference and smooth form. -/
theorem arbitrary_primitive {d : ℕ} (M : SmoothManifold d) (P : RadialReference M)
    (lam : M.Form 1) (hlam : M.IsSmoothForm lam) :
    ∃ rho : ℝ → ℝ, ContDiff ℝ ∞ rho ∧ Monotone rho ∧
      (∀ r ∈ Icc 1 P.rstar, rho r = rho 1) ∧
      (∀ r, 0 ≤ deriv rho r) ∧ (∀ r, 1 ≤ rho r) ∧
      (∀ r, 1 ≤ r → 0 < rho r + r * deriv rho r) ∧
      (∀ x, 1 + P.compatible.dualNorm x (LargeCoefficient.oneCovector lam x) ≤ rho (P.R x)) := by
  obtain ⟨hs, hm, hc, hd, h1, hp, hdom⟩ := LargeCoefficient.coefficient_properties P lam hlam
  refine ⟨LargeCoefficient.A P lam, hs, hm, ?_, hd, h1, hp, hdom⟩
  intro r hr
  rw [hc r hr, LargeCoefficient.A_core P lam P.one_lt_rstar.le]

/-- Endpoint ordering uses the delivered small coefficient without changing it. -/
theorem interpolation_endpoints {d : ℕ} (M : SmoothManifold d) (P : RadialReference M)
    (T : ExactSymplecticStructure M) (G : AdmissibleGrowth 1) :
    ∀ r ∈ Ici (1 : ℝ), SmallCoefficient.k G P.rstar r ≤ LargeCoefficient.A P T.primitive r ∧
      0 < LargeCoefficient.A P T.primitive r + r * deriv (LargeCoefficient.A P T.primitive) r := by
  intro r hr
  exact ⟨LargeCoefficient.k_le_A P T.primitive T.smooth_primitive G hr,
    LargeCoefficient.A_radial_pos P T.primitive T.smooth_primitive hr⟩

/-- Empty manifolds are allowed; all sublevel suprema have the stipulated value. -/
theorem empty_manifold_levels {d : ℕ} (M : SmoothManifold d) [IsEmpty M.Point]
    (P : RadialReference M) (lam : M.Form 1) (n : ℕ) : LargeCoefficient.levels P lam n = 1 := by
  apply LargeCoefficient.levels_empty
  exact Set.eq_empty_of_isEmpty _

end ExactLiouvilleComparison.LargeCoefficientChecks

#print ExactLiouvilleComparison.LargeCoefficientChecks.arbitrary_primitive
#print ExactLiouvilleComparison.LargeCoefficientChecks.interpolation_endpoints
#print ExactLiouvilleComparison.LargeCoefficientChecks.empty_manifold_levels
#print axioms ExactLiouvilleComparison.LargeCoefficientChecks.arbitrary_primitive
#print axioms ExactLiouvilleComparison.LargeCoefficientChecks.interpolation_endpoints
#print axioms ExactLiouvilleComparison.LargeCoefficientChecks.empty_manifold_levels
#eval IO.println "LARGE_COEFFICIENT_CONSUMER_COMPLETE"
