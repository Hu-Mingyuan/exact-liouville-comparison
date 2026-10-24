import ExactLiouvilleComparison.SmallCoefficientAsymptotic

noncomputable section
open Set Filter FsFltz.Geometry
open scoped Topology ContDiff
namespace ExactLiouvilleComparison.SmallCoefficient.Consumer

/-- A consumer with precisely the accepted growth witness, including its
within-set smoothness and divergent interval-integral hypothesis. -/
theorem construction (G : AdmissibleGrowth 1) (rstar : ℝ) (hs : 1 < rstar) :
    ContDiffOn ℝ ∞ (S G) (Ici 1) ∧
    (∀ r, 1 ≤ r → HasDerivWithinAt (S G) (r / (G.B r)^2) (Ici 1) r) ∧
    (∀ r, 1 ≤ r → 1 ≤ S G r ∧ S G r ≤ 1 + Real.log r) ∧
    ContDiffOn ℝ ∞ (k G rstar) (Ici 1) ∧
    (∀ r, 1 ≤ r → 0 < k G rstar r ∧ k G rstar r ≤ 1 ∧
      kprime G rstar r ≤ 0 ∧ 0 < m G rstar r) ∧
    (∀ r ∈ Icc 1 rstar, k G rstar r = 1 ∧ kprime G rstar r = 0) ∧
    (∃ b : ℝ, 0 < b ∧ ∀ r, rstar + 1 ≤ r →
      k G rstar r = b * Real.sqrt (S G r) / r ∧
      m G rstar r = b * r / (2 * (G.B r)^2 * Real.sqrt (S G r))) ∧
    Tendsto (fun r => r * k G rstar r) atTop atTop ∧
    Tendsto (fun r => Real.log (S G r)) atTop atTop := by
  exact ⟨S_smooth G, fun _ hr => S_hasDerivWithinAt G hr,
    fun _ hr => ⟨one_le_S G hr, S_le_one_add_log G hr⟩,
    k_smooth G rstar,
    fun r hr => ⟨k_pos G rstar r, k_le_one G rstar hr,
      kprime_nonpos G rstar hr, m_pos G rstar hr⟩,
    fun _ hr => ⟨k_eq_one G hr.1 hr.2, kprime_zero G hr.1 hr.2⟩,
    exists_tail_constant G hs, radius_mul_k_tendsto G hs, log_S_tendsto G⟩

/-- Extraction from the main theorem's actual growth hypothesis, retaining its
same B, bound constant and compact exception. No linear-growth replacement. -/
theorem from_growthAtInfinity {d : ℕ} {M : SmoothManifold d}
    (P : RadialReference M) (T : ExactSymplecticStructure M)
    (h : GrowthAtInfinity P.compatible T P.R 1) :
    ∃ G : AdmissibleGrowth 1, ∃ C : ℝ, 0 < C ∧
      ∃ K : Set M.Point, IsCompact K ∧
        (∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * G.B (P.R x)) ∧
        Tendsto (fun r => r * k G P.rstar r) atTop atTop ∧
        Tendsto (fun r => Real.log (S G r)) atTop atTop := by
  obtain ⟨G, C, hC, K, hK, hbound⟩ := h
  exact ⟨G, C, hC, K, hK, hbound,
    radius_mul_k_tendsto G P.one_lt_rstar, log_S_tendsto G⟩

end ExactLiouvilleComparison.SmallCoefficient.Consumer

#print axioms ExactLiouvilleComparison.SmallCoefficient.Consumer.construction
#print axioms ExactLiouvilleComparison.SmallCoefficient.Consumer.from_growthAtInfinity
#eval IO.println "SMALL_COEFFICIENT_CONSUMER_COMPLETE"
