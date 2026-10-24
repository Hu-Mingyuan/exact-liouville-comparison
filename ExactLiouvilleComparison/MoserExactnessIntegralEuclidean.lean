import ExactLiouvilleComparison.MoserExactnessIntegralEuclideanStatement
import ExactLiouvilleComparison.MoserExactnessIntegralRegularity

noncomputable section
open scoped ContDiff Topology Interval
open Set MeasureTheory Filter Metric
namespace ExactLiouvilleComparison.MoserExactnessIntegralEuclidean

universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] [CompleteSpace F] in
/-- Restriction to compact time gives Bochner integrability, also for operator-valued F. -/
theorem intervalIntegrable_slice {g : ℝ × E → F} {U : Set (ℝ × E)}
    (hg : ContinuousOn g U) {x : E} (hx : ∀ t ∈ Icc (0 : ℝ) 1, (t, x) ∈ U) :
    IntervalIntegrable (fun t => g (t, x)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  simpa [Function.comp_def] using hg.comp (continuous_id.prodMk continuous_const).continuousOn hx

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- The actual spatial derivative is integrable in the operator norm. -/
theorem intervalIntegrable_fderiv {g : ℝ × E → F} {U : Set (ℝ × E)}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) {x : E}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, (t, x) ∈ U) :
    IntervalIntegrable (fun t => fderiv ℝ (fun y => g (t, y)) x) volume 0 1 :=
  intervalIntegrable_slice (MoserExactnessIntegral.spatial_fderiv_smooth hU hg).continuousOn hx

/-- Compact time and a local compact spatial ball yield all domination hypotheses. -/
theorem hasFDerivAt_integral {g : ℝ × E → F} {U : Set (ℝ × E)}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) {x : E}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, (t, x) ∈ U) :
    HasFDerivAt (fun y => ∫ t in (0 : ℝ)..1, g (t, y))
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun y => g (t, y)) x) x := by
  obtain ⟨a, v, ha, hv, hIa, hxv, hav⟩ := generalized_tube_lemma
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)) (isCompact_singleton (x := x)) hU
    (by rintro ⟨t, y⟩ ⟨ht, hy⟩; obtain rfl := mem_singleton_iff.mp hy; exact hx t ht)
  obtain ⟨r, hr, hrv⟩ := nhds_basis_closedBall.mem_iff.mp
    (hv.mem_nhds (hxv (mem_singleton x)))
  have hK : Icc (0 : ℝ) 1 ×ˢ closedBall x r ⊆ U :=
    fun p hp => hav ⟨hIa hp.1, hrv hp.2⟩
  have hD := (MoserExactnessIntegral.spatial_fderiv_smooth hU hg).continuousOn
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall x r)).exists_bound_of_continuousOn
    (hD.mono hK)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F' := fun y t => fderiv ℝ (fun z => g (t, z)) y)
    (bound := fun _ => C) (closedBall_mem_nhds x hr)
  · filter_upwards [closedBall_mem_nhds x hr] with y hy
    exact (intervalIntegrable_slice hg.continuousOn (fun t ht => hK ⟨ht, hy⟩)).aestronglyMeasurable_restrict_uIoc
  · exact intervalIntegrable_slice hg.continuousOn hx
  · exact (intervalIntegrable_fderiv hU hg hx).aestronglyMeasurable_restrict_uIoc
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    intro y hy
    exact hC (t, y) ⟨by simpa using (uIoc_subset_uIcc ht), hy⟩
  · exact intervalIntegrable_const
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    intro y hy
    have hty : (t, y) ∈ U := hK ⟨by simpa using (uIoc_subset_uIcc ht), hy⟩
    exact ((hg.contDiffAt (hU.mem_nhds hty)).comp y
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp) |>.hasFDerivAt

/-- Finite-order induction, generalized over the complete codomain for CLM-valued steps. -/
theorem contDiffOn_integral_nat (n : ℕ) {g : ℝ × E → F} {s : Set E} {U : Set (ℝ × E)}
    (hs : IsOpen s) (hU : IsOpen U) (hsub : Icc (0 : ℝ) 1 ×ˢ s ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ n (fun x => ∫ t in (0 : ℝ)..1, g (t, x)) s := by
  induction n generalizing F with
  | zero =>
    apply contDiffOn_zero.mpr
    intro x hx
    exact (hasFDerivAt_integral hU hg (fun t ht => hsub ⟨ht, hx⟩)).continuousAt.continuousWithinAt
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen hs]
    refine ⟨?_, by simp, ?_⟩
    · intro x hx
      exact (hasFDerivAt_integral hU hg (fun t ht => hsub ⟨ht, hx⟩)).differentiableAt.differentiableWithinAt
    · exact (ih (MoserExactnessIntegral.spatial_fderiv_smooth hU hg)).congr
        (fun x hx => (hasFDerivAt_integral hU hg (fun t ht => hsub ⟨ht, hx⟩)).fderiv)

/-- Smoothness of the spatial integral on an arbitrary open spatial domain. -/
theorem contDiffOn_integral {g : ℝ × E → F} {s : Set E} {U : Set (ℝ × E)}
    (hs : IsOpen s) (hU : IsOpen U) (hsub : Icc (0 : ℝ) 1 ×ˢ s ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, g (t, x)) s :=
  contDiffOn_infty.mpr (fun n => contDiffOn_integral_nat n hs hU hsub hg)

/-- The reviewed bounded contract is proved, without integral-regularity premises. -/
theorem target : Target := by
  intro E F _ _ _ _ _ _ g s U hs hU hsub hg
  refine ⟨contDiffOn_integral hs hU hsub hg, ?_⟩
  intro x hx
  exact ⟨intervalIntegrable_fderiv hU hg (fun t ht => hsub ⟨ht, hx⟩),
    hasFDerivAt_integral hU hg (fun t ht => hsub ⟨ht, hx⟩)⟩

end ExactLiouvilleComparison.MoserExactnessIntegralEuclidean
