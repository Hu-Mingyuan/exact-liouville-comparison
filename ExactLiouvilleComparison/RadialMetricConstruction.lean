import ExactLiouvilleComparison.RadialMetricBundle
import ExactLiouvilleComparison.RadialMetricDual
import FsFltz.Geometry.BoundaryContactDistribution

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology InnerProductSpace
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison
namespace RadialCoefficient
variable {d : ℕ} {M : SmoothManifold d} {P : RadialReference M}
variable (q : RadialCoefficient P.rstar)

def metricBilin (x : M.Point) : M.Tangent x →L[ℝ] M.Tangent x →L[ℝ] ℝ :=
  let l : M.Tangent x →L[ℝ] ℝ := mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x
  let j : M.Tangent x →L[ℝ] ℝ := l.comp (P.compatible.J x)
  q.rho (P.R x) • P.compatible.g.inner x +
    (P.c * q.rhoPrime (P.R x)) • (l.smulRight l + j.smulRight j)

theorem metricBilin_apply (x : M.Point) (v w : M.Tangent x) :
    q.metricBilin x v w = q.metricValue x v w := by
  rw [q.metricValue_eq]
  rfl

theorem smooth_metricBilin :
    ContMDiff (𝓘(ℝ, Model d))
      ((𝓘(ℝ, Model d)).prod (𝓘(ℝ, Model d →L[ℝ] Model d →L[ℝ] ℝ))) ∞
      (fun x => Bundle.TotalSpace.mk' (Model d →L[ℝ] Model d →L[ℝ] ℝ) x (q.metricBilin x)) := by
  have hl := RadialMetricBundle.smooth_differential M P.R P.smooth_R
  have hj := RadialMetricBundle.smooth_comp M _ hl _ P.compatible.smooth_J
  have hs : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞
      (fun x => P.c * q.rhoPrime (P.R x)) :=
    (show ContDiff ℝ ∞ (fun r : ℝ => P.c * r) from
      contDiff_const.mul contDiff_id).comp_contMDiff q.smooth_prime_comp
  exact (q.smooth_comp.smul_section P.compatible.g.contMDiff).add_section
    (hs.smul_section
      ((RadialMetricBundle.smooth_tensor M _ hl).add_section
        (RadialMetricBundle.smooth_tensor M _ hj)))

/-- A positive reference-metric lower bound valid at every point. -/
theorem metricValue_uniform_lower (x : M.Point) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v, δ * P.compatible.g.inner x v v ≤ q.metricValue x v v := by
  by_cases hd : 0 ≤ q.rhoPrime (P.R x)
  · exact ⟨q.rho (P.R x), q.positive (P.R x) (P.lower_R x), q.metricValue_ge_of_nonneg x hd⟩
  · exact ⟨q.rho (P.R x) + P.R x * q.rhoPrime (P.R x),
      q.radial_positive (P.R x) (P.lower_R x), q.metricValue_lower_of_nonpos x (le_of_not_ge hd)⟩

/-- Boundedness in the original tangent topology follows from the reference metric. -/
theorem metricBilin_bounded (x : M.Point) :
    Bornology.IsVonNBounded ℝ {v : M.Tangent x | q.metricBilin x v v < 1} := by
  obtain ⟨δ, hδ, hbound⟩ := q.metricValue_uniform_lower x
  let s := Real.sqrt δ
  have hs : 0 < s := Real.sqrt_pos.2 hδ
  have hs2 : s ^ 2 = δ := Real.sq_sqrt hδ.le
  let L : M.Tangent x →L[ℝ] M.Tangent x := s⁻¹ • ContinuousLinearMap.id ℝ _
  apply Bornology.IsVonNBounded.subset (s₂ := L '' {v | P.compatible.g.inner x v v < 1})
    _ ((P.compatible.g.isVonNBounded x).image L)
  intro v hv
  refine ⟨s • v, ?_, ?_⟩
  · change P.compatible.g.inner x (s • v) (s • v) < 1
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [show s * (s * P.compatible.g.inner x v v) = δ * P.compatible.g.inner x v v by
      rw [← hs2]; ring]
    exact lt_of_le_of_lt (hbound v) (by change q.metricBilin x v v < 1 at hv; rwa [q.metricBilin_apply] at hv)
  · change s⁻¹ • (s • v) = v
    rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

/-- Native smooth Riemannian metric constructed from the radial hypotheses. -/
def metric : Bundle.ContMDiffRiemannianMetric (𝓘(ℝ, Model d)) ∞ (Model d) M.Tangent where
  inner := q.metricBilin
  symm := by intros; simpa only [metricBilin_apply] using q.metricValue_symm _ _ _
  pos := by intros; simpa only [metricBilin_apply] using q.metricValue_pos _ _ ‹_›
  isVonNBounded := q.metricBilin_bounded
  contMDiff := q.smooth_metricBilin

theorem invariant (x : M.Point) (v w : M.Tangent x) :
    evalTwo (M.exteriorDerivative q.primitive) x (P.compatible.J x v) (P.compatible.J x w) =
      evalTwo (M.exteriorDerivative q.primitive) x v w := by
  have h := q.metricValue_symm x (P.compatible.J x v) w
  unfold metricValue at h
  rw [P.compatible.square] at h
  have hn := evalTwo_smul_right (M.exteriorDerivative q.primitive) x (-1) w v
  simp only [neg_one_smul, neg_one_mul] at hn
  rw [hn, evalTwo_swap (M.exteriorDerivative q.primitive) x w v, neg_neg] at h
  exact h

/-- The same J, with compatibility and smooth metric obligations proved. -/
def compatible : CompatibleStructure q.exactStructure where
  J := P.compatible.J
  smooth_J := P.compatible.smooth_J
  square := P.compatible.square
  invariant := q.invariant
  g := q.metric
  metric_eq := q.metricBilin_apply

end RadialCoefficient
end ExactLiouvilleComparison
