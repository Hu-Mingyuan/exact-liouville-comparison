import ExactLiouvilleComparison.CylindricalCompatibilityRelativeMetricStatement
import Mathlib.Analysis.Normed.Module.FiniteDimension
import ExactLiouvilleComparison.CylindricalCompatibilityContactBundleMetric

/-! Construction of native smooth metrics relative to a closed set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
open Bundle Set Filter FsFltz.Geometry
open scoped Manifold ContDiff Topology

namespace ExactLiouvilleComparison.CylindricalCompatibility.RelativeMetric

/-- Strict positivity in finite dimension bounds the quadratic unit ball in
its original topology. The compact-sphere argument includes rank zero. -/
theorem spd_unitBall_bounded {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (q : E →L[ℝ] E →L[ℝ] ℝ) (hq : SPD q) :
    Bornology.IsVonNBounded ℝ {v : E | q v v < 1} := by
  have hc : Continuous (fun v : E => q v v) := q.continuous.clm_apply continuous_id
  obtain ⟨m, hm, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_forall_le'
    hc.continuousOn (a := 0) (by
      intro v hv
      apply hq.2 v
      intro h
      simp [h] at hv)
  rw [NormedSpace.isVonNBounded_iff, isBounded_iff_forall_norm_le]
  refine ⟨max 1 (1 / m), fun v hv => ?_⟩
  by_cases hv0 : v = 0
  · simp only [hv0, norm_zero]
    exact le_trans (by norm_num) (le_max_left _ _)
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hs : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : E) 1 := by
    simp [norm_smul, hn.ne']
  have hscale : q (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) = q v v / ‖v‖ ^ 2 := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hmv : m * ‖v‖ ^ 2 ≤ q v v := by
    have h := hmin _ hs
    rw [hscale] at h
    exact (le_div_iff₀ (sq_pos_of_pos hn)).mp h
  by_cases hn1 : ‖v‖ ≤ 1
  · exact hn1.trans (le_max_left _ _)
  · apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ hm).mpr
    have hprod := mul_nonneg hm.le (mul_nonneg hn.le (sub_nonneg.mpr (le_of_not_ge hn1)))
    change q v v < 1 at hv
    nlinarith

variable {d : ℕ} (M : SmoothManifold d)

-- Temporary model norms on native fibers, used only for continuous-map instances.
-- Their topology is definitionally the original tangent topology.
local instance tangentNormedAddCommGroup : ∀ x : M.Point, NormedAddCommGroup (M.Tangent x) :=
  fun _ => inferInstanceAs (NormedAddCommGroup (Model d))
local instance tangentNormedSpace : ∀ x : M.Point, NormedSpace ℝ (M.Tangent x) :=
  fun _ => inferInstanceAs (NormedSpace ℝ (Model d))

/-- Convert a native global SPD section to the native smooth metric record.
The original tangent topology is retained; no metric is supplied as input. -/
def ofSPD (q : BilinField M) (hq : SmoothOn M q univ) (hpos : ∀ x, SPD (q x)) :
    NativeMetric M where
  inner := q
  symm x := (hpos x).1
  pos x := (hpos x).2
  isVonNBounded x := by
    exact spd_unitBall_bounded (q x) (hpos x)
  contMDiff := contMDiffOn_univ.mp hq

@[simp] theorem ofSPD_inner (q : BilinField M) (hq : SmoothOn M q univ)
    (hpos : ∀ x, SPD (q x)) (x : M.Point) :
    (ofSPD M q hq hpos).inner x = q x := rfl

/-- Reuse the exact published generic native local-metric construction. -/
abbrev chartMetric (a : M.Point) : BilinField M :=
  ContactBundle.Metric.localMetric (k := d) M M.Tangent a

/-- The published positive metric gives precisely the parent's SPD predicate. -/
theorem chartMetric_spd (a x : M.Point)
    (hx : x ∈ (trivializationAt (Model d) M.Tangent a).baseSet) :
    SPD (chartMetric M a x) := by
  have h := ContactBundle.Metric.localMetric_positive (k := d) M M.Tangent a x hx
  exact ⟨h.1, h.2.1⟩

/-- Native nested Hom smoothness from the published generic bundle proof. -/
theorem chartMetric_smooth (a : M.Point) :
    SmoothOn M (chartMetric M a) (trivializationAt (Model d) M.Tangent a).baseSet :=
  ContactBundle.Metric.localMetric_smooth (k := d) M M.Tangent a

/-- Native relative metric extension without a background metric or supplied local sections. -/
theorem exists_relative_metric (K U : Set M.Point) (hK : IsClosed K)
    (hU : IsOpen U) (hKU : K ⊆ U) (q : BilinField M)
    (hq : SmoothOn M q U) (hpos : ∀ x ∈ U, SPD (q x)) :
    ∃ g : NativeMetric M, ∀ x ∈ K, g.inner x = q x := by
  have : LocallyCompactSpace M.Point := ChartedSpace.locallyCompactSpace (Model d) M.Point
  obtain ⟨s, hs, heq⟩ := RelativeSection.exists_relative_section
    (F := Model d →L[ℝ] Model d →L[ℝ] ℝ)
    (𝓘(ℝ, Model d)) (fun x => M.Tangent x →L[ℝ] M.Tangent x →L[ℝ] ℝ)
    (fun _ => {g | SPD g}) (fun _ => convex_SPD)
    K U hK hU hKU q hq hpos (by
      intro x _
      exact ⟨(trivializationAt (Model d) M.Tangent x).baseSet,
        (trivializationAt (Model d) M.Tangent x).open_baseSet.mem_nhds
          (FiberBundle.mem_baseSet_trivializationAt (Model d) M.Tangent x),
        chartMetric M x, chartMetric_smooth M x, fun y hy => chartMetric_spd M x y hy⟩)
  exact ⟨ofSPD M s s.contMDiff.contMDiffOn hs, heq⟩

/-- Proof of the pre-proof independently reviewed relative contract. -/
theorem relativeMetric : RelativeMetricTarget := fun _ M => exists_relative_metric M

/-- Proof of the pre-proof independently reviewed global conversion contract. -/
theorem spdMetric : SPDMetricTarget := fun _ M q hq hpos =>
  ⟨ofSPD M q hq hpos, fun _ => rfl⟩

end ExactLiouvilleComparison.CylindricalCompatibility.RelativeMetric
