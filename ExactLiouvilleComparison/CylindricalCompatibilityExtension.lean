import ExactLiouvilleComparison.CylindricalCompatibilityBasinSmooth
import ExactLiouvilleComparison.CylindricalCompatibilityMetricPairing
import ExactLiouvilleComparison.CylindricalCompatibilityRelativeMetric
import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationConsumers

/-! Relative extension of every prescribed smooth compatible contact end. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Bundle Set

namespace ExactLiouvilleComparison.CylindricalCompatibility
open RelativeMetric
attribute [local instance] tangentNormedAddCommGroup tangentNormedSpace

variable {d : ℕ} {D : LiouvilleDomain d} (C : Completion D) (P : ContactData D)

/-- Compatibility on the actual open end uses the actual exterior derivative. -/
theorem compatible_endJOn (x : C.ambient.manifold.Point) (hx : x ∈ C.escapingBasin) :
    Normalization.Compatible ((referenceBundleForm (completionReference C)).form x)
      (endJOn C P x) := by
  obtain ⟨⟨y,t⟩,rfl⟩ := hx
  rw [endJOn_endMap]
  simp only [Normalization.Compatible, referenceBundleForm_apply]
  exact ⟨endTangentJ_square C P y t, endTangentJ_invariant C P y t,
    endTangentJ_positive C P y t⟩

/-- The prescribed positive pairing extends as an auxiliary native smooth metric.
Its value is fixed on the entire nonnegative end, including the seam. -/
theorem exists_endMetric :
    ∃ h : RelativeMetric.NativeMetric C.ambient.manifold,
      ∀ x ∈ closedEnd C, h.inner x =
        metricPairing (C.ambient.manifold.exteriorDerivative C.ambient.primitive) (endJOn C P) x := by
  apply RelativeMetric.exists_relative_metric C.ambient.manifold (closedEnd C)
    C.escapingBasin (isClosed_closedEnd C) C.escapingBasin.isOpen (closedEnd_subset_basin C)
  · intro x hx
    exact (smoothAt_metricPairing _ C.ambient.symplectic.1 _ x
      ((smoothOn_endJOn C P x hx).contMDiffAt (C.escapingBasin.isOpen.mem_nhds hx))).contMDiffWithinAt
  · intro x hx
    have hc := compatible_endJOn C P x hx
    simp only [Normalization.Compatible, referenceBundleForm_apply] at hc
    refine ⟨metricPairing_symm _ _ x hc.1 hc.2.1, ?_⟩
    simpa only [metricPairing_apply, completionReference] using hc.2.2

/-- Construct global compatible J and its required metric, recovering every
prescribed end value. The auxiliary extended metric is only an input to normalization. -/
theorem extension (C : Completion D) (P : ContactData D) :
    ∃ A : CompatibleStructure (completionReference C), Extends C P A := by
  obtain ⟨h,heq⟩ := exists_endMetric C P
  obtain ⟨J,hJs,hJq,hJi,hJp,hJr⟩ := Normalization.tangent_normalization
    C.ambient.manifold (referenceBundleForm (completionReference C)) h
  simp only [referenceBundleForm_apply] at hJi hJp
  have hrec : ∀ x ∈ closedEnd C, J x = endJOn C P x := by
    intro x hx
    apply hJr x _ (compatible_endJOn C P x (closedEnd_subset_basin C hx))
    intro v w
    rw [heq x hx, metricPairing_apply, referenceBundleForm_apply]
    rfl
  let q := metricPairing (C.ambient.manifold.exteriorDerivative C.ambient.primitive) J
  have hqs : RelativeMetric.SmoothOn C.ambient.manifold q univ := by
    intro x _
    exact (smoothAt_metricPairing _ C.ambient.symplectic.1 J x (hJs x)).contMDiffWithinAt
  have hqp : ∀ x, SPD (q x) := by
    intro x
    refine ⟨metricPairing_symm _ J x (hJq x) (hJi x), ?_⟩
    simpa only [q, metricPairing_apply, completionReference] using hJp x
  let A : CompatibleStructure (completionReference C) := {
    J := J
    smooth_J := hJs
    square := hJq
    invariant := hJi
    g := RelativeMetric.ofSPD C.ambient.manifold q hqs hqp
    metric_eq := fun x v w => metricPairing_apply _ J x v w }
  refine ⟨A, ?_⟩
  intro y t ht v s
  change J (C.endMap (y,t)) _ = _
  rw [hrec _ ⟨(y,t),⟨mem_univ _,ht⟩,rfl⟩, endJOn_endMap]
  exact endTangentJ_formula C P y t (v,s)

/-- The original unrestricted prescribed-end extension obligation. -/
theorem extensionTarget : ExtensionTarget := fun _ _ C P => extension C P

end ExactLiouvilleComparison.CylindricalCompatibility
