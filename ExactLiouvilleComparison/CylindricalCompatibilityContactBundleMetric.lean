import ExactLiouvilleComparison.CylindricalCompatibilityContactBundleStatement
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.VectorBundle.FiniteDimensional

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
open Bundle Set Filter Bornology
open scoped Manifold ContDiff Topology
open FsFltz.Geometry

namespace ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle.Metric

section Fiber
variable {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

/-- The fiber conditions of a native Riemannian metric, including compatibility
with the existing topology. No norm on the fiber is presumed. -/
def PositiveMetric (g : V →L[ℝ] V →L[ℝ] ℝ) : Prop :=
  (∀ v w, g v w = g w v) ∧ (∀ v, v ≠ 0 → 0 < g v v) ∧
    IsVonNBounded ℝ {v | g v v < 1}

theorem nonneg {g : V →L[ℝ] V →L[ℝ] ℝ} (hg : PositiveMetric g) (v : V) :
    0 ≤ g v v := by
  by_cases hv : v = 0
  · subst v; simp
  · exact (hg.2.1 v hv).le

theorem bounded_of_lower {g h : V →L[ℝ] V →L[ℝ] ℝ}
    (hg : PositiveMetric g) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ v, a * g v v ≤ h v v) : IsVonNBounded ℝ {v | h v v < 1} := by
  let s := Real.sqrt a
  have hs : 0 < s := Real.sqrt_pos.2 ha
  have hs2 : s ^ 2 = a := Real.sq_sqrt ha.le
  let L : V →L[ℝ] V := s⁻¹ • ContinuousLinearMap.id ℝ V
  apply IsVonNBounded.subset (s₂ := L '' {v | g v v < 1}) _ (hg.2.2.image L)
  intro v hv
  refine ⟨s • v, ?_, ?_⟩
  · change g (s • v) (s • v) < 1
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [show s * (s * g v v) = a * g v v by rw [← hs2]; ring]
    exact lt_of_le_of_lt (hlower v) hv
  · change s⁻¹ • (s • v) = v
    rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

theorem convex_positiveMetric : Convex ℝ {g : V →L[ℝ] V →L[ℝ] ℝ | PositiveMetric g} := by
  intro g hg h hh a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · intro v w
    change a * g v w + b * h v w = a * g w v + b * h w v
    rw [hg.1 v w, hh.1 v w]
  · intro v hv
    change 0 < a * g v v + b * h v v
    rcases lt_or_eq_of_le ha with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hg.2.1 v hv))
        (mul_nonneg hb (nonneg hh v))
    · have hb' : b = 1 := by linarith
      simp [← ha', hb', hh.2.1 v hv]
  · rcases lt_or_eq_of_le ha with ha' | ha'
    · apply bounded_of_lower hg ha'
      intro v
      change a * g v v ≤ a * g v v + b * h v v
      exact le_add_of_nonneg_right (mul_nonneg hb (nonneg hh v))
    · have hb' : b = 1 := by linarith
      simpa [← ha', hb'] using hh.2.2

end Fiber

section Bundle
variable {n k : ℕ} (M : SmoothManifold n) (E : M.Point → Type*)
  [∀ y, TopologicalSpace (E y)] [∀ y, AddCommGroup (E y)] [∀ y, Module ℝ (E y)]
  [∀ y, IsTopologicalAddGroup (E y)] [∀ y, ContinuousSMul ℝ (E y)]
  [TopologicalSpace (TotalSpace (Model k) E)] [FiberBundle (Model k) E]
  [VectorBundle ℝ (Model k) E] [ContMDiffVectorBundle ∞ (Model k) E 𝓘(ℝ, Model n)]

/-- Pull the model's Euclidean inner product back by a native local
trivialization. This is only a local auxiliary metric. -/
def localMetric (x y : M.Point) : E y →L[ℝ] E y →L[ℝ] ℝ :=
  let e := (trivializationAt (Model k) E x).continuousLinearMapAt ℝ y
  (e.precomp ℝ).comp ((innerSL ℝ).comp e)

theorem localMetric_apply (x y : M.Point) (v w : E y) :
    localMetric (k := k) M E x y v w = inner ℝ
      ((trivializationAt (Model k) E x).continuousLinearMapAt ℝ y v)
      ((trivializationAt (Model k) E x).continuousLinearMapAt ℝ y w) := rfl

theorem localMetric_positive (x y : M.Point)
    (hy : y ∈ (trivializationAt (Model k) E x).baseSet) :
    PositiveMetric (localMetric (k := k) M E x y) := by
  let e := trivializationAt (Model k) E x
  let L := e.continuousLinearEquivAt ℝ y hy
  have he (v w : E y) : localMetric (k := k) M E x y v w = inner ℝ (L v) (L w) := by
    rw [localMetric_apply (k := k)]
    simp [L, e, Trivialization.continuousLinearEquivAt_apply,
      Trivialization.coe_linearMapAt_of_mem _ hy]
  refine ⟨?_, ?_, ?_⟩
  · intro v w; rw [he, he]; exact real_inner_comm _ _
  · intro v hv
    rw [he]
    exact real_inner_self_pos.mpr (fun hz ↦ hv (L.injective (by simpa using hz)))
  · apply IsVonNBounded.subset
      (s₂ := L.symm.toContinuousLinearMap '' Metric.ball (0 : Model k) 1) _
      ((NormedSpace.isVonNBounded_ball ℝ (Model k) 1).image L.symm.toContinuousLinearMap)
    intro v hv
    refine ⟨L v, ?_, L.symm_apply_apply v⟩
    rw [Metric.mem_ball, dist_zero_right]
    change localMetric (k := k) M E x y v v < 1 at hv
    rw [he, real_inner_self_eq_norm_sq] at hv
    nlinarith [norm_nonneg (L v)]

theorem localMetric_smooth (x : M.Point) :
    ContMDiffOn 𝓘(ℝ, Model n)
      ((𝓘(ℝ, Model n)).prod 𝓘(ℝ, Model k →L[ℝ] Model k →L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (Model k →L[ℝ] Model k →L[ℝ] ℝ) y
        (localMetric (k := k) M E x y)) (trivializationAt (Model k) E x).baseSet := by
  let e := trivializationAt (Model k) E x
  let b := trivializationAt (Model k →L[ℝ] Model k →L[ℝ] ℝ)
    (fun y ↦ E y →L[ℝ] E y →L[ℝ] ℝ) x
  rw [b.contMDiffOn_section_iff e.open_baseSet (by
    intro y hy
    simpa [b, hom_trivializationAt_baseSet] using hy)]
  let c : Model k →L[ℝ] Model k →L[ℝ] ℝ := innerSL ℝ
  apply (contMDiffOn_const (c := c)).congr
  intro y hy
  ext v w
  rw [hom_trivializationAt_apply, inCoordinates_apply_eq₂ hy hy (by simp)]
  simp only [Trivialization.linearMapAt_apply]
  simp only [show (trivializationAt ℝ (fun _ : M.Point ↦ ℝ) x).baseSet = univ from rfl,
    Set.mem_univ, ↓reduceIte]
  change localMetric (k := k) M E x y (e.symm y v) (e.symm y w) = inner ℝ v w
  rw [localMetric_apply]
  rw [← e.symmL_apply (R := ℝ) hy v, ← e.symmL_apply (R := ℝ) hy w]
  rw [e.continuousLinearMapAt_symmL (R := ℝ) hy, e.continuousLinearMapAt_symmL (R := ℝ) hy]

/-- Native smooth positive definite metrics exist on the constructed finite
rank bundle. Mathlib glues local metric sections in a convex set; neither a
global frame nor a compatible J is used. -/
theorem exists_metric :
    Nonempty (ContMDiffRiemannianMetric 𝓘(ℝ, Model n) ∞ (Model k) E) := by
  letI : LocallyCompactSpace M.Point := ChartedSpace.locallyCompactSpace (Model n) M.Point
  obtain ⟨g, hg⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    (𝓘(ℝ, Model n)) (fun y ↦ E y →L[ℝ] E y →L[ℝ] ℝ)
    (fun _ ↦ {g | PositiveMetric g}) (fun _ ↦ convex_positiveMetric)
    (fun x ↦ ⟨(trivializationAt (Model k) E x).baseSet,
      (trivializationAt (Model k) E x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt (Model k) E x),
      localMetric (k := k) M E x, localMetric_smooth (k := k) M E x,
      fun y hy ↦ localMetric_positive (k := k) M E x y hy⟩)
  exact ⟨{
    inner := g
    symm := fun y ↦ (hg y).1
    pos := fun y ↦ (hg y).2.1
    isVonNBounded := fun y ↦ (hg y).2.2
    contMDiff := g.contMDiff }⟩

/-- The norm installed for normalization is the norm of the supplied auxiliary
metric on the same fiber, not a chart norm. -/
theorem metric_norm_eq
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, Model n) ∞ (Model k) E) :
    letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
    ∀ y (v : E y), ‖v‖ = Real.sqrt (g.inner y v v) := by
  intro y v
  rfl

theorem metric_smooth_norm_inputs
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, Model n) ∞ (Model k) E) :
    letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
    IsContMDiffRiemannianBundle 𝓘(ℝ, Model n) ∞ (Model k) E := by
  letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
  infer_instance

end Bundle
end ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle.Metric

namespace ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle

/-- The metric part of the boundary bundle result follows from its atlas.
Atlas existence itself is a separate, still required construction. -/
theorem metric_of_atlas {d : ℕ} (D : LiouvilleDomain d) (P : Prebundle D)
    (hP : AtlasProperties D P) :
    letI : TopologicalSpace (TotalSpace (Model (d - 2)) (Fiber D)) := P.totalSpaceTopology
    letI : FiberBundle (Model (d - 2)) (Fiber D) := P.toFiberBundle
    letI : VectorBundle ℝ (Model (d - 2)) (Fiber D) := P.toVectorBundle
    Nonempty (ContMDiffRiemannianMetric 𝓘(ℝ, Model (d - 1)) ∞ (Model (d - 2)) (Fiber D)) := by
  letI : TopologicalSpace (TotalSpace (Model (d - 2)) (Fiber D)) := P.totalSpaceTopology
  letI : FiberBundle (Model (d - 2)) (Fiber D) := P.toFiberBundle
  letI : VectorBundle ℝ (Model (d - 2)) (Fiber D) := P.toVectorBundle
  letI : ContMDiffVectorBundle ∞ (Model (d - 2)) (Fiber D) 𝓘(ℝ, Model (d - 1)) := hP.1
  exact Metric.exists_metric D.domain.boundary (Fiber D)

end ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle
