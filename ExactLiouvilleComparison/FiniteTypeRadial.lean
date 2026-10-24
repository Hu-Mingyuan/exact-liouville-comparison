import ExactLiouvilleComparison.FiniteTypeRadialGrowth
import ExactLiouvilleComparison.FiniteTypeRadialMetric

/-! Construction from the original completion and cylindrical structure. -/
noncomputable section
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set

namespace ExactLiouvilleComparison.FiniteTypeRadial
variable {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
  (A : CompatibleStructure (completionReference C)) (cyl : CylindricalStructure C A)

/-- The compact-core bound locates every point requiring a radial identity. -/
theorem exists_end_of_two_lt (x : C.ambient.manifold.Point) (hx : 2 < radius C x) :
    ∃ y t, Real.log 2 < t ∧ C.endMap (y,t) = x := by
  have hm : x ∈ farEnd C (Real.log 2) := by
    by_contra hn
    exact (not_le_of_gt hx) (radius_core_bound C x hn)
  obtain ⟨⟨y,t⟩, ht, he⟩ := hm
  exact ⟨y,t,ht.2,he⟩

include cyl in
/-- Literal primitive identity at the constructed exhaustion. -/
theorem radius_primitive (x : C.ambient.manifold.Point) (hx : 2 < radius C x)
    (v : C.ambient.manifold.Tangent x) :
    evalOne C.ambient.primitive x v =
      -C.ambient.manifold.scalarDerivative (radius C) x (A.J x v) := by
  obtain ⟨y,t,ht,rfl⟩ := exists_end_of_two_lt C x hx
  exact FiniteTypeRadialMetric.primitive_identity C A cyl (radius C)
    (radius_smooth C) (radius_end_eq C) y t ht v

include cyl in
/-- Exact original g-dual square, stronger than the radial bound. -/
theorem radius_dual_sq (x : C.ambient.manifold.Point) (hx : 2 < radius C x) :
    (A.dualNorm x (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) (radius C) x)) ^ 2 = radius C x := by
  obtain ⟨y,t,ht,rfl⟩ := exists_end_of_two_lt C x hx
  exact FiniteTypeRadialMetric.radius_dualNorm_sq C A cyl (radius C)
    (radius_smooth C) (radius_end_eq C) y t ht

/-- All output fields are constructed; no radial data is an input. -/
def constructedRadius : Radius C A where
  R := radius C
  smooth := radius_smooth C
  proper := radius_proper C
  lower := radius_lower C
  end_eq := radius_end_eq C
  core_bound := radius_core_bound C
  compact_core := compact_farEnd_compl C (Real.log 2)
  primitive_eq := radius_primitive C A cyl
  dual_sq := radius_dual_sq C A cyl

/-- The actual reference, with c=1 and rstar=2 and the original exact metric data. -/
def reference : RadialReference C.ambient.manifold := (constructedRadius C A cyl).toReference

theorem constructionTarget : ConstructionTarget := by
  intro d D C A cyl
  exact ⟨constructedRadius C A cyl⟩

theorem reference_growth (T : ExactSymplecticStructure C.ambient.manifold)
    (h : ∃ B : AdmissibleGrowth 1, ∃ C₀ : ℝ, 0 < C₀ ∧
      ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ y t, t₀ ≤ t →
        A.inverseNorm T (C.endMap (y,t)) ≤ C₀ * B.B (Real.exp t)) :
    GrowthAtInfinity A T (reference C A cyl).R 1 :=
  growth (constructedRadius C A cyl) T h

/-- Proof of the entire bounded output interface, before any comparison theorem. -/
theorem consumerTarget : ConsumerTarget := by
  intro d D C A cyl
  exact ⟨reference C A cyl, rfl, HEq.rfl, rfl, rfl, reference_growth C A cyl⟩

end ExactLiouvilleComparison.FiniteTypeRadial
