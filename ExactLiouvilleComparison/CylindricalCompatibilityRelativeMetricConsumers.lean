import ExactLiouvilleComparison.CylindricalCompatibilityRelativeMetric

/-! Consumers of the native relative metric construction, including degenerate cases. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle Set FsFltz.Geometry
open scoped Manifold ContDiff Bundle

namespace ExactLiouvilleComparison.CylindricalCompatibility.RelativeMetric

/-- The empty prescription constructs a global native smooth metric from no metric input. -/
theorem exists_metric {d : ℕ} (M : SmoothManifold d) : Nonempty (NativeMetric M) := by
  obtain ⟨g, _⟩ := exists_relative_metric M ∅ ∅ isClosed_empty isOpen_empty
    (Subset.refl _) (fun _ => 0) (by intro x hx; exact hx.elim) (by intro x hx; exact hx.elim)
  exact ⟨g⟩

/-- A dimension-zero native manifold, with a nonempty base. -/
def zeroManifold : SmoothManifold 0 where
  Point := Model 0
  topology := inferInstance
  charts := inferInstance
  hausdorff := inferInstance
  secondCountable := inferInstance
  smooth := inferInstance

/-- The construction applies in rank zero without a nontriviality premise. -/
theorem zero_dimensional_metric : Nonempty (NativeMetric zeroManifold) := exists_metric _

/-- An empty native manifold in any dimension. -/
def emptyManifold (d : ℕ) : SmoothManifold d where
  Point := Empty
  topology := inferInstance
  charts := ChartedSpace.empty (Model d) Empty
  hausdorff := inferInstance
  secondCountable := inferInstance
  smooth := by
    let := ChartedSpace.empty (Model d) Empty
    infer_instance

/-- The construction applies to an actually empty base in every dimension. -/
theorem empty_base_metric (d : ℕ) : Nonempty (NativeMetric (emptyManifold d)) := exists_metric _

/-- Registering the output through Mathlib's RiemannianBundle yields precisely q,
not the temporary chart inner product or norm. -/
theorem ofSPD_native_inner {d : ℕ} (M : SmoothManifold d)
    (q : BilinField M) (hq : SmoothOn M q univ) (hpos : ∀ x, SPD (q x)) :
    letI : RiemannianBundle M.Tangent := ⟨(ofSPD M q hq hpos).toRiemannianMetric⟩
    ∀ (x : M.Point) (v w : M.Tangent x), inner ℝ v w = q x v w := by
  intros
  rfl

/-- Native smooth metric registration succeeds for the constructed global field. -/
theorem ofSPD_native_smooth {d : ℕ} (M : SmoothManifold d)
    (q : BilinField M) (hq : SmoothOn M q univ) (hpos : ∀ x, SPD (q x)) :
    letI : RiemannianBundle M.Tangent := ⟨(ofSPD M q hq hpos).toRiemannianMetric⟩
    IsContMDiffRiemannianBundle (𝓘(ℝ, Model d)) ∞ (Model d) M.Tangent := by
  infer_instance

/-- Pointwise equality on the prescribed closed set includes every pair of actual tangent vectors. -/
theorem relative_metric_values {d : ℕ} (M : SmoothManifold d)
    (K U : Set M.Point) (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (q : BilinField M) (hq : SmoothOn M q U) (hpos : ∀ x ∈ U, SPD (q x)) :
    ∃ g : NativeMetric M, ∀ x ∈ K, ∀ v w : M.Tangent x, g.inner x v w = q x v w := by
  obtain ⟨g, hg⟩ := exists_relative_metric M K U hK hU hKU q hq hpos
  exact ⟨g, fun x hx v w => congrArg (fun B => B v w) (hg x hx)⟩

end ExactLiouvilleComparison.CylindricalCompatibility.RelativeMetric
