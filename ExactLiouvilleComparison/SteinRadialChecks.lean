import ExactLiouvilleComparison.SteinRadial

/-! Consumers expose the literal radius and the original reference metric. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.SteinRadial

variable {d N : ℕ} {M : SmoothManifold d} (i : ProperComplexEmbedding M N)
  (P : SteinReference i)

theorem literal_radius_smooth : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞
    (fun x => Real.exp 1 + ‖i.map x‖ ^ 2) := radius_smooth i

theorem literal_radius_proper :
    IsProperMap (fun x => Real.exp 1 + ‖i.map x‖ ^ 2) := radius_proper i

theorem literal_radius_lower (x : M.Point) :
    1 ≤ Real.exp 1 + ‖i.map x‖ ^ 2 := radius_lower i x

theorem literal_dual_bound (x : M.Point) :
    (P.compatible.dualNorm x (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ))
      (fun y => Real.exp 1 + ‖i.map y‖ ^ 2) x)) ^ 2 ≤ 4 * ‖i.map x‖ ^ 2 := by
  calc
    _ ≤ 4 * (steinRadius i x - Real.exp 1) := radius_dualNorm_sq i P x
    _ = _ := by dsimp [steinRadius]; ring

theorem reference_identity_original (x : M.Point) (v : M.Tangent x) :
    evalOne P.exactStructure.primitive x v =
      -(reference i P).c * M.scalarDerivative (reference i P).R x (P.compatible.J x v) :=
  radial_identity i P x v

theorem reference_bound_original (x : M.Point) :
    (reference i P).c * (P.compatible.dualNorm x
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) (reference i P).R x)) ^ 2 ≤
      (reference i P).R x := radial_bound i P x

/-- The sharper pair of inequalities displayed in the manuscript. -/
theorem reference_bound_sharp (x : M.Point) :
    (reference i P).c * (P.compatible.dualNorm x
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) (reference i P).R x)) ^ 2 ≤
      (reference i P).R x - Real.exp 1 ∧
    (reference i P).R x - Real.exp 1 < (reference i P).R x := by
  change (1 / 4 : ℝ) * (P.compatible.dualNorm x
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) (steinRadius i) x)) ^ 2 ≤
      steinRadius i x - Real.exp 1 ∧ _
  constructor
  · have h := radius_dualNorm_sq i P x
    linarith
  · exact sub_lt_self _ (Real.exp_pos _)

/-- The constructed package supplies the original exterior-field interfaces. -/
theorem reference_exterior (x : M.Point) (hx : 2 < steinRadius i x) :
    (∀ v, evalOne P.exactStructure.primitive x v =
      -(1 / 4 : ℝ) * M.scalarDerivative (steinRadius i) x (P.compatible.J x v)) ∧
    (1 / 4 : ℝ) * (P.compatible.dualNorm x
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) (steinRadius i) x)) ^ 2 ≤ steinRadius i x :=
  ⟨(reference i P).radial_identity x hx, (reference i P).radial_bound x hx⟩

/-- Zero real dimension is an ordinary specialization, with no extra premise. -/
theorem zero_dimension_reference {M₀ : SmoothManifold 0}
    (i₀ : ProperComplexEmbedding M₀ N) (P₀ : SteinReference i₀) :
    Nonempty (RadialReference M₀) := ⟨reference i₀ P₀⟩

/-- The zero-dimensional ambient space is also admitted by the same interface. -/
theorem zero_ambient_reference (i₀ : ProperComplexEmbedding M 0) (P₀ : SteinReference i₀) :
    Nonempty (RadialReference M) := ⟨reference i₀ P₀⟩

theorem checked_target : Target := target

end ExactLiouvilleComparison.SteinRadial
