import ExactLiouvilleComparison.CylindricalCompatibilityContactBundleStatement

noncomputable section
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle

/-- The expected dimension is a consequence of the actual nonvanishing boundary
primitive, not an assumption about an inhabited boundary. -/
theorem dimensionTarget : DimensionTarget := by
  intro d D y
  have h := D.domain.boundary.finrank_contactHyperplane_add_one (boundaryAlpha D) y
    (D.liouville.boundaryForm_exists_eval_ne_zero y)
  constructor
  · omega
  · exact D.liouville.boundary_contactHyperplane_finrank y

theorem boundary_isEmpty_of_lt_two {d : ℕ} (D : LiouvilleDomain d) (hd : d < 2) :
    IsEmpty D.domain.boundary.Point :=
  ⟨fun y ↦ (Nat.not_le_of_lt hd) (dimensionTarget d D y).1⟩

/-- Topological currying preserves the actual restricted differential, with the
positive contraction convention and no auxiliary norm. -/
theorem differential_apply {d : ℕ} (D : LiouvilleDomain d)
    (y : D.domain.boundary.Point) (v w : Fiber D y) :
    differential D y v w =
      D.domain.boundary.contactHyperplaneDifferential (boundaryAlpha D) y ![v, w] := by
  change (D.domain.boundary.contactHyperplaneDifferential (boundaryAlpha D) y)
    (Fin.cons v (fun _ : Fin 1 ↦ w)) = _
  congr 1
  ext i
  fin_cases i <;> rfl

theorem differential_eq_evalTwo {d : ℕ} (D : LiouvilleDomain d)
    (y : D.domain.boundary.Point) (v w : Fiber D y) :
    differential D y v w =
      evalTwo (D.domain.boundary.exteriorDerivative (boundaryAlpha D)) y v w := by
  rw [differential_apply, contactHyperplaneDifferential_apply]

theorem differential_alternating {d : ℕ} (D : LiouvilleDomain d)
    (y : D.domain.boundary.Point) (v : Fiber D y) : differential D y v v = 0 := by
  rw [differential_apply]
  exact (D.domain.boundary.contactHyperplaneDifferential (boundaryAlpha D) y).map_eq_zero_of_eq ![v, v] (by rfl) (by decide : (0 : Fin 2) ≠ 1)

theorem differential_nondegenerate {d : ℕ} (D : LiouvilleDomain d)
    (y : D.domain.boundary.Point) (v : Fiber D y)
    (h : ∀ w, differential D y v w = 0) : v = 0 := by
  apply D.liouville.boundary_contactHyperplaneDifferential_nondegenerate y v
  intro w
  rw [← differential_apply]
  exact h w

end ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle
