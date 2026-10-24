import ExactLiouvilleComparison.CylindricalCompatibilityStatement
import FsFltz.Geometry.BoundaryContactDistribution

/-! Fiberwise bridges for the reviewed contact-data representation.
The kernel is the existing native tangent submodule. This file does not claim
to construct its smooth bundle structure or to prove contact existence. -/

noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.CylindricalCompatibility

variable {d : ℕ} {D : LiouvilleDomain d}

/-- The literal kernel of the boundary primitive, reusing FsFltz. -/
abbrev ContactFiber (D : LiouvilleDomain d) (y : D.domain.boundary.Point) :=
  D.domain.boundary.contactHyperplane (alpha D) y

/-- The boundary one-form as a continuous linear functional. -/
def alphaLinear (D : LiouvilleDomain d) (y : D.domain.boundary.Point) :
    D.domain.boundary.Tangent y →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0 : Fin 1)).symm (alpha D y)

@[simp] theorem alphaLinear_apply (y : D.domain.boundary.Point)
    (v : D.domain.boundary.Tangent y) : alphaLinear D y v = evalOne (alpha D) y v := rfl

namespace ContactData

variable (P : ContactData D)

/-- Projection along the normalized Reeb line. -/
def projection (y : D.domain.boundary.Point) :
    D.domain.boundary.Tangent y →L[ℝ] D.domain.boundary.Tangent y :=
  ContinuousLinearMap.id ℝ _ - (alphaLinear D y).smulRight (P.reeb y)

@[simp] theorem projection_apply (y : D.domain.boundary.Point)
    (v : D.domain.boundary.Tangent y) :
    P.projection y v = v - evalOne (alpha D) y v • P.reeb y := rfl

theorem projection_mem (y : D.domain.boundary.Point)
    (v : D.domain.boundary.Tangent y) : P.projection y v ∈ ContactFiber D y := by
  change evalOne (alpha D) y (v - evalOne (alpha D) y v • P.reeb y) = 0
  rw [evalOne_sub, evalOne_smul, P.normalized, mul_one, sub_self]

/-- The same projection with its actual kernel codomain. -/
def kernelProjection (y : D.domain.boundary.Point) :
    D.domain.boundary.Tangent y →L[ℝ] ContactFiber D y :=
  (P.projection y).codRestrict _ (P.projection_mem y)

@[simp] theorem kernelProjection_coe (y : D.domain.boundary.Point)
    (v : D.domain.boundary.Tangent y) :
    (P.kernelProjection y v : D.domain.boundary.Tangent y) = P.projection y v := rfl

@[simp] theorem projection_of_mem (y : D.domain.boundary.Point) (v : ContactFiber D y) :
    P.projection y v = v := by
  have hv : evalOne (alpha D) y v = 0 := v.property
  rw [projection_apply, hv, zero_smul, sub_zero]

@[simp] theorem kernelProjection_of_mem (y : D.domain.boundary.Point)
    (v : ContactFiber D y) : P.kernelProjection y v = v := by
  apply Subtype.ext
  exact P.projection_of_mem y v

@[simp] theorem projection_reeb (y : D.domain.boundary.Point) :
    P.projection y (P.reeb y) = 0 := by
  rw [projection_apply, P.normalized, one_smul, sub_self]

theorem projection_idempotent (y : D.domain.boundary.Point)
    (v : D.domain.boundary.Tangent y) :
    P.projection y (P.projection y v) = P.projection y v :=
  P.projection_of_mem y (P.kernelProjection y v)

/-- Restriction of the reviewed ambient endomorphism to the native kernel. -/
def kernelJ (y : D.domain.boundary.Point) : ContactFiber D y →L[ℝ] ContactFiber D y :=
  ((P.J y).comp (ContactFiber D y).subtypeL).codRestrict _
    (fun v => P.horizontal y v)

@[simp] theorem kernelJ_coe (y : D.domain.boundary.Point) (v : ContactFiber D y) :
    (P.kernelJ y v : D.domain.boundary.Tangent y) = P.J y v := rfl

theorem kernelJ_square (y : D.domain.boundary.Point) (v : ContactFiber D y) :
    P.kernelJ y (P.kernelJ y v) = -v := by
  apply Subtype.ext
  change P.J y (P.J y v) = -(v : D.domain.boundary.Tangent y)
  have hv : evalOne (alpha D) y v = 0 := v.property
  rw [P.square, hv, zero_smul, add_zero]

theorem kernelJ_invariant (y : D.domain.boundary.Point) (v w : ContactFiber D y) :
    D.domain.boundary.contactHyperplaneDifferential (alpha D) y
      ![P.kernelJ y v, P.kernelJ y w] =
    D.domain.boundary.contactHyperplaneDifferential (alpha D) y ![v, w] := by
  simpa using P.invariant y v w

theorem kernelJ_positive (y : D.domain.boundary.Point) (v : ContactFiber D y) (hv : v ≠ 0) :
    0 < D.domain.boundary.contactHyperplaneDifferential (alpha D) y ![v, P.kernelJ y v] := by
  rw [contactHyperplaneDifferential_apply, kernelJ_coe]
  apply P.positive y v v.property
  intro h
  apply hv
  exact Subtype.ext h

theorem J_projection (y : D.domain.boundary.Point) (v : D.domain.boundary.Tangent y) :
    P.J y (P.projection y v) = P.J y v := by
  rw [projection_apply, map_sub, map_smul, P.annihilate_reeb, smul_zero, sub_zero]

/-- Restriction followed by zero extension recovers exactly the supplied J. -/
theorem zeroExtension_kernelJ (y : D.domain.boundary.Point) :
    (ContactFiber D y).subtypeL.comp ((P.kernelJ y).comp (P.kernelProjection y)) = P.J y := by
  ext v
  exact P.J_projection y v

/-- The Reeb equations in the reviewed data uniquely determine its vector field. -/
theorem reeb_unique (Q : ContactData D) (y : D.domain.boundary.Point) :
    P.reeb y = Q.reeb y := by
  apply sub_eq_zero.mp
  apply D.liouville.boundaryForm_differential_nondegenerate_on_kernel y
  · rw [evalOne_sub, P.normalized, Q.normalized, sub_self]
  · intro w _
    rw [evalTwo_sub_left, P.kernel, Q.kernel, sub_self]

end ContactData

/-- The genuine native kernel has the expected rank, including rank zero. -/
theorem contactFiber_finrank (y : D.domain.boundary.Point) :
    Module.finrank ℝ (ContactFiber D y) = d - 2 :=
  D.liouville.boundary_contactHyperplane_finrank y

/-- No positive dimension assumption is needed: a boundary point forces d ≥ 2. -/
theorem two_le_dimension_of_boundary (y : D.domain.boundary.Point) : 2 ≤ d := by
  have h := D.domain.boundary.finrank_contactHyperplane_add_one (alpha D) y
    (D.liouville.boundaryForm_exists_eval_ne_zero y)
  omega

/-- On an empty boundary every field is the unique empty section. -/
def emptyContactData [IsEmpty D.domain.boundary.Point] : ContactData D where
  reeb := fun y => isEmptyElim y
  smooth_reeb := fun y => isEmptyElim y
  normalized := fun y => isEmptyElim y
  kernel := fun y => isEmptyElim y
  J := fun y => isEmptyElim y
  smooth_J := by
    intro y
    exact isEmptyElim y
  annihilate_reeb := fun y => isEmptyElim y
  horizontal := fun y => isEmptyElim y
  square := fun y => isEmptyElim y
  invariant := fun y => isEmptyElim y
  positive := fun y => isEmptyElim y

/-- The zero-dimensional case of contact existence is unconditional. -/
theorem contact_exists_dimension_zero (D : LiouvilleDomain 0) : Nonempty (ContactData D) := by
  letI := D.domain.zero_boundary rfl
  exact ⟨emptyContactData⟩

/-- The one-dimensional case also has empty boundary, by contact nonvanishing. -/
theorem contact_exists_dimension_one (D : LiouvilleDomain 1) : Nonempty (ContactData D) := by
  letI : IsEmpty D.domain.boundary.Point := ⟨fun y => by
    have h := two_le_dimension_of_boundary y
    omega⟩
  exact ⟨emptyContactData⟩

end ExactLiouvilleComparison.CylindricalCompatibility
