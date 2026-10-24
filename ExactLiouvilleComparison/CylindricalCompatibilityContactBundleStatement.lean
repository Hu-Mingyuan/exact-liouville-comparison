import ExactLiouvilleComparison.Geometry
import FsFltz.Geometry.BoundaryContactDistribution
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! Auxiliary native kernel-bundle specification. The targets below are not
proofs of existence. No compatible complex structure or Reeb field is constructed
or assumed in the bundle-existence target. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle

abbrev boundaryAlpha {d : ℕ} (D : LiouvilleDomain d) : D.domain.boundary.Form 1 :=
  D.domain.boundaryForm D.liouville.primitive

/-- Literally the pinned tangent submodule, with its existing subtype topology. -/
abbrev Fiber {d : ℕ} (D : LiouvilleDomain d) (y : D.domain.boundary.Point) : Type :=
  D.domain.boundary.contactHyperplane (boundaryAlpha D) y

/-- Native currying of the actual restricted exterior derivative. -/
def differential {d : ℕ} (D : LiouvilleDomain d) (y : D.domain.boundary.Point) :
    Fiber D y →L[ℝ] Fiber D y →L[ℝ] ℝ :=
  ((MultilinearMap.ofSubsingletonₗ ℝ ℝ (Fiber D y) ℝ
    (0 : Fin 1)).symm.toLinearMap.comp
      (D.domain.boundary.contactHyperplaneDifferential (boundaryAlpha D) y).toContinuousMultilinearMap.toMultilinearMap.curryLeft).toContinuousBilinearMap

/-- A presentation contains only native local trivializations. In particular,
it is not a global frame and the fiber type is not replaced by the model. -/
abbrev Prebundle {d : ℕ} (D : LiouvilleDomain d) :=
  VectorPrebundle ℝ (Model (d - 2)) (Fiber D)

section Properties
variable {d : ℕ} (D : LiouvilleDomain d) (P : Prebundle D)

def SmoothKernelEndomorphism (j : (y : D.domain.boundary.Point) →
    Fiber D y →L[ℝ] Fiber D y) : Prop :=
  letI : TopologicalSpace (TotalSpace (Model (d - 2)) (Fiber D)) := P.totalSpaceTopology
  letI : FiberBundle (Model (d - 2)) (Fiber D) := P.toFiberBundle
  letI : VectorBundle ℝ (Model (d - 2)) (Fiber D) := P.toVectorBundle
  ContMDiff 𝓘(ℝ, Model (d - 1))
    ((𝓘(ℝ, Model (d - 1))).prod
      𝓘(ℝ, Model (d - 2) →L[ℝ] Model (d - 2))) ∞
    (fun y ↦ TotalSpace.mk' (Model (d - 2) →L[ℝ] Model (d - 2)) y (j y))

/-- The native atlas, inclusion and smooth restriction properties. These form
the structural prerequisite; no form, metric or Reeb is part of this package. -/
def AtlasProperties : Prop :=
  letI : TopologicalSpace (TotalSpace (Model (d - 2)) (Fiber D)) := P.totalSpaceTopology
  letI : FiberBundle (Model (d - 2)) (Fiber D) := P.toFiberBundle
  letI : VectorBundle ℝ (Model (d - 2)) (Fiber D) := P.toVectorBundle
  ContMDiffVectorBundle ∞ (Model (d - 2)) (Fiber D) 𝓘(ℝ, Model (d - 1)) ∧
  ContMDiff 𝓘(ℝ, Model (d - 1))
    ((𝓘(ℝ, Model (d - 1))).prod
      𝓘(ℝ, Model (d - 2) →L[ℝ] Model (d - 1))) ∞
    (fun y ↦ TotalSpace.mk' (Model (d - 2) →L[ℝ] Model (d - 1)) y
      (D.domain.boundary.contactHyperplane (boundaryAlpha D) y).subtypeL) ∧
  (∀ (n : ℕ) (N : SmoothManifold n) (f : N.Point → D.domain.boundary.Point)
      (s : (z : N.Point) → Fiber D (f z)),
    ContMDiff 𝓘(ℝ, Model n)
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, Model (d - 2))) ∞
      (fun z ↦ TotalSpace.mk' (Model (d - 2)) (f z) (s z)) ↔
    ContMDiff 𝓘(ℝ, Model n)
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, Model (d - 1))) ∞
      (fun z ↦ TotalSpace.mk' (Model (d - 1)) (f z)
        (s z : D.domain.boundary.Tangent (f z))))

/-- The full native output, including the actual restricted differential and
an auxiliary positive definite metric for normalization. -/
def NativeProperties : Prop :=
  letI : TopologicalSpace (TotalSpace (Model (d - 2)) (Fiber D)) := P.totalSpaceTopology
  letI : FiberBundle (Model (d - 2)) (Fiber D) := P.toFiberBundle
  letI : VectorBundle ℝ (Model (d - 2)) (Fiber D) := P.toVectorBundle
  AtlasProperties D P ∧
  ContMDiff 𝓘(ℝ, Model (d - 1))
    ((𝓘(ℝ, Model (d - 1))).prod
      𝓘(ℝ, Model (d - 2) →L[ℝ] Model (d - 2) →L[ℝ] ℝ)) ∞
    (fun y ↦ TotalSpace.mk'
      (Model (d - 2) →L[ℝ] Model (d - 2) →L[ℝ] ℝ) y (differential D y)) ∧
  (∀ y v, differential D y v v = 0) ∧
  (∀ y v, (∀ w, differential D y v w = 0) → v = 0) ∧
  Nonempty (ContMDiffRiemannianMetric 𝓘(ℝ, Model (d - 1)) ∞
    (Model (d - 2)) (Fiber D))

/-- Restriction of any smooth ambient endomorphism preserving the literal kernel,
and zero extension of any smooth kernel endomorphism through any supplied actual
smooth normalized Reeb. All maps are tied to their fiberwise formulas. -/
def TransferProperties : Prop :=
  letI : TopologicalSpace (TotalSpace (Model (d - 2)) (Fiber D)) := P.totalSpaceTopology
  letI : FiberBundle (Model (d - 2)) (Fiber D) := P.toFiberBundle
  letI : VectorBundle ℝ (Model (d - 2)) (Fiber D) := P.toVectorBundle
  (∀ A : (y : D.domain.boundary.Point) →
      D.domain.boundary.Tangent y →L[ℝ] D.domain.boundary.Tangent y,
    SmoothEndomorphism D.domain.boundary A →
    (∀ y v, v ∈ D.domain.boundary.contactHyperplane (boundaryAlpha D) y →
      A y v ∈ D.domain.boundary.contactHyperplane (boundaryAlpha D) y) →
    ∃ j, SmoothKernelEndomorphism D P j ∧
      ∀ y v, (j y v : D.domain.boundary.Tangent y) = A y v) ∧
  (∀ (R : (y : D.domain.boundary.Point) → D.domain.boundary.Tangent y),
    D.domain.boundary.IsSmoothVectorField R →
    (∀ y, evalOne (boundaryAlpha D) y (R y) = 1) →
    (∀ y v, evalTwo (D.domain.boundary.exteriorDerivative (boundaryAlpha D)) y
      (R y) v = 0) →
    ∃ p : (y : D.domain.boundary.Point) → D.domain.boundary.Tangent y →L[ℝ] Fiber D y,
      (∀ y v, (p y v : D.domain.boundary.Tangent y) =
        v - evalOne (boundaryAlpha D) y v • R y) ∧
      ContMDiff 𝓘(ℝ, Model (d - 1))
        ((𝓘(ℝ, Model (d - 1))).prod
          𝓘(ℝ, Model (d - 1) →L[ℝ] Model (d - 2))) ∞
        (fun y ↦ TotalSpace.mk' (Model (d - 1) →L[ℝ] Model (d - 2)) y (p y)) ∧
      ∀ j, SmoothKernelEndomorphism D P j →
        SmoothEndomorphism D.domain.boundary
          (fun y ↦ (D.domain.boundary.contactHyperplane (boundaryAlpha D) y).subtypeL.comp
            ((j y).comp (p y))))

end Properties

/-- Unconditional construction in every dimension, including empty boundaries.
No presentation, frame, J, Reeb, or smooth restriction is an input. -/
def BundleExistenceTarget : Prop :=
  ∀ (d : ℕ) (D : LiouvilleDomain d),
    ∃ P : Prebundle D, NativeProperties D P ∧ TransferProperties D P

/-- Boundary points force the dimension needed for the subtraction model. -/
def DimensionTarget : Prop :=
  ∀ (d : ℕ) (D : LiouvilleDomain d) (y : D.domain.boundary.Point),
    2 ≤ d ∧ Module.finrank ℝ (Fiber D y) = d - 2

end ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle
