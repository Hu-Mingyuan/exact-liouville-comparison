import ExactLiouvilleComparison.CylindricalCompatibilityContactBundleInputs

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle.Checks

theorem emptyBoundaryZero (D : LiouvilleDomain 0) : IsEmpty D.domain.boundary.Point :=
  boundary_isEmpty_of_lt_two D (by decide)

theorem emptyBoundaryOne (D : LiouvilleDomain 1) : IsEmpty D.domain.boundary.Point :=
  boundary_isEmpty_of_lt_two D (by decide)

theorem rankZeroBundle (D : LiouvilleDomain 2) :
    ∃ P : Prebundle D, NativeProperties D P ∧ TransferProperties D P :=
  bundleExistence 2 D

theorem arbitraryRankBundle (d : ℕ) (D : LiouvilleDomain d) :
    ∃ P : Prebundle D, NativeProperties D P ∧ TransferProperties D P :=
  bundleExistence d D

theorem suppliedReebProjection {d : ℕ} (D : LiouvilleDomain d)
    (R : (y : D.domain.boundary.Point) → D.domain.boundary.Tangent y)
    (hn : ∀ y, evalOne (boundaryAlpha D) y (R y) = 1) :
    (∀ y, Transfer.projection D R hn y (R y) = 0) ∧
    (∀ y (v : Fiber D y), Transfer.projection D R hn y v = v) :=
  ⟨Transfer.projection_self D R hn, Transfer.projection_subtype D R hn⟩

end ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle.Checks
