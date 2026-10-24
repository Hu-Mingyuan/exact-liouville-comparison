import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationBundle
import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationDegenerate
import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationAlgebraChecks
import ExactLiouvilleComparison.Geometry

/-! Native tangent-bundle consumers of supplied-metric normalization.
These do not assert the parent's relative metric gluing or cylindrical extension. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold
open scoped Manifold ContDiff

namespace ExactLiouvilleComparison.CylindricalCompatibility.Normalization

local instance tangentNormedAddCommGroup {d : ℕ} (M : SmoothManifold d) :
    ∀ x : M.Point, NormedAddCommGroup (M.Tangent x) := fun _ ↦ inferInstanceAs (NormedAddCommGroup (Model d))
local instance tangentNormedSpace {d : ℕ} (M : SmoothManifold d) :
    ∀ x : M.Point, NormedSpace ℝ (M.Tangent x) := fun _ ↦ inferInstanceAs (NormedSpace ℝ (Model d))

/-- The general bundle theorem produces the project's actual smooth tangent endomorphism. -/
theorem tangent_normalization {d : ℕ} (M : SmoothManifold d)
    (omega : SymplecticForm (𝓘(ℝ, Model d)) (Model d) M.Tangent)
    (h : ContMDiffRiemannianMetric (𝓘(ℝ, Model d)) ∞ (Model d) M.Tangent) :
    ∃ J : (x : M.Point) → M.Tangent x →L[ℝ] M.Tangent x,
      SmoothEndomorphism M J ∧
      (∀ x v, J x (J x v) = -v) ∧
      (∀ x v w, omega.form x (J x v) (J x w) = omega.form x v w) ∧
      (∀ x v, v ≠ 0 → 0 < omega.form x v (J x v)) ∧
      (∀ x (J₀ : M.Tangent x →L[ℝ] M.Tangent x), Compatible (omega.form x) J₀ →
        (∀ v w, h.inner x v w = omega.form x v (J₀ w)) → J x = J₀) := by
  obtain ⟨J, hJs, hJc, hJr⟩ := normalization omega h
  exact ⟨J, hJs, fun x ↦ (hJc x).1, fun x ↦ (hJc x).2.1,
    fun x ↦ (hJc x).2.2, hJr⟩

/-- A parent may supply a metric matching prescribed data on any set.
The normalization itself imposes no regularity or extension assumption on that set. -/
theorem tangent_normalization_relative_recovery {d : ℕ} (M : SmoothManifold d)
    (omega : SymplecticForm (𝓘(ℝ, Model d)) (Model d) M.Tangent)
    (h : ContMDiffRiemannianMetric (𝓘(ℝ, Model d)) ∞ (Model d) M.Tangent)
    (s : Set M.Point) (J₀ : (x : M.Point) → M.Tangent x →L[ℝ] M.Tangent x)
    (hJ : ∀ x ∈ s, Compatible (omega.form x) (J₀ x))
    (heq : ∀ x ∈ s, ∀ v w, h.inner x v w = omega.form x v (J₀ x w)) :
    SmoothEndomorphism M (normalizedEndomorphism omega h) ∧
      (∀ x, Compatible (omega.form x) (normalizedEndomorphism omega h x)) ∧
      (∀ x ∈ s, normalizedEndomorphism omega h x = J₀ x) :=
  ⟨normalizedEndomorphism_contMDiff omega h, normalizedEndomorphism_compatible omega h,
    fun x hx ↦ normalizedEndomorphism_recovery omega h x (J₀ x) (hJ x hx) (heq x hx)⟩

end ExactLiouvilleComparison.CylindricalCompatibility.Normalization
