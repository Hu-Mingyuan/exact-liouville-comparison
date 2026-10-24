import FsFltz.Geometry.Family
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Bounded scalar integration contract. The target below is a statement, not a proof. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set MeasureTheory

namespace ExactLiouvilleComparison.MoserExactnessIntegral
variable {d : ℕ} {M : SmoothManifold d}

/-- The guarded real-time representative of an interval scalar family. -/
def integrand (f : Parameter → M.Point → ℝ) (t : ℝ) (x : M.Point) : ℝ := by
  classical
  exact if ht : t ∈ parameterInterval then f ⟨t, ht⟩ x else 0

/-- The literal gauge, with no choice of extension in its definition. -/
def integral (f : Parameter → M.Point → ℝ) (x : M.Point) : ℝ :=
  ∫ t in (0 : ℝ)..1, integrand f t x

/-- Guarded native spatial derivative, evaluated on an arbitrary tangent vector. -/
def derivativeIntegrand (f : Parameter → M.Point → ℝ)
    (x : M.Point) (v : M.Tangent x) (t : ℝ) : ℝ := by
  classical
  exact if ht : t ∈ parameterInterval then M.scalarDerivative (f ⟨t, ht⟩) x v else 0

/-- All analytic outputs required by the endpoint FTC consumer. The sole regularity
premise is the pinned genuine open-extension predicate. -/
def Target : Prop :=
  ∀ (f : Parameter → M.Point → ℝ), M.IsSmoothIntervalScalarFamily f →
    ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ (integral f) ∧
    (∀ x, ContinuousOn (fun t => integrand f t x) parameterInterval) ∧
    (∀ x, IntervalIntegrable (fun t => integrand f t x) volume 0 1) ∧
    (∀ x v, ContinuousOn (derivativeIntegrand f x v) parameterInterval) ∧
    (∀ x v, IntervalIntegrable (derivativeIntegrand f x v) volume 0 1) ∧
    (∀ x v, M.scalarDerivative (integral f) x v =
      ∫ t in (0 : ℝ)..1, derivativeIntegrand f x v t)

end ExactLiouvilleComparison.MoserExactnessIntegral
