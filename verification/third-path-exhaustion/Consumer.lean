import ExactLiouvilleComparison.ThirdPathExhaustion

noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
open ExactLiouvilleComparison

-- This consumer has precisely the scalar premises the parent must discharge.
example {d : ℕ} {M : SmoothManifold d} (P : RadialReference M)
    (Z : Parameter → (x : M.Point) → M.Tangent x)
    (hZ : MoserRegularity.NativeJoint Z)
    (hZnorm : ∀ s x, @norm (P.compatible.MetricTangent x) _ (Z s x) ≤ 1) :
    ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ (ThirdPath.exhaustion P) ∧
    IsProperMap (ThirdPath.exhaustion P) ∧
    (∀ x, 1 ≤ ThirdPath.exhaustion P x) ∧
    (∀ s x, P.rstar < P.R x →
      |M.scalarDerivative (ThirdPath.exhaustion P) x (Z s x)| ≤ 1 / (2 * Real.sqrt P.c)) ∧
    (∃ D : ℝ, 0 ≤ D ∧ ∀ s x, P.R x ≤ P.rstar →
      |M.scalarDerivative (ThirdPath.exhaustion P) x (Z s x)| ≤ D) ∧
    (∃ D : ℝ, 0 ≤ D ∧ ∀ s x,
      |M.scalarDerivative (ThirdPath.exhaustion P) x (Z s x)| ≤ D) :=
  ⟨ThirdPath.exhaustion_smooth P, ThirdPath.exhaustion_proper P,
    ThirdPath.exhaustion_lower P,
    fun s x hx => ThirdPath.exhaustion_exterior_bound P x hx (Z s x) (hZnorm s x),
    ThirdPath.exhaustion_core_bound P hZ, ThirdPath.exhaustion_global_bound P hZ hZnorm⟩

#eval IO.println "THIRD_PATH_SCALAR_CONSUMER_COMPLETE"
