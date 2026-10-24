import ExactLiouvilleComparison.RadialInterpolationFlowCoefficients
import ExactLiouvilleComparison.FirstPathFlowStatement

/-! Bounded third-path specification. `Target` is not an existence theorem.
All flow, regularity and estimate fields below are outputs to be constructed. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.ThirdPath
variable {d : ℕ} {M : SmoothManifold d}

/-- The manuscript forward primitive, with the delivered literal large coefficient. -/
def primitive (P : RadialReference M) (T : ExactSymplecticStructure M)
    (s : ℝ) : M.Form 1 :=
  LinearAlgebraChecks.radialPrimitive P (LargeCoefficient.A P T.primitive) + s • T.primitive

/-- Proper scalar used for continuation; no completeness of g is requested. -/
def exhaustion (P : RadialReference M) (x : M.Point) : ℝ := Real.sqrt (P.R x)

/-- Complete bounded output contract. In particular no trajectory, inverse field,
or evolution is an input to `Target`. Norms explicitly use the reference g. -/
structure Construction (P : RadialReference M) (T : ExactSymplecticStructure M) where
  field : Parameter → (x : M.Point) → M.Tangent x
  smooth_primitive : M.IsSmoothFormFamily (primitive P T)
  symplectic : ∀ s : Parameter,
    M.IsSymplecticOn (M.exteriorDerivative (primitive P T s.val)) univ
  equation : ∀ s x v,
    evalTwo (M.exteriorDerivative (primitive P T s.val)) x (field s x) v =
      -evalOne T.primitive x v
  unique_field : ∀ s x (v : M.Tangent x),
    (∀ w, evalTwo (M.exteriorDerivative (primitive P T s.val)) x v w =
      -evalOne T.primitive x w) → v = field s x
  joint : MoserRegularity.NativeJoint field
  norm_bound : ∀ s x,
    @norm (P.compatible.MetricTangent x) _ (field s x) ≤
      P.compatible.dualNorm x (LargeCoefficient.oneCovector T.primitive x) /
        LargeCoefficient.A P T.primitive (P.R x)
  ratio_le_one : ∀ x,
    P.compatible.dualNorm x (LargeCoefficient.oneCovector T.primitive x) /
      LargeCoefficient.A P T.primitive (P.R x) ≤ 1
  exterior_bound : ∀ s x, P.rstar < P.R x →
    |M.scalarDerivative (exhaustion P) x (field s x)| ≤ 1 / (2 * Real.sqrt P.c)
  smooth_exhaustion : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ (exhaustion P)
  proper_exhaustion : IsProperMap (exhaustion P)
  lower_exhaustion : ∀ x, 1 ≤ exhaustion P x
  core_bound : ∃ D : ℝ, 0 ≤ D ∧ ∀ s x, P.R x ≤ P.rstar →
    |M.scalarDerivative (exhaustion P) x (field s x)| ≤ D
  global_bound : ∃ D : ℝ, 0 ≤ D ∧ ∀ s x,
    |M.scalarDerivative (exhaustion P) x (field s x)| ≤ D
  evolution : FirstPathFlow.Evolution field
  inverse_isotopy : SmoothlyIsotopicToIdentity M
    (evolution.map parameterOne parameterZero)

/-- No B or inverse-growth estimate is needed for this path. This proves a stronger
bounded intermediate statement, directly applicable to every manuscript input. -/
def Target : Prop :=
  ∀ (P : RadialReference M) (T : ExactSymplecticStructure M),
    WeaklyTames P.compatible T → Nonempty (Construction P T)

end ExactLiouvilleComparison.ThirdPath
