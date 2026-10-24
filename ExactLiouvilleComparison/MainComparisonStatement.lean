import ExactLiouvilleComparison.FirstPathExactness
import ExactLiouvilleComparison.ThirdPathFlow
import ExactLiouvilleComparison.RadialInterpolationFlow
import ExactLiouvilleComparison.ExactComparisonAlgebra

/-! Bounded assembly specification; the targets below are not proof terms. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.MainComparison
variable {d : ℕ} {M : SmoothManifold d}

/-- Literal second path, for all real parameters (symplecticity only on [0,1]). -/
def secondPrimitive (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (u : ℝ) : M.Form 1 :=
  T.primitive + LinearAlgebraChecks.radialPrimitive P
    (fun r => (1-u)*SmallCoefficient.k G P.rstar r + u*LargeCoefficient.A P T.primitive r)

/-- Literal fourth forward path; the comparison arrow uses its inverse. -/
def fourthPrimitive (P : RadialReference M) (T : ExactSymplecticStructure M)
    (v : ℝ) : M.Form 1 :=
  LinearAlgebraChecks.radialPrimitive P (fun r => 1 + v*(LargeCoefficient.A P T.primitive r-1))

/-- Actual delivered evolution, with every radial applicability premise discharged. -/
def secondEvolution (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T) :=
  RadialInterpolationFlow.evolution P (FirstPath.coefficient P G)
    (RadialInterpolationFlow.largeCoefficient P T.primitive T.smooth_primitive)
    (RadialInterpolationFlow.second_applicable P G T hw).1
    (RadialInterpolationFlow.second_applicable P G T hw).2.1 T.primitive T.smooth_primitive
    (RadialInterpolationFlow.second_applicable P G T hw).2.2

/-- Actual delivered evolution for sigma=0 and rho0=1, rho1=A. -/
def fourthEvolution (P : RadialReference M) (T : ExactSymplecticStructure M) :=
  RadialInterpolationFlow.evolution P (RadialInterpolationFlow.oneCoefficient P)
    (RadialInterpolationFlow.largeCoefficient P T.primitive T.smooth_primitive)
    (RadialInterpolationFlow.fourth_applicable P T.primitive T.smooth_primitive).1
    (RadialInterpolationFlow.fourth_applicable P T.primitive T.smooth_primitive).2.1
    0 M.isSmoothForm_zero
    (RadialInterpolationFlow.fourth_applicable P T.primitive T.smooth_primitive).2.2

/-- All three literal forward paths, with the literal integral gauges and actual evolutions. -/
def RemainingPathsTarget : Prop :=
  ∀ (P : RadialReference M) (G : AdmissibleGrowth 1) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T),
    MoserExactness.Endpoint (secondPrimitive P G T) (secondEvolution P G T hw) ∧
    MoserExactness.Endpoint (ThirdPath.primitive P T) (ThirdPath.evolution P T hw) ∧
    MoserExactness.Endpoint (fourthPrimitive P T) (fourthEvolution P T)

/-- Exactly the unchanged general radial theorem, with no extra premises. -/
abbrev Target : Prop := MainTarget

end ExactLiouvilleComparison.MainComparison
