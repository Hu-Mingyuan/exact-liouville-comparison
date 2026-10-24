import ExactLiouvilleComparison.Statement

/-! Consumers of the statement interfaces. These prove only definition bridges,
not any of the manuscript target propositions. -/
noncomputable section
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold
namespace ExactLiouvilleComparison

theorem completePrimitive_preserves_flow {d : ℕ} {M : SmoothManifold d}
    {lambda : M.Form 1} (C : CompletePrimitive M lambda) :
    C.toCompleteLiouvilleManifold.completeFlow = C.completeFlow := rfl

theorem completePrimitive_positive_contraction {d : ℕ} {M : SmoothManifold d}
    {lambda : M.Form 1} (C : CompletePrimitive M lambda) (x : M.Point) (v : M.Tangent x) :
    evalTwo (M.exteriorDerivative lambda) x (M.liouvilleVector lambda x) v =
      evalOne lambda x v := C.contraction x v

/-- All negative and positive real times are genuine flow times. -/
def completeFlowAt {d : ℕ} {M : SmoothManifold d} {lambda : M.Form 1}
    (C : CompletePrimitive M lambda) (t : ℝ) (x : M.Point) : M.Point :=
  C.completeFlow.flow t x

/-- The radial quantity uses the g-dual of the actual differential. -/
theorem radial_quantity_eq {d : ℕ} {M : SmoothManifold d} (P : RadialReference M)
    (x : M.Point) :
    P.compatible.dualNorm x (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x) =
    ‖P.compatible.covector x (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x)‖ := rfl

end ExactLiouvilleComparison
