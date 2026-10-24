import ExactLiouvilleComparison.RadialMetric

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology InnerProductSpace
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison
namespace RadialReference
variable {d : ℕ} {M : SmoothManifold d} (P : RadialReference M)

/-- Native one-form converted to a native continuous covector, before metric transport. -/
def betaCovector (x : M.Point) : M.Tangent x →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model d) (F := ℝ) (0 : Fin 1)).symm (P.exactStructure.primitive x)

/-- The gradient is the Riesz representative in the reference metric `g`. -/
def radialGradient (x : M.Point) : P.compatible.MetricTangent x :=
  (InnerProductSpace.toDual ℝ (P.compatible.MetricTangent x)).symm
    (P.compatible.covector x (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x))

theorem radialGradient_inner (x : M.Point) (v : P.compatible.MetricTangent x) :
    ⟪P.radialGradient x, v⟫_ℝ = M.scalarDerivative P.R x v :=
  InnerProductSpace.toDual_symm_apply

theorem radialGradient_norm (x : M.Point) :
    ‖P.radialGradient x‖ =
      P.compatible.dualNorm x (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x) :=
  (InnerProductSpace.toDual ℝ (P.compatible.MetricTangent x)).symm.norm_map _

theorem dR_gradient (x : M.Point) :
    M.scalarDerivative P.R x (P.radialGradient x) =
      (P.compatible.dualNorm x (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x)) ^ 2 := by
  rw [← P.radialGradient_inner, real_inner_self_eq_norm_sq, P.radialGradient_norm]

theorem dR_J_gradient (x : M.Point) :
    M.scalarDerivative P.R x (P.compatible.J x (P.radialGradient x)) = 0 := by
  rw [← P.radialGradient_inner]
  exact P.compatible.inner_J_self x (P.radialGradient x)

/-- The reference beta norm is derived from the radial identity and J-orthogonality. -/
theorem beta_dualNorm (x : M.Point) (hx : P.rstar < P.R x) :
    P.compatible.dualNorm x (P.betaCovector x) =
      P.c * P.compatible.dualNorm x (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x) := by
  have hb : P.compatible.covector x (P.betaCovector x) =
      P.c • (InnerProductSpace.toDual ℝ (P.compatible.MetricTangent x))
        (P.compatible.metricJ x (P.radialGradient x)) := by
    ext v
    change evalOne P.exactStructure.primitive x v =
      P.c * ⟪P.compatible.metricJ x (P.radialGradient x), v⟫_ℝ
    rw [P.radial_identity x hx, P.compatible.inner_J_left, P.radialGradient_inner]
    change -P.c * M.scalarDerivative P.R x (P.compatible.J x v) =
      P.c * (-M.scalarDerivative P.R x (P.compatible.J x v))
    ring
  unfold CompatibleStructure.dualNorm
  rw [hb, norm_smul, Real.norm_eq_abs, abs_of_pos P.positive_c,
    (InnerProductSpace.toDual ℝ (P.compatible.MetricTangent x)).norm_map,
    (P.compatible.metricJ x).norm_map, P.radialGradient_norm]
  rfl

end RadialReference
namespace RadialCoefficient
variable {d : ℕ} {M : SmoothManifold d} {P : RadialReference M}
variable (q : RadialCoefficient P.rstar)

theorem beta_dualNorm_sq (x : M.Point) (hx : P.rstar < P.R x) :
    (P.compatible.dualNorm x (P.betaCovector x)) ^ 2 = P.c * q.radialA x := by
  rw [P.beta_dualNorm x hx]
  unfold radialA
  ring

end RadialCoefficient
end ExactLiouvilleComparison
