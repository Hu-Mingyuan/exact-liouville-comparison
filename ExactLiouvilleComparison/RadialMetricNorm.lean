import ExactLiouvilleComparison.RadialMetricConstruction

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology InnerProductSpace
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.RadialCoefficient
variable {d : ℕ} {M : SmoothManifold d} {P : RadialReference M}
variable (q : RadialCoefficient P.rstar)

/-- The reference gradient is an eigenvector of the radial metric, with no
nonvanishing assumption on that gradient. -/
theorem metric_gradient_pair (x : M.Point) (v : M.Tangent x) :
    q.metricBilin x (P.radialGradient x) v =
      q.radialD x * M.scalarDerivative P.R x v := by
  have hg := P.radialGradient_inner x v
  change P.compatible.g.inner x (P.radialGradient x) v = M.scalarDerivative P.R x v at hg
  rw [q.metricBilin_apply, q.metricValue_eq, hg, P.dR_gradient, P.dR_J_gradient]
  unfold radialD radialA
  ring

/-- The dual norm is the operator norm on the actual constructed h-metric
fiber. This proof divides only by D, not by the norm of dR. -/
theorem radial_dualNorm_sq (x : M.Point) (hx : P.rstar < P.R x) :
    (q.compatible.dualNorm x (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x)) ^ 2 =
      q.radialA x / (P.c * q.radialD x) := by
  let z : q.compatible.MetricTangent x := (q.radialD x)⁻¹ • P.radialGradient x
  let l := q.compatible.covector x (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x)
  have hd : q.radialD x ≠ 0 := (q.radialD_pos x hx).ne'
  have hre : l = (InnerProductSpace.toDual ℝ (q.compatible.MetricTangent x)) z := by
    ext v
    change M.scalarDerivative P.R x v = q.metricBilin x z v
    change M.scalarDerivative P.R x v =
      q.metricBilin x ((q.radialD x)⁻¹ • P.radialGradient x) v
    rw [map_smul, smul_apply, smul_eq_mul, q.metric_gradient_pair]
    field_simp
  have he : ‖l‖ ^ 2 = M.scalarDerivative P.R x z := by
    calc
      ‖l‖ ^ 2 = ‖z‖ ^ 2 := by rw [hre, (InnerProductSpace.toDual ℝ _).norm_map]
      _ = ⟪z, z⟫_ℝ := (real_inner_self_eq_norm_sq z).symm
      _ = M.scalarDerivative P.R x z := (congrArg (fun f => f z) hre).symm
  change ‖l‖ ^ 2 = _
  rw [he]
  change (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x)
      ((q.radialD x)⁻¹ • P.radialGradient x) = _
  rw [map_smul, smul_eq_mul]
  change (q.radialD x)⁻¹ * M.scalarDerivative P.R x (P.radialGradient x) = _
  rw [P.dR_gradient]
  unfold radialA
  field_simp [P.positive_c.ne', hd]

/-- Manuscript Lemma lem:metric, its exterior dual identities in the explicit
g and constructed h norms. The metric formulas and global inequalities are
provided by metricValue_eq, metricValue_core and metricValue_*_of_* . -/
theorem dual_identities (x : M.Point) (hx : P.rstar < P.R x) :
    0 < q.radialD x ∧
    (q.compatible.dualNorm x (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x)) ^ 2 =
      q.radialA x / (P.c * q.radialD x) ∧
    (P.compatible.dualNorm x (P.betaCovector x)) ^ 2 = P.c * q.radialA x :=
  ⟨q.radialD_pos x hx, q.radial_dualNorm_sq x hx, q.beta_dualNorm_sq x hx⟩

end ExactLiouvilleComparison.RadialCoefficient
