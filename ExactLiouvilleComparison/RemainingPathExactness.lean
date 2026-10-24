import ExactLiouvilleComparison.MainComparisonStatement

/-! Exactness of the literal remaining paths, from the delivered actual evolutions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter
namespace ExactLiouvilleComparison.MainComparison
variable {d : ℕ} {M : SmoothManifold d}

/-- All-real interpolation primitive; no off-interval symplecticity is used. -/
def interpolationPrimitive (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (σ : M.Form 1) (t : ℝ) : M.Form 1 :=
  σ + LinearAlgebraChecks.radialPrimitive P (RadialInterpolation.rho q₀ q₁ t)

theorem interpolation_affine (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (σ : M.Form 1) (t : ℝ) :
    interpolationPrimitive P q₀ q₁ σ t =
      (σ + q₀.primitive) + t • (q₁.primitive - q₀.primitive) := by
  funext x
  ext vs
  simp only [interpolationPrimitive, RadialCoefficient.primitive,
    LinearAlgebraChecks.radialPrimitive, RadialInterpolation.rho,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring

theorem interpolation_family (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ) :
    M.IsSmoothFormFamily (interpolationPrimitive P q₀ q₁ σ) := by
  have he := funext (interpolation_affine P q₀ q₁ σ)
  rw [he]
  exact MoserRegularity.smoothFormFamily_affine _ _ (hσ.add q₀.smooth_primitive)
    (q₁.smooth_primitive.sub q₀.smooth_primitive)

theorem interpolation_equation (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ)
    (hw : RadialInterpolation.WeakDifferential (P := P) σ) :
    MoserExactness.Equation (interpolationPrimitive P q₀ q₁ σ)
      (MoserRegularity.interpolationField P q₀ q₁ σ hσ hw) := by
  intro t x v
  unfold interpolationPrimitive
  rw [(RadialInterpolation.primitive_parameter_derivative q₀ q₁ σ t.val x v).deriv]
  simpa only [neg_mul, MoserRegularity.interpolationField, RadialInterpolation.primitive,
    RadialCoefficient.primitive, RadialInterpolation.coefficient] using
    RadialInterpolation.vector_equation (P := P)
      (RadialInterpolation.coefficient q₀ q₁ t.val t.property) σ hσ hw
      (RadialInterpolation.delta q₀ q₁) x v

/-- Every analytic premise is discharged; the evolution is the delivered construction. -/
theorem interpolation_exactness (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (horder : ∀ r ∈ Ici 1, q₀.rho r ≤ q₁.rho r)
    (htend : Tendsto (fun r => r * q₀.rho r) atTop atTop)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ)
    (hw : RadialInterpolation.WeakDifferential (P := P) σ) :
    MoserExactness.PullbackDerivative (interpolationPrimitive P q₀ q₁ σ)
      (RadialInterpolationFlow.evolution P q₀ q₁ horder htend σ hσ hw) ∧
    MoserExactness.Endpoint (interpolationPrimitive P q₀ q₁ σ)
      (RadialInterpolationFlow.evolution P q₀ q₁ horder htend σ hσ hw) :=
  MoserExactness.moserExactness _ (interpolation_family P q₀ q₁ σ hσ) _
    (MoserRegularity.interpolation_intervalSmooth P q₀ q₁ σ hσ hw)
    (interpolation_equation P q₀ q₁ σ hσ hw) _

theorem second_eq_interpolation (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) : secondPrimitive P G T =
    interpolationPrimitive P (FirstPath.coefficient P G)
      (RadialInterpolationFlow.largeCoefficient P T.primitive T.smooth_primitive) T.primitive := rfl

theorem fourth_eq_interpolation (P : RadialReference M) (T : ExactSymplecticStructure M) :
    fourthPrimitive P T = interpolationPrimitive P (RadialInterpolationFlow.oneCoefficient P)
      (RadialInterpolationFlow.largeCoefficient P T.primitive T.smooth_primitive) 0 := by
  funext t
  simp only [fourthPrimitive, interpolationPrimitive, zero_add]
  congr 1
  funext r
  exact (RadialInterpolationFlow.fourth_rho P T.primitive T.smooth_primitive t r).symm

theorem second_exactness (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T) :
    MoserExactness.PullbackDerivative (secondPrimitive P G T) (secondEvolution P G T hw) ∧
    MoserExactness.Endpoint (secondPrimitive P G T) (secondEvolution P G T hw) :=
  interpolation_exactness P _ _ (RadialInterpolationFlow.second_applicable P G T hw).1
    (RadialInterpolationFlow.second_applicable P G T hw).2.1 _ T.smooth_primitive
    (RadialInterpolationFlow.second_applicable P G T hw).2.2

theorem third_equation (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) :
    MoserExactness.Equation (ThirdPath.primitive P T) (ThirdPath.field P T hw) := by
  intro t x v
  rw [(ThirdPath.primitive_parameter_derivative P T t.val x v).deriv]
  exact ThirdPath.field_equation P T hw t x v

theorem third_exactness (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) :
    MoserExactness.PullbackDerivative (ThirdPath.primitive P T) (ThirdPath.evolution P T hw) ∧
    MoserExactness.Endpoint (ThirdPath.primitive P T) (ThirdPath.evolution P T hw) :=
  MoserExactness.moserExactness _ (ThirdPath.primitive_family P T) _
    (ThirdPath.field_intervalSmooth P T hw) (third_equation P T hw) _

theorem fourth_exactness (P : RadialReference M) (T : ExactSymplecticStructure M) :
    MoserExactness.PullbackDerivative (fourthPrimitive P T) (fourthEvolution P T) ∧
    MoserExactness.Endpoint (fourthPrimitive P T) (fourthEvolution P T) := by
  rw [fourth_eq_interpolation]
  exact interpolation_exactness P _ _
    (RadialInterpolationFlow.fourth_applicable P T.primitive T.smooth_primitive).1
    (RadialInterpolationFlow.fourth_applicable P T.primitive T.smooth_primitive).2.1
    _ M.isSmoothForm_zero
    (RadialInterpolationFlow.fourth_applicable P T.primitive T.smooth_primitive).2.2

/-- Actual proof of the independently reviewed literal three-path contract. -/
theorem remainingPaths : RemainingPathsTarget (M := M) := by
  intro P G T hw
  exact ⟨(second_exactness P G T hw).2, (third_exactness P T hw).2,
    (fourth_exactness P T).2⟩

end ExactLiouvilleComparison.MainComparison
