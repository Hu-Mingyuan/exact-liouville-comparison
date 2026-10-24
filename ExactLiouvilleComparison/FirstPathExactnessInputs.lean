import ExactLiouvilleComparison.FirstPathExactnessStatement

/-! Analytic premises for the literal first primitive and constructed field.
This file does not assert the Cartan or endpoint exactness theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.FirstPathExactness
variable {d : ℕ} {M : SmoothManifold d}

theorem primitive_smooth (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (t : ℝ) : M.IsSmoothForm (primitive P G T t) :=
  T.smooth_primitive.add ((FirstPath.coefficient P G).smooth_primitive.smul t)

theorem primitive_smoothFamily (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) : M.IsSmoothFormFamily (primitive P G T) :=
  MoserRegularity.smoothFormFamily_affine _ _ T.smooth_primitive
    (FirstPath.coefficient P G).smooth_primitive

theorem primitive_exteriorDerivative (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (t : ℝ) :
    M.exteriorDerivative (primitive P G T t) = FirstPath.form P G T t := by
  change M.exteriorDerivative (T.primitive + t • (FirstPath.coefficient P G).primitive) = _
  rw [RadialInterpolation.exteriorDerivative_add T.smooth_primitive
    ((FirstPath.coefficient P G).smooth_primitive.smul t),
    M.exteriorDerivative_const_smul_one _ (FirstPath.coefficient P G).smooth_primitive]
  rfl

theorem primitive_parameter_derivative (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (t : ℝ) (x : M.Point) (v : M.Tangent x) :
    HasDerivAt (fun u => evalOne (primitive P G T u) x v)
      (SmallCoefficient.k G P.rstar (P.R x) * evalOne P.exactStructure.primitive x v) t := by
  convert (hasDerivAt_id t).mul_const
    (SmallCoefficient.k G P.rstar (P.R x) * evalOne P.exactStructure.primitive x v)
    |>.const_add (evalOne T.primitive x v) using 1 <;> simp [primitive, evalOne,
      LinearAlgebraChecks.radialPrimitive]

theorem field_equation (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T) :
    MoserExactness.Equation (primitive P G T) (MoserRegularity.firstField P G T hw) := by
  intro t x v
  rw [primitive_exteriorDerivative, (primitive_parameter_derivative P G T t.val x v).deriv]
  simpa only [MoserRegularity.firstField, neg_mul] using
    FirstPath.X_equation P G T hw x t.val t.property.1 v

theorem field_smooth (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T) :
    M.IsSmoothIntervalVectorFieldFamily (MoserRegularity.firstField P G T hw) :=
  MoserRegularity.first_intervalSmooth P G T hw

end ExactLiouvilleComparison.FirstPathExactness
