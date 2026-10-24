import ExactLiouvilleComparison.MoserRegularityInverse
import FsFltz.Geometry.IntrinsicShrinkingPairScaling

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.MoserRegularity
variable {d : ℕ} {M : SmoothManifold d}

/-- Affine families of smooth forms have genuine joint chart smoothness for all times. -/
theorem smoothFormFamily_affine {k : ℕ} (eta zeta : M.Form k)
    (he : M.IsSmoothForm eta) (hz : M.IsSmoothForm zeta) :
    M.IsSmoothFormFamily (fun t => eta + t • zeta) := by
  intro a
  refine ⟨univ ×ˢ (chartAt (Model d) a).target,
    isOpen_univ.prod (chartAt (Model d) a).open_target,
    prod_mono (subset_univ _) subset_rfl, ?_⟩
  have h₀ : ContDiffOn ℝ ∞ (fun p : ℝ × Model d => M.formInChart a eta p.2)
      (univ ×ˢ (chartAt (Model d) a).target) :=
    (he a).comp contDiffOn_snd (fun _ h => h.2)
  have h₁ : ContDiffOn ℝ ∞ (fun p : ℝ × Model d => M.formInChart a zeta p.2)
      (univ ×ˢ (chartAt (Model d) a).target) :=
    (hz a).comp contDiffOn_snd (fun _ h => h.2)
  simpa only [formInChart_add, formInChart_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply'] using
    h₀.add (contDiffOn_fst.smul h₁)

theorem smoothFormFamily_const {k : ℕ} (eta : M.Form k) (he : M.IsSmoothForm eta) :
    M.IsSmoothFormFamily (fun _ : ℝ => eta) := by
  simpa using smoothFormFamily_affine eta 0 he M.isSmoothForm_zero

theorem first_joint (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T) :
    NativeJoint (firstField P G T hw) := by
  let q := FirstPath.coefficient P G
  apply nativeJoint_of_equation (FirstPath.form P G T) (fun _ => (-1 : ℝ) • q.primitive)
  · exact smoothFormFamily_affine _ _ T.symplectic.1
      (M.isSmoothForm_exteriorDerivative q.primitive q.smooth_primitive)
  · exact smoothFormFamily_const _ (q.smooth_primitive.smul (-1))
  · intro t ht x
    exact FirstPath.nondegenerate P G T hw x ht.1
  · intro t x w
    rw [firstField, FirstPath.X_equation]
    change -SmallCoefficient.k G P.rstar (P.R x) * evalOne P.exactStructure.primitive x w =
      -1 * (SmallCoefficient.k G P.rstar (P.R x) * evalOne P.exactStructure.primitive x w)
    ring

/-- Native smoothness of the auxiliary field is a consequence of the t=0 slice. -/
theorem W_smooth (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T) :
    ContMDiff 𝓘(ℝ, Model d) (𝓘(ℝ, Model d)).tangent ∞
      (fun x => (⟨x, FirstPath.W P G T x⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)) := by
  obtain ⟨E, he, hs⟩ := first_joint P G T hw
  intro x
  have h := (hs (0, x) (by constructor <;> norm_num)).comp x
    (contMDiffAt_const.prodMk contMDiffAt_id)
  apply h.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro y
  have he0 := congrFun (he parameterZero) y
  change E 0 y = FirstPath.X P G T hw y 0 _ at he0
  simp only [Function.comp_def]
  rw [he0, FirstPath.X_zero]

/-- Smooth affine two-form family equal to the actual interpolation differential. -/
def interpolationForm (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (σ : M.Form 1) (t : ℝ) : M.Form 2 :=
  (M.exteriorDerivative σ + M.exteriorDerivative q₀.primitive) +
    t • (M.exteriorDerivative q₁.primitive - M.exteriorDerivative q₀.primitive)

theorem interpolationForm_eq (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ) (t : ℝ) (ht : t ∈ parameterInterval) :
    M.exteriorDerivative (RadialInterpolation.primitive
      (RadialInterpolation.coefficient q₀ q₁ t ht) σ) = interpolationForm P q₀ q₁ σ t := by
  have hp : RadialInterpolation.primitive (RadialInterpolation.coefficient q₀ q₁ t ht) σ =
      σ + ((1-t) • q₀.primitive + t • q₁.primitive) := by
    funext x
    ext vs
    simp only [RadialInterpolation.primitive, RadialCoefficient.primitive,
      LinearAlgebraChecks.radialPrimitive, RadialInterpolation.coefficient,
      RadialInterpolation.rho, Pi.add_apply, Pi.smul_apply,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    ring
  rw [hp, RadialInterpolation.exteriorDerivative_add hσ
    ((q₀.smooth_primitive.smul (1-t)).add (q₁.smooth_primitive.smul t)),
    RadialInterpolation.exteriorDerivative_add (q₀.smooth_primitive.smul (1-t))
      (q₁.smooth_primitive.smul t),
    M.exteriorDerivative_const_smul_one _ q₀.smooth_primitive,
    M.exteriorDerivative_const_smul_one _ q₁.smooth_primitive]
  ext x vs
  simp only [interpolationForm, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.sub_apply, smul_eq_mul]
  ring

theorem interpolation_joint (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ) (hw : RadialInterpolation.WeakDifferential (P := P) σ) :
    NativeJoint (interpolationField P q₀ q₁ σ hσ hw) := by
  apply nativeJoint_of_equation (interpolationForm P q₀ q₁ σ)
    (fun _ => q₀.primitive - q₁.primitive)
  · exact smoothFormFamily_affine _ _
      ((M.isSmoothForm_exteriorDerivative σ hσ).add
        (M.isSmoothForm_exteriorDerivative q₀.primitive q₀.smooth_primitive))
      ((M.isSmoothForm_exteriorDerivative q₁.primitive q₁.smooth_primitive).sub
        (M.isSmoothForm_exteriorDerivative q₀.primitive q₀.smooth_primitive))
  · exact smoothFormFamily_const _ (q₀.smooth_primitive.sub q₁.smooth_primitive)
  · intro t ht x
    rw [← interpolationForm_eq P q₀ q₁ σ hσ t ht]
    exact RadialInterpolation.nondegenerate _ σ hσ hw x
  · intro t x w
    rw [← interpolationForm_eq P q₀ q₁ σ hσ t.val t.property]
    rw [interpolationField, RadialInterpolation.vector_equation]
    change -(q₁.rho (P.R x) - q₀.rho (P.R x)) * evalOne P.exactStructure.primitive x w =
      q₀.rho (P.R x) * evalOne P.exactStructure.primitive x w -
      q₁.rho (P.R x) * evalOne P.exactStructure.primitive x w
    ring

theorem first_intervalSmooth (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T) :
    M.IsSmoothIntervalVectorFieldFamily (firstField P G T hw) := by
  let q := FirstPath.coefficient P G
  apply intervalSmooth_of_equation (FirstPath.form P G T) (fun _ => (-1 : ℝ) • q.primitive)
  · exact smoothFormFamily_affine _ _ T.symplectic.1
      (M.isSmoothForm_exteriorDerivative q.primitive q.smooth_primitive)
  · exact smoothFormFamily_const _ (q.smooth_primitive.smul (-1))
  · intro t ht x
    exact FirstPath.nondegenerate P G T hw x ht.1
  · intro t x w
    rw [firstField, FirstPath.X_equation]
    change -SmallCoefficient.k G P.rstar (P.R x) * evalOne P.exactStructure.primitive x w =
      -1 * (SmallCoefficient.k G P.rstar (P.R x) * evalOne P.exactStructure.primitive x w)
    ring


theorem interpolation_intervalSmooth (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ) (hw : RadialInterpolation.WeakDifferential (P := P) σ) :
    M.IsSmoothIntervalVectorFieldFamily (interpolationField P q₀ q₁ σ hσ hw) := by
  apply intervalSmooth_of_equation (interpolationForm P q₀ q₁ σ)
    (fun _ => q₀.primitive - q₁.primitive)
  · exact smoothFormFamily_affine _ _
      ((M.isSmoothForm_exteriorDerivative σ hσ).add
        (M.isSmoothForm_exteriorDerivative q₀.primitive q₀.smooth_primitive))
      ((M.isSmoothForm_exteriorDerivative q₁.primitive q₁.smooth_primitive).sub
        (M.isSmoothForm_exteriorDerivative q₀.primitive q₀.smooth_primitive))
  · exact smoothFormFamily_const _ (q₀.smooth_primitive.sub q₁.smooth_primitive)
  · intro t ht x
    rw [← interpolationForm_eq P q₀ q₁ σ hσ t ht]
    exact RadialInterpolation.nondegenerate _ σ hσ hw x
  · intro t x w
    rw [← interpolationForm_eq P q₀ q₁ σ hσ t.val t.property]
    rw [interpolationField, RadialInterpolation.vector_equation]
    change -(q₁.rho (P.R x) - q₀.rho (P.R x)) * evalOne P.exactStructure.primitive x w =
      q₀.rho (P.R x) * evalOne P.exactStructure.primitive x w -
      q₁.rho (P.R x) * evalOne P.exactStructure.primitive x w
    ring


end ExactLiouvilleComparison.MoserRegularity
