import ExactLiouvilleComparison.MoserRegularityGlobal

/-! Generic consumers expose the original vectors and hypotheses literally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.MoserRegularityChecks
open MoserRegularity
variable {d : ℕ} {M : SmoothManifold d}

theorem inverse_is_existing_first (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    (x : M.Point) (t : ℝ) (ht : 0 ≤ t) :
    solve (FirstPath.form P G T t) ((-1 : ℝ) • (FirstPath.coefficient P G).primitive) x =
      FirstPath.X P G T hw x t ht := by
  apply FirstPath.X_unique P G T hw x t ht
  intro w
  rw [solve_equation _ _ x (FirstPath.nondegenerate P G T hw x ht)]
  change -1 * (SmallCoefficient.k G P.rstar (P.R x) * evalOne P.exactStructure.primitive x w) = _
  ring

theorem inverse_is_existing_interpolation (P : RadialReference M)
    (q₀ q₁ : RadialCoefficient P.rstar) (σ : M.Form 1) (hσ : M.IsSmoothForm σ)
    (hw : RadialInterpolation.WeakDifferential (P := P) σ) (t : Parameter) (x : M.Point) :
    solve (interpolationForm P q₀ q₁ σ t.val) (q₀.primitive - q₁.primitive) x =
      RadialInterpolation.vector (RadialInterpolation.coefficient q₀ q₁ t.val t.property)
        σ hσ hw (RadialInterpolation.delta q₀ q₁) x := by
  apply RadialInterpolation.vector_unique _ σ hσ hw (RadialInterpolation.delta q₀ q₁) x
  rw [interpolationForm_eq P q₀ q₁ σ hσ t.val t.property]
  intro w
  have hn : M.Nondegenerate (interpolationForm P q₀ q₁ σ t.val) x := by
    rw [← interpolationForm_eq P q₀ q₁ σ hσ t.val t.property]
    exact RadialInterpolation.nondegenerate _ σ hσ hw x
  rw [solve_equation _ _ x hn]
  change q₀.rho (P.R x) * evalOne P.exactStructure.primitive x w -
      q₁.rho (P.R x) * evalOne P.exactStructure.primitive x w =
      -(q₁.rho (P.R x) - q₀.rho (P.R x)) * evalOne P.exactStructure.primitive x w
  ring

theorem first_actual (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    {C : ℝ} (hC : 0 < C) (K : Set M.Point) (hK : IsCompact K)
    (hb : ∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * G.B (P.R x)) :
    NativeJoint (fun t x => FirstPath.X P G T hw x t.val t.property.1) ∧
    M.IsSmoothIntervalVectorFieldFamily (fun t x => FirstPath.X P G T hw x t.val t.property.1) ∧
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : Parameter, ∀ x,
      |M.scalarDerivative (fun y => Real.log (SmallCoefficient.S G (P.R y))) x
        (FirstPath.X P G T hw x t.val t.property.1)| ≤ D :=
  ⟨first_joint P G T hw, first_intervalSmooth P G T hw, first_global P G T hw hC K hK hb⟩

theorem interpolation_actual (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (horder : ∀ r ∈ Ici 1, q₀.rho r ≤ q₁.rho r)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ) (hw : RadialInterpolation.WeakDifferential (P := P) σ) :
    NativeJoint (fun t x => RadialInterpolation.vector
      (RadialInterpolation.coefficient q₀ q₁ t.val t.property) σ hσ hw
        (fun r => q₁.rho r - q₀.rho r) x) ∧
    ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ t : Parameter, ∀ x,
      M.scalarDerivative P.R x (RadialInterpolation.vector
        (RadialInterpolation.coefficient q₀ q₁ t.val t.property) σ hσ hw
          (fun r => q₁.rho r - q₀.rho r) x) ≤ C₀ ∧
      -C₁ ≤ barrierRate P q₀ q₁ (interpolationField P q₀ q₁ σ hσ hw) t x :=
  ⟨interpolation_joint P q₀ q₁ σ hσ hw, interpolation_global P q₀ q₁ horder σ hσ hw⟩

theorem zero_parameter (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T) (x : M.Point) :
    firstField P G T hw parameterZero x = FirstPath.W P G T x :=
  FirstPath.X_zero P G T hw x

theorem degenerate_sigma (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar) :
    NativeJoint (interpolationField P q₀ q₁ 0 M.isSmoothForm_zero RadialInterpolationChecks.weak_zero) :=
  interpolation_joint P q₀ q₁ 0 M.isSmoothForm_zero RadialInterpolationChecks.weak_zero

end ExactLiouvilleComparison.MoserRegularityChecks
