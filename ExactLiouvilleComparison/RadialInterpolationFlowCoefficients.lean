import ExactLiouvilleComparison.RadialInterpolationFlowInputs
import ExactLiouvilleComparison.LargeCoefficient

/-! Actual coefficient applicability for manuscript paths two and four. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter
namespace ExactLiouvilleComparison.RadialInterpolationFlow
variable {d : ℕ} {M : SmoothManifold d}

/-- The constant-one radial coefficient, including the closed-ray derivative. -/
def oneCoefficient (P : RadialReference M) : RadialCoefficient P.rstar where
  rho := fun _ => 1
  smooth := contDiffOn_const
  positive := by intros; norm_num
  constant_core := by intros; rfl
  radial_positive := by intros; simp

/-- The delivered literal A, with its ordinary derivative bridged to the closed ray. -/
def largeCoefficient (P : RadialReference M) (lam : M.Form 1) (hlam : M.IsSmoothForm lam) :
    RadialCoefficient P.rstar where
  rho := LargeCoefficient.A P lam
  smooth := (LargeCoefficient.A_smooth P lam).contDiffOn
  positive := fun r _ => lt_of_lt_of_le zero_lt_one (LargeCoefficient.one_le_A P lam hlam r)
  constant_core := fun r hr => (LargeCoefficient.A_core P lam hr.2).trans
    (LargeCoefficient.A_core P lam P.one_lt_rstar.le).symm
  radial_positive := by
    intro r hr
    have hd := ((LargeCoefficient.A_smooth P lam).differentiable (by simp) r).hasDerivAt
    rw [hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 1 r hr)]
    exact LargeCoefficient.A_radial_pos P lam hlam hr

theorem largeCoefficient_prime (P : RadialReference M) (lam : M.Form 1)
    (hlam : M.IsSmoothForm lam) {r : ℝ} (hr : 1 ≤ r) :
    (largeCoefficient P lam hlam).rhoPrime r = deriv (LargeCoefficient.A P lam) r :=
  ((LargeCoefficient.A_smooth P lam).differentiable (by simp) r).hasDerivAt.hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Ici 1 r hr)

/-- All extra hypotheses of the bridge for path two follow from the delivered k/A.
The primitive's weak taming is its original hypothesis, not strengthened. -/
theorem second_applicable (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T) :
    (∀ r ∈ Ici 1, (FirstPath.coefficient P G).rho r ≤
      (largeCoefficient P T.primitive T.smooth_primitive).rho r) ∧
    Tendsto (fun r => r * (FirstPath.coefficient P G).rho r) atTop atTop ∧
    RadialInterpolation.WeakDifferential (P := P) T.primitive := by
  exact ⟨fun _ hr => LargeCoefficient.k_le_A P T.primitive T.smooth_primitive G hr,
    SmallCoefficient.radius_mul_k_tendsto G P.one_lt_rstar, hw⟩

/-- Path four permits sigma=0 literally and discharges order/divergence for rho0=1. -/
theorem fourth_applicable (P : RadialReference M) (lam : M.Form 1)
    (hlam : M.IsSmoothForm lam) :
    (∀ r ∈ Ici 1, (oneCoefficient P).rho r ≤ (largeCoefficient P lam hlam).rho r) ∧
    Tendsto (fun r => r * (oneCoefficient P).rho r) atTop atTop ∧
    RadialInterpolation.WeakDifferential (P := P) (0 : M.Form 1) := by
  refine ⟨fun r _ => LargeCoefficient.one_le_A P lam hlam r, ?_,
    RadialInterpolationChecks.weak_zero⟩
  change Tendsto (fun r : ℝ => r * 1) atTop atTop
  simp only [mul_one]
  exact tendsto_id

/-- The specialized affine radial coefficient is literally the manuscript expression. -/
theorem second_rho (P : RadialReference M) (G : AdmissibleGrowth 1)
    (lam : M.Form 1) (hlam : M.IsSmoothForm lam) (t r : ℝ) :
    RadialInterpolation.rho (FirstPath.coefficient P G) (largeCoefficient P lam hlam) t r =
      (1-t)*SmallCoefficient.k G P.rstar r + t*LargeCoefficient.A P lam r := rfl

theorem fourth_rho (P : RadialReference M) (lam : M.Form 1)
    (hlam : M.IsSmoothForm lam) (t r : ℝ) :
    RadialInterpolation.rho (oneCoefficient P) (largeCoefficient P lam hlam) t r =
      1 + t*(LargeCoefficient.A P lam r-1) := by
  dsimp [RadialInterpolation.rho, oneCoefficient, largeCoefficient]
  ring
end ExactLiouvilleComparison.RadialInterpolationFlow
