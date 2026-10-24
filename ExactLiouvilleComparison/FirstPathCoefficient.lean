import ExactLiouvilleComparison.SmallCoefficientAsymptotic
import ExactLiouvilleComparison.RadialMetricChecks

/-! The delivered small coefficient, with no additional coefficient hypotheses. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.FirstPath
variable {d : ℕ} {M : SmoothManifold d}
open SmallCoefficient

def coefficient (P : RadialReference M) (G : AdmissibleGrowth 1) :
    RadialCoefficient P.rstar where
  rho := k G P.rstar
  smooth := k_smooth G P.rstar
  positive := fun r _ => k_pos G P.rstar r
  constant_core := fun _r hr =>
    (k_eq_one G hr.1 hr.2).trans (k_eq_one G le_rfl P.one_lt_rstar.le).symm
  radial_positive := fun _r hr => m_pos G P.rstar hr

theorem coefficient_rhoPrime (P : RadialReference M) (G : AdmissibleGrowth 1) (r : ℝ) :
    (coefficient P G).rhoPrime r = kprime G P.rstar r := rfl

theorem coefficient_radial (P : RadialReference M) (G : AdmissibleGrowth 1) (r : ℝ) :
    (coefficient P G).rho r + r * (coefficient P G).rhoPrime r = m G P.rstar r := rfl

theorem metric_bounds (P : RadialReference M) (G : AdmissibleGrowth 1)
    (x : M.Point) (v : M.Tangent x) :
    m G P.rstar (P.R x) * P.compatible.g.inner x v v ≤
      (coefficient P G).compatible.g.inner x v v ∧
    (coefficient P G).compatible.g.inner x v v ≤
      k G P.rstar (P.R x) * P.compatible.g.inner x v v :=
  RadialMetricChecks.decreasing_metric_bounds P (coefficient P G)
    (fun _ hr => kprime_nonpos G P.rstar hr) x v

end ExactLiouvilleComparison.FirstPath
