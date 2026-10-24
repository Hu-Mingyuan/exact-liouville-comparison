import ExactLiouvilleComparison.LinearAlgebraChecks
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! Coefficients on the closed half-line. No extension to the left is assumed. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter
namespace ExactLiouvilleComparison

/-- The hypotheses of manuscript Lemma `lem:metric`, with the actual within derivative. -/
structure RadialCoefficient (rstar : ℝ) where
  rho : ℝ → ℝ
  smooth : ContDiffOn ℝ ∞ rho (Ici 1)
  positive : ∀ r ∈ Ici 1, 0 < rho r
  constant_core : ∀ r ∈ Icc 1 rstar, rho r = rho 1
  radial_positive : ∀ r ∈ Ici 1, 0 < rho r + r * derivWithin rho (Ici 1) r

namespace RadialCoefficient
variable {d : ℕ} {M : SmoothManifold d} {P : RadialReference M}
variable (q : RadialCoefficient P.rstar)

def rhoPrime (r : ℝ) : ℝ := derivWithin q.rho (Ici 1) r

/-- Away from the lower endpoint this is the ordinary derivative. -/
theorem rhoPrime_eq_deriv {r : ℝ} (hr : 1 < r) : q.rhoPrime r = deriv q.rho r :=
  derivWithin_of_mem_nhds (Ici_mem_nhds hr)

theorem hasDerivWithinAt {r : ℝ} (hr : 1 ≤ r) :
    HasDerivWithinAt q.rho (q.rhoPrime r) (Ici 1) r :=
  (q.smooth.differentiableOn (by simp) r hr).hasDerivWithinAt

/-- Includes both endpoints; uniqueness on the nontrivial closed core interval
compares the restricted half-line derivative with the derivative of a constant. -/
theorem rhoPrime_eq_zero {r : ℝ} (hr : r ∈ Icc 1 P.rstar) : q.rhoPrime r = 0 := by
  have hq := (q.hasDerivWithinAt hr.1).mono (Icc_subset_Ici_self :
    Icc (1 : ℝ) P.rstar ⊆ Ici 1)
  have hc : HasDerivWithinAt q.rho 0 (Icc 1 P.rstar) r :=
    (hasDerivWithinAt_const r (Icc 1 P.rstar) (q.rho 1)).congr_of_mem
      (fun y hy => q.constant_core y hy) hr
  exact (hq.derivWithin (uniqueDiffOn_Icc P.one_lt_rstar r hr)).symm.trans
    (hc.derivWithin (uniqueDiffOn_Icc P.one_lt_rstar r hr))

/-- The scalar composition is globally smooth on the manifold, including `R=1`. -/
theorem smooth_comp :
    ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ (q.rho ∘ P.R) := by
  rw [← contMDiffOn_univ]
  intro x _
  exact (q.smooth (P.R x) (P.lower_R x)).comp_contMDiffWithinAt
    (P.smooth_R x).contMDiffWithinAt (fun y _ => P.lower_R y)

/-- The native differential chain rule uses the half-line derivative even at
its lower endpoint, since the entire range of `R` lies in that half-line. -/
theorem scalarDerivative_comp (x : M.Point) (v : M.Tangent x) :
    M.scalarDerivative (q.rho ∘ P.R) x v =
      q.rhoPrime (P.R x) * M.scalarDerivative P.R x v := by
  have h := (q.hasDerivWithinAt (P.lower_R x)).hasFDerivWithinAt.hasMFDerivWithinAt.comp x
    (P.smooth_R.mdifferentiable (by simp) x).hasMFDerivAt.hasMFDerivWithinAt
    (fun y (_ : y ∈ (univ : Set M.Point)) => P.lower_R y)
  have he := h.mfderivWithin (uniqueMDiffWithinAt_univ (I := 𝓘(ℝ, Model d)))
  rw [mfderivWithin_univ] at he
  change mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) (q.rho ∘ P.R) x v = _
  rw [he]
  change M.scalarDerivative P.R x v * q.rhoPrime (P.R x) = _
  ring

/-- Derivative composition is also smooth; no arbitrary chart norm is involved. -/
theorem smooth_prime_comp :
    ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ (q.rhoPrime ∘ P.R) := by
  rw [← contMDiffOn_univ]
  intro x _
  exact ((q.smooth.derivWithin (uniqueDiffOn_Ici (1 : ℝ)) (by simp))
    (P.R x) (P.lower_R x)).comp_contMDiffWithinAt
    (P.smooth_R x).contMDiffWithinAt (fun y _ => P.lower_R y)

end RadialCoefficient
end ExactLiouvilleComparison
