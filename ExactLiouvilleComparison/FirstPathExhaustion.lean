import ExactLiouvilleComparison.FirstPathCoefficient
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter
namespace ExactLiouvilleComparison.FirstPath
variable {d : ℕ} {M : SmoothManifold d}
open SmallCoefficient

def exhaustion (P : RadialReference M) (G : AdmissibleGrowth 1) (x : M.Point) : ℝ :=
  Real.log (S G (P.R x))

theorem exhaustion_smooth (P : RadialReference M) (G : AdmissibleGrowth 1) :
    ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ (exhaustion P G) := by
  have hs := (S_smooth G).log (fun r hr => (S_pos G hr).ne')
  rw [← contMDiffOn_univ]
  intro x _
  exact (hs (P.R x) (P.lower_R x)).comp_contMDiffWithinAt
    (P.smooth_R x).contMDiffWithinAt (fun y _ => P.lower_R y)

theorem exhaustion_nonneg (P : RadialReference M) (G : AdmissibleGrowth 1) (x : M.Point) :
    0 ≤ exhaustion P G x := Real.log_nonneg (one_le_S G (P.lower_R x))

theorem exhaustion_bddBelow (P : RadialReference M) (G : AdmissibleGrowth 1) :
    BddBelow (range (exhaustion P G)) :=
  ⟨0, by rintro _ ⟨x, rfl⟩; exact exhaustion_nonneg P G x⟩

theorem exhaustion_derivative (P : RadialReference M) (G : AdmissibleGrowth 1)
    (x : M.Point) (v : M.Tangent x) :
    M.scalarDerivative (exhaustion P G) x v =
      (density G (P.R x) / S G (P.R x)) * M.scalarDerivative P.R x v := by
  have h := (log_S_hasDerivWithinAt G (P.lower_R x)).hasFDerivWithinAt.hasMFDerivWithinAt.comp x
    (P.smooth_R.mdifferentiable (by simp) x).hasMFDerivAt.hasMFDerivWithinAt
    (fun y (_ : y ∈ (univ : Set M.Point)) => P.lower_R y)
  have he := h.mfderivWithin (uniqueMDiffWithinAt_univ (I := 𝓘(ℝ, Model d)))
  rw [mfderivWithin_univ] at he
  change mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) (exhaustion P G) x v = _
  rw [show exhaustion P G = (fun r => Real.log (S G r)) ∘ P.R from rfl, he]
  change M.scalarDerivative P.R x v * _ = _
  ring

theorem exhaustion_proper (P : RadialReference M) (G : AdmissibleGrowth 1) :
    IsProperMap (exhaustion P G) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨(exhaustion_smooth P G).continuous, ?_⟩
  intro K hK
  obtain ⟨b, hb⟩ := hK.bddAbove
  obtain ⟨a, ha⟩ := (tendsto_atTop_atTop.mp (log_S_tendsto G)) (b + 1)
  apply (P.proper_R.isCompact_preimage (isCompact_Icc (a := 1) (b := a))).of_isClosed_subset
    (hK.isClosed.preimage (exhaustion_smooth P G).continuous)
  intro x hx
  refine ⟨P.lower_R x, ?_⟩
  by_contra hn
  have h := ha (P.R x) (le_of_lt (lt_of_not_ge hn))
  have hu := hb hx
  change exhaustion P G x ≤ b at hu
  change b + 1 ≤ exhaustion P G x at h
  linarith

end ExactLiouvilleComparison.FirstPath
