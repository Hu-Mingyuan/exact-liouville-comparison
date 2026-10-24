import ExactLiouvilleComparison.SteinRadialStatement
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! The literal Stein exhaustion and its bound in the prescribed induced metric. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter

namespace ExactLiouvilleComparison.SteinRadial

variable {d N : ℕ} {M : SmoothManifold d} (i : ProperComplexEmbedding M N)

theorem radius_smooth :
    ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ (steinRadius i) := by
  exact contMDiff_const.add ((contDiff_norm_sq ℝ).contMDiff.comp i.smooth)

theorem radius_proper : IsProperMap (steinRadius i) := by
  have h : IsProperMap (fun z : EuclideanSpace ℂ (Fin N) => Real.exp 1 + ‖z‖ ^ 2) := by
    apply isProperMap_iff_tendsto_cocompact.mpr
    refine ⟨continuous_const.add (continuous_norm.pow 2), ?_⟩
    apply Tendsto.mono_right _ atTop_le_cocompact
    exact tendsto_atTop_add_const_left _ _
      ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_norm_cocompact_atTop)
  exact h.comp i.proper

theorem radius_lower (x : M.Point) : 1 ≤ steinRadius i x := by
  have he := Real.add_one_le_exp (1 : ℝ)
  dsimp [steinRadius]
  nlinarith [sq_nonneg ‖i.map x‖]

/-- The derivative uses the real inner product on complex Euclidean space. -/
theorem radius_derivative (x : M.Point) (v : M.Tangent x) :
    mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) (steinRadius i) x v =
      2 * inner ℝ (i.map x)
        (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x v) := by
  have hi : MDifferentiableAt (𝓘(ℝ, Model d))
      (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x :=
    i.smooth.mdifferentiableAt (by simp)
  have hn := ((hasStrictFDerivAt_norm_sq (i.map x)).hasFDerivAt.const_add
    (Real.exp 1)).hasMFDerivAt.comp x hi.hasMFDerivAt
  rw [show steinRadius i =
    (fun z : EuclideanSpace ℂ (Fin N) => Real.exp 1 + ‖z‖ ^ 2) ∘ i.map from rfl,
    hn.mfderiv]
  change (2 : ℕ) • (inner ℝ (i.map x)
    (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x v) : ℝ) =
      (2 : ℝ) * inner ℝ (i.map x)
        (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x v)
  simp only [two_smul, two_mul]

variable (P : SteinReference i)

/-- The metric norm is identified by the given metric, not the chart norm. -/
theorem metric_norm_eq (x : M.Point) (v : P.compatible.MetricTangent x) :
    ‖v‖ = ‖(show EuclideanSpace ℂ (Fin N) from mfderiv (𝓘(ℝ, Model d))
      (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x v)‖ := by
  change Real.sqrt (P.compatible.g.inner x v v) = _
  erw [P.induced_metric, real_inner_self_eq_norm_sq]
  exact Real.sqrt_sq (norm_nonneg _)

theorem radius_dualNorm_le (x : M.Point) :
    P.compatible.dualNorm x
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) (steinRadius i) x) ≤ 2 * ‖i.map x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖(show ℝ from mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ))
    (steinRadius i) x v)‖ ≤ 2 * ‖i.map x‖ * ‖v‖
  erw [radius_derivative]
  erw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), metric_norm_eq i P]
  calc
    2 * ‖inner ℝ (i.map x) _‖ ≤
        2 * (‖i.map x‖ * ‖(show EuclideanSpace ℂ (Fin N) from mfderiv (𝓘(ℝ, Model d))
          (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x v)‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
    _ = _ := by ring

theorem radius_dualNorm_sq (x : M.Point) :
    (P.compatible.dualNorm x
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) (steinRadius i) x)) ^ 2 ≤
      4 * (steinRadius i x - Real.exp 1) := by
  have h := radius_dualNorm_le i P x
  have hn : 0 ≤ P.compatible.dualNorm x
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) (steinRadius i) x) := norm_nonneg _
  have hs := mul_self_le_mul_self hn h
  dsimp [steinRadius]
  nlinarith

theorem radial_identity (x : M.Point) (v : M.Tangent x) :
    evalOne P.exactStructure.primitive x v =
      -(1 / 4 : ℝ) * M.scalarDerivative (steinRadius i) x (P.compatible.J x v) := by
  simpa only [P.complex_eq] using P.primitive_eq x v

theorem radial_bound (x : M.Point) :
    (1 / 4 : ℝ) * (P.compatible.dualNorm x
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) (steinRadius i) x)) ^ 2 ≤ steinRadius i x := by
  have h := radius_dualNorm_sq i P x
  have he := Real.exp_pos (1 : ℝ)
  linarith

/-- Every field of the unchanged radial reference is discharged. -/
def reference : RadialReference M where
  exactStructure := P.exactStructure
  compatible := P.compatible
  R := steinRadius i
  smooth_R := radius_smooth i
  proper_R := radius_proper i
  lower_R := radius_lower i
  c := 1 / 4
  positive_c := by norm_num
  rstar := 2
  one_lt_rstar := by norm_num
  radial_identity := fun x _ v => radial_identity i P x v
  radial_bound := fun x _ => radial_bound i P x

theorem reference_exactStructure : (reference i P).exactStructure = P.exactStructure := rfl
theorem reference_compatible : (reference i P).compatible = P.compatible := rfl
theorem reference_radius : (reference i P).R = steinRadius i := rfl
theorem reference_c : (reference i P).c = (1 / 4 : ℝ) := rfl
theorem reference_rstar : (reference i P).rstar = 2 := rfl

theorem target : Target := by
  intro d N M i P
  exact ⟨radius_smooth i, radius_proper i, radius_lower i, radius_dualNorm_sq i P,
    reference i P, rfl, HEq.rfl, rfl, rfl, rfl⟩

end ExactLiouvilleComparison.SteinRadial
