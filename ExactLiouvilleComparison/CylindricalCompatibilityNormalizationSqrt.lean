import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationSqrtSylvester

noncomputable section
open scoped MatrixOrder Matrix.Norms.L2Operator ContDiff Topology
open Filter

namespace ExactLiouvilleComparison.NormalizationSqrt
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The native square root is smooth relative to the positive-definite cone.
The local smooth extension is the inverse of ambient squaring, not ambient CFC.sqrt. -/
theorem contDiffOn_sqrt_posDef :
    ContDiffOn ℝ ∞ (CFC.sqrt : Matrix n n ℝ → Matrix n n ℝ) {A | A.PosDef} := by
  intro A hA
  let S := CFC.sqrt A
  have hS : S.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt A hA.isStrictlyPositive)
  let q := fun B : Matrix n n ℝ => B * B
  have hq : ContDiffAt ℝ ∞ q S := (contDiff_id.mul contDiff_id).contDiffAt
  have hd : HasFDerivAt q (sylvesterEquiv hS : _ →L[ℝ] _) S := hasFDerivAt_sq S
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hsq : q S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hinv := hq.to_localInverse hd hn
  rw [hsq] at hinv
  have hcont : ContinuousWithinAt CFC.sqrt {B : Matrix n n ℝ | B.PosDef} A :=
    (CFC.continuousOn_sqrt A hA.posSemidef.nonneg).mono
      (fun _ hB => hB.posSemidef.nonneg)
  have heq : ∀ᶠ B in 𝓝[{B : Matrix n n ℝ | B.PosDef}] A,
      hq.localInverse hd hn B = CFC.sqrt B := by
    have he := hcont (hq.hasStrictFDerivAt' hd hn).eventually_left_inverse
    filter_upwards [he, self_mem_nhdsWithin] with B hB hpos
    change hq.localInverse hd hn (q (CFC.sqrt B)) = CFC.sqrt B at hB
    rwa [show q (CFC.sqrt B) = B from CFC.sqrt_mul_sqrt_self B hpos.posSemidef.nonneg] at hB
  exact hinv.contDiffWithinAt.congr_of_eventuallyEq_of_mem (Filter.EventuallyEq.symm heq) hA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smooth square-root composition on arbitrary parameter subsets. -/
theorem contDiffOn_sqrt_comp {f : E → Matrix n n ℝ} {s : Set E}
    (hf : ContDiffOn ℝ ∞ f s) (hp : ∀ x ∈ s, (f x).PosDef) :
    ContDiffOn ℝ ∞ (fun x => CFC.sqrt (f x)) s :=
  contDiffOn_sqrt_posDef.comp hf hp

/-- Smooth inverse square-root composition; positivity proves the needed unit condition. -/
theorem contDiffOn_inverse_sqrt_comp {f : E → Matrix n n ℝ} {s : Set E}
    (hf : ContDiffOn ℝ ∞ f s) (hp : ∀ x ∈ s, (f x).PosDef) :
    ContDiffOn ℝ ∞ (fun x => Ring.inverse (CFC.sqrt (f x))) s := by
  intro x hx
  have hu := (CFC.isUnit_sqrt_iff (f x) (hp x hx).posSemidef.nonneg).mpr (hp x hx).isUnit
  obtain ⟨u, hu⟩ := hu
  have hi : ContDiffAt ℝ ∞ Ring.inverse (CFC.sqrt (f x)) :=
    hu ▸ contDiffAt_ringInverse ℝ u
  exact hi.comp_contDiffWithinAt x (contDiffOn_sqrt_comp hf hp x hx)

/-- Global smooth families, including families of zero-by-zero matrices. -/
theorem contDiff_sqrt_comp {f : E → Matrix n n ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : ∀ x, (f x).PosDef) :
    ContDiff ℝ ∞ (fun x => CFC.sqrt (f x)) := by
  rw [← contDiffOn_univ]
  exact contDiffOn_sqrt_comp hf.contDiffOn (fun x _ => hp x)

theorem contDiff_inverse_sqrt_comp {f : E → Matrix n n ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : ∀ x, (f x).PosDef) :
    ContDiff ℝ ∞ (fun x => Ring.inverse (CFC.sqrt (f x))) := by
  rw [← contDiffOn_univ]
  exact contDiffOn_inverse_sqrt_comp hf.contDiffOn (fun x _ => hp x)

theorem relative_sqrt_contract : RelativeSqrtContract n := contDiffOn_sqrt_posDef

theorem sqrt_composition_contract : SqrtCompositionContract n E :=
  fun _ _ => contDiffOn_sqrt_comp

theorem inverse_sqrt_composition_contract : InverseSqrtCompositionContract n E :=
  fun _ _ => contDiffOn_inverse_sqrt_comp

end ExactLiouvilleComparison.NormalizationSqrt
