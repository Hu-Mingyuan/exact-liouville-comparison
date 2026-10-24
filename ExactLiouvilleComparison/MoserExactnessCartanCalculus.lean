import ExactLiouvilleComparison.MoserExactnessCartanRegularity
import FsFltz.Geometry.LiouvilleFlowPrimitive

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology FsFltz.Geometry FsFltz.Geometry.SmoothManifold
namespace ExactLiouvilleComparison.MoserExactness

/-- The time derivative of a coordinate pullback, with the mixed second derivative
eliminated by symmetry. All derivatives here are actual Fréchet derivatives. -/
theorem coordinate_cartan {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : ℝ × F → F →L[ℝ] ℝ) (g : ℝ × E → F)
    (t : ℝ) (x v : E)
    (ha : ContDiffAt ℝ ∞ a (t, g (t, x)))
    (hg : ContDiffAt ℝ ∞ g (t, x)) :
    HasDerivAt (fun s => a (s, g (s, x)) (fderiv ℝ g (s, x) (0, v)))
      ((fderiv ℝ a (t, g (t, x)) (1, 0)) (fderiv ℝ g (t, x) (0, v)) +
       (fderiv ℝ a (t, g (t, x)) (0, fderiv ℝ g (t, x) (1, 0)))
         (fderiv ℝ g (t, x) (0, v)) -
       (fderiv ℝ a (t, g (t, x)) (0, fderiv ℝ g (t, x) (0, v)))
         (fderiv ℝ g (t, x) (1, 0)) +
       fderiv ℝ (fun y => a (t, g (t, y)) (fderiv ℝ g (t, y) (1, 0))) x v) t := by
  have hdg := hg.differentiableAt (by simp)
  have hddg := (hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hda := ha.differentiableAt (by simp)
  have hG := (hasFDerivAt_fst (𝕜 := ℝ) (p := (t, x))).prodMk hdg.hasFDerivAt
  have hA := hda.hasFDerivAt.comp (t, x) hG
  have hD (w : ℝ × E) := hddg.hasFDerivAt.clm_apply (hasFDerivAt_const w (t, x))
  have hq := (hA.clm_apply (hD (0, v))).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hr := (hA.clm_apply (hD (1, 0))).comp x (hasFDerivAt_prodMk_right t x)
  have hr' := congrArg (fun L => L v) hr.fderiv
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', zero_apply,
    ContinuousLinearMap.inr_apply, map_zero, zero_add] at hr'
  apply hq.congr_deriv
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', zero_apply,
    map_zero, zero_add, Function.comp_def]
  dsimp only [Function.comp_def] at hr'
  rw [hr', (hg.isSymmSndFDerivAt (by simp)).eq (1, 0) (0, v)]
  have hsplit : ((1 : ℝ), fderiv ℝ g (t, x) (1, 0)) =
      (1, (0 : F)) + (0, fderiv ℝ g (t, x) (1, 0)) := by simp
  rw [hsplit, map_add, add_apply]
  ring

/-- Cartan's identity in coordinates, expressed using Mathlib's actual exterior
and time derivatives, before inserting any differential equation. -/
theorem coordinate_cartan_forms {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ℝ × F → F [⋀^Fin 1]→L[ℝ] ℝ) (g : ℝ × E → F)
    (t : ℝ) (x v : E)
    (hA : ContDiffAt ℝ ∞ A (t, g (t, x)))
    (hg : ContDiffAt ℝ ∞ g (t, x)) :
    HasDerivAt (fun s => A (s, g (s, x)) (fun _ => fderiv ℝ g (s, x) (0, v)))
      (deriv (fun u => A (u, g (t, x)) (fun _ => fderiv ℝ g (t, x) (0, v))) t +
       extDeriv (fun y => A (t, y)) (g (t, x))
         ![fderiv ℝ g (t, x) (1, 0), fderiv ℝ g (t, x) (0, v)] +
       fderiv ℝ (fun y => A (t, g (t, y))
         (fun _ => fderiv ℝ g (t, y) (1, 0))) x v) t := by
  let e := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := F) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let a := fun p => e.symm (A p)
  have ha : ContDiffAt ℝ ∞ a (t, g (t, x)) :=
    e.symm.contDiff.contDiffAt.comp _ hA
  have htime := ((ha.differentiableAt (by simp)).hasFDerivAt.clm_apply
    (hasFDerivAt_const (fderiv ℝ g (t, x) (0, v)) (t, g (t, x)))).comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t (g (t, x))))
  have htime' : deriv (fun u => A (u, g (t, x))
      (fun _ => fderiv ℝ g (t, x) (0, v))) t =
      fderiv ℝ a (t, g (t, x)) (1, 0) (fderiv ℝ g (t, x) (0, v)) := by
    convert htime.deriv using 1 <;> simp [a, e, Function.comp_def]
  have hs := ((ha.differentiableAt (by simp)).hasFDerivAt.comp (g (t, x))
    (hasFDerivAt_prodMk_right t (g (t, x))))
  have he := (e.toContinuousLinearMap.hasFDerivAt.comp (g (t, x)) hs).fderiv
  have hcoeff : (fun y => e (a (t, y))) = fun y => A (t, y) := by
    funext y
    exact e.apply_symm_apply _
  change fderiv ℝ (fun y => e (a (t, y))) (g (t, x)) = _ at he
  rw [hcoeff] at he
  have hext : extDeriv (fun y => A (t, y)) (g (t, x))
      ![fderiv ℝ g (t, x) (1, 0), fderiv ℝ g (t, x) (0, v)] =
      fderiv ℝ a (t, g (t, x)) (0, fderiv ℝ g (t, x) (1, 0))
        (fderiv ℝ g (t, x) (0, v)) -
      fderiv ℝ a (t, g (t, x)) (0, fderiv ℝ g (t, x) (0, v))
        (fderiv ℝ g (t, x) (1, 0)) := by
    rw [LiouvilleFlowPrimitive.extDeriv_one_apply, he]
    rfl
  rw [htime', hext]
  convert coordinate_cartan a g t x v ha hg using 1 <;> simp [a, e] <;> ring

end ExactLiouvilleComparison.MoserExactness
