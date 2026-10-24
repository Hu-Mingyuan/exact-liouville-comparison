import ExactLiouvilleComparison.CylindricalCompatibilityContactReebStatement
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set

namespace ExactLiouvilleComparison.CylindricalCompatibility

variable {n : ℕ}

private theorem single_eq_const (v : Model n) : ![v] = (fun _ : Fin 1 => v) := by
  ext i
  fin_cases i
  rfl

theorem augmentedContactOperator_fst
    (a : Model n [⋀^Fin 1]→L[ℝ] ℝ) (b : Model n [⋀^Fin 2]→L[ℝ] ℝ)
    (p : Model n × ℝ) :
    (chartOneFormEquiv n) (augmentedContactOperator a b p).1 =
      b.curryLeft p.1 + p.2 • a := by
  simp [augmentedContactOperator, chartContraction]

theorem augmentedContactOperator_snd
    (a : Model n [⋀^Fin 1]→L[ℝ] ℝ) (b : Model n [⋀^Fin 2]→L[ℝ] ℝ)
    (p : Model n × ℝ) :
    (augmentedContactOperator a b p).2 = a ![p.1] := by
  rw [single_eq_const]
  rfl

/-- Contact nondegeneracy gives invertibility of the augmented operator,
although the two-form itself is degenerate on the full tangent space. -/
theorem augmentedContactOperator_invertible
    (a : Model n [⋀^Fin 1]→L[ℝ] ℝ) (b : Model n [⋀^Fin 2]→L[ℝ] ℝ)
    (ha : ∃ w, a ![w] ≠ 0)
    (hb : ∀ v, a ![v] = 0 → (∀ w, a ![w] = 0 → b ![v, w] = 0) → v = 0) :
    (augmentedContactOperator a b).IsInvertible := by
  have hzero (p : Model n × ℝ) (hp : augmentedContactOperator a b p = 0) : p = 0 := by
    have hv : a ![p.1] = 0 := by
      simpa only [augmentedContactOperator_snd, Prod.snd_zero] using congrArg Prod.snd hp
    have he : b.curryLeft p.1 + p.2 • a = 0 := by
      rw [← augmentedContactOperator_fst, hp]
      simp
    have h1 : p.1 = 0 := by
      apply hb _ hv
      intro w hw
      have h := congrArg (fun c : Model n [⋀^Fin 1]→L[ℝ] ℝ => c ![w]) he
      change b ![p.1, w] + p.2 * a ![w] = 0 at h
      simpa only [hw, mul_zero, add_zero] using h
    have h2 : p.2 = 0 := by
      obtain ⟨w, hw⟩ := ha
      have h := congrArg (fun c : Model n [⋀^Fin 1]→L[ℝ] ℝ => c ![w]) he
      change b ![p.1, w] + p.2 * a ![w] = 0 at h
      have hz : b ![(0 : Model n), w] = 0 := by
        exact b.map_coord_zero 0 rfl
      rw [h1, hz, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_right hw
    exact Prod.ext h1 h2
  have hinj : Function.Injective (augmentedContactOperator a b) := by
    intro p q hpq
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hpq, sub_self]
  exact ⟨ContinuousLinearEquiv.ofBijective (augmentedContactOperator a b)
    (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr (LinearMap.surjective_of_injective hinj)), rfl⟩

theorem augmentedContactOperator_inverse_equations
    (a : Model n [⋀^Fin 1]→L[ℝ] ℝ) (b : Model n [⋀^Fin 2]→L[ℝ] ℝ)
    (hi : (augmentedContactOperator a b).IsInvertible) :
    let p := (augmentedContactOperator a b).inverse (0, 1)
    a ![p.1] = 1 ∧ p.2 = 0 ∧ ∀ w, b ![p.1, w] = 0 := by
  dsimp only
  let p := (augmentedContactOperator a b).inverse (0, 1)
  have hp : augmentedContactOperator a b p = (0, 1) := hi.self_apply_inverse _
  have hn : a ![p.1] = 1 := by
    simpa only [augmentedContactOperator_snd, Prod.snd_zero] using congrArg Prod.snd hp
  have he : b.curryLeft p.1 + p.2 • a = 0 := by
    rw [← augmentedContactOperator_fst, hp]
    simp
  have hs : p.2 = 0 := by
    have h := congrArg (fun c : Model n [⋀^Fin 1]→L[ℝ] ℝ => c ![p.1]) he
    change b ![p.1, p.1] + p.2 * a ![p.1] = 0 at h
    have hz : b ![p.1, p.1] = 0 :=
      b.map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
    simpa only [hz, hn, mul_one, zero_add] using h
  refine ⟨hn, hs, ?_⟩
  intro w
  have h := congrArg (fun c : Model n [⋀^Fin 1]→L[ℝ] ℝ => c ![w]) he
  change b ![p.1, w] + p.2 * a ![w] = 0 at h
  simpa only [hs, zero_mul, add_zero] using h

variable {d : ℕ}

/-- The canonical actual boundary Reeb candidate, defined by native finite-dimensional inversion. -/
def boundaryReeb (D : LiouvilleDomain d) (y : D.domain.boundary.Point) :
    D.domain.boundary.Tangent y :=
  ((augmentedContactOperator (alpha D y)
    (D.domain.boundary.exteriorDerivative (alpha D) y)).inverse (0, 1)).1

theorem boundary_augmented_invertible (D : LiouvilleDomain d) (y : D.domain.boundary.Point) :
    (augmentedContactOperator (alpha D y)
      (D.domain.boundary.exteriorDerivative (alpha D) y)).IsInvertible := by
  apply augmentedContactOperator_invertible (n := d - 1)
  · obtain ⟨v, hv⟩ := D.liouville.boundaryForm_exists_eval_ne_zero y
    refine ⟨v, ?_⟩
    rw [single_eq_const]
    exact hv
  · intro v hv hh
    apply D.liouville.boundaryForm_differential_nondegenerate_on_kernel y v
    · rw [single_eq_const] at hv
      exact hv
    · intro w hw
      apply hh w
      rw [single_eq_const]
      exact hw

theorem boundaryReeb_normalized (D : LiouvilleDomain d) (y : D.domain.boundary.Point) :
    evalOne (alpha D) y (boundaryReeb D y) = 1 := by
  have h := (augmentedContactOperator_inverse_equations (n := d - 1) _ _
    (boundary_augmented_invertible D y)).1
  rw [single_eq_const] at h
  exact h

theorem boundaryReeb_kernel (D : LiouvilleDomain d) (y : D.domain.boundary.Point)
    (v : D.domain.boundary.Tangent y) :
    evalTwo (D.domain.boundary.exteriorDerivative (alpha D)) y (boundaryReeb D y) v = 0 :=
  (augmentedContactOperator_inverse_equations (n := d - 1) _ _ (boundary_augmented_invertible D y)).2.2 v

end ExactLiouvilleComparison.CylindricalCompatibility
