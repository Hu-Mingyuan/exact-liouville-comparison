import ExactLiouvilleComparison.CylindricalCompatibilityEndAlgebra
import ExactLiouvilleComparison.FiniteTypeRadialMetric
import FsFltz.Geometry.FormScalarDerivative

/-! Identification of the explicit end pairing with the actual exterior
derivative of the completion primitive, at every real end time. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set

namespace ExactLiouvilleComparison.CylindricalCompatibility

variable {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)

/-- A fixed-time boundary slice of the given complete end map. -/
def endSlice (t : ℝ) : D.domain.boundary.SmoothMap C.ambient.manifold :=
  ⟨fun y => C.endMap (y, t), C.smooth_endMap.comp (contMDiff_id.prodMk contMDiff_const)⟩

theorem endSlice_derivative (y : D.domain.boundary.Point) (t : ℝ)
    (v : D.domain.boundary.Tangent y) :
    mfderiv (𝓘(ℝ, Model (d - 1))) (𝓘(ℝ, Model d)) (endSlice C t) y v =
      mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
        C.endMap (y, t) (v, 0) := by
  have hp := (hasMFDerivAt_id (I := 𝓘(ℝ, Model (d - 1))) y).prodMk
    (hasMFDerivAt_const (I := 𝓘(ℝ, Model (d - 1))) (I' := 𝓘(ℝ, ℝ)) t y)
  have hc := (C.smooth_endMap.mdifferentiableAt (by simp)).hasMFDerivAt.comp y hp
  exact congrArg (fun L => L v) hc.mfderiv

/-- The primitive equality is proved as an equality of native forms. -/
theorem endSlice_primitive (t : ℝ) :
    D.domain.boundary.pullback C.ambient.manifold (endSlice C t) C.ambient.primitive =
      fun y => Real.exp t • alpha D y := by
  funext y
  ext vs
  have he := C.end_primitive y t (vs 0) 0
  rw [← endSlice_derivative C y t (vs 0)] at he
  have hv : vs = fun _ : Fin 1 => vs 0 := by
    funext i
    rw [Fin.eq_zero i]
  rw [hv]
  exact he

/-- Tangential part of the actual end two-form, by exterior-derivative
naturality on the boundary slice. -/
theorem end_twoForm_horizontal (y : D.domain.boundary.Point) (t : ℝ)
    (v w : D.domain.boundary.Tangent y) :
    evalTwo (C.ambient.manifold.exteriorDerivative C.ambient.primitive)
      (C.endMap (y, t))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
        C.endMap (y, t) (v, 0))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
        C.endMap (y, t) (w, 0)) =
      Real.exp t * evalTwo (D.domain.boundary.exteriorDerivative (alpha D)) y v w := by
  have hn := D.domain.boundary.exteriorDerivative_pullback C.ambient.manifold
    (endSlice C t) C.ambient.primitive C.ambient.smooth_primitive
  rw [endSlice_primitive C t] at hn
  have he := congrArg (fun η => evalTwo η y v w) hn
  have hα : D.domain.boundary.IsSmoothForm (alpha D) :=
    D.domain.boundary.isSmoothForm_pullback_one D.domain.extension
      D.domain.boundaryInclusion.map D.liouville.primitive D.liouville.smooth_primitive
  rw [D.domain.boundary.evalTwo_exteriorDerivative_smul
    (fun _ => Real.exp t) (alpha D) contMDiff_const hα] at he
  simp only [scalarDerivative, mfderiv_const, zero_apply,
    zero_mul, add_zero, sub_zero] at he
  have hvw : (fun i : Fin 2 => mfderiv (𝓘(ℝ, Model (d - 1))) (𝓘(ℝ, Model d))
      (endSlice C t) y (![v, w] i)) =
      ![mfderiv (𝓘(ℝ, Model (d - 1))) (𝓘(ℝ, Model d)) (endSlice C t) y v,
        mfderiv (𝓘(ℝ, Model (d - 1))) (𝓘(ℝ, Model d)) (endSlice C t) y w] := by
    ext i
    fin_cases i <;> rfl
  change Real.exp t * _ = (C.ambient.manifold.exteriorDerivative C.ambient.primitive
    ((endSlice C t) y)) (fun i => mfderiv _ _ (endSlice C t) y (![v, w] i)) at he
  rw [hvw] at he
  rw [endSlice_derivative C y t v, endSlice_derivative C y t w] at he
  exact he.symm

/-- Mixed part, with the positive Liouville contraction convention. -/
theorem end_twoForm_time (y : D.domain.boundary.Point) (t : ℝ)
    (w : D.domain.boundary.Tangent y × ℝ) :
    evalTwo (C.ambient.manifold.exteriorDerivative C.ambient.primitive)
      (C.endMap (y, t))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
        C.endMap (y, t) (0, 1))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
        C.endMap (y, t) w) =
      Real.exp t * evalOne (alpha D) y w.1 := by
  rw [FiniteTypeRadialMetric.end_time_derivative, C.ambient.contraction]
  exact C.end_primitive y t w.1 w.2

/-- The explicit pairing is literally the native completion form under the
actual end differential; it is not an independently supplied operation. -/
theorem end_twoForm (y : D.domain.boundary.Point) (t : ℝ)
    (z w : D.domain.boundary.Tangent y × ℝ) :
    evalTwo (C.ambient.manifold.exteriorDerivative C.ambient.primitive)
      (C.endMap (y, t))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
        C.endMap (y, t) z)
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
        C.endMap (y, t) w) = ContactData.endPairing y t z w := by
  rcases z with ⟨v, s⟩
  rcases w with ⟨w, u⟩
  let L := mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
    C.endMap (y, t)
  have hs : (v, s) = (v, 0) + s • (0, (1 : ℝ)) := by ext <;> simp
  have hu : (w, u) = (w, 0) + u • (0, (1 : ℝ)) := by ext <;> simp
  have hright : evalTwo (C.ambient.manifold.exteriorDerivative C.ambient.primitive)
      (C.endMap (y, t)) (L (v, 0)) (L (0, 1)) =
      -(Real.exp t * evalOne (alpha D) y v) := by
    rw [evalTwo_swap]
    exact congrArg Neg.neg (end_twoForm_time C y t (v, 0))
  change evalTwo _ _ (L (v, s)) (L (w, u)) = _
  rw [hs, map_add, map_smul, evalTwo_add_left, evalTwo_smul_left]
  rw [show evalTwo _ _ (L (0, 1)) (L (w, u)) = _ from end_twoForm_time C y t (w, u)]
  rw [hu, map_add, map_smul, evalTwo_add_right, evalTwo_smul_right, hright]
  rw [show evalTwo _ _ (L (v, 0)) (L (w, 0)) = _ from end_twoForm_horizontal C y t v w]
  simp [ContactData.endPairing]
  ring

end ExactLiouvilleComparison.CylindricalCompatibility
