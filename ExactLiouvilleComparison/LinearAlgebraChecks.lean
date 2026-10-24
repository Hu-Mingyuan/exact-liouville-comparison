import ExactLiouvilleComparison.LinearAlgebra
import ExactLiouvilleComparison.Statement

/-! First-path consumer. Radial compatibility is an explicit input for its later
owner to prove; this file constructs pointwise solutions and proves their estimate. -/
noncomputable section
open scoped Manifold ContDiff InnerProductSpace
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.LinearAlgebraChecks
variable {d : ℕ} {M : SmoothManifold d}

/-- The actual first-path primitive `k(R) beta`. -/
def radialPrimitive (P : RadialReference M) (k : ℝ → ℝ) : M.Form 1 :=
  fun x => k (P.R x) • P.exactStructure.primitive x

/-- The compatible metric of the radial form is explicitly `h`, not the original `g`. -/
theorem radial_metric_norm (P : RadialReference M) (k : ℝ → ℝ)
    (H : ExactSymplecticStructure M) (hH : H.primitive = radialPrimitive P k)
    (A : CompatibleStructure H) (hJ : ∀ x, A.J x = P.compatible.J x)
    (x : M.Point) (v : A.MetricTangent x) :
    ‖v‖ = Real.sqrt (evalTwo (M.exteriorDerivative (radialPrimitive P k)) x v
      (P.compatible.J x v)) := by
  rw [A.tangent_norm_eq, hH, hJ]

/-- Actual covector `-k(R) beta`, transported to the compatible metric fiber. -/
def firstPathCovector (P : RadialReference M) (k : ℝ → ℝ)
    {H : ExactSymplecticStructure M} (A : CompatibleStructure H) (x : M.Point) : A.Dual x :=
  A.covector x ((ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model d) (F := ℝ) (0 : Fin 1)).symm
      (-k (P.R x) • P.exactStructure.primitive x))

theorem firstPathCovector_apply (P : RadialReference M) (k : ℝ → ℝ)
    {H : ExactSymplecticStructure M} (A : CompatibleStructure H)
    (x : M.Point) (v : A.MetricTangent x) :
    firstPathCovector P k A x v = -k (P.R x) * evalOne P.exactStructure.primitive x v := by
  rfl

/-- For every nonnegative parameter, the first-path form is nondegenerate and
there are actual pointwise solutions to both contraction equations, with the
required `h`-norm estimate. This asserts no flow or smoothness of these solutions. -/
theorem first_path_linear_estimate (P : RadialReference M) (k : ℝ → ℝ)
    (H : ExactSymplecticStructure M) (hH : H.primitive = radialPrimitive P k)
    (A : CompatibleStructure H) (hJ : ∀ x, A.J x = P.compatible.J x)
    (T : ExactSymplecticStructure M) (hweak : WeaklyTames P.compatible T)
    (x : M.Point) {t : ℝ} (ht : 0 ≤ t) :
    M.Nondegenerate (M.exteriorDerivative T.primitive +
      t • M.exteriorDerivative (radialPrimitive P k)) x ∧
    ∃ X W : A.MetricTangent x,
      (∀ v, evalTwo (M.exteriorDerivative T.primitive) x W v =
        -k (P.R x) * evalOne P.exactStructure.primitive x v) ∧
      (∀ v, evalTwo (M.exteriorDerivative T.primitive +
        t • M.exteriorDerivative (radialPrimitive P k)) x X v =
        -k (P.R x) * evalOne P.exactStructure.primitive x v) ∧
      ‖X‖ ≤ ‖W‖ := by
  have hnd := T.symplectic.2.2 x (Set.mem_univ x)
  have hw : ∀ v, 0 ≤ evalTwo (M.exteriorDerivative T.primitive) x v (A.J x v) := by
    intro v
    rw [hJ]
    exact hweak x v
  have hn := A.weak_taming_nondegenerate (M.exteriorDerivative T.primitive) x hnd hw ht
  let l := firstPathCovector P k A x
  let X := A.inverseContraction (M.exteriorDerivative T.primitive +
    t • M.exteriorDerivative H.primitive) x hn l
  let W := A.inverseContraction (M.exteriorDerivative T.primitive) x hnd l
  refine ⟨by simpa only [hH] using hn, X, W, ?_, ?_, ?_⟩
  · intro v
    exact A.inverseContraction_equation _ x hnd l v
  · intro v
    have hx : evalTwo (M.exteriorDerivative T.primitive +
        t • M.exteriorDerivative H.primitive) x X v =
        -k (P.R x) * evalOne P.exactStructure.primitive x v :=
      A.inverseContraction_equation _ x hn l v
    simpa only [hH] using hx
  · exact A.inverseContraction_norm_le _ x hnd hw ht l

/-- Explicit zero-parameter consumer: nondegeneracy is not obtained by strict taming. -/
theorem zero_parameter (P : RadialReference M) (k : ℝ → ℝ)
    (H : ExactSymplecticStructure M) (hH : H.primitive = radialPrimitive P k)
    (A : CompatibleStructure H) (hJ : ∀ x, A.J x = P.compatible.J x)
    (T : ExactSymplecticStructure M) (hweak : WeaklyTames P.compatible T)
    (x : M.Point) :
    ∃ X W : A.MetricTangent x,
      (∀ v, evalTwo (M.exteriorDerivative T.primitive) x W v =
        -k (P.R x) * evalOne P.exactStructure.primitive x v) ∧
      (∀ v, evalTwo (M.exteriorDerivative T.primitive) x X v =
        -k (P.R x) * evalOne P.exactStructure.primitive x v) ∧ ‖X‖ ≤ ‖W‖ := by
  simpa using (first_path_linear_estimate P k H hH A hJ T hweak x (t := 0) le_rfl).2

end ExactLiouvilleComparison.LinearAlgebraChecks
