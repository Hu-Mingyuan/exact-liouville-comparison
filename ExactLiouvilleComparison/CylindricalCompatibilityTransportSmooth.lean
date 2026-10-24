import ExactLiouvilleComparison.CylindricalCompatibilityEndTransport
import FsFltz.Geometry.CompletionCollar
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! Smoothness of native endomorphism transport through an actual local diffeomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Bundle Set Filter ContinuousLinearMap

namespace ExactLiouvilleComparison.CylindricalCompatibility

section Transport
variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [TopologicalSpace G]
  (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ F G)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold I' ∞ N]

/-- Conjugation by the genuine derivative, using the native totalized inverse.
Invertibility will be proved at every point where the end construction uses it. -/
def transportEndomorphism (f : M → N)
    (J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x) (x : M) :
    TangentSpace I' (f x) →L[ℝ] TangentSpace I' (f x) :=
  (mfderiv I I' f x).comp ((J x).comp (mfderiv I I' f x).inverse)

/-- Actual native Hom-section smoothness of transported endomorphisms. -/
theorem smooth_transportEndomorphism (f : M → N)
    (hf : ContMDiff I I' ∞ f)
    (hinv : ∀ x, (mfderiv I I' f x).IsInvertible)
    (J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x)
    (hJ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (J x))) :
    ContMDiff I (I'.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] F)
        (E := fun z : N => TangentSpace I' z →L[ℝ] TangentSpace I' z) (f x)
        (transportEndomorphism I I' f J x)) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨hf x₀, ?_⟩
  let A := inTangentCoordinates I I' id f (mfderiv I I' f) x₀
  have hA : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] F) ∞ A x₀ :=
    (hf x₀).mfderiv_const (by simp)
  have hAi : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] E) ∞
      (fun x => (A x).inverse) x₀ := by
    have hi : ContDiffAt ℝ ∞ (ContinuousLinearMap.inverse :
        (E →L[ℝ] F) → (F →L[ℝ] E)) (A x₀) := by
      apply IsInvertible.contDiffAt_map_inverse
      dsimp only [A, inTangentCoordinates, id_eq]
      rw [inCoordinates_eq (FiberBundle.mem_baseSet_trivializationAt' x₀)
        (FiberBundle.mem_baseSet_trivializationAt' (f x₀))]
      exact isInvertible_equiv.comp ((hinv x₀).comp isInvertible_equiv)
    exact hi.contMDiffAt.comp x₀ hA
  have hK := ((contMDiffAt_hom_bundle _).mp (hJ x₀)).2
  apply (hA.clm_comp (hK.clm_comp hAi)).congr_of_eventuallyEq
  have hsrc : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt _ _ _).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' _)
  have htgt : f ⁻¹' (trivializationAt F (TangentSpace I') (f x₀)).baseSet ∈ 𝓝 x₀ :=
    (hf x₀).continuousAt.preimage_mem_nhds
      ((trivializationAt _ _ _).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' _))
  filter_upwards [hsrc, htgt] with x hx hfx
  dsimp only [A, inTangentCoordinates, id_eq]
  rw [inCoordinates_eq hfx hfx, inCoordinates_eq hx hx,
    inCoordinates_eq hx hfx]
  simp only [inverse_equiv_comp, inverse_comp_equiv,
    ContinuousLinearEquiv.symm_symm]
  ext v
  simp only [transportEndomorphism, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]

end Transport
end ExactLiouvilleComparison.CylindricalCompatibility
