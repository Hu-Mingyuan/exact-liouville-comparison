import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationCoordinates
import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationAlgebraNative

/-! Frame transport of the actual matrix normalization to native fibers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace ExactLiouvilleComparison.CylindricalCompatibility.Normalization
open NormalizationAlgebra

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem matrixIn_posDef (e : V ≃L[ℝ] Vec n) (A : V →L[ℝ] V →L[ℝ] ℝ)
    (hsymm : ∀ v w, A v w = A w v) (hpos : ∀ v, v ≠ 0 → 0 < A v v) :
    (matrixIn e A).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · change (matrixIn e A).conjTranspose = matrixIn e A
    ext i j
    simpa using hsymm (e.symm (Pi.single j 1)) (e.symm (Pi.single i 1))
  · intro v hv
    have hv' : e.symm v ≠ 0 := fun h ↦ hv (e.symm.injective (by simpa using h))
    have hp := hpos (e.symm v) hv'
    simpa only [← form_matrixIn e A v v, form, Matrix.toBilin'_apply', star_trivial] using hp

theorem matrixIn_skew (e : V ≃L[ℝ] Vec n) (A : V →L[ℝ] V →L[ℝ] ℝ)
    (halt : ∀ v, A v v = 0) : (matrixIn e A).transpose = -matrixIn e A := by
  have ha : A.toBilinForm.IsAlt := halt
  ext i j
  exact (ha.neg_eq (e.symm (Pi.single i 1)) (e.symm (Pi.single j 1))).symm

theorem matrixIn_isUnit (e : V ≃L[ℝ] Vec n) (A : V →L[ℝ] V →L[ℝ] ℝ)
    (halt : ∀ v, A v v = 0)
    (hnd : ∀ v, (∀ w, A v w = 0) → v = 0) : IsUnit (matrixIn e A) := by
  apply (form_nondegenerate_iff _).mp
  have ha : A.toBilinForm.IsAlt := halt
  have hl : ∀ v, (∀ w, form (matrixIn e A) v w = 0) → v = 0 := by
    intro v hv
    apply e.symm.injective
    simp only [map_zero]
    apply hnd
    intro w
    simpa only [form_matrixIn, ContinuousLinearEquiv.symm_apply_apply] using hv (e w)
  refine ⟨hl, ?_⟩
  intro v hv
  apply hl v
  intro w
  have hs := form_skew (matrixIn_skew e A halt) v w
  rw [hv w, neg_zero] at hs
  exact hs

/-- The explicit normalization, transported through an actual continuous frame. -/
def normalizeIn (e : V ≃L[ℝ] Vec n)
    (h w : V →L[ℝ] V →L[ℝ] ℝ) : V →L[ℝ] V :=
  endomorphismIn e (normalize (matrixIn e h) (matrixIn e w))

theorem normalizeIn_compatible (e : V ≃L[ℝ] Vec n)
    (h w : V →L[ℝ] V →L[ℝ] ℝ)
    (hsymm : ∀ v u, h v u = h u v) (hpos : ∀ v, v ≠ 0 → 0 < h v v)
    (halt : ∀ v, w v v = 0) (hnd : ∀ v, (∀ u, w v u = 0) → v = 0) :
    Compatible w (normalizeIn e h w) := by
  have hc := normalize_native (matrixIn_posDef e h hsymm hpos)
    (matrixIn_skew e w halt) (matrixIn_isUnit e w halt hnd)
  dsimp only at hc
  refine ⟨?_, ?_, ?_⟩
  · intro v
    apply e.injective
    simpa only [normalizeIn, endomorphismIn_apply, ContinuousLinearEquiv.apply_symm_apply,
      map_neg, endomorphism_apply] using hc.1 (e v)
  · intro v u
    simpa only [normalizeIn, endomorphismIn_apply, continuousForm_apply,
      form_matrixIn, ContinuousLinearEquiv.symm_apply_apply, endomorphism_apply]
      using hc.2.1 (e v) (e u)
  · intro v hv
    have he : e v ≠ 0 := fun hz ↦ hv (e.injective (by simpa using hz))
    simpa only [normalizeIn, endomorphismIn_apply, continuousForm_apply,
      form_matrixIn, ContinuousLinearEquiv.symm_apply_apply, endomorphism_apply]
      using hc.2.2 (e v) he

/-- Matrix of a native endomorphism in a continuous frame. -/
def endMatrixIn (e : V ≃L[ℝ] Vec n) (J : V →L[ℝ] V) : Mat n :=
  LinearMap.toMatrix' (e.toLinearMap.comp (J.toLinearMap.comp e.symm.toLinearMap))

@[simp] theorem endMatrixIn_mulVec (e : V ≃L[ℝ] Vec n) (J : V →L[ℝ] V)
    (v : Vec n) : endMatrixIn e J *ᵥ v = e (J (e.symm v)) := by
  exact LinearMap.toMatrix'_mulVec _ _

theorem normalizeIn_recovery (e : V ≃L[ℝ] Vec n)
    (h w : V →L[ℝ] V →L[ℝ] ℝ)
    (hsymm : ∀ v u, h v u = h u v) (hpos : ∀ v, v ≠ 0 → 0 < h v v)
    (J₀ : V →L[ℝ] V) (hJ : ∀ v, J₀ (J₀ v) = -v)
    (hmetric : ∀ v u, h v u = w v (J₀ u)) : normalizeIn e h w = J₀ := by
  have hs : endMatrixIn e J₀ * endMatrixIn e J₀ = -1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLin'_apply, ← mulVec_mulVec, endMatrixIn_mulVec,
      ContinuousLinearEquiv.symm_apply_apply, hJ, map_neg,
      ContinuousLinearEquiv.apply_symm_apply, LinearMap.neg_apply,
      Matrix.toLin'_one, LinearMap.id_apply]
  have hm : matrixIn e h = matrixIn e w * endMatrixIn e J₀ := by
    apply Matrix.toBilin'.injective
    apply LinearMap.BilinForm.ext
    intro v u
    change form (matrixIn e h) v u = form (matrixIn e w * endMatrixIn e J₀) v u
    rw [form_matrixIn, hmetric]
    have he : form (matrixIn e w * endMatrixIn e J₀) v u =
        form (matrixIn e w) v (endMatrixIn e J₀ *ᵥ u) := by
      simp only [form, Matrix.toBilin'_apply', ← mulVec_mulVec]
    rw [he]
    simp only [form_matrixIn, endMatrixIn_mulVec, ContinuousLinearEquiv.symm_apply_apply]
  have hn := normalize_recovery (matrixIn_posDef e h hsymm hpos) hs hm
  ext v
  simp only [normalizeIn, endomorphismIn_apply, hn, endMatrixIn_mulVec,
    ContinuousLinearEquiv.symm_apply_apply]

/-- Coordinate change from the `f` frame to the `e` frame. -/
def frameChange (e f : V ≃L[ℝ] Vec n) : Mat n :=
  LinearMap.toMatrix' (e.toLinearMap.comp f.symm.toLinearMap)

@[simp] theorem frameChange_mulVec (e f : V ≃L[ℝ] Vec n) (v : Vec n) :
    frameChange e f *ᵥ v = e (f.symm v) := by
  exact LinearMap.toMatrix'_mulVec _ _

theorem frameChange_isUnit (e f : V ≃L[ℝ] Vec n) : IsUnit (frameChange e f) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v u hvu
  exact f.symm.injective (e.injective (by simpa only [frameChange_mulVec] using hvu))

theorem matrixIn_frameChange (e f : V ≃L[ℝ] Vec n)
    (A : V →L[ℝ] V →L[ℝ] ℝ) :
    matrixIn f A = pull (frameChange e f) (matrixIn e A) := by
  apply Matrix.toBilin'.injective
  apply LinearMap.BilinForm.ext
  intro v u
  change form (matrixIn f A) v u = form (pull (frameChange e f) (matrixIn e A)) v u
  simp only [form_pull, form_matrixIn, frameChange_mulVec,
    ContinuousLinearEquiv.symm_apply_apply]

theorem normalizeIn_frame_independent (e f : V ≃L[ℝ] Vec n)
    (h w : V →L[ℝ] V →L[ℝ] ℝ)
    (hsymm : ∀ v u, h v u = h u v) (hpos : ∀ v, v ≠ 0 → 0 < h v v)
    (halt : ∀ v, w v v = 0) (hnd : ∀ v, (∀ u, w v u = 0) → v = 0) :
    normalizeIn e h w = normalizeIn f h w := by
  have hn := normalize_naturality (matrixIn_posDef e h hsymm hpos)
    (matrixIn_skew e w halt) (matrixIn_isUnit e w halt hnd) (frameChange_isUnit e f)
  rw [← matrixIn_frameChange e f h, ← matrixIn_frameChange e f w] at hn
  ext v
  apply e.injective
  simp only [normalizeIn, endomorphismIn_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hn]
  rw [← frameChange_mulVec e f]
  simp only [← mulVec_mulVec]
  rw [mulVec_mulVec _ (frameChange e f) (frameChange e f)⁻¹]
  rw [NormalizationAlgebra.mul_inv _ (frameChange_isUnit e f), one_mulVec]
  simp only [frameChange_mulVec, ContinuousLinearEquiv.symm_apply_apply]

end ExactLiouvilleComparison.CylindricalCompatibility.Normalization
