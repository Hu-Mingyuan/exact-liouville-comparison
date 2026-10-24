import ExactLiouvilleComparison.SteinReferencePullback

/-! The Stein primitive from source data and its symplecticity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology InnerProductSpace
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter
namespace ExactLiouvilleComparison.SteinReferenceConstruction
variable {d N : ℕ} {M : SmoothManifold d}

abbrev embeddingDerivative (i : ProperComplexEmbedding M N) (x : M.Point) :
    M.Tangent x →L[ℝ] Ambient N :=
  mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Ambient N)) i.map x

theorem embeddingDerivative_complex (i : ProperComplexEmbedding M N) (x : M.Point)
    (v : M.Tangent x) :
    embeddingDerivative i x (i.J x v) = Complex.I • embeddingDerivative i x v := by
  convert! i.complex_linear x v using 1

def primitive (i : ProperComplexEmbedding M N) : M.Form 1 :=
  pullbackAmbient M i.map (ambientPrimitive N)

theorem primitive_apply (i : ProperComplexEmbedding M N) (x : M.Point) (v : M.Tangent x) :
    evalOne (primitive i) x v =
      -(1 / 2 : ℝ) * inner ℝ (i.map x) (Complex.I • embeddingDerivative i x v) := rfl

theorem smooth_primitive (i : ProperComplexEmbedding M N) : M.IsSmoothForm (primitive i) :=
  smooth_pullbackAmbient_one M i.map i.smooth (ambientCovector N) (ambientCovector N).contDiff

theorem smooth_radius (i : ProperComplexEmbedding M N) :
    ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ (steinRadius i) :=
  contMDiff_const.add ((contDiff_norm_sq ℂ).comp_contMDiff i.smooth)

theorem radius_derivative (i : ProperComplexEmbedding M N) (x : M.Point) (v : M.Tangent x) :
    M.scalarDerivative (steinRadius i) x v =
      2 * inner ℝ (i.map x) (embeddingDerivative i x v) := by
  have hρ : ContDiff ℝ ∞ (fun z : Ambient N => Real.exp 1 + ‖z‖ ^ 2) :=
    contDiff_const.add (contDiff_norm_sq ℝ)
  change (show ℝ from mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ))
    ((fun z : Ambient N => Real.exp 1 + ‖z‖ ^ 2) ∘ i.map) x v) =
    2 * inner ℝ (i.map x) (embeddingDerivative i x v)
  have hc := mfderiv_comp x (hρ.contMDiff.mdifferentiableAt (by simp))
    (i.smooth.mdifferentiableAt (by simp))
  have hd := (hasStrictFDerivAt_norm_sq (i.map x)).hasFDerivAt.const_add (Real.exp 1)
  have hc' := congrArg (fun L => (show ℝ from L v)) hc
  convert! hc' using 1
  rw [mfderiv_eq_fderiv, hd.fderiv]
  dsimp [ContinuousLinearMap.comp, ContinuousLinearMap.smul_def, embeddingDerivative]
  simp only [two_smul]
  change (2 : ℝ) * inner ℝ (i.map x) (embeddingDerivative i x v) =
    inner ℝ (i.map x) (embeddingDerivative i x v) +
      inner ℝ (i.map x) (embeddingDerivative i x v)
  ring

theorem primitive_eq (i : ProperComplexEmbedding M N) (x : M.Point) (v : M.Tangent x) :
    evalOne (primitive i) x v =
      -(1 / 4 : ℝ) * M.scalarDerivative (steinRadius i) x (i.J x v) := by
  rw [primitive_apply, radius_derivative, embeddingDerivative_complex i]
  ring

theorem exteriorDerivative_apply (i : ProperComplexEmbedding M N)
    (x : M.Point) (v w : M.Tangent x) :
    evalTwo (M.exteriorDerivative (primitive i)) x v w =
      -inner ℝ (embeddingDerivative i x v) (Complex.I • embeddingDerivative i x w) := by
  rw [primitive, exteriorDerivative_pullbackAmbient M i.map i.smooth _
    (ambientPrimitive N).differentiable]
  change extDeriv (ambientPrimitive N) (i.map x)
    (embeddingDerivative i x ∘ ![v,w]) = _
  have hp : embeddingDerivative i x ∘ ![v,w] =
      ![embeddingDerivative i x v, embeddingDerivative i x w] := by
    ext j
    fin_cases j <;> rfl
  rw [hp, ambient_exteriorDerivative]

theorem compatible_value (i : ProperComplexEmbedding M N)
    (x : M.Point) (v w : M.Tangent x) :
    evalTwo (M.exteriorDerivative (primitive i)) x v (i.J x w) =
      inner ℝ (embeddingDerivative i x v) (embeddingDerivative i x w) := by
  rw [exteriorDerivative_apply, embeddingDerivative_complex i]
  simp [smul_smul, Complex.I_mul_I]

theorem nondegenerate (i : ProperComplexEmbedding M N) (x : M.Point) :
    M.Nondegenerate (M.exteriorDerivative (primitive i)) x := by
  intro v hv
  have h := hv (i.J x v)
  rw [compatible_value] at h
  have hz : embeddingDerivative i x v = 0 := (inner_self_eq_zero).mp h
  apply i.immersion x
  convert! hz using 1
  simp

theorem invariant (i : ProperComplexEmbedding M N) (x : M.Point) (v w : M.Tangent x) :
    evalTwo (M.exteriorDerivative (primitive i)) x (i.J x v) (i.J x w) =
      evalTwo (M.exteriorDerivative (primitive i)) x v w := by
  rw [compatible_value, exteriorDerivative_apply, embeddingDerivative_complex i, real_inner_comm]
  exact ambient_inner_I_swap _ _

def exactStructure (i : ProperComplexEmbedding M N) : ExactSymplecticStructure M where
  primitive := primitive i
  smooth_primitive := smooth_primitive i
  symplectic := (M.isSymplecticOn_exteriorDerivative_iff _ (smooth_primitive i) univ).2
    (fun x _ => nondegenerate i x)

end ExactLiouvilleComparison.SteinReferenceConstruction
