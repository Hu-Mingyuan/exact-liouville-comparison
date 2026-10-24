import ExactLiouvilleComparison.CylindricalCompatibilityContactBundleStatement

/-! Local linear algebra for the native kernel atlas. No bundle or global
transverse field is an input or an output of these local constructions. -/

noncomputable section
open scoped Manifold ContDiff

namespace ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle.Atlas

section Projection
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

/-- Projection along one transverse vector, retaining the literal kernel. -/
def kernelProjection (a : V →L[ℝ] ℝ) (u : V) (hu : a u ≠ 0) : V →L[ℝ] a.ker :=
  (ContinuousLinearMap.id ℝ V - a.smulRight ((a u)⁻¹ • u)).codRestrict a.ker
    (fun v ↦ by
      change a (v - a v • ((a u)⁻¹ • u)) = 0
      simp [map_sub, map_smul, hu])

@[simp] theorem kernelProjection_coe (a : V →L[ℝ] ℝ) (u : V) (hu : a u ≠ 0)
    (v : V) :
    (kernelProjection a u hu v : V) = v - (a v / a u) • u := by
  simp [kernelProjection, div_eq_mul_inv, smul_smul]

@[simp] theorem kernelProjection_self (a : V →L[ℝ] ℝ) (u : V) (hu : a u ≠ 0) :
    kernelProjection a u hu u = 0 := by
  apply Subtype.ext
  simp [hu]

@[simp] theorem kernelProjection_subtype (a : V →L[ℝ] ℝ) (u : V) (hu : a u ≠ 0)
    (v : a.ker) : kernelProjection a u hu v = v := by
  apply Subtype.ext
  simp

theorem kernelProjection_comp_coe (a b : V →L[ℝ] ℝ) (u : V)
    (ha : a u ≠ 0) (hb : b u ≠ 0) (v : V) :
    kernelProjection b u hb (kernelProjection a u ha v : V) =
      kernelProjection b u hb v := by
  rw [kernelProjection_coe, map_sub, map_smul, kernelProjection_self, smul_zero, sub_zero]

/-- Two kernels with a common transverse vector are continuously linearly
equivalent by projection. This is local data, not a global trivialization. -/
def kernelEquiv (a b : V →L[ℝ] ℝ) (u : V) (ha : a u ≠ 0) (hb : b u ≠ 0) :
    a.ker ≃L[ℝ] b.ker :=
  ContinuousLinearEquiv.equivOfInverse
    ((kernelProjection b u hb).comp a.ker.subtypeL)
    ((kernelProjection a u ha).comp b.ker.subtypeL)
    (fun v ↦ by
      change kernelProjection a u ha (kernelProjection b u hb v : V) = v
      rw [kernelProjection_comp_coe, kernelProjection_subtype])
    (fun v ↦ by
      change kernelProjection b u hb (kernelProjection a u ha v : V) = v
      rw [kernelProjection_comp_coe, kernelProjection_subtype])

@[simp] theorem kernelEquiv_apply (a b : V →L[ℝ] ℝ) (u : V)
    (ha : a u ≠ 0) (hb : b u ≠ 0) (v : a.ker) :
    (kernelEquiv a b u ha hb v : V) = v - (b v / b u) • u :=
  kernelProjection_coe b u hb v

@[simp] theorem kernelEquiv_symm_apply (a b : V →L[ℝ] ℝ) (u : V)
    (ha : a u ≠ 0) (hb : b u ≠ 0) (v : b.ker) :
    ((kernelEquiv a b u ha hb).symm v : V) = v - (a v / a u) • u :=
  kernelProjection_coe a u ha v

end Projection

section Transport
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]

/-- Restrict an actual continuous linear change of coordinates to its kernels. -/
def kernelCongr (e : V ≃L[ℝ] W) (a : V →L[ℝ] ℝ) (b : W →L[ℝ] ℝ)
    (h : ∀ v, b (e v) = a v) : a.ker ≃L[ℝ] b.ker :=
  ContinuousLinearEquiv.equivOfInverse
    ((e.toContinuousLinearMap.comp a.ker.subtypeL).codRestrict b.ker
      (fun v ↦ by change b (e v) = 0; rw [h]; exact v.property))
    ((e.symm.toContinuousLinearMap.comp b.ker.subtypeL).codRestrict a.ker
      (fun v ↦ by
        change a (e.symm v) = 0
        rw [← h, e.apply_symm_apply]; exact v.property))
    (fun v ↦ Subtype.ext (e.symm_apply_apply v))
    (fun v ↦ Subtype.ext (e.apply_symm_apply v))

@[simp] theorem kernelCongr_coe (e : V ≃L[ℝ] W) (a : V →L[ℝ] ℝ)
    (b : W →L[ℝ] ℝ) (h : ∀ v, b (e v) = a v) (v : a.ker) :
    (kernelCongr e a b h v : W) = e v := rfl

@[simp] theorem kernelCongr_symm_coe (e : V ≃L[ℝ] W) (a : V →L[ℝ] ℝ)
    (b : W →L[ℝ] ℝ) (h : ∀ v, b (e v) = a v) (v : b.ker) :
    ((kernelCongr e a b h).symm v : V) = e.symm v := rfl

end Transport

end ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle.Atlas
