import ExactLiouvilleComparison.ThirdPathEstimates

/-! Literal endpoint directions and inversion of the accepted smooth isotopy. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.ThirdPath
variable {d : ℕ} {M : SmoothManifold d}

theorem primitive_zero (P : RadialReference M) (T : ExactSymplecticStructure M) :
    primitive P T 0 =
      LinearAlgebraChecks.radialPrimitive P (LargeCoefficient.A P T.primitive) := by
  simp [primitive]

theorem primitive_one (P : RadialReference M) (T : ExactSymplecticStructure M) :
    primitive P T 1 = T.primitive +
      LinearAlgebraChecks.radialPrimitive P (LargeCoefficient.A P T.primitive) := by
  simp [primitive, add_comm]

/-- The time derivative of the literal primitive, on every actual tangent vector. -/
theorem primitive_parameter_derivative (P : RadialReference M) (T : ExactSymplecticStructure M)
    (s : ℝ) (x : M.Point) (v : M.Tangent x) :
    HasDerivAt (fun t => evalOne (primitive P T t) x v) (evalOne T.primitive x v) s := by
  have h := ((hasDerivAt_id s).mul_const (evalOne T.primitive x v)).const_add
    (evalOne (LinearAlgebraChecks.radialPrimitive P (LargeCoefficient.A P T.primitive)) x v)
  simpa only [primitive, evalOne, Pi.add_apply, Pi.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    id_eq, one_mul] using h

/-- Inversion preserves the literal smooth isotopy, including smooth inverse family. -/
theorem isotopy_symm {F : M.SmoothEquiv M} (hF : SmoothlyIsotopicToIdentity M F) :
    SmoothlyIsotopicToIdentity M F.symm := by
  obtain ⟨H, hzero, hone, hs, hi⟩ := hF
  refine ⟨fun t => (H t).symm, ?_, ?_, hi, ?_⟩
  · intro x
    calc
      (H 0).symm x = H 0 ((H 0).symm x) := (hzero _).symm
      _ = x := (H 0).apply_symm_apply x
  · have he : H 1 = F := by ext x; exact hone x
    intro x
    change (H 1).symm x = F.symm x
    rw [he]
  · exact hs

/-- For the accepted two-time output, the comparison arrow uses map 1 0. -/
theorem evolution_inverse_isotopy
    {Z : Parameter → (x : M.Point) → M.Tangent x} (H : FirstPathFlow.Evolution Z) :
    SmoothlyIsotopicToIdentity M (H.map parameterOne parameterZero) := by
  rw [← H.inverse parameterZero parameterOne]
  exact isotopy_symm (H.isotopy parameterOne)

end ExactLiouvilleComparison.ThirdPath
