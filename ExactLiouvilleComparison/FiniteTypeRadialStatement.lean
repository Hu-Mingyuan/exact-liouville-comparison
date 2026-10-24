import ExactLiouvilleComparison.Statement

/-! Bounded specifications for the finite-type reference. These specifications
are not proofs and supply no radial data as hypotheses of ConstructionTarget. -/
noncomputable section
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set

namespace ExactLiouvilleComparison.FiniteTypeRadial

/-- The portion beyond logarithmic time `a`, with strict cutoff. -/
def farEnd {d : ℕ} {D : LiouvilleDomain d} (C : Completion D) (a : ℝ) :
    Set C.ambient.manifold.Point := C.endMap '' (univ ×ˢ Ioi a)

/-- Output data, to be constructed from the original completion and J.
The primitive, J and metric are fixed parameters, not new selectable fields. -/
structure Radius {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    (A : CompatibleStructure (completionReference C)) where
  R : C.ambient.manifold.Point → ℝ
  smooth : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ R
  proper : IsProperMap R
  lower : ∀ x, 1 ≤ R x
  end_eq : ∀ y t, 2 ≤ Real.exp t → R (C.endMap (y, t)) = Real.exp t
  core_bound : ∀ x, x ∉ farEnd C (Real.log 2) → R x ≤ 2
  compact_core : IsCompact ((farEnd C (Real.log 2))ᶜ)
  primitive_eq : ∀ x, 2 < R x → ∀ v,
    evalOne C.ambient.primitive x v =
      -C.ambient.manifold.scalarDerivative R x (A.J x v)
  dual_sq : ∀ x, 2 < R x →
    (A.dualNorm x (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) R x)) ^ 2 = R x

/-- Unconditional bounded geometric obligation; no MainTarget input. -/
def ConstructionTarget : Prop :=
  ∀ (d : ℕ) (D : LiouvilleDomain d) (C : Completion D)
    (A : CompatibleStructure (completionReference C)),
    CylindricalStructure C A → Nonempty (Radius C A)

/-- Reusable witness-level conversion. Every input radius must be constructed
by ConstructionTarget for the final unconditional consumer. B and C₀ stay fixed. -/
def GrowthWitnessTarget : Prop :=
  ∀ (d : ℕ) (D : LiouvilleDomain d) (C : Completion D)
    (A : CompatibleStructure (completionReference C)) (Q : Radius C A)
    (T : ExactSymplecticStructure C.ambient.manifold)
    (B : AdmissibleGrowth 1) (C₀ t₀ : ℝ), 0 < C₀ → 0 ≤ t₀ →
    (∀ y t, t₀ ≤ t → A.inverseNorm T (C.endMap (y, t)) ≤ C₀ * B.B (Real.exp t)) →
    ∃ K : Set C.ambient.manifold.Point, IsCompact K ∧
      ∀ x, x ∉ K → A.inverseNorm T x ≤ C₀ * B.B (Q.R x)

/-- Full bounded interface consumer: the reference is an output before T and
the growth premise are supplied. This asserts no exact comparison. -/
def ConsumerTarget : Prop :=
  ∀ (d : ℕ) (D : LiouvilleDomain d) (C : Completion D)
    (A : CompatibleStructure (completionReference C)), CylindricalStructure C A →
    ∃ P : RadialReference C.ambient.manifold,
      P.exactStructure = completionReference C ∧ HEq P.compatible A ∧
      P.c = 1 ∧ P.rstar = 2 ∧
      ∀ T : ExactSymplecticStructure C.ambient.manifold,
        (∃ B : AdmissibleGrowth 1, ∃ C₀ : ℝ, 0 < C₀ ∧
          ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ y t, t₀ ≤ t →
            A.inverseNorm T (C.endMap (y, t)) ≤ C₀ * B.B (Real.exp t)) →
        GrowthAtInfinity A T P.R 1

end ExactLiouvilleComparison.FiniteTypeRadial
