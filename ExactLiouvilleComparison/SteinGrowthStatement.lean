import ExactLiouvilleComparison.Statement

/-! Bounded specifications only. The constructions live in `SteinGrowth`. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter

namespace ExactLiouvilleComparison.SteinGrowth

/-- The original function need only be smooth within `[e,∞)`. -/
def ScalarTarget : Prop :=
  ∀ B : AdmissibleGrowth (Real.exp 1), ∃ B₁ : AdmissibleGrowth 1,
    ∀ r, Real.exp 1 + 2 ≤ r → B₁.B r = B.B r

/-- Keep the very same metric, inverse contraction norm, and constant. -/
def WitnessTarget : Prop :=
  ∀ (d : ℕ) (M : SmoothManifold d) (S : ExactSymplecticStructure M)
    (A : CompatibleStructure S) (T : ExactSymplecticStructure M)
    (R : M.Point → ℝ), IsProperMap R → (∀ x, 1 ≤ R x) →
    ∀ (B : AdmissibleGrowth (Real.exp 1)) (C : ℝ), 0 < C →
    ∀ K : Set M.Point, IsCompact K →
    (∀ x, x ∉ K → A.inverseNorm T x ≤ C * B.B (R x)) →
    ∃ B₁ : AdmissibleGrowth 1, ∃ K₁ : Set M.Point,
      IsCompact K₁ ∧ K ⊆ K₁ ∧
      (∀ r, Real.exp 1 + 2 ≤ r → B₁.B r = B.B r) ∧
      ∀ x, x ∉ K₁ → A.inverseNorm T x ≤ C * B₁.B (R x)

/-- The bounded geometric implication, with no comparison conclusion. -/
def GrowthTarget : Prop :=
  ∀ (d : ℕ) (M : SmoothManifold d) (S : ExactSymplecticStructure M)
    (A : CompatibleStructure S) (T : ExactSymplecticStructure M)
    (R : M.Point → ℝ), IsProperMap R → (∀ x, 1 ≤ R x) →
    GrowthAtInfinity A T R (Real.exp 1) → GrowthAtInfinity A T R 1

/-- Consumer contract: properness and the lower bound remain separately owned. -/
def SteinConsumerTarget : Prop :=
  ∀ (d N : ℕ) (M : SmoothManifold d) (i : ProperComplexEmbedding M N)
    (P : SteinReference i) (T : ExactSymplecticStructure M),
    IsProperMap (steinRadius i) → (∀ x, 1 ≤ steinRadius i x) →
    GrowthAtInfinity P.compatible T (steinRadius i) (Real.exp 1) →
    GrowthAtInfinity P.compatible T (steinRadius i) 1

end ExactLiouvilleComparison.SteinGrowth
