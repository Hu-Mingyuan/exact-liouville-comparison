import ExactLiouvilleComparison.SteinGrowthGeometry

/-! Consumers for the separately owned radius facts and the existing radial interface. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter

namespace ExactLiouvilleComparison.SteinGrowth

/-- The literal Stein radius; its properness and lower bound are external inputs. -/
theorem steinRadius_growth {d N : ℕ} {M : SmoothManifold d}
    (i : ProperComplexEmbedding M N) (P : SteinReference i)
    (T : ExactSymplecticStructure M) (hR : IsProperMap (steinRadius i))
    (hlower : ∀ x, 1 ≤ steinRadius i x)
    (h : GrowthAtInfinity P.compatible T (steinRadius i) (Real.exp 1)) :
    GrowthAtInfinity P.compatible T (steinRadius i) 1 :=
  growthAtInfinity P.compatible T (steinRadius i) hR hlower h

theorem steinConsumerTarget : SteinConsumerTarget := by
  intro d N M i P T hR hlower h
  exact steinRadius_growth i P T hR hlower h

/-- No reference data is changed when using the existing radial package. -/
theorem radialReference_growth {d : ℕ} {M : SmoothManifold d}
    (P : RadialReference M) (T : ExactSymplecticStructure M)
    (h : GrowthAtInfinity P.compatible T P.R (Real.exp 1)) :
    GrowthAtInfinity P.compatible T P.R 1 :=
  growthAtInfinity P.compatible T P.R P.proper_R P.lower_R h

/-- The scalar output exposes every unchanged admissibility field to consumers. -/
theorem scalarConsumer (B : AdmissibleGrowth (Real.exp 1)) :
    ∃ B₁ : AdmissibleGrowth 1,
      ContDiffOn ℝ ∞ B₁.B (Ici 1) ∧
      (∀ r, 1 ≤ r → 0 < B₁.B r ∧ r ≤ B₁.B r) ∧
      Tendsto (fun b : ℝ => ∫ r in 1..b, r / (B₁.B r)^2) atTop atTop ∧
      B₁.B =ᶠ[atTop] B.B :=
  ⟨extend B, (extend B).smooth,
    fun r hr => ⟨(extend B).positive r hr, (extend B).dominates r hr⟩,
    (extend B).divergent, extend_eventuallyEq B⟩

end ExactLiouvilleComparison.SteinGrowth
