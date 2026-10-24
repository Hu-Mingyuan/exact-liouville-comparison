import ExactLiouvilleComparison.SteinComparison
import ExactLiouvilleComparison.CommonReferenceComparison

/-! Native consumers of the unconditional bounded corollaries. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.CorollaryComparisonConsumers

theorem packaged : PackagedSteinTarget := SteinComparison.packagedSteinTarget
theorem source : SteinTarget := SteinComparison.steinTarget
theorem common : CommonReferenceTarget := CommonReferenceComparison.commonReferenceTarget

/-- Embedding-only reference with its literal primitive and induced metric. -/
theorem referenceIdentities {d N : ℕ} {M : SmoothManifold d}
    (i : ProperComplexEmbedding M N) :
    let P := SteinReferenceConstruction.reference i
    (∀ x, (SteinRadial.reference i P).R x = Real.exp 1 + ‖i.map x‖ ^ 2) ∧
    (∀ x v, evalOne P.exactStructure.primitive x v =
      -(1 / 4 : ℝ) * M.scalarDerivative (steinRadius i) x (i.J x v)) ∧
    (∀ x v w, P.compatible.g.inner x v w =
      @inner ℝ (EuclideanSpace ℂ (Fin N)) _
        (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x v)
        (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x w)) :=
  ⟨fun _ => rfl, (SteinReferenceConstruction.reference i).primitive_eq,
    (SteinReferenceConstruction.reference i).induced_metric⟩

/-- Original Stein inputs give actual maps, both smooth isotopy families,
the literal prescribed primitive, and equality of the exterior derivatives. -/
theorem steinNativeConclusion (d N : ℕ) (M : SmoothManifold d)
    (i : ProperComplexEmbedding M N) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames (SteinReferenceConstruction.reference i).compatible T)
    (hg : GrowthAtInfinity (SteinReferenceConstruction.reference i).compatible T
      (steinRadius i) (Real.exp 1)) :
    ∃ (F : M.SmoothEquiv M) (h : M.Point → ℝ) (H : ℝ → M.SmoothEquiv M),
      (∀ x, H 0 x = x) ∧ (∀ x, H 1 x = F x) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × M.Point => H p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × M.Point => (H p.1).symm p.2) (Icc (0 : ℝ) 1 ×ˢ univ) ∧
      ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ h ∧
      (∀ x v, evalOne (M.pullback M F T.primitive) x v =
        -(1 / 4 : ℝ) * M.scalarDerivative (steinRadius i) x (i.J x v) +
          M.scalarDerivative h x v) ∧
      M.pullback M F (M.exteriorDerivative T.primitive) =
        M.exteriorDerivative (SteinReferenceConstruction.reference i).exactStructure.primitive := by
  obtain ⟨F, ⟨H, h0, h1, hs, hi⟩, h, hh, hp, hd⟩ :=
    SteinComparison.constructedSteinTarget d N M i T hw hg
  refine ⟨F, h, H, h0, h1, hs, hi, hh, ?_, hd⟩
  intro x v
  rw [hp, (SteinReferenceConstruction.reference i).primitive_eq]

/-- Keep the two actual comparisons, and expose Phi=F1 o F2 inverse and
q=(h1-h2) o F2 inverse in the native identity and smooth isotopy endpoint. -/
theorem commonNativeConclusion (d : ℕ) (M : SmoothManifold d) (P : RadialReference M)
    (T₁ T₂ : ExactSymplecticStructure M)
    (hw₁ : WeaklyTames P.compatible T₁) (hg₁ : GrowthAtInfinity P.compatible T₁ P.R 1)
    (hw₂ : WeaklyTames P.compatible T₂) (hg₂ : GrowthAtInfinity P.compatible T₂ P.R 1) :
    ∃ (F₁ F₂ : M.SmoothEquiv M) (h₁ h₂ : M.Point → ℝ) (H : ℝ → M.SmoothEquiv M),
      ExactComparisonAlgebra.Witness M T₁.primitive P.exactStructure.primitive F₁ h₁ ∧
      ExactComparisonAlgebra.Witness M T₂.primitive P.exactStructure.primitive F₂ h₂ ∧
      (∀ x, H 0 x = x) ∧ (∀ x, H 1 x = F₁ (F₂.symm x)) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × M.Point => H p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × M.Point => (H p.1).symm p.2) (Icc (0 : ℝ) 1 ×ˢ univ) ∧
      ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ (fun x => (h₁-h₂) (F₂.symm x)) ∧
      (∀ x v, evalOne (M.pullback M (fun x => F₁ (F₂.symm x)) T₁.primitive) x v =
        evalOne T₂.primitive x v + M.scalarDerivative (fun x => (h₁-h₂) (F₂.symm x)) x v) ∧
      M.pullback M (fun x => F₁ (F₂.symm x)) (M.exteriorDerivative T₁.primitive) =
        M.exteriorDerivative T₂.primitive := by
  obtain ⟨F₁, F₂, h₁, h₂, w₁, w₂, ⟨H, h0, h1, hs, hi⟩, hh, hp, hd⟩ :=
    CommonReferenceComparison.explicitCommonTarget d M P T₁ T₂ hw₁ hg₁ hw₂ hg₂
  exact ⟨F₁, F₂, h₁, h₂, H, w₁, w₂, h0, h1, hs, hi, hh, hp, hd⟩

/-- Distinct B_i and C_i and compact exceptions are retained literally. -/
theorem separateGrowthWitnesses {d : ℕ} {M : SmoothManifold d} (P : RadialReference M)
    (T₁ T₂ : ExactSymplecticStructure M) (hw₁ : WeaklyTames P.compatible T₁)
    (hw₂ : WeaklyTames P.compatible T₂) (B₁ B₂ : AdmissibleGrowth 1)
    (C₁ C₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (K₁ K₂ : Set M.Point) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hb₁ : ∀ x, x ∉ K₁ → P.compatible.inverseNorm T₁ x ≤ C₁ * B₁.B (P.R x))
    (hb₂ : ∀ x, x ∉ K₂ → P.compatible.inverseNorm T₂ x ≤ C₂ * B₂.B (P.R x)) :
    ExactComparison M T₁.primitive T₂.primitive :=
  common _ M P T₁ T₂ hw₁ ⟨B₁, C₁, hC₁, K₁, hK₁, hb₁⟩
    hw₂ ⟨B₂, C₂, hC₂, K₂, hK₂, hb₂⟩

end ExactLiouvilleComparison.CorollaryComparisonConsumers
#eval IO.println "COROLLARIES_CONSUMERS_COMPLETE"
