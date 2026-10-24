import ExactLiouvilleComparison.ManuscriptComparison

/-! Native interface consumers for the complete bounded assembly. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.ManuscriptComparisonConsumers

theorem manuscript : ManuscriptTarget := ManuscriptComparison.manuscriptTarget
theorem main : MainTarget := manuscript.1
theorem finiteType : FiniteTypeTarget := manuscript.2.1
theorem stein : SteinTarget := manuscript.2.2.1
theorem common : CommonReferenceTarget := manuscript.2.2.2
theorem complete : CompleteLiouvilleComparisonTarget :=
  ManuscriptComparison.completeLiouvilleComparisonTarget

/-- The finite-type corollary supplies the native diffeomorphism, gauge and
both smooth isotopy families, with the original primitive and exterior identities. -/
theorem finiteTypeNative (d : ℕ) (D : LiouvilleDomain d) (C : Completion D)
    (A : CompatibleStructure (completionReference C)) (cyl : CylindricalStructure C A)
    (T : ExactSymplecticStructure C.ambient.manifold) (hw : WeaklyTames A T)
    (hg : ∃ B : AdmissibleGrowth 1, ∃ C₀ : ℝ, 0 < C₀ ∧
      ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ y t, t₀ ≤ t →
        A.inverseNorm T (C.endMap (y, t)) ≤ C₀ * B.B (Real.exp t)) :
    let M := C.ambient.manifold
    ∃ (F : M.SmoothEquiv M) (h : M.Point → ℝ) (H : ℝ → M.SmoothEquiv M),
      (∀ x, H 0 x = x) ∧ (∀ x, H 1 x = F x) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × M.Point => H p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × M.Point => (H p.1).symm p.2) (Icc (0 : ℝ) 1 ×ˢ univ) ∧
      ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ h ∧
      (∀ x v, evalOne (M.pullback M F T.primitive) x v =
        evalOne C.ambient.primitive x v + M.scalarDerivative h x v) ∧
      M.pullback M F (M.exteriorDerivative T.primitive) =
        M.exteriorDerivative C.ambient.primitive :=
  FiniteTypeComparison.nativeConclusion C A cyl T hw hg

/-- Complete data retains literally the prescribed native flow and its positive
contraction. No completeness is manufactured by the comparison or its gauge. -/
theorem prescribedFlow {d : ℕ} {M : SmoothManifold d} {lambda : M.Form 1}
    (L : CompletePrimitive M lambda) :
    L.toCompleteLiouvilleManifold.primitive = lambda ∧
    L.toCompleteLiouvilleManifold.completeFlow.flow = L.completeFlow.flow ∧
    (∀ x v, evalTwo (M.exteriorDerivative lambda) x (M.liouvilleVector lambda x) v =
      evalOne lambda x v) ∧
    ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × M.Point => L.completeFlow.flow p.1 p.2) ∧
    (∀ (x : M.Point) (t : ℝ) (a : M.Point),
      L.completeFlow.flow t x ∈ (chartAt (Model d) a).source →
      HasDerivAt (fun s : ℝ => chartAt (Model d) a (L.completeFlow.flow s x))
        (M.chartTangentMap a (L.completeFlow.flow t x)
          (M.liouvilleVector lambda (L.completeFlow.flow t x))) t) :=
  ⟨rfl, rfl, L.contraction, L.completeFlow.smooth_action, L.completeFlow.solves⟩

theorem completeNative (d : ℕ) (M : SmoothManifold d) (P : RadialReference M)
    (L₀ : CompletePrimitive M P.exactStructure.primitive)
    (T : ExactSymplecticStructure M) (L₁ : CompletePrimitive M T.primitive)
    (hw : WeaklyTames P.compatible T) (hg : GrowthAtInfinity P.compatible T P.R 1) :
    FiniteTypeComparison.NativeConclusion M T.primitive P.exactStructure.primitive ∧
    L₀.toCompleteLiouvilleManifold.completeFlow.flow = L₀.completeFlow.flow ∧
    L₁.toCompleteLiouvilleManifold.completeFlow.flow = L₁.completeFlow.flow :=
  ⟨FiniteTypeComparison.native_of_exactComparison (complete d M P L₀ T L₁ hw hg), rfl, rfl⟩

end ExactLiouvilleComparison.ManuscriptComparisonConsumers
#eval IO.println "MANUSCRIPT_CONSUMERS_COMPLETE"
