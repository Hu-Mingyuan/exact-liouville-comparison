import ExactLiouvilleComparison.MainComparison
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
open ExactLiouvilleComparison

example : MainTarget := MainComparison.mainTarget
example : MainComparison.Target := MainComparison.mainTarget
example {d : ℕ} {M : SmoothManifold d} : MainComparison.RemainingPathsTarget (M := M) :=
  MainComparison.remainingPaths

/-- Native output with both jointly smooth forward and inverse isotopies unfolded. -/
theorem nativeConclusion (d : ℕ) (M : SmoothManifold d) (P : RadialReference M)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    (hg : GrowthAtInfinity P.compatible T P.R 1) :
    ∃ (F : M.SmoothEquiv M) (h : M.Point → ℝ) (H : ℝ → M.SmoothEquiv M),
      (∀ x, H 0 x = x) ∧ (∀ x, H 1 x = F x) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × M.Point => H p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × M.Point => (H p.1).symm p.2) (Icc (0 : ℝ) 1 ×ˢ univ) ∧
      ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ h ∧
      (∀ x v, evalOne (M.pullback M F T.primitive) x v =
        evalOne P.exactStructure.primitive x v + M.scalarDerivative h x v) ∧
      M.pullback M F (M.exteriorDerivative T.primitive) =
        M.exteriorDerivative P.exactStructure.primitive := by
  obtain ⟨F, ⟨H, h0, h1, hs, hi⟩, h, hh, hp, hd⟩ :=
    MainComparison.mainTarget d M P T hw hg
  exact ⟨F, h, H, h0, h1, hs, hi, hh, hp, hd⟩

/-- The constructed comparison has the advertised final inverse and negative gauge. -/
example {d : ℕ} {M : SmoothManifold d} (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    {C : ℝ} (hC : 0 < C) (K : Set M.Point) (hK : IsCompact K)
    (hb : ∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * G.B (P.R x)) :
    ExactComparisonAlgebra.Witness M T.primitive P.exactStructure.primitive
      (MainComparison.psi P G T hw hC K hK hb).symm
      (fun x => -MainComparison.psiGauge P G T hw hC K hK hb
        ((MainComparison.psi P G T hw hC K hK hb).symm x)) :=
  MainComparison.comparisonWitness P G T hw hC K hK hb

#print axioms MainComparison.mainTarget
#print axioms nativeConclusion
#eval IO.println "MAIN_COMPARISON_CONSUMERS_COMPLETE"
