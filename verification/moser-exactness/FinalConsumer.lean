import ExactLiouvilleComparison.FirstPathExactness
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
open ExactLiouvilleComparison

example {d : ℕ} {M : SmoothManifold d} : MoserExactness.Target (M := M) :=
  MoserExactness.moserExactness

example {d : ℕ} {M : SmoothManifold d} : FirstPathExactness.Target (M := M) :=
  FirstPathExactness.firstPathExactness

/-- The native first-path endpoint and the literal integral gauge at the original inputs. -/
example {d : ℕ} {M : SmoothManifold d} (P : RadialReference M)
    (G : AdmissibleGrowth 1) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) {C : ℝ} (hC : 0 < C)
    (K : Set M.Point) (hK : IsCompact K)
    (hb : ∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * G.B (P.R x)) :
    let E := FirstPathFlow.evolution P G T hw hC K hK hb
    let H := MoserExactness.gauge (FirstPathExactness.primitive P G T) E
    ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ H ∧
    (∀ x v, evalOne (M.pullback M (E.map parameterZero parameterOne)
      (FirstPathExactness.primitive P G T 1)) x v =
        evalOne T.primitive x v + M.scalarDerivative H x v) ∧
    M.pullback M (E.map parameterZero parameterOne)
      (M.exteriorDerivative (FirstPathExactness.primitive P G T 1)) =
        M.exteriorDerivative T.primitive := by
  have h := (FirstPathExactness.firstPathExactness P G T hw C hC K hK hb).2
  simpa only [MoserExactness.Endpoint, FirstPathExactness.primitive, zero_smul, add_zero] using h

example {d : ℕ} {M : SmoothManifold d} (P : RadialReference M)
    (G : AdmissibleGrowth 1) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) {C : ℝ} (hC : 0 < C)
    (K : Set M.Point) (hK : IsCompact K)
    (hb : ∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * G.B (P.R x)) :
    ExactComparison M (FirstPathExactness.primitive P G T 1) T.primitive :=
  FirstPathExactness.exactComparison P G T hw hC K hK hb

#eval IO.println "MOSER_FINAL_CONSUMER_COMPLETE"
