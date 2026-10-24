import ExactLiouvilleComparison.RemainingPathExactness

/-! The general radial comparison theorem, with explicit endpoint map and gauge. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
open ExactLiouvilleComparison.ExactComparisonAlgebra
namespace ExactLiouvilleComparison.MainComparison
variable {d : ℕ} {M : SmoothManifold d}

/-- Repackage the proved endpoint equality with the actual evolution isotopy. -/
theorem endpointWitness (mu : ℝ → M.Form 1)
    {Z : Parameter → (x : M.Point) → M.Tangent x} (E : FirstPathFlow.Evolution Z)
    (he : MoserExactness.Endpoint mu E) :
    Witness M (mu 1) (mu 0) (E.map parameterZero parameterOne) (MoserExactness.gauge mu E) :=
  ⟨E.isotopy parameterOne, he⟩

theorem second_zero (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) :
    secondPrimitive P G T 0 = FirstPathExactness.primitive P G T 1 := by
  simp [secondPrimitive, FirstPathExactness.primitive]

theorem second_one (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) :
    secondPrimitive P G T 1 = ThirdPath.primitive P T 1 := by
  simp [secondPrimitive, ThirdPath.primitive, add_comm]

theorem fourth_zero (P : RadialReference M) (T : ExactSymplecticStructure M) :
    fourthPrimitive P T 0 = P.exactStructure.primitive := by
  funext x
  simp [fourthPrimitive, LinearAlgebraChecks.radialPrimitive]

theorem fourth_one (P : RadialReference M) (T : ExactSymplecticStructure M) :
    fourthPrimitive P T 1 = ThirdPath.primitive P T 0 := by
  simp [fourthPrimitive, ThirdPath.primitive]

section ExplicitWitness
variable (P : RadialReference M) (G : AdmissibleGrowth 1) (T : ExactSymplecticStructure M)
  (hw : WeaklyTames P.compatible T) {C : ℝ} (hC : 0 < C)
  (K : Set M.Point) (hK : IsCompact K)
  (hb : ∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * G.B (P.R x))

/-- Ψ = G4⁻¹ ∘ G3⁻¹ ∘ G2 ∘ G1, using all four actual forward endpoints. -/
def psi : M.SmoothEquiv M :=
  let G1 := (FirstPathFlow.evolution P G T hw hC K hK hb).map parameterZero parameterOne
  let G2 := (secondEvolution P G T hw).map parameterZero parameterOne
  let G3 := (ThirdPath.evolution P T hw).map parameterZero parameterOne
  let G4 := (fourthEvolution P T).map parameterZero parameterOne
  G1.trans (G2.trans (G3.symm.trans G4.symm))

/-- Literal composition/inversion gauge f for Ψ*β=λ+df. -/
def psiGauge : M.Point → ℝ :=
  let E1 := FirstPathFlow.evolution P G T hw hC K hK hb
  let E2 := secondEvolution P G T hw
  let E3 := ThirdPath.evolution P T hw
  let E4 := fourthEvolution P T
  let G1 := E1.map parameterZero parameterOne
  let G2 := E2.map parameterZero parameterOne
  let G3 := E3.map parameterZero parameterOne
  let G4 := E4.map parameterZero parameterOne
  let H1 := MoserExactness.gauge (FirstPathExactness.primitive P G T) E1
  let H2 := MoserExactness.gauge (secondPrimitive P G T) E2
  let H3 := MoserExactness.gauge (ThirdPath.primitive P T) E3
  let H4 := MoserExactness.gauge (fourthPrimitive P T) E4
  fun x => H1 x + (H2 (G1 x) +
    (-H3 (G3.symm (G2 (G1 x))) + -H4 (G4.symm (G3.symm (G2 (G1 x))))))

/-- Actual endpoint diffeomorphism F=Ψ⁻¹. -/
def comparisonMap : M.SmoothEquiv M := (psi P G T hw hC K hK hb).symm

/-- Actual smooth gauge h=-f∘F. -/
def comparisonGauge : M.Point → ℝ :=
  fun x => -psiGauge P G T hw hC K hK hb (comparisonMap P G T hw hC K hK hb x)

/-- All forward exactness applications are unconditional at the manuscript inputs.
The third and fourth arrows are inverted before composing; no endpoint is assumed. -/
theorem psiWitness : Witness M P.exactStructure.primitive T.primitive
    (psi P G T hw hC K hK hb) (psiGauge P G T hw hC K hK hb) := by
  have w1 := endpointWitness _ _
    (FirstPathExactness.firstPathExactness P G T hw C hC K hK hb).2
  have w2 := endpointWitness _ _ (second_exactness P G T hw).2
  have w3 := endpointWitness _ _ (third_exactness P T hw).2
  have w4 := endpointWitness _ _ (fourth_exactness P T).2
  rw [second_zero, second_one] at w2
  rw [fourth_zero, fourth_one] at w4
  have w := ((w4.symm.comp w3.symm).comp w2).comp w1
  simpa only [psi, psiGauge, FirstPathExactness.primitive, zero_smul, add_zero] using w

/-- Explicit native witness for the unchanged comparison conclusion. -/
theorem comparisonWitness : Witness M T.primitive P.exactStructure.primitive
    (comparisonMap P G T hw hC K hK hb) (comparisonGauge P G T hw hC K hK hb) :=
  (psiWitness P G T hw hC K hK hb).symm

include G hw hC K hK hb in
/-- Both primitive and exterior-derivative identities, with smooth forward/inverse isotopy. -/
theorem exactComparison : ExactComparison M T.primitive P.exactStructure.primitive :=
  (comparisonWitness P G T hw hC K hK hb).exactComparison

end ExplicitWitness

/-- Manuscript Theorem 1.1 at exactly the original quantifiers and compact exception. -/
theorem mainTarget : MainTarget := by
  intro d M P T hw hg
  obtain ⟨G, C, hC, K, hK, hb⟩ := hg
  exact exactComparison P G T hw hC K hK hb

end ExactLiouvilleComparison.MainComparison
