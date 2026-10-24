import ExactLiouvilleComparison.FirstPathFlowInputs
import ExactLiouvilleComparison.ODEClosedUniqueness

/-! Constructed first-path evolution and identity-start smooth diffeomorphism isotopy. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.FirstPathFlow
variable {d : ℕ} {M : SmoothManifold d}

/-- Construct the bounded evolution from native open regularity and proper scalar control.
The all-real auxiliary field is proved to agree with the supplied field on the strip. -/
theorem evolution_of_scalar_bound (E : ℝ → (x : M.Point) → M.Tangent x)
    {Ω : Set (ℝ × M.Point)} (hΩ : IsOpen Ω) (hstrip : parameterInterval ×ˢ univ ⊆ Ω)
    (hE : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, E p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)) Ω)
    (P : M.Point → ℝ) (hP : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ P)
    (hp : IsProperMap P) (hl : BddBelow (range P))
    {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ t ∈ parameterInterval, ∀ x, |M.scalarDerivative P x (E t x)| ≤ D) :
    Nonempty (Evolution (fun t : Parameter => E t.val)) := by
  obtain ⟨W, hW, heq, hbound⟩ := ODE.globally_bounded_extension E hΩ hstrip hE P hP hD hb
  obtain ⟨H⟩ := ODE.smoothEvolution_of_scalar_bound W hW P hP hp hl (by linarith : 0 ≤ D+2) hbound
  have hsol (s : Parameter) (x : M.Point) :
      IsSolution (fun t : Parameter => E t.val) (fun t => H.map s.val t x) parameterInterval := by
    refine ⟨?_, ?_⟩
    · exact (continuous_iff_continuousAt.mpr (fun t => (H.solves s.val x t).continuousAt)).continuousOn
    · intro t _ ht
      simpa only [heq t ht] using (H.solves s.val x t).hasMFDerivWithinAt (s := parameterInterval)
  refine ⟨{
    map := fun s t => H.map s.val t.val
    extension := fun s t => H.map s t
    agrees := fun _ _ => rfl
    smooth := ⟨univ, isOpen_univ, subset_univ _, H.smooth.contMDiffOn⟩
    initial := fun s => H.initial s.val
    solves := hsol
    chart_solves := ?_
    unique := ?_
    compose := fun r s t => H.compose r.val s.val t.val
    inverse := fun s t => H.inverse s.val t.val
    isotopy := fun t => H.isotopy t.val }⟩
  · intro s t x a ha
    exact ODE.chart_hasDerivWithinAt _ (hsol s x) t.property t.property a ha
  · intro s t γ hγ
    apply H.unique_closed hW
    intro u hu
    have hi : u ∈ parameterInterval := by
      have hsub : uIcc s.val t.val ⊆ Icc (0 : ℝ) 1 :=
        uIcc_subset_Icc s.property t.property
      exact hsub hu
    simpa only [heq u hi] using hγ.2 u hu hi

/-- The exact reviewed first-path target, for every admissible B and its original
arbitrary compact exception. Every output field is constructed by the preceding proofs. -/
theorem firstPathFlow : Target (M := M) := by
  intro P G T hw C hC K hK hb
  obtain ⟨E, heq, ⟨Ω, hΩ, hstrip, hE⟩, hP, hp, hl, D, hD, hbound⟩ :=
    first_native_data P G T hw hC K hK hb
  have hfields : (fun t : Parameter => E t.val) = MoserRegularity.firstField P G T hw := by
    funext t x
    exact heq t x
  simpa only [hfields] using evolution_of_scalar_bound E hΩ hstrip hE
    (FirstPath.exhaustion P G) hP hp hl hD hbound

/-- Original GrowthAtInfinity consumer, using the same delivered smoothness and
proper-exhaustion witness and exposing the literal FirstPath.X. -/
theorem firstPathFlow_of_growth : GrowthTarget (M := M) := by
  intro P T hw hg
  obtain ⟨G, E, heq, ⟨Ω, hΩ, hstrip, hE⟩, hP, hp, hl, D, hD, hbound⟩ :=
    first_growth_data P T hw hg
  refine ⟨G, ?_⟩
  have hfields : (fun t : Parameter => E t.val) =
      (fun t x => FirstPath.X P G T hw x t.val t.property.1) := by
    funext t x
    exact heq t x
  simpa only [hfields] using evolution_of_scalar_bound E hΩ hstrip hE
    (FirstPath.exhaustion P G) hP hp hl hD hbound

/-- A chosen actual evolution, justified by firstPathFlow rather than assumed. -/
def evolution (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    {C : ℝ} (hC : 0 < C) (K : Set M.Point) (hK : IsCompact K)
    (hb : ∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * G.B (P.R x)) :
    Evolution (MoserRegularity.firstField P G T hw) :=
  Classical.choice (firstPathFlow P G T hw C hC K hK hb)
end ExactLiouvilleComparison.FirstPathFlow
