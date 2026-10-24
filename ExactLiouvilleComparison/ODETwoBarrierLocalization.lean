import ExactLiouvilleComparison.ODEClosedUniqueness

/-! Compact trajectory localization. Completeness is proved only for auxiliary cutoffs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter Function
namespace ExactLiouvilleComparison.ODE
variable {d : ℕ} {M : SmoothManifold d}

/-- Compactly supported native fields have actual globally smooth evolutions. -/
theorem smoothEvolution_of_compact_support
    (Z : ℝ → (x : M.Point) → M.Tangent x)
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)))
    {K : Set (ℝ × M.Point)} (hK : IsCompact K) (hz : ∀ p ∉ K, Z p.1 p.2 = 0) :
    Nonempty (SmoothEvolution Z) := by
  choose γ hi hd using CollarFlow.exists_global_solution hZ hK hz
  let Φ : ℝ → ℝ → M.Point → M.Point := fun s t x => γ s x t
  have hself : ∀ s x, Φ s s x = x := hi
  have hcomp : ∀ r s t x, Φ s t (Φ r s x) = Φ r t x := by
    intro r s t x
    exact congrFun (CollarFlow.eq_of_hasMFDerivAt hZ (hd s (Φ r s x)) (hd r x)
      (hi s (Φ r s x))) t
  have hinv : ∀ s t x, Φ t s (Φ s t x) = x := by
    intro s t x
    rw [hcomp, hself]
  have hs := CollarFlow.contMDiff_joint_of_hasMFDerivAt hZ Φ hself hd
  have hslice (s t : ℝ) : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ (Φ s t) :=
    hs.comp (contMDiff_const.prodMk (contMDiff_const.prodMk contMDiff_id))
  let H : ℝ → ℝ → M.SmoothEquiv M := fun s t =>
    { toEquiv := ⟨Φ s t, Φ t s, hinv s t, hinv t s⟩
      contMDiff_toFun := hslice s t
      contMDiff_invFun := hslice t s }
  refine ⟨⟨H, hself, hd, hs, hcomp, ?_⟩⟩
  intro s t
  ext x
  rfl

/-- Localize simultaneously around any compact collection of spacetime points. -/
theorem compact_field_localization
    (Z : ℝ → (x : M.Point) → M.Tangent x)
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)))
    {K : Set (ℝ × M.Point)} (hK : IsCompact K) :
    ∃ (W : ℝ → (x : M.Point) → M.Tangent x) (_H : SmoothEvolution W)
      (V : TopologicalSpace.Opens (ℝ × M.Point)),
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
        (fun p : ℝ × M.Point => (⟨p.2, W p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)) ∧
      K ⊆ V ∧ ∀ p ∈ V, W p.1 p.2 = Z p.1 p.2 := by
  let : LocallyCompactSpace (ModelProd ℝ (Model d)) :=
    inferInstanceAs (LocallyCompactSpace (ℝ × Model d))
  obtain ⟨χ, V, hχ, _, hKV, hone, hsupport, hsupp⟩ :=
    exists_bounded_smooth_compact_cutoff (I := (𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      hK isOpen_univ (subset_univ _)
  let W : ℝ → (x : M.Point) → M.Tangent x := fun t x => χ (t,x) • Z t x
  have hW := contMDiff_cutoff_field Z isOpen_univ hZ.contMDiffOn χ hχ hsupp
  obtain ⟨H⟩ := smoothEvolution_of_compact_support W hW hsupport
    (fun p hp => by simp only [W, image_eq_zero_of_notMem_tsupport hp, zero_smul])
  exact ⟨W, H, V, hW, hKV, fun p hp => by simp only [W, hone p hp, one_smul]⟩

/-- Native uniqueness on arbitrary closed time segments, proved using compact traces.
The original globally smooth field need not be complete. -/
theorem eqOn_closed_of_hasMFDerivWithinAt
    (Z : ℝ → (x : M.Point) → M.Tangent x)
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)))
    {γ δ : ℝ → M.Point} {s t : ℝ}
    (hcγ : ContinuousOn γ (uIcc s t)) (hcδ : ContinuousOn δ (uIcc s t))
    (hγ : ∀ u ∈ uIcc s t, HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ (uIcc s t) u
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z u (γ u))))
    (hδ : ∀ u ∈ uIcc s t, HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) δ (uIcc s t) u
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z u (δ u))))
    (hi : γ s = δ s) : γ t = δ t := by
  have hK := (isCompact_uIcc.image_of_continuousOn (continuousOn_id.prodMk hcγ)).union
    (isCompact_uIcc.image_of_continuousOn (continuousOn_id.prodMk hcδ))
  obtain ⟨W, H, V, hW, hKV, heq⟩ := compact_field_localization Z hZ hK
  have heγ : γ t = H.map s t (γ s) := H.unique_closed hW (fun u hu => by
    rw [heq (u, γ u) (hKV (Or.inl ⟨u, hu, rfl⟩))]
    exact hγ u hu)
  have heδ : δ t = H.map s t (δ s) := H.unique_closed hW (fun u hu => by
    rw [heq (u, δ u) (hKV (Or.inr ⟨u, hu, rfl⟩))]
    exact hδ u hu)
  rw [heγ, heδ, hi]

end ExactLiouvilleComparison.ODE
