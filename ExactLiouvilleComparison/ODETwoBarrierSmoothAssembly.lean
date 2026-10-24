import ExactLiouvilleComparison.ODETwoBarrierLocalizationPatch

/-! Uniqueness glues the smooth patches on an actual open double-time domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Classical
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter Function
namespace ExactLiouvilleComparison.ODE
variable {d : ℕ} {M : SmoothManifold d}

/-- The union of domains of constructed local representatives. -/
def evolutionDomain (Z : ℝ → (x : M.Point) → M.Tangent x) : Set (ℝ × (ℝ × M.Point)) :=
  {p | ∃ P : EvolutionPatch Z, p ∈ P.domain}

/-- The value is independent of the chosen patch by native uniqueness. Outside the
open domain the arbitrary value is the input point; no regularity is claimed there. -/
def localEvolution (Z : ℝ → (x : M.Point) → M.Tangent x) (s t : ℝ) (x : M.Point) : M.Point :=
  if h : (s, t, x) ∈ evolutionDomain Z then (Classical.choose h).map s t x else x

variable {Z : ℝ → (x : M.Point) → M.Tangent x}
variable (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
  (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)))

include hZ

theorem localEvolution_eq_patch (P : EvolutionPatch Z) {p : ℝ × (ℝ × M.Point)}
    (hp : p ∈ P.domain) : localEvolution Z p.1 p.2.1 p.2.2 = P.map p.1 p.2.1 p.2.2 := by
  have h : p ∈ evolutionDomain Z := ⟨P, hp⟩
  rw [localEvolution, dite_eq_left h]
  exact (Classical.choose h).agree hZ P (Classical.choose_spec h) hp

omit hZ in
theorem isOpen_evolutionDomain : IsOpen (evolutionDomain Z) := by
  apply isOpen_iff_eventually.mpr
  rintro p ⟨P, hp⟩
  filter_upwards [P.open_domain.mem_nhds hp] with q hq
  exact ⟨P, hq⟩

theorem localEvolution_contMDiffAt {p : ℝ × (ℝ × M.Point)} (hp : p ∈ evolutionDomain Z) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
      𝓘(ℝ, Model d) ∞ (fun q => localEvolution Z q.1 q.2.1 q.2.2) p := by
  obtain ⟨P, hp⟩ := hp
  apply (P.smooth p).congr_of_eventuallyEq
  filter_upwards [P.open_domain.mem_nhds hp] with q hq
  exact localEvolution_eq_patch hZ P hq

theorem localEvolution_initial (s : ℝ) (x : M.Point) : localEvolution Z s s x = x := by
  by_cases h : (s,s,x) ∈ evolutionDomain Z
  · obtain ⟨P, hp⟩ := h
    rw [localEvolution_eq_patch hZ P hp, P.initial]
  · simp only [localEvolution, dite_eq_right h]

theorem localEvolution_solves {s t : ℝ} {x : M.Point}
    (hp : (s,t,x) ∈ evolutionDomain Z) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun u => localEvolution Z s u x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (localEvolution Z s t x))) := by
  obtain ⟨P, hp⟩ := hp
  have he : (fun u => localEvolution Z s u x) =ᶠ[𝓝 t] (fun u => P.map s u x) := by
    filter_upwards [isOpen_Ioo.mem_nhds hp.2] with u hu
    exact localEvolution_eq_patch hZ P (show (s,u,x) ∈ P.domain from ⟨hp.1, hu⟩)
  rw [localEvolution_eq_patch hZ P hp]
  exact (P.solves _ hp.1 t hp.2).congr_of_eventuallyEq_abuse he

/-- Finite existence covers the entire closed double-time strip by genuine open patches. -/
theorem strip_subset_evolutionDomain
    (hex : ∀ (s : Parameter) (x : M.Point), ∃ γ : ℝ → M.Point, γ s.val = x ∧
      ∀ t ∈ parameterInterval, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t)))) :
    parameterInterval ×ˢ (parameterInterval ×ˢ (univ : Set M.Point)) ⊆ evolutionDomain Z := by
  intro p hp
  obtain ⟨γ, hi, hd⟩ := hex ⟨p.1, hp.1⟩ p.2.2
  obtain ⟨P, hP⟩ := evolutionPatch_of_finite_curve Z hZ ⟨p.1, hp.1⟩ p.2.2 hi hd
  exact ⟨P, hP, P.left.trans_le hp.2.1.1, hp.2.1.2.trans_lt P.right⟩

end ExactLiouvilleComparison.ODE
