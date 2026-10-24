import ExactLiouvilleComparison.ODETwoBarrierLocalization

/-! Smooth local representatives on open neighborhoods of both time parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter Function
namespace ExactLiouvilleComparison.ODE
variable {d : ℕ} {M : SmoothManifold d}

/-- An auxiliary evolution restricted to an open set where it solves the original field.
These patches are constructed below from individual finite trajectories. -/
structure EvolutionPatch (Z : ℝ → (x : M.Point) → M.Tangent x) where
  map : ℝ → ℝ → M.Point → M.Point
  smooth : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
    𝓘(ℝ, Model d) ∞ (fun p : ℝ × (ℝ × M.Point) => map p.1 p.2.1 p.2.2)
  initial : ∀ s x, map s s x = x
  a : ℝ
  b : ℝ
  left : a < 0
  right : 1 < b
  source : Set (ℝ × M.Point)
  open_source : IsOpen source
  source_time : ∀ p ∈ source, p.1 ∈ Ioo a b
  solves : ∀ p ∈ source, ∀ t ∈ Ioo a b,
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun u => map p.1 u p.2) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (map p.1 t p.2)))

/-- An open set containing the unit interval contains a slightly larger closed interval. -/
theorem enlarged_interval {S : Set ℝ} (hS : IsOpen S) (hI : Icc (0 : ℝ) 1 ⊆ S) :
    ∃ a b : ℝ, a < 0 ∧ 1 < b ∧ Icc a b ⊆ S := by
  obtain ⟨l, r, hlr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hS.mem_nhds (hI (left_mem_Icc.mpr zero_le_one)))
  obtain ⟨l', r', hlr', hsub'⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hS.mem_nhds (hI (right_mem_Icc.mpr zero_le_one)))
  refine ⟨l/2, (r'+1)/2, by linarith [hlr.1], by linarith [hlr'.2], ?_⟩
  intro u hu
  by_cases h0 : u < 0
  · apply hsub
    constructor <;> linarith [hu.1, hlr.1, hlr.2]
  by_cases h1 : 1 < u
  · apply hsub'
    constructor <;> linarith [hu.2, hlr'.1, hlr'.2]
  exact hI ⟨le_of_not_gt h0, le_of_not_gt h1⟩

/-- A finite native trajectory yields one globally smooth representative on an open
neighborhood of its initial data and all terminal parameters, including both endpoints. -/
theorem evolutionPatch_of_finite_curve
    (Z : ℝ → (x : M.Point) → M.Tangent x)
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)))
    (s : Parameter) (x : M.Point) {γ : ℝ → M.Point} (hi : γ s.val = x)
    (hγ : ∀ t ∈ parameterInterval, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t)))) :
    ∃ P : EvolutionPatch Z, (s.val, x) ∈ P.source := by
  have hc : ContinuousOn γ parameterInterval := fun t ht => (hγ t ht).continuousAt.continuousWithinAt
  have hK := (show IsCompact parameterInterval from isCompact_Icc).image_of_continuousOn
    (continuousOn_id.prodMk hc)
  obtain ⟨W, H, V, hW, hKV, heq⟩ := compact_field_localization Z hZ hK
  have hsame (t : ℝ) (ht : t ∈ parameterInterval) : γ t = H.map s.val t x := by
    rw [← hi]
    apply H.unique_closed hW
    intro u hu
    have huI := uIcc_subset_Icc s.property ht hu
    rw [heq (u, γ u) (hKV ⟨u, huI, rfl⟩)]
    exact (hγ u huI).hasMFDerivWithinAt
  have hcont : Continuous (fun p : (ℝ × M.Point) × ℝ =>
      (p.2, H.map p.1.1 p.2 p.1.2)) :=
    continuous_snd.prodMk (H.smooth.continuous.comp
      ((continuous_fst.fst).prodMk (continuous_snd.prodMk continuous_fst.snd)))
  have htime : IsOpen {u : ℝ | (u, H.map s.val u x) ∈ V} :=
    V.isOpen.preimage (continuous_id.prodMk (H.smooth.continuous.comp
      (continuous_const.prodMk (continuous_id.prodMk continuous_const))))
  obtain ⟨a, b, ha, hb, habV⟩ := enlarged_interval htime (fun t ht => by
    change (t, H.map s.val t x) ∈ V
    rw [← hsame t ht]
    exact hKV ⟨t, ht, rfl⟩)
  let A : Set (ℝ × M.Point) := {p | ∀ u ∈ Icc a b, (u, H.map p.1 u p.2) ∈ V}
  have hA : IsOpen A := by
    apply isOpen_iff_eventually.mpr
    intro p hp
    exact isCompact_Icc.eventually_forall_of_forall_eventually (fun u hu =>
      hcont.continuousAt.preimage_mem_nhds (V.isOpen.mem_nhds (hp u hu)))
  let S : Set (ℝ × M.Point) := A ∩ Prod.fst ⁻¹' Ioo a b
  refine ⟨{
    map := fun r t y => H.map r t y
    smooth := H.smooth
    initial := H.initial
    a := a
    b := b
    left := ha
    right := hb
    source := S
    open_source := hA.inter (isOpen_Ioo.preimage continuous_fst)
    source_time := fun _ hp => hp.2
    solves := ?_ }, ?_⟩
  · intro p hp t ht
    simpa only [heq (t, H.map p.1 t p.2) (hp.1 t (Ioo_subset_Icc_self ht))] using
      H.solves p.1 p.2 t
  · exact ⟨habV, ⟨ha.trans_le s.property.1, s.property.2.trans_lt hb⟩⟩

namespace EvolutionPatch
variable {Z : ℝ → (x : M.Point) → M.Tangent x}
def domain (P : EvolutionPatch Z) : Set (ℝ × (ℝ × M.Point)) :=
  {p | (p.1, p.2.2) ∈ P.source ∧ p.2.1 ∈ Ioo P.a P.b}

theorem open_domain (P : EvolutionPatch Z) : IsOpen P.domain :=
  (P.open_source.preimage (continuous_fst.prodMk continuous_snd.snd)).inter
    (isOpen_Ioo.preimage continuous_snd.fst)

/-- Distinct auxiliary cutoffs give the same original trajectory on overlapping patches. -/
theorem agree
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)))
    (P Q : EvolutionPatch Z) {p : ℝ × (ℝ × M.Point)}
    (hp : p ∈ P.domain) (hq : p ∈ Q.domain) :
    P.map p.1 p.2.1 p.2.2 = Q.map p.1 p.2.1 p.2.2 := by
  apply CollarFlow.eqOn_of_hasMFDerivAt hZ
    (a := max P.a Q.a) (b := min P.b Q.b) (t₀ := p.1)
    ⟨max_lt (P.source_time _ hp.1).1 (Q.source_time _ hq.1).1,
      lt_min (P.source_time _ hp.1).2 (Q.source_time _ hq.1).2⟩
    (fun u hu => P.solves _ hp.1 u ⟨(le_max_left _ _).trans_lt hu.1,
      hu.2.trans_le (min_le_left _ _)⟩)
    (fun u hu => Q.solves _ hq.1 u ⟨(le_max_right _ _).trans_lt hu.1,
      hu.2.trans_le (min_le_right _ _)⟩)
    (by rw [P.initial, Q.initial])
    ⟨max_lt hp.2.1 hq.2.1, lt_min hp.2.2 hq.2.2⟩
end EvolutionPatch
end ExactLiouvilleComparison.ODE
