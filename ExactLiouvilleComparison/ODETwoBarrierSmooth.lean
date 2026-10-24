import ExactLiouvilleComparison.ODETwoBarrierSmoothAssembly
import ExactLiouvilleComparison.ODEIntervalRegularity

/-! Finite native existence implies the full closed-interval smooth evolution contract. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Classical
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter Function
namespace ExactLiouvilleComparison.ODE
variable {d : ℕ} {M : SmoothManifold d}

/-- Assemble actual smooth diffeomorphisms, equations, uniqueness, inverse and isotopy
from finite trajectories. The globally smooth field is not assumed complete. -/
theorem evolution_of_finite_existence_global
    (Z : ℝ → (x : M.Point) → M.Tangent x)
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)))
    (hex : ∀ (s : Parameter) (x : M.Point), ∃ γ : ℝ → M.Point, γ s.val = x ∧
      ∀ t ∈ parameterInterval, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t)))) :
    Nonempty (FirstPathFlow.Evolution (fun t : Parameter => Z t.val)) := by
  let Φ := localEvolution Z
  have hcover := strip_subset_evolutionDomain hZ hex
  have hmem (s t : Parameter) (x : M.Point) : (s.val,t.val,x) ∈ evolutionDomain Z :=
    hcover ⟨s.property, t.property, mem_univ _⟩
  have hi (s : ℝ) (x : M.Point) : Φ s s x = x := localEvolution_initial hZ s x
  have hd (s : Parameter) (x : M.Point) (t : ℝ) (ht : t ∈ parameterInterval) :
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun u => Φ s.val u x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (Φ s.val t x))) :=
    localEvolution_solves hZ (hmem s ⟨t, ht⟩ x)
  have hc (s : Parameter) (x : M.Point) : ContinuousOn (fun u => Φ s.val u x) parameterInterval :=
    fun t ht => (hd s x t ht).continuousAt.continuousWithinAt
  have huniq (s t : Parameter) (γ : ℝ → M.Point)
      (hγ : FirstPathFlow.IsSolution (fun t : Parameter => Z t.val) γ (uIcc s.val t.val)) :
      γ t.val = Φ s.val t.val (γ s.val) := by
    have hsub : uIcc s.val t.val ⊆ parameterInterval := uIcc_subset_Icc s.property t.property
    exact eqOn_closed_of_hasMFDerivWithinAt Z hZ hγ.1 ((hc s (γ s.val)).mono hsub)
      (fun u hu => hγ.2 u hu (hsub hu))
      (fun u hu => (hd s (γ s.val) u (hsub hu)).hasMFDerivWithinAt)
      (hi s.val (γ s.val)).symm
  have hcomp (r s t : Parameter) (x : M.Point) :
      Φ s.val t.val (Φ r.val s.val x) = Φ r.val t.val x := by
    symm
    apply huniq s t (fun u => Φ r.val u x)
    exact ⟨(hc r x).mono (uIcc_subset_Icc s.property t.property),
      fun u _ hu => (hd r x u hu).hasMFDerivWithinAt⟩
  have hinv (s t : Parameter) (x : M.Point) : Φ t.val s.val (Φ s.val t.val x) = x := by
    rw [hcomp, hi]
  have hslice (s t : Parameter) : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ (Φ s.val t.val) := by
    intro x
    exact (localEvolution_contMDiffAt hZ (hmem s t x)).comp x
      (contMDiffAt_const.prodMk (contMDiffAt_const.prodMk contMDiffAt_id))
  let H : Parameter → Parameter → M.SmoothEquiv M := fun s t =>
    { toEquiv := ⟨Φ s.val t.val, Φ t.val s.val, hinv s t, hinv t s⟩
      contMDiff_toFun := hslice s t
      contMDiff_invFun := hslice t s }
  have hsol (s : Parameter) (x : M.Point) :
      FirstPathFlow.IsSolution (fun t : Parameter => Z t.val) (fun u => Φ s.val u x) parameterInterval :=
    ⟨hc s x, fun u _ hu => (hd s x u hu).hasMFDerivWithinAt⟩
  refine ⟨{
    map := H
    extension := Φ
    agrees := fun _ _ => rfl
    smooth := ⟨evolutionDomain Z, isOpen_evolutionDomain, hcover,
      fun p hp => (localEvolution_contMDiffAt hZ hp).contMDiffWithinAt⟩
    initial := fun s => hi s.val
    solves := hsol
    chart_solves := ?_
    unique := huniq
    compose := hcomp
    inverse := ?_
    isotopy := ?_ }⟩
  · intro s t x a ha
    exact chart_hasDerivWithinAt _ (hsol s x) t.property t.property a ha
  · intro s t
    ext x
    rfl
  · intro t
    let q : ℝ → Parameter := fun u => ⟨(projIcc 0 1 zero_le_one u).val * t.val,
      mul_nonneg (projIcc 0 1 zero_le_one u).property.1 t.property.1,
      (mul_le_mul_of_nonneg_right (projIcc 0 1 zero_le_one u).property.2 t.property.1).trans (by simpa using t.property.2)⟩
    have hq (u : ℝ) (hu : u ∈ parameterInterval) : (q u).val = u * t.val := by
      simp only [q, projIcc_of_mem _ hu]
    have hq0 : q 0 = parameterZero := Subtype.ext (by rw [hq _ ⟨le_rfl, zero_le_one⟩, zero_mul]; rfl)
    have hq1 : q 1 = t := Subtype.ext (by rw [hq _ ⟨zero_le_one, le_rfl⟩, one_mul])
    refine ⟨fun u => H parameterZero (q u), ?_, ?_, ?_, ?_⟩
    · intro x
      change H parameterZero (q 0) x = x
      rw [hq0]
      exact hi 0 x
    · intro x
      change H parameterZero (q 1) x = H parameterZero t x
      rw [hq1]
    · have hs : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
          (fun p : ℝ × M.Point => Φ 0 (p.1*t.val) p.2) (parameterInterval ×ˢ univ) := by
        intro p hp
        have hm : (0, p.1*t.val, p.2) ∈ evolutionDomain Z := by
          rw [← hq p.1 hp.1]
          exact hmem parameterZero (q p.1) p.2
        exact ((localEvolution_contMDiffAt hZ hm).comp p
          (contMDiffAt_const.prodMk ((contMDiffAt_fst.mul contMDiffAt_const).prodMk contMDiffAt_snd))).contMDiffWithinAt
      apply hs.congr
      intro p hp
      change Φ 0 (q p.1).val p.2 = Φ 0 (p.1*t.val) p.2
      rw [hq p.1 hp.1]
    · have hs : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
          (fun p : ℝ × M.Point => Φ (p.1*t.val) 0 p.2) (parameterInterval ×ˢ univ) := by
        intro p hp
        have hm : (p.1*t.val, 0, p.2) ∈ evolutionDomain Z := by
          rw [← hq p.1 hp.1]
          exact hmem (q p.1) parameterZero p.2
        exact ((localEvolution_contMDiffAt hZ hm).comp p
          ((contMDiffAt_fst.mul contMDiffAt_const).prodMk
            (contMDiffAt_const.prodMk contMDiffAt_snd))).contMDiffWithinAt
      apply hs.congr
      intro p hp
      change Φ (q p.1).val 0 p.2 = Φ (p.1*t.val) 0 p.2
      rw [hq p.1 hp.1]

/-- The mission bridge: native smoothness on an open neighborhood of the closed strip
and finite native trajectories imply the entire unchanged `Evolution` contract. -/
theorem evolution_of_finite_existence
    (Z : ℝ → (x : M.Point) → M.Tangent x)
    {Ω : Set (ℝ × M.Point)} (hΩ : IsOpen Ω) (hstrip : parameterInterval ×ˢ univ ⊆ Ω)
    (hZ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)) Ω)
    (hex : ∀ (s : Parameter) (x : M.Point), ∃ γ : ℝ → M.Point, γ s.val = x ∧
      ∀ t ∈ parameterInterval, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t)))) :
    Nonempty (FirstPathFlow.Evolution (fun t : Parameter => Z t.val)) := by
  obtain ⟨W, hW, heq⟩ := extend_strip_field Z hΩ hstrip hZ
  have hexW : ∀ (s : Parameter) (x : M.Point), ∃ γ : ℝ → M.Point, γ s.val = x ∧
      ∀ t ∈ parameterInterval, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (W t (γ t))) := by
    intro s x
    obtain ⟨γ, hi, hd⟩ := hex s x
    exact ⟨γ, hi, fun t ht => by rw [heq t ht]; exact hd t ht⟩
  have hfields : (fun t : Parameter => W t.val) = (fun t : Parameter => Z t.val) := by
    funext t
    exact heq t.val t.property
  simpa only [hfields] using evolution_of_finite_existence_global W hW hexW

end ExactLiouvilleComparison.ODE
