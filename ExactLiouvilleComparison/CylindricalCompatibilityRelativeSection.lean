import FsFltz.Geometry.Smooth
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-! Relative gluing of native smooth sections in convex fiber sets.
This will glue positive metrics while fixing the entire closed end. -/
noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace ExactLiouvilleComparison.CylindricalCompatibility.RelativeSection

variable {E H M F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (V : M → Type*) [∀ x, AddCommGroup (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

/-- Relative convex gluing. Only local sections away from the prescribed closed
set are needed. The result agrees on every point of K, including its boundary. -/
theorem exists_relative_section
    (t : ∀ x, Set (V x)) (ht : ∀ x, Convex ℝ (t x))
    (K U : Set M) (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (s₀ : (x : M) → V x)
    (hs₀ : ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x (s₀ x)) U)
    (hs₀mem : ∀ x ∈ U, s₀ x ∈ t x)
    (hloc : ∀ x ∉ K, ∃ W ∈ 𝓝 x, ∃ s : (y : M) → V y,
      ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞
        (fun y => TotalSpace.mk' F y (s y)) W ∧ ∀ y ∈ W, s y ∈ t y) :
    ∃ s : Cₛ^∞⟮I; F, V⟯, (∀ x, s x ∈ t x) ∧ ∀ x ∈ K, s x = s₀ x := by
  let A (x : M) : Set (V x) := {v | v ∈ t x ∧ (x ∈ K → v = s₀ x)}
  have hconv : ∀ x, Convex ℝ (A x) := by
    intro x v hv w hw a b ha hb hab
    refine ⟨ht x hv.1 hw.1 ha hb hab, ?_⟩
    intro hx
    simp only [hv.2 hx, hw.2 hx, ← add_smul, hab, one_smul]
  have hlocal : ∀ x : M, ∃ W ∈ 𝓝 x, ∃ s : (y : M) → V y,
      ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞
        (fun y => TotalSpace.mk' F y (s y)) W ∧ ∀ y ∈ W, s y ∈ A y := by
    intro x
    by_cases hx : x ∈ K
    · exact ⟨U, hU.mem_nhds (hKU hx), s₀, hs₀,
        fun y hy => ⟨hs₀mem y hy, fun _ => rfl⟩⟩
    · obtain ⟨W, hW, s, hs, hsmem⟩ := hloc x hx
      refine ⟨W ∩ Kᶜ, inter_mem hW (hK.isOpen_compl.mem_nhds hx),
        s, hs.mono inter_subset_left, ?_⟩
      intro y hy
      exact ⟨hsmem y hy.1, fun hyK => False.elim (hy.2 hyK)⟩
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local I V A hconv hlocal
  exact ⟨s, fun x => (hs x).1, fun x hx => (hs x).2 hx⟩

end ExactLiouvilleComparison.CylindricalCompatibility.RelativeSection

namespace ExactLiouvilleComparison.CylindricalCompatibility.RelativeMetric

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

def SPD (g : E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  (∀ v w, g v w = g w v) ∧ ∀ v, v ≠ 0 → 0 < g v v

theorem convex_SPD : Convex ℝ {g : E →L[ℝ] E →L[ℝ] ℝ | SPD g} := by
  intro g hg h hh a b ha hb hab
  constructor
  · intro v w
    change a * g v w + b * h v w = a * g w v + b * h w v
    rw [hg.1 v w, hh.1 v w]
  · intro v hv
    change 0 < a * g v v + b * h v v
    have hgv := hg.2 v hv
    have hhv := hh.2 v hv
    rcases lt_or_eq_of_le ha with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hgv) (mul_nonneg hb hhv.le)
    · have hb' : b = 1 := by linarith
      simp [← ha', hb', hhv]

end ExactLiouvilleComparison.CylindricalCompatibility.RelativeMetric
