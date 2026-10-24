import ExactLiouvilleComparison.ODEGlobalExistence
import FsFltz.Geometry.CollarSmoothEvolution

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Function
namespace ExactLiouvilleComparison.ODE
variable {d : ℕ} {M : SmoothManifold d}

/-- Output of the global auxiliary-field construction. -/
structure SmoothEvolution (Z : ℝ → (x : M.Point) → M.Tangent x) where
  map : ℝ → ℝ → M.SmoothEquiv M
  initial : ∀ s x, map s s x = x
  solves : ∀ s x t, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun u => map s u x) t
    ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (map s t x)))
  smooth : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
    𝓘(ℝ, Model d) ∞ (fun p : ℝ × (ℝ × M.Point) => map p.1 p.2.1 p.2.2)
  compose : ∀ r s t x, map s t (map r s x) = map r t x
  inverse : ∀ s t, (map s t).symm = map t s

/-- Choose only the already constructed curves; native uniqueness and the pinned
smooth-dependence theorem then construct actual smooth diffeomorphisms. -/
theorem smoothEvolution_of_scalar_bound
    (Z : ℝ → (x : M.Point) → M.Tangent x)
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)))
    (P : M.Point → ℝ) (hP : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ P)
    (hp : IsProperMap P) (hl : BddBelow (range P))
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ t x, |M.scalarDerivative P x (Z t x)| ≤ D) :
    Nonempty (SmoothEvolution Z) := by
  choose γ hi hd using global_solution_of_scalar_bound Z hZ P hP hp hl hD hb
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

/-- Every slice of the constructed evolution starting at zero is smoothly
isotopic to identity, with smooth inverse family as required by Geometry.lean. -/
theorem SmoothEvolution.isotopy {Z : ℝ → (x : M.Point) → M.Tangent x}
    (H : SmoothEvolution Z) (t : ℝ) : SmoothlyIsotopicToIdentity M (H.map 0 t) := by
  refine ⟨fun u => H.map 0 (u*t), ?_, ?_, ?_, ?_⟩
  · intro x
    simpa only [zero_mul] using H.initial 0 x
  · intro x
    simp only [one_mul]
  · exact (H.smooth.comp
      (contMDiff_const.prodMk ((contMDiff_fst.mul contMDiff_const).prodMk contMDiff_snd))).contMDiffOn
  · have he : (fun p : ℝ × M.Point => (H.map 0 (p.1*t)).symm p.2) =
        (fun p : ℝ × M.Point => H.map (p.1*t) 0 p.2) := by
      funext p
      rw [H.inverse]
    rw [he]
    exact (H.smooth.comp
      ((contMDiff_fst.mul contMDiff_const).prodMk (contMDiff_const.prodMk contMDiff_snd))).contMDiffOn
end ExactLiouvilleComparison.ODE
