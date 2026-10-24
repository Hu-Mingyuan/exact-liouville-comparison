import ExactLiouvilleComparison.MoserRegularityFields
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.MoserRegularity
variable {d : ℕ} {M : SmoothManifold d}

/-- Continuity on the actual compact time parameter space follows from native joint regularity. -/
theorem NativeJoint.continuous_section {Z : Parameter → (x : M.Point) → M.Tangent x}
    (hZ : NativeJoint Z) :
    Continuous (fun p : Parameter × M.Point =>
      (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)) := by
  obtain ⟨E, he, hs⟩ := hZ
  have hc : Continuous (fun p : Parameter × M.Point => (p.1.val, p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  apply continuous_iff_continuousAt.mpr
  intro p
  have h := (hs (p.1.val, p.2) p.1.property).continuousAt.comp (f := fun q : Parameter × M.Point => (q.1.val, q.2))
    (hc.continuousAt (x := p))
  simpa only [Function.comp_def, he] using h

theorem NativeJoint.continuous_scalarDerivative
    {Z : Parameter → (x : M.Point) → M.Tangent x} (hZ : NativeJoint Z)
    (f : M.Point → ℝ) (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ f) :
    Continuous (fun p : Parameter × M.Point => M.scalarDerivative f p.2 (Z p.1 p.2)) := by
  exact ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).continuous.comp
    ((hf.continuous_tangentMap (by simp)).comp hZ.continuous_section)).snd

/-- Compactness yields a uniform absolute bound, including an empty compact set. -/
theorem compact_abs_bound (f : Parameter × M.Point → ℝ) (hf : Continuous f)
    (K : Set M.Point) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : Parameter, ∀ x ∈ K, |f (t,x)| ≤ C := by
  obtain ⟨b, hb⟩ := ((isCompact_univ (X := Parameter)).prod hK).bddAbove_image
    hf.abs.continuousOn
  refine ⟨max 0 b, le_max_left _ _, ?_⟩
  intro t x hx
  exact (hb (mem_image_of_mem _ ⟨mem_univ t, hx⟩)).trans (le_max_right _ _)

theorem NativeJoint.compact_scalar_bound
    {Z : Parameter → (x : M.Point) → M.Tangent x} (hZ : NativeJoint Z)
    (f : M.Point → ℝ) (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ f)
    (K : Set M.Point) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : Parameter, ∀ x ∈ K, |M.scalarDerivative f x (Z t x)| ≤ C :=
  compact_abs_bound _ (hZ.continuous_scalarDerivative f hf) K hK

theorem first_compact (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T) :
    FirstTarget P G T hw :=
  ⟨first_joint P G T hw, fun K hK => (first_joint P G T hw).compact_scalar_bound _
    (FirstPath.exhaustion_smooth P G) K hK⟩

/-- Differential linearity for the actual scalar derivative. -/
theorem scalarDerivative_linear (f g : M.Point → ℝ)
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ g)
    (a b : ℝ) (x : M.Point) (v : M.Tangent x) :
    M.scalarDerivative (fun y => a * f y + b * g y) x v =
      a * M.scalarDerivative f x v + b * M.scalarDerivative g x v := by
  have h := ((hf.mdifferentiable (by simp) x).hasMFDerivAt.const_smul a).add
    ((hg.mdifferentiable (by simp) x).hasMFDerivAt.const_smul b)
  exact congrArg (fun L => L v) h.mfderiv

def radialQ (P : RadialReference M) (q : RadialCoefficient P.rstar) (x : M.Point) : ℝ :=
  P.R x * q.rho (P.R x)

theorem radialQ_smooth (P : RadialReference M) (q : RadialCoefficient P.rstar) :
    ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ (radialQ P q) :=
  contDiff_mul.contMDiff.comp (P.smooth_R.prodMk_space q.smooth_comp)

theorem barrierRate_linear (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (Z : Parameter → (x : M.Point) → M.Tangent x) (t : Parameter) (x : M.Point) :
    barrierRate P q₀ q₁ Z t x = RadialInterpolation.delta q₀ q₁ (P.R x) * P.R x +
      ((1-t.val) * M.scalarDerivative (radialQ P q₀) x (Z t x) +
      t.val * M.scalarDerivative (radialQ P q₁) x (Z t x)) := by
  unfold barrierRate
  have he : (fun y => RadialInterpolation.Q q₀ q₁ t.val (P.R y)) =
      (fun y => (1-t.val) * radialQ P q₀ y + t.val * radialQ P q₁ y) := by
    funext y
    dsimp [RadialInterpolation.Q, RadialInterpolation.rho, radialQ]
    ring
  rw [he, scalarDerivative_linear _ _ (radialQ_smooth P q₀) (radialQ_smooth P q₁)]

theorem barrierRate_continuous (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (Z : Parameter → (x : M.Point) → M.Tangent x) (hZ : NativeJoint Z) :
    Continuous (fun p : Parameter × M.Point => barrierRate P q₀ q₁ Z p.1 p.2) := by
  have ht : Continuous (fun p : Parameter × M.Point => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hd : Continuous (fun p : Parameter × M.Point =>
      RadialInterpolation.delta q₀ q₁ (P.R p.2) * P.R p.2) :=
    ((q₁.smooth_comp.continuous.sub q₀.smooth_comp.continuous).mul P.smooth_R.continuous).comp
      continuous_snd
  have h := hd.add ((((continuous_const (y := (1 : ℝ))).sub ht).mul
    (hZ.continuous_scalarDerivative _ (radialQ_smooth P q₀))).add
    (ht.mul (hZ.continuous_scalarDerivative _ (radialQ_smooth P q₁))))
  apply h.congr
  intro p
  exact (barrierRate_linear P q₀ q₁ Z p.1 p.2).symm

theorem core_compact (P : RadialReference M) : IsCompact {x | P.R x ≤ P.rstar} := by
  have he : {x | P.R x ≤ P.rstar} = P.R ⁻¹' Icc 1 P.rstar := by
    ext x
    exact ⟨fun h => ⟨P.lower_R x, h⟩, fun h => h.2⟩
  rw [he]
  exact P.proper_R.isCompact_preimage isCompact_Icc

theorem interpolation_compact (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ) (hw : RadialInterpolation.WeakDifferential (P := P) σ) :
    InterpolationTarget P q₀ q₁ σ hσ hw := by
  have hZ := interpolation_joint P q₀ q₁ σ hσ hw
  obtain ⟨C₀, h₀, hb₀⟩ := hZ.compact_scalar_bound P.R P.smooth_R _ (core_compact P)
  obtain ⟨C₁, h₁, hb₁⟩ := compact_abs_bound _ (barrierRate_continuous P q₀ q₁ _ hZ)
    _ (core_compact P)
  refine ⟨hZ, C₀, C₁, h₀, h₁, ?_⟩
  intro t x hx
  exact ⟨(le_abs_self _).trans (hb₀ t x hx), (abs_le.mp (hb₁ t x hx)).1⟩

end ExactLiouvilleComparison.MoserRegularity
