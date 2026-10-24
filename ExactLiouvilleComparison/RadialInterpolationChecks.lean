import ExactLiouvilleComparison.RadialInterpolationEstimates

/-! Generic compiled consumers of the bounded interpolation estimates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology InnerProductSpace
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.RadialInterpolationChecks
open RadialInterpolation
variable {d : ℕ} {M : SmoothManifold d} {P : RadialReference M}

/-- Symplecticity and existence/uniqueness at every point, including the compact core. -/
theorem constructed (q₀ q₁ : RadialCoefficient P.rstar)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (σ : M.Form 1)
    (hσ : M.IsSmoothForm σ) (hw : WeakDifferential (P := P) σ) (x : M.Point) :
    let q := coefficient q₀ q₁ u hu
    M.IsSymplecticOn (M.exteriorDerivative (primitive q σ)) univ ∧
    ∃! X : M.Tangent x, ∀ v,
      evalTwo (M.exteriorDerivative (primitive q σ)) x X v =
        -delta q₀ q₁ (P.R x) * evalOne P.exactStructure.primitive x v := by
  dsimp only
  let q := coefficient q₀ q₁ u hu
  exact ⟨(exactStructure q σ hσ hw).symplectic,
    vector q σ hσ hw (delta q₀ q₁) x,
    vector_equation q σ hσ hw (delta q₀ q₁) x,
    fun v hv => vector_unique q σ hσ hw (delta q₀ q₁) x v hv⟩

theorem core_derivative (q₀ q₁ : RadialCoefficient P.rstar)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (r : ℝ) (hr : r ∈ Icc 1 P.rstar) :
    (coefficient q₀ q₁ u hu).rhoPrime r = 0 :=
  (coefficient q₀ q₁ u hu).rhoPrime_eq_zero hr

theorem weak_zero : WeakDifferential (P := P) (0 : M.Form 1) := by
  intro x v
  simp [exteriorDerivative, formInChart_zero, extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply, evalTwo]

/-- Degenerate d sigma = 0 is allowed literally; no nondegenerate sigma input. -/
theorem sigma_zero (q₀ q₁ : RadialCoefficient P.rstar)
    (horder : ∀ r ∈ Ici 1, q₀.rho r ≤ q₁.rho r)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (x : M.Point) (hx : P.rstar < P.R x) :
    let q := coefficient q₀ q₁ u hu
    let X := vector q 0 M.isSmoothForm_zero weak_zero (delta q₀ q₁) x
    @norm (q.compatible.MetricTangent x) _ X ^ 2 =
      -P.c * delta q₀ q₁ (P.R x) * M.scalarDerivative P.R x X ∧
    0 ≤ -M.scalarDerivative P.R x X ∧
    -M.scalarDerivative P.R x X ≤ delta q₀ q₁ (P.R x) * q.radialA x / q.radialD x := by
  dsimp only
  let q := coefficient q₀ q₁ u hu
  constructor
  · have h := energy q 0 M.isSmoothForm_zero weak_zero (delta q₀ q₁) x hx
    simpa [exteriorDerivative, formInChart_zero, extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply, evalTwo] using h
  · exact radial q 0 M.isSmoothForm_zero weak_zero (delta q₀ q₁) x hx
      (sub_nonneg.mpr (horder _ (P.lower_R x)))

/-- The zero-delta case holds globally, independent of any radial coordinate derivative. -/
theorem equal_coefficients (q : RadialCoefficient P.rstar)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (σ : M.Form 1)
    (hσ : M.IsSmoothForm σ) (hw : WeakDifferential (P := P) σ) (x : M.Point) :
    vector (coefficient q q u hu) σ hσ hw (delta q q) x = 0 :=
  vector_eq_zero _ σ hσ hw _ x (sub_self _)

/-- At an exterior critical point, the radial identity forces beta and X to vanish. -/
theorem critical_point (q : RadialCoefficient P.rstar) (σ : M.Form 1)
    (hσ : M.IsSmoothForm σ) (hw : WeakDifferential (P := P) σ)
    (δ : ℝ → ℝ) (x : M.Point) (hx : P.rstar < P.R x)
    (hdR : mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x = 0) :
    vector q σ hσ hw δ x = 0 := by
  apply nondegenerate q σ hσ hw x
  intro v
  rw [vector_equation, P.radial_identity x hx v]
  simp [scalarDerivative, hdR]

/-- An arbitrary scalar curve with the pointwise radial velocity has the native
Q derivative and the nonnegative lower bound. No such curve is asserted to exist. -/
theorem scalar_barrier (q₀ q₁ : RadialCoefficient P.rstar)
    (horder : ∀ r ∈ Ici 1, q₀.rho r ≤ q₁.rho r)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (σ : M.Form 1)
    (hσ : M.IsSmoothForm σ) (hw : WeakDifferential (P := P) σ)
    (x : M.Point) (hx : P.rstar < P.R x) (f : ℝ → ℝ) (hfval : f u = P.R x)
    (hf : HasDerivAt f
      (M.scalarDerivative P.R x (vector (coefficient q₀ q₁ u hu) σ hσ hw
        (delta q₀ q₁) x)) u) :
    let q := coefficient q₀ q₁ u hu
    let XR := M.scalarDerivative P.R x (vector q σ hσ hw (delta q₀ q₁) x)
    let B := delta q₀ q₁ (P.R x) * P.R x +
      (q.rho (P.R x) + P.R x * q.rhoPrime (P.R x)) * XR
    HasDerivAt (fun t => Q q₀ q₁ t (f t)) B u ∧ 0 ≤ B := by
  dsimp only
  constructor
  · have h := Q_curve_derivative q₀ q₁ f hf
      (show 1 < f u by rw [hfval]; exact P.one_lt_rstar.trans hx)
    rw [hfval] at h
    rw [coefficient_prime q₀ q₁ u hu (P.lower_R x)]
    exact h
  · have h := Q_directional q₀ q₁ horder u hu σ hσ hw x hx
    exact h.2.trans h.1

end ExactLiouvilleComparison.RadialInterpolationChecks
