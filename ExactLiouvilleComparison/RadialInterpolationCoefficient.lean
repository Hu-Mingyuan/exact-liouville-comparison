import ExactLiouvilleComparison.RadialMetricNorm

/-! Convex interpolation on the closed half-line; no flow assertions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter
namespace ExactLiouvilleComparison.RadialInterpolation
variable {d : ℕ} {M : SmoothManifold d} {P : RadialReference M}

def rho (q₀ q₁ : RadialCoefficient P.rstar) (u r : ℝ) : ℝ :=
  (1 - u) * q₀.rho r + u * q₁.rho r

def delta (q₀ q₁ : RadialCoefficient P.rstar) (r : ℝ) : ℝ :=
  q₁.rho r - q₀.rho r

theorem rho_hasDerivWithinAt (q₀ q₁ : RadialCoefficient P.rstar) (u : ℝ)
    {r : ℝ} (hr : 1 ≤ r) :
    HasDerivWithinAt (rho q₀ q₁ u)
      ((1-u) * q₀.rhoPrime r + u * q₁.rhoPrime r) (Ici 1) r :=
  ((q₀.hasDerivWithinAt hr).const_mul (1-u)).add
    ((q₁.hasDerivWithinAt hr).const_mul u)

theorem rho_derivWithin (q₀ q₁ : RadialCoefficient P.rstar) (u : ℝ)
    {r : ℝ} (hr : 1 ≤ r) :
    derivWithin (rho q₀ q₁ u) (Ici 1) r =
      (1-u) * q₀.rhoPrime r + u * q₁.rhoPrime r :=
  (rho_hasDerivWithinAt q₀ q₁ u hr).derivWithin (uniqueDiffOn_Ici 1 r hr)

theorem convex_pos {a b u : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : u ∈ Icc (0 : ℝ) 1) : 0 < (1-u)*a+u*b := by
  have h₀ := mul_nonneg (sub_nonneg.mpr hu.2) ha.le
  have h₁ := mul_nonneg hu.1 hb.le
  rcases lt_or_eq_of_le hu.1 with h | h
  · exact add_pos_of_nonneg_of_pos h₀ (mul_pos h hb)
  · rw [← h]; simpa using ha

/-- All coefficient hypotheses are proved, including positivity at u=0,1. -/
def coefficient (q₀ q₁ : RadialCoefficient P.rstar) (u : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) : RadialCoefficient P.rstar where
  rho := rho q₀ q₁ u
  smooth := (contDiffOn_const.mul q₀.smooth).add (contDiffOn_const.mul q₁.smooth)
  positive := fun r hr => convex_pos (q₀.positive r hr) (q₁.positive r hr) hu
  constant_core := by
    intro r hr
    dsimp [rho]
    rw [q₀.constant_core r hr, q₁.constant_core r hr]
  radial_positive := by
    intro r hr
    rw [rho_derivWithin q₀ q₁ u hr]
    have h := convex_pos (q₀.radial_positive r hr) (q₁.radial_positive r hr) hu
    dsimp [rho, RadialCoefficient.rhoPrime] at *
    nlinarith

theorem coefficient_prime (q₀ q₁ : RadialCoefficient P.rstar) (u : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) {r : ℝ} (hr : 1 ≤ r) :
    (coefficient q₀ q₁ u hu).rhoPrime r =
      (1-u) * q₀.rhoPrime r + u * q₁.rhoPrime r :=
  rho_derivWithin q₀ q₁ u hr

def Q (q₀ q₁ : RadialCoefficient P.rstar) (u r : ℝ) : ℝ := r * rho q₀ q₁ u r

theorem Q_radial_derivative (q₀ q₁ : RadialCoefficient P.rstar) (u : ℝ)
    {r : ℝ} (hr : 1 ≤ r) :
    HasDerivWithinAt (Q q₀ q₁ u)
      (rho q₀ q₁ u r + r * ((1-u)*q₀.rhoPrime r + u*q₁.rhoPrime r)) (Ici 1) r := by
  convert (hasDerivWithinAt_id r (Ici 1)).mul
    (rho_hasDerivWithinAt q₀ q₁ u hr) using 1 <;> first | rfl | simp

theorem rho_parameter_derivative (q₀ q₁ : RadialCoefficient P.rstar) (u r : ℝ) :
    HasDerivAt (fun v => rho q₀ q₁ v r) (delta q₀ q₁ r) u := by
  convert (((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)).mul_const
    (q₀.rho r)).add ((hasDerivAt_id u).mul_const (q₁.rho r)) using 1 <;>
    first | rfl | (dsimp [delta]; ring)

theorem Q_parameter_derivative (q₀ q₁ : RadialCoefficient P.rstar) (u r : ℝ) :
    HasDerivAt (fun v => Q q₀ q₁ v r) (delta q₀ q₁ r * r) u := by
  convert (rho_parameter_derivative q₀ q₁ u r).const_mul r using 1 <;>
    first | rfl | ring

theorem Q_lower (q₀ q₁ : RadialCoefficient P.rstar)
    (horder : ∀ r ∈ Ici 1, q₀.rho r ≤ q₁.rho r)
    {u r : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hr : 1 ≤ r) :
    r * q₀.rho r ≤ Q q₀ q₁ u r := by
  have h := mul_nonneg hu.1 (sub_nonneg.mpr (horder r hr))
  have h' := mul_nonneg (show 0 ≤ r by linarith) h
  dsimp [Q, rho]
  nlinarith

/-- One radial threshold works for every parameter in the closed interval. -/
theorem uniform_exhaustion (q₀ q₁ : RadialCoefficient P.rstar)
    (horder : ∀ r ∈ Ici 1, q₀.rho r ≤ q₁.rho r)
    (htend : Tendsto (fun r => r * q₀.rho r) atTop atTop) (L : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ u ∈ Icc (0 : ℝ) 1, ∀ r, T ≤ r → L ≤ Q q₀ q₁ u r := by
  obtain ⟨T, hT⟩ := (eventually_atTop.1 ((tendsto_atTop.1 htend) L))
  refine ⟨max 1 T, le_max_left _ _, ?_⟩
  intro u hu r hr
  exact (hT r ((le_max_right _ _).trans hr)).trans
    (Q_lower q₀ q₁ horder hu ((le_max_left _ _).trans hr))

/-- Native derivative along any differentiable scalar curve at an exterior radius.
This is a chain rule, not a trajectory existence assertion. -/
theorem Q_curve_derivative (q₀ q₁ : RadialCoefficient P.rstar)
    (f : ℝ → ℝ) {u v : ℝ} (hf : HasDerivAt f v u) (hr : 1 < f u) :
    HasDerivAt (fun t => Q q₀ q₁ t (f t))
      (delta q₀ q₁ (f u) * f u +
        (rho q₀ q₁ u (f u) + f u * ((1-u)*q₀.rhoPrime (f u) +
          u*q₁.rhoPrime (f u))) * v) u := by
  have h₀ := ((q₀.hasDerivWithinAt hr.le).hasDerivAt (Ici_mem_nhds hr)).comp u hf
  have h₁ := ((q₁.hasDerivWithinAt hr.le).hasDerivAt (Ici_mem_nhds hr)).comp u hf
  have h := hf.mul ((((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)).mul h₀).add
    ((hasDerivAt_id u).mul h₁))
  convert h using 1 <;> first | rfl | (dsimp [Q, rho, delta]; ring)

end ExactLiouvilleComparison.RadialInterpolation
