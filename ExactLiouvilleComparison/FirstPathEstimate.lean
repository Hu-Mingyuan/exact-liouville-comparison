import ExactLiouvilleComparison.FirstPathVector
import ExactLiouvilleComparison.FirstPathExhaustion

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.FirstPath
variable {d : ℕ} {M : SmoothManifold d}
open SmallCoefficient

theorem tail_ratio (G : AdmissibleGrowth 1) {s r : ℝ} (hs : 1 < s) (hr : s + 1 ≤ r) :
    Real.sqrt (k G s r / m G s r) =
      Real.sqrt 2 * G.B r * Real.sqrt (S G r) / r := by
  have hr1 : 1 ≤ r := by linarith
  have hR : 0 < r := by linarith
  have hB := G.positive r hr1
  have hS := S_pos G hr1
  have hb := b0_pos G s
  have hq := Real.sqrt_pos.mpr hS
  apply (Real.sqrt_eq_iff_eq_sq (div_nonneg (k_pos G s r).le (m_pos G s hr1).le)
    (by positivity)).mpr
  rw [k_tail G hs hr, m_tail G hs hr, div_pow, mul_pow, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hS.le]
  field_simp
  nlinarith [Real.sq_sqrt hS.le]

theorem tail_factor (G : AdmissibleGrowth 1) {s r : ℝ} (hs : 1 < s) (hr : s + 1 ≤ r)
    (C : ℝ) :
    C * G.B r * k G s r * Real.sqrt (k G s r / m G s r) * r =
      Real.sqrt 2 * C * b0 G s * (G.B r) ^ 2 * S G r / r := by
  have hr1 : 1 ≤ r := by linarith
  have hR : r ≠ 0 := ne_of_gt (by linarith)
  rw [tail_ratio G hs hr, k_tail G hs hr]
  field_simp
  ring_nf
  rw [Real.sq_sqrt (S_pos G hr1).le]

theorem radial_pair_bound (P : RadialReference M) (x : M.Point) (hx : P.rstar < P.R x) :
    P.compatible.dualNorm x (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x) *
      P.compatible.dualNorm x (P.betaCovector x) ≤ P.R x := by
  rw [P.beta_dualNorm x hx]
  nlinarith [P.radial_bound x hx]

/-- Manuscript firstestimate, on the tail and wherever the original inverse bound holds. -/
theorem firstestimate (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    (x : M.Point) (t : ℝ) (ht : 0 ≤ t) {C : ℝ} (hC : 0 < C)
    (hx : P.rstar + 1 ≤ P.R x)
    (hb : P.compatible.inverseNorm T x ≤ C * G.B (P.R x)) :
    |M.scalarDerivative P.R x (X P G T hw x t ht)| ≤
      Real.sqrt 2 * C * b0 G P.rstar * (G.B (P.R x)) ^ 2 * S G (P.R x) / P.R x := by
  let D := P.compatible.dualNorm x (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x)
  let b := P.compatible.dualNorm x (P.betaCovector x)
  let q := Real.sqrt (k G P.rstar (P.R x) / m G P.rstar (P.R x))
  have hD : 0 ≤ D := norm_nonneg _
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hk := (k_pos G P.rstar (P.R x)).le
  have hB := (G.positive (P.R x) (P.lower_R x)).le
  have hd : |M.scalarDerivative P.R x (X P G T hw x t ht)| ≤
      D * ‖X P G T hw x t ht‖ :=
    (P.compatible.covector x (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) P.R x)).le_opNorm _
  calc
    _ ≤ D * ‖X P G T hw x t ht‖ := hd
    _ ≤ D * (q * ‖W P G T x‖) := mul_le_mul_of_nonneg_left
      (X_g_bound P G T hw x t ht) hD
    _ ≤ D * (q * (C * G.B (P.R x) * k G P.rstar (P.R x) * b)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (W_bound P G T x hb) hq) hD
    _ = (C * G.B (P.R x) * k G P.rstar (P.R x) * q) * (D * b) := by ring
    _ ≤ (C * G.B (P.R x) * k G P.rstar (P.R x) * q) * P.R x :=
      mul_le_mul_of_nonneg_left (radial_pair_bound P x (by linarith)) (by positivity)
    _ = _ := tail_factor G P.one_lt_rstar hx C

/-- The actual native derivative of log S(R), including zero vectors and dR=0. -/
theorem firstproper (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    (x : M.Point) (t : ℝ) (ht : 0 ≤ t) {C : ℝ} (hC : 0 < C)
    (hx : P.rstar + 1 ≤ P.R x)
    (hb : P.compatible.inverseNorm T x ≤ C * G.B (P.R x)) :
    |M.scalarDerivative (exhaustion P G) x (X P G T hw x t ht)| ≤
      Real.sqrt 2 * C * b0 G P.rstar := by
  rw [exhaustion_derivative, abs_mul,
    abs_of_pos (div_pos (density_pos G (P.lower_R x)) (S_pos G (P.lower_R x)))]
  apply (mul_le_mul_of_nonneg_left (firstestimate P G T hw x t ht hC hx hb)
    (div_nonneg (density_pos G (P.lower_R x)).le (S_pos G (P.lower_R x)).le)).trans_eq
  unfold density
  have hR : P.R x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (P.lower_R x))
  have hB := (G.positive (P.R x) (P.lower_R x)).ne'
  have hS := (S_pos G (P.lower_R x)).ne'
  field_simp

/-- Retain the supplied compact exception; enlarge it by the compact tail cutoff. -/
theorem exterior_estimate (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    {C : ℝ} (hC : 0 < C) (K : Set M.Point) (hK : IsCompact K)
    (hb : ∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * G.B (P.R x)) :
    ∃ L : Set M.Point, IsCompact L ∧ K ⊆ L ∧
      ∀ x, x ∉ L → ∀ t (ht : 0 ≤ t),
        |M.scalarDerivative (exhaustion P G) x (X P G T hw x t ht)| ≤
          Real.sqrt 2 * C * b0 G P.rstar := by
  let L := K ∪ P.R ⁻¹' Icc 1 (P.rstar + 1)
  refine ⟨L, hK.union (P.proper_R.isCompact_preimage isCompact_Icc), subset_union_left, ?_⟩
  intro x hx t ht
  have hn : x ∉ K ∧ x ∉ P.R ⁻¹' Icc 1 (P.rstar + 1) := not_or.mp hx
  have hr : P.rstar + 1 ≤ P.R x := by
    by_contra h
    exact hn.2 ⟨P.lower_R x, (lt_of_not_ge h).le⟩
  exact firstproper P G T hw x t ht hC hr (hb x hn.1)

end ExactLiouvilleComparison.FirstPath
