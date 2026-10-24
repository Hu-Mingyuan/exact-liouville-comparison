import ExactLiouvilleComparison.FiniteTypeRadialStatement
import FsFltz.Geometry.CompletionIntervalMapFamily
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

noncomputable section
open scoped Manifold ContDiff Classical
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter Topology

namespace ExactLiouvilleComparison.FiniteTypeRadial

/-- Constant near the compact piece, exactly the radius from 2 onwards. -/
def profile (r : ℝ) : ℝ := 1 + Real.smoothTransition (2 * r - 3) * (r - 1)

theorem profile_smooth : ContDiff ℝ ∞ profile :=
  contDiff_const.add ((Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
    (contDiff_id.sub contDiff_const))

theorem profile_eq_one {r : ℝ} (hr : r ≤ 3 / 2) : profile r = 1 := by
  rw [profile, Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

theorem profile_eq_self {r : ℝ} (hr : 2 ≤ r) : profile r = r := by
  rw [profile, Real.smoothTransition.one_of_one_le (by linarith)]
  ring

theorem profile_lower (r : ℝ) : 1 ≤ profile r := by
  by_cases hr : r ≤ 3 / 2
  · rw [profile_eq_one hr]
  · have h := Real.smoothTransition.nonneg (2 * r - 3)
    dsimp [profile]
    nlinarith

theorem profile_le_two {r : ℝ} (hr : r ≤ 2) : profile r ≤ 2 := by
  by_cases h : r ≤ 3 / 2
  · rw [profile_eq_one h]; norm_num
  · have hχ := Real.smoothTransition.le_one (2 * r - 3)
    dsimp [profile]
    nlinarith

variable {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)

/-- Gluing through the actual all-time end inverse, with constant value off its range. -/
def radius (x : C.ambient.manifold.Point) : ℝ :=
  if hx : x ∈ C.escapingBasin then
    profile (Real.exp (C.endCoordinates ⟨x, hx⟩).2)
  else 1

theorem radius_end (y : D.domain.boundary.Point) (t : ℝ) :
    radius C (C.endMap (y, t)) = profile (Real.exp t) := by
  classical
  have hx : C.endMap (y, t) ∈ C.escapingBasin := ⟨(y, t), rfl⟩
  rw [radius, dite_eq_left hx]
  change profile (Real.exp (C.endCoordinates (C.endInBasin (y, t))).2) = _
  rw [C.endCoordinates_endInBasin]

theorem radius_lower (x : C.ambient.manifold.Point) : 1 ≤ radius C x := by
  classical
  unfold radius
  split
  · exact profile_lower _
  · rfl

theorem radius_end_eq (y : D.domain.boundary.Point) (t : ℝ) (ht : 2 ≤ Real.exp t) :
    radius C (C.endMap (y, t)) = Real.exp t := by
  rw [radius_end, profile_eq_self ht]

theorem radius_eq_one_off_ray (x : C.ambient.manifold.Point)
    (hx : x ∉ C.endMap '' (univ ×ˢ Ici (Real.log (3 / 2)))) : radius C x = 1 := by
  classical
  by_cases hb : x ∈ C.escapingBasin
  · let q := C.endCoordinates ⟨x, hb⟩
    have hq : C.endMap q = x := C.endMap_endCoordinates ⟨x, hb⟩
    have ht : q.2 < Real.log (3 / 2) := by
      by_contra hn
      exact hx ⟨q, ⟨mem_univ _, le_of_not_gt hn⟩, hq⟩
    rw [← hq, radius_end]
    exact profile_eq_one ((Real.le_log_iff_exp_le (by norm_num)).mp ht.le)
  · simp [radius, hb]

theorem radius_smooth : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ (radius C) := by
  intro x
  by_cases hx : x ∈ C.escapingBasin
  · obtain ⟨q, rfl⟩ := hx
    let l := C.endMap_isLocalDiffeomorph q
    have hs : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : D.domain.boundary.Point × ℝ => profile (Real.exp p.2)) :=
      (profile_smooth.comp Real.contDiff_exp).comp_contMDiff contMDiff_snd
    apply ((hs _).comp _ l.localInverse_contMDiffAt).congr_of_eventuallyEq
    filter_upwards [l.localInverse_eventuallyEq_right] with z hz
    change C.endMap (l.localInverse z) = z at hz
    change radius C z = profile (Real.exp (l.localInverse z).2)
    exact (congrArg (radius C) hz).symm.trans (radius_end C _ _)
  · have hout : x ∉ C.endMap '' (univ ×ˢ Ici (Real.log (3 / 2))) := by
      rintro ⟨q, _, rfl⟩
      exact hx ⟨q, rfl⟩
    apply (contMDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(C.isClosed_endMap_image_Ici (Real.log (3 / 2))).isOpen_compl.mem_nhds
      hout] with z hz
    exact radius_eq_one_off_ray C z hz

theorem farEnd_open (a : ℝ) : IsOpen (farEnd C a) :=
  C.endMap_isLocalDiffeomorph.isOpenMap _ (isOpen_univ.prod isOpen_Ioi)

/-- Compact truncation, using the actual compact boundary, not an assumed exhaustion. -/
theorem compact_farEnd_compl (a : ℝ) : IsCompact ((farEnd C a)ᶜ) := by
  have hK : IsCompact (C.inclusion.map '' D.domain.carrier ∪
      C.endMap '' (univ ×ˢ Icc 0 a)) :=
    (D.domain.compact.image C.inclusion.map.contMDiff.continuous).union
      ((D.domain.isCompact_boundary.prod isCompact_Icc).image C.smooth_endMap.continuous)
  apply hK.of_isClosed_subset (farEnd_open C a).isClosed_compl
  intro x hx
  have hc : x ∈ C.inclusion.map '' D.domain.carrier ∪
      C.endMap '' (univ ×ˢ Ici (0 : ℝ)) := by rw [C.covering]; trivial
  rcases hc with hc | ⟨⟨y,t⟩, ht, rfl⟩
  · exact Or.inl hc
  · right
    refine ⟨(y,t), ⟨mem_univ _, ht.2, ?_⟩, rfl⟩
    by_contra hn
    exact hx ⟨(y,t), ⟨mem_univ _, lt_of_not_ge hn⟩, rfl⟩

theorem radius_core_bound (x : C.ambient.manifold.Point)
    (hx : x ∉ farEnd C (Real.log 2)) : radius C x ≤ 2 := by
  classical
  by_cases hb : x ∈ C.escapingBasin
  · let q := C.endCoordinates ⟨x, hb⟩
    have hq : C.endMap q = x := C.endMap_endCoordinates ⟨x, hb⟩
    have ht : q.2 ≤ Real.log 2 := by
      by_contra hn
      exact hx ⟨q, ⟨mem_univ _, lt_of_not_ge hn⟩, hq⟩
    rw [← hq, radius_end]
    exact profile_le_two ((Real.le_log_iff_exp_le (by norm_num)).mp ht)
  · simp [radius, hb]

theorem radius_sublevel_compact (b : ℝ) : IsCompact {x | radius C x ≤ b} := by
  apply (compact_farEnd_compl C (Real.log (max 2 b))).of_isClosed_subset
    (isClosed_le (radius_smooth C).continuous continuous_const)
  intro x hx
  rintro ⟨⟨y,t⟩, ht, rfl⟩
  have hb : 0 < max (2 : ℝ) b := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have he : max 2 b < Real.exp t := (Real.log_lt_iff_lt_exp hb).mp ht.2
  rw [mem_ofPred_eq, radius_end_eq C y t ((le_max_left 2 b).trans he.le)] at hx
  exact (not_lt_of_ge hx) ((le_max_right 2 b).trans_lt he)

theorem radius_proper : IsProperMap (radius C) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨(radius_smooth C).continuous, ?_⟩
  intro K hK
  obtain ⟨b, hb⟩ := hK.bddAbove
  exact (radius_sublevel_compact C b).of_isClosed_subset
    (hK.isClosed.preimage (radius_smooth C).continuous) (fun x hx => hb hx)

end ExactLiouvilleComparison.FiniteTypeRadial
