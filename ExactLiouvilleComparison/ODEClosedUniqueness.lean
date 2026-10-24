import ExactLiouvilleComparison.ODESmoothEvolution

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter Function
namespace ExactLiouvilleComparison.ODE
variable {d : ℕ} {M : SmoothManifold d}

/-- Extend a closed-interval solution using the constructed auxiliary evolution
on either side. Matching within derivatives prove the full ODE at both joins. -/
theorem SmoothEvolution.extend_closed_curve
    {Z : ℝ → (x : M.Point) → M.Tangent x} (H : SmoothEvolution Z)
    {γ : ℝ → M.Point} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ Icc a b, HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ (Icc a b) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t)))) :
    ∃ η : ℝ → M.Point, EqOn η γ (Icc a b) ∧
      ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) η t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (η t))) := by
  let η : ℝ → M.Point := fun t => if t < a then H.map a t (γ a)
    else if b < t then H.map b t (γ b) else γ t
  have heq : EqOn η γ (Icc a b) := by
    intro t ht
    simp only [η, not_lt.mpr ht.1, not_lt.mpr ht.2, ite_false]
  have heqa := heq (left_mem_Icc.mpr hab.le)
  have heqb := heq (right_mem_Icc.mpr hab.le)
  have hleft : EqOn η (fun t => H.map a t (γ a)) (Iic a) := by
    intro t ht
    rcases (show t ≤ a from ht).lt_or_eq with hlt | rfl
    · simp only [η, hlt, ite_true]
    · simpa only [H.initial] using heqa
  have hright : EqOn η (fun t => H.map b t (γ b)) (Ici b) := by
    intro t ht
    rcases (show b ≤ t from ht).lt_or_eq with hlt | rfl
    · simp only [η, not_lt.mpr (hab.le.trans hlt.le), hlt, ite_false, ite_true]
    · simpa only [H.initial] using heqb
  have hwithin (t : ℝ) (ht : t ∈ Icc a b) :
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) η (Icc a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (η t))) := by
    have h := (hγ t ht).congr_mono (fun u hu => heq hu) (heq ht) (Subset.refl _)
    change HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) η (Icc a b) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t))) at h
    rw [heq ht]
    exact h
  refine ⟨η, heq, ?_⟩
  intro t
  by_cases hta : t < a
  · have he : η =ᶠ[𝓝 t] (fun u => H.map a u (γ a)) := by
      filter_upwards [Iio_mem_nhds hta] with u hu
      simp only [η, show u < a from hu, ite_true]
    have h := (H.solves a (γ a) t).congr_of_eventuallyEq_abuse he
    rw [he.self_of_nhds]
    exact h
  by_cases hbt : b < t
  · have he : η =ᶠ[𝓝 t] (fun u => H.map b u (γ b)) := by
      filter_upwards [Ioi_mem_nhds hbt] with u hu
      have hub : b < u := hu
      simp only [η, not_lt.mpr (hab.le.trans hub.le), hub, ite_false, ite_true]
    have h := (H.solves b (γ b) t).congr_of_eventuallyEq_abuse he
    rw [he.self_of_nhds]
    exact h
  have ht : t ∈ Icc a b := ⟨le_of_not_gt hta, le_of_not_gt hbt⟩
  by_cases hea : t = a
  · subst t
    have hdleft := (H.solves a (γ a) a).hasMFDerivWithinAt.congr_mono
      (fun u hu => hleft hu) (hleft (by simp)) (show Iic a ⊆ univ from subset_univ _)
    have hdl : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) η (Iic a) a
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z a (η a))) := by
      change HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) η (Iic a) a
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z a (H.map a a (γ a)))) at hdleft
      rw [heqa]
      apply hdleft.congr_mfderiv
      congr 1
      exact congrArg (fun x : M.Point => (Z a x : Model d)) (H.initial a (γ a))
    apply (hdl.union (hwithin a ht)).hasMFDerivAt
    apply mem_of_superset (Iio_mem_nhds hab)
    intro u hu
    by_cases hua : u ≤ a
    · exact Or.inl hua
    · exact Or.inr ⟨le_of_not_ge hua, hu.le⟩
  by_cases heb : t = b
  · subst t
    have hdright := (H.solves b (γ b) b).hasMFDerivWithinAt.congr_mono
      (fun u hu => hright hu) (hright (by simp)) (show Ici b ⊆ univ from subset_univ _)
    have hdr : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) η (Ici b) b
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z b (η b))) := by
      change HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) η (Ici b) b
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z b (H.map b b (γ b)))) at hdright
      rw [heqb]
      apply hdright.congr_mfderiv
      congr 1
      exact congrArg (fun x : M.Point => (Z b x : Model d)) (H.initial b (γ b))
    apply ((hwithin b ht).union hdr).hasMFDerivAt
    apply mem_of_superset (Ioi_mem_nhds hab)
    intro u hu
    by_cases hub : u ≤ b
    · exact Or.inl ⟨hu.le, hub⟩
    · exact Or.inr (le_of_not_ge hub)
  exact (hwithin t ht).hasMFDerivAt (Icc_mem_nhds (lt_of_le_of_ne ht.1 (Ne.symm hea))
    (lt_of_le_of_ne ht.2 heb))

/-- Uniqueness on a closed interval includes initial time at either endpoint. -/
theorem SmoothEvolution.unique_closed
    {Z : ℝ → (x : M.Point) → M.Tangent x} (H : SmoothEvolution Z)
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)))
    {γ : ℝ → M.Point} {s t : ℝ}
    (hγ : ∀ u ∈ uIcc s t, HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ (uIcc s t) u
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z u (γ u)))) :
    γ t = H.map s t (γ s) := by
  by_cases hst : s = t
  · subst t
    rw [H.initial]
  have hab : min s t < max s t := lt_of_le_of_ne (min_le_max (a := s) (b := t)) (by
    intro he
    apply hst
    have h₁ := min_le_left s t
    have h₂ := min_le_right s t
    have h₃ := le_max_left s t
    have h₄ := le_max_right s t
    linarith)
  obtain ⟨η, heq, hη⟩ := H.extend_closed_curve hab hγ
  have h := CollarFlow.eq_of_hasMFDerivAt hZ hη (H.solves s (γ s))
    (by rw [H.initial]; exact heq (left_mem_uIcc))
  rw [← heq right_mem_uIcc]
  exact congrFun h t
end ExactLiouvilleComparison.ODE
