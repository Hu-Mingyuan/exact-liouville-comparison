import ExactLiouvilleComparison.MoserRegularityStatement

/-! Generalization of pinned FsFltz SmoothLiouville/FamilyLiouville chart inversion
from the primitive Liouville RHS to an independent covector. No flow is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter
namespace ExactLiouvilleComparison.MoserRegularity
variable {d : ℕ} {M : SmoothManifold d}

/-- Total inverse contraction in the native fiber; inverse is zero when singular.
Only the nondegenerate locus is used for equations and regularity. -/
def solve (eta : M.Form 2) (alpha : M.Form 1) (x : M.Point) : M.Tangent x :=
  (chartContraction (eta x)).inverse ((chartOneFormEquiv d).symm (alpha x))

theorem solve_equation (eta : M.Form 2) (alpha : M.Form 1) (x : M.Point)
    (hn : M.Nondegenerate eta x) (w : M.Tangent x) :
    evalTwo eta x (solve eta alpha x) w = evalOne alpha x w := by
  let om : Model d [⋀^Fin 2]→L[ℝ] ℝ := eta x
  have hi := chartContraction_invertible om hn
  have he : om.curryLeft (solve eta alpha x) = alpha x := by
    apply (chartOneFormEquiv d).symm.injective
    exact hi.self_apply_inverse _
  have hv := congrArg (fun beta => beta (fun _ : Fin 1 => w)) he
  convert hv using 1
  · apply congrArg (eta x)
    funext i
    fin_cases i <;> rfl
  · rfl

theorem solution_unique (eta : M.Form 2) (x : M.Point) (hn : M.Nondegenerate eta x)
    (v z : M.Tangent x) (he : ∀ w, evalTwo eta x v w = evalTwo eta x z w) : v = z := by
  apply (chartContraction_invertible (eta x) hn).injective
  apply congrArg (chartOneFormEquiv d).symm
  ext vs
  convert he (vs 0) using 1 <;>
    (apply congrArg (eta x); ext i; fin_cases i <;> simp)

theorem solve_eq_inverseContraction {S : ExactSymplecticStructure M} (A : CompatibleStructure S)
    (eta : M.Form 2) (alpha : M.Form 1) (x : M.Point) (hn : M.Nondegenerate eta x)
    (l : A.Dual x) (hl : ∀ w, l w = evalOne alpha x w) :
    solve eta alpha x = A.inverseContraction eta x hn l := by
  apply solution_unique eta x hn
  intro w
  rw [solve_equation eta alpha x hn, A.inverseContraction_equation, hl]

/-- Intrinsic contraction transports through the actual inverse-chart differential. -/
theorem contraction_chart (eta : M.Form 2) (alpha : M.Form 1)
    (Z : (x : M.Point) → M.Tangent x) (a : M.Point) {y : Model d}
    (hy : y ∈ (chartAt (Model d) a).target)
    (hsol : ∀ w, evalTwo eta ((chartAt (Model d) a).symm y)
      (Z ((chartAt (Model d) a).symm y)) w =
      evalOne alpha ((chartAt (Model d) a).symm y) w) :
    (M.formInChart a eta y).curryLeft (M.vectorInChart a Z y) =
      M.formInChart a alpha y := by
  let x := (chartAt (Model d) a).symm y
  have hx := (chartAt (Model d) a).map_target hy
  have hxy := (chartAt (Model d) a).right_inv hy
  have hinv := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).symm_comp_deriv hx
  have hZ : M.inverseChartTangentMap a y (M.vectorInChart a Z y) = Z x := by
    have hi := congrArg (fun L => L (Z x)) hinv
    change M.inverseChartTangentMap a (chartAt (Model d) a x)
      (M.vectorInChart a Z y) = Z x at hi
    erw [hxy] at hi
    exact hi
  ext vs
  have hv : vs = ![vs 0] := by ext i; fin_cases i; rfl
  rw [hv]
  change eta x ((M.inverseChartTangentMap a y) ∘ ![M.vectorInChart a Z y, vs 0]) =
    alpha x ((M.inverseChartTangentMap a y) ∘ ![vs 0])
  convert hsol (M.inverseChartTangentMap a y (vs 0)) using 1
  · apply congrArg (eta x)
    ext i
    fin_cases i
    · exact hZ
    · rfl
  · apply congrArg (alpha x)
    ext i
    fin_cases i
    rfl

theorem solve_chart (eta : M.Form 2) (alpha : M.Form 1) (a : M.Point) {y : Model d}
    (hy : y ∈ (chartAt (Model d) a).target)
    (hn : M.Nondegenerate eta ((chartAt (Model d) a).symm y)) :
    M.vectorInChart a (solve eta alpha) y =
      (chartContraction (M.formInChart a eta y)).inverse
        ((chartOneFormEquiv d).symm (M.formInChart a alpha y)) := by
  have hi := chartContraction_invertible _ (M.nondegenerate_formInChart eta a hy hn)
  symm
  apply hi.inverse_apply_eq.mpr
  symm
  change (chartOneFormEquiv d).symm
    ((M.formInChart a eta y).curryLeft (M.vectorInChart a (solve eta alpha) y)) = _
  rw [contraction_chart eta alpha (solve eta alpha) a hy (solve_equation eta alpha _ hn)]

/-- The explicit open locus is retained by IsSmoothVectorFieldFamily.
Nondegeneracy is required only at closed-interval parameters. -/
theorem solve_smoothFamily (eta : ℝ → M.Form 2) (alpha : ℝ → M.Form 1)
    (he : M.IsSmoothFormFamily eta) (ha : M.IsSmoothFormFamily alpha)
    (hn : ∀ t ∈ parameterInterval, ∀ x, M.Nondegenerate (eta t) x) :
    M.IsSmoothVectorFieldFamily (fun t => solve (eta t) (alpha t)) := by
  intro a
  obtain ⟨U, hU, hUs, hE⟩ := he a
  obtain ⟨V, hV, hVs, hB⟩ := ha a
  let c := chartAt (Model d) a
  let A := fun p : ℝ × Model d => chartContraction (M.formInChart a (eta p.1) p.2)
  let b := fun p : ℝ × Model d => (chartOneFormEquiv d).symm (M.formInChart a (alpha p.1) p.2)
  have hcur : ContDiff ℝ ∞ (ContinuousAlternatingMap.curryLeft :
      (Model d [⋀^Fin 2]→L[ℝ] ℝ) → Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Model d [⋀^Fin 2]→L[ℝ] ℝ)
      (F := Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ)
      (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Model d) (F := ℝ)
        (n := 1)).toContinuousLinearMap
  have hA : ContDiffOn ℝ ∞ A U := contDiffOn_const.clm_comp (hcur.comp_contDiffOn hE)
  have hb : ContDiffOn ℝ ∞ b V := (chartOneFormEquiv d).symm.contDiff.comp_contDiffOn hB
  let D := (U ∩ V) ∩ (univ ×ˢ c.target)
  have hD : IsOpen D := (hU.inter hV).inter (isOpen_univ.prod c.open_target)
  let W := D ∩ A ⁻¹' {T | T.IsInvertible}
  have hW : IsOpen W := (hA.continuousOn.mono (fun _ h => h.1.1)).isOpen_inter_preimage
    hD ContinuousLinearMap.isOpen_setOfPred_isInvertible
  refine ⟨W, hW, ?_, ?_⟩
  · intro p hp
    refine ⟨⟨⟨hUs hp, hVs hp⟩, ⟨mem_univ _, hp.2⟩⟩, ?_⟩
    exact chartContraction_invertible _ (M.nondegenerate_formInChart _ a hp.2 (hn _ hp.1 _))
  · have hAi : ContDiffOn ℝ ∞ (fun p => (A p).inverse) W := by
      intro p hp
      exact hp.2.contDiffAt_map_inverse.comp_contDiffWithinAt p
        ((hA p hp.1.1.1).mono (fun _ h => h.1.1.1))
    apply (hAi.clm_apply (hb.mono (fun _ h => h.1.1.2))).congr
    intro p hp
    exact solve_chart _ _ a hp.1.2.2 (M.nondegenerate_of_formInChart _ a hp.1.2.2
      (nondegenerate_of_chartContraction_invertible _ hp.2))

theorem nativeJoint_of_smoothFamily
    (E : ℝ → (x : M.Point) → M.Tangent x) (hE : M.IsSmoothVectorFieldFamily E)
    (Z : Parameter → (x : M.Point) → M.Tangent x) (he : ∀ t : Parameter, E t.val = Z t) :
    NativeJoint Z := by
  refine ⟨E, he, ?_⟩
  intro p hp
  obtain ⟨U, hU, hsub, hs⟩ := hE p.2
  exact M.contMDiffAt_familySection_of_chart E p.2 p (mem_chart_source _ _)
    (hs.contDiffAt (hU.mem_nhds (hsub ⟨hp, (chartAt (Model d) p.2).map_source
      (mem_chart_source _ _)⟩)))

/-- Consumer for any specified interval solution, with no regularity assumed of it. -/
theorem nativeJoint_of_equation (eta : ℝ → M.Form 2) (alpha : ℝ → M.Form 1)
    (he : M.IsSmoothFormFamily eta) (ha : M.IsSmoothFormFamily alpha)
    (hn : ∀ t ∈ parameterInterval, ∀ x, M.Nondegenerate (eta t) x)
    (Z : Parameter → (x : M.Point) → M.Tangent x)
    (hZ : ∀ t x w, evalTwo (eta t.val) x (Z t x) w = evalOne (alpha t.val) x w) :
    NativeJoint Z := by
  apply nativeJoint_of_smoothFamily _ (solve_smoothFamily eta alpha he ha hn) Z
  intro t
  funext x
  apply solution_unique _ x (hn t.val t.property x)
  intro w
  rw [solve_equation _ _ x (hn t.val t.property x), hZ]

theorem inverse_bridge : InverseBridgeTarget (M := M) := by
  intro eta alpha he ha hn
  let Z := fun t : Parameter => solve (eta t.val) (alpha t.val)
  refine ⟨Z, nativeJoint_of_equation eta alpha he ha hn Z (fun t x w =>
    solve_equation _ _ x (hn _ t.property x) w), ?_⟩
  intro t x
  refine ⟨solve_equation _ _ x (hn _ t.property x), ?_⟩
  intro v hv
  apply solution_unique _ x (hn _ t.property x)
  intro w
  exact (hv w).trans (solve_equation _ _ x (hn _ t.property x) w).symm


/-- Stronger endpoint output retaining open chart neighborhoods and exact agreement. -/
theorem intervalSmooth_of_equation (eta : ℝ → M.Form 2) (alpha : ℝ → M.Form 1)
    (he : M.IsSmoothFormFamily eta) (ha : M.IsSmoothFormFamily alpha)
    (hn : ∀ t ∈ parameterInterval, ∀ x, M.Nondegenerate (eta t) x)
    (Z : Parameter → (x : M.Point) → M.Tangent x)
    (hZ : ∀ t x w, evalTwo (eta t.val) x (Z t x) w = evalOne (alpha t.val) x w) :
    M.IsSmoothIntervalVectorFieldFamily Z := by
  refine ⟨fun t => solve (eta t) (alpha t), solve_smoothFamily eta alpha he ha hn, ?_⟩
  intro t
  funext x
  apply solution_unique _ x (hn t.val t.property x)
  intro w
  rw [solve_equation _ _ x (hn t.val t.property x), hZ]

end ExactLiouvilleComparison.MoserRegularity
