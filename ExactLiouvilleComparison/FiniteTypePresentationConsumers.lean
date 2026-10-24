import ExactLiouvilleComparison.FiniteTypePresentation

/-! Source-first consumers: the completed geometry is an output of native data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.FiniteTypePresentation.Consumers
variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  (α : IntrinsicLiouville.Form k M 1)
  (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
  (hnd : ∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative α) x)
  (hout : LocalOutward α)

abbrev nativeCompletion := (fromNative α hα hnd hout).completed hα

theorem sourceGeometry : (fromNative α hα hnd hout).Identifications hα :=
  (fromNative α hα hnd hout).identifications hα

/-- Full tangent-fiber primitive equality, including at boundary points. -/
theorem primitive_on_original (x : M) :
    let P := fromNative α hα hnd hout
    ((P.completed hα).ambient.primitive (P.nativeIn x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) P.nativeIn x) = α x := by
  obtain ⟨_, _, _, _, _, _, hp, _⟩ := sourceGeometry α hα hnd hout
  exact hp x

theorem field_on_original (x : M) :
    let P := fromNative α hα hnd hout
    (P.completed hα).ambient.field (P.nativeIn x) =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) P.nativeIn x
        (IntrinsicLiouville.liouvilleVector α (IntrinsicLiouville.exteriorDerivative α) x) := by
  obtain ⟨_, _, _, _, _, _, _, hf, _⟩ := sourceGeometry α hα hnd hout
  exact hf x

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] [IsManifold (𝓡∂ (k + 1)) ∞ M] in
include hnd in
theorem original_positive_contraction (x : M) (v : TangentSpace (𝓡∂ (k + 1)) x) :
    IntrinsicLiouville.exteriorDerivative α x
      ![IntrinsicLiouville.liouvilleVector α (IntrinsicLiouville.exteriorDerivative α) x, v] =
      α x ![v] :=
  IntrinsicLiouville.contraction_liouvilleVector α (IntrinsicLiouville.exteriorDerivative α) hnd x v

theorem attached_end (b : IntrinsicBoundary.Point k M) (t : ℝ)
    (ht : -(fromNative α hα hnd hout).width < t) :
    let P := fromNative α hα hnd hout
    (P.completed hα).endMap (b, t) =
      IntrinsicCompletionGluing.outwardEndMap P.positive P.collar (b, t) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, he, _⟩ := sourceGeometry α hα hnd hout
  exact he b t ht

theorem exponential_end (b : IntrinsicBoundary.Point k M) (t : ℝ)
    (v : Model k) (s : ℝ) :
    let Q := nativeCompletion α hα hnd hout
    evalOne Q.ambient.primitive (Q.endMap (b, t))
      (mfderiv (𝓘(ℝ, Model k).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model (k + 1)) Q.endMap (b, t) (v, s)) =
      Real.exp t * evalOne (M := IntrinsicBoundary.smoothManifold k M)
        (IntrinsicBoundary.restrictForm α) b v := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, he⟩ := sourceGeometry α hα hnd hout
  exact he b t v s

/-- Every real time, including negative times, satisfies the actual chart ODE. -/
theorem all_real_flow
    (x : (nativeCompletion α hα hnd hout).ambient.manifold.Point) (t : ℝ)
    (a : (nativeCompletion α hα hnd hout).ambient.manifold.Point)
    (ha : (nativeCompletion α hα hnd hout).ambient.completeFlow.flow t x ∈
      (chartAt (Model (k + 1)) a).source) :
    let Q := nativeCompletion α hα hnd hout
    HasDerivAt (fun s : ℝ => chartAt (Model (k + 1)) a (Q.ambient.completeFlow.flow s x))
      (Q.ambient.manifold.chartTangentMap a (Q.ambient.completeFlow.flow t x)
        (Q.ambient.field (Q.ambient.completeFlow.flow t x))) t :=
  (nativeCompletion α hα hnd hout).ambient.completeFlow.solves x t a ha

variable (A : CompatibleStructure (completionReference (nativeCompletion α hα hnd hout)))
  (cyl : CylindricalStructure (nativeCompletion α hα hnd hout) A)

/-- The radial application uses exactly the chosen reference metric. -/
theorem metric_kept (x : (nativeCompletion α hα hnd hout).ambient.manifold.Point)
    (v w : (nativeCompletion α hα hnd hout).ambient.manifold.Tangent x) :
    (FiniteTypeRadial.reference (nativeCompletion α hα hnd hout) A cyl).compatible.g.inner x v w =
      A.g.inner x v w := rfl

theorem dual_norm_kept (x : (nativeCompletion α hα hnd hout).ambient.manifold.Point)
    (l : (nativeCompletion α hα hnd hout).ambient.manifold.Tangent x →L[ℝ] ℝ) :
    (FiniteTypeRadial.reference (nativeCompletion α hα hnd hout) A cyl).compatible.dualNorm x l =
      A.dualNorm x l := rfl

theorem inverse_norm_kept
    (T : ExactSymplecticStructure (nativeCompletion α hα hnd hout).ambient.manifold)
    (x : (nativeCompletion α hα hnd hout).ambient.manifold.Point) :
    (FiniteTypeRadial.reference (nativeCompletion α hα hnd hout) A cyl).compatible.inverseNorm T x =
      A.inverseNorm T x := rfl

include cyl in
/-- Native source data, chosen cylindrical J, and the original hypotheses give
the actual diffeomorphism, smooth gauge, and smooth identity-start isotopy. -/
theorem nativeComparison
    (T : ExactSymplecticStructure (nativeCompletion α hα hnd hout).ambient.manifold)
    (hw : WeaklyTames A T)
    (hg : ∃ B : AdmissibleGrowth 1, ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ t₀ : ℝ, 0 ≤ t₀ ∧
      ∀ y t, t₀ ≤ t → A.inverseNorm T ((nativeCompletion α hα hnd hout).endMap (y, t)) ≤
        C₀ * B.B (Real.exp t)) :
    FiniteTypeComparison.NativeConclusion (nativeCompletion α hα hnd hout).ambient.manifold
      T.primitive (nativeCompletion α hα hnd hout).ambient.primitive :=
  comparisonFromNative α hα hnd hout A cyl T hw hg

end ExactLiouvilleComparison.FiniteTypePresentation.Consumers

#eval IO.println "FINITE_TYPE_PRESENTATION_CONSUMERS_COMPLETE"
