import ExactLiouvilleComparison.ThirdPathFlow

/-! Unconditional consumers of the constructed third-path evolution.
The endpoint direction is geometric evolution from parameter 1 to 0;
Cartan exactness and the pullback comparison remain separate obligations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.ThirdPath
variable {d : ℕ} {M : SmoothManifold d}

/-- Native diffeomorphism from any initial to any terminal parameter. -/
def flow (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (s t : Parameter) : M.SmoothEquiv M :=
  (evolution P T hw).map s t

/-- Actual real-time extension, smooth near the entire closed double time strip. -/
def trajectory (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) : ℝ → ℝ → M.Point → M.Point :=
  (evolution P T hw).extension

theorem trajectory_agrees (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (s t : Parameter) :
    trajectory P T hw s.val t.val = flow P T hw s t :=
  (evolution P T hw).agrees s t

theorem trajectory_smooth (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) :
    ∃ U : Set (ℝ × (ℝ × M.Point)), IsOpen U ∧
      parameterInterval ×ˢ (parameterInterval ×ˢ univ) ⊆ U ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
        𝓘(ℝ, Model d) ∞ (fun p => trajectory P T hw p.1 p.2.1 p.2.2) U :=
  (evolution P T hw).smooth

theorem flow_initial (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (s : Parameter) (x : M.Point) :
    flow P T hw s s x = x := (evolution P T hw).initial s x

theorem trajectory_solves (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (s : Parameter) (x : M.Point) :
    FirstPathFlow.IsSolution (field P T hw)
      (fun t => trajectory P T hw s.val t x) parameterInterval :=
  (evolution P T hw).solves s x

theorem trajectory_chart_solves (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (s t : Parameter) (x a : M.Point)
    (ha : flow P T hw s t x ∈ (chartAt (Model d) a).source) :
    HasDerivWithinAt (fun u => chartAt (Model d) a (trajectory P T hw s.val u x))
      (M.chartTangentMap a (flow P T hw s t x) (field P T hw t (flow P T hw s t x)))
      parameterInterval t.val :=
  (evolution P T hw).chart_solves s t x a ha

/-- No ordering restriction on the two parameters; singleton intervals are included. -/
theorem flow_unique (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (s t : Parameter) (γ : ℝ → M.Point)
    (hγ : FirstPathFlow.IsSolution (field P T hw) γ (uIcc s.val t.val)) :
    γ t.val = flow P T hw s t (γ s.val) :=
  (evolution P T hw).unique s t γ hγ

theorem flow_compose (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (r s t : Parameter) (x : M.Point) :
    flow P T hw s t (flow P T hw r s x) = flow P T hw r t x :=
  (evolution P T hw).compose r s t x

theorem flow_inverse (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (s t : Parameter) :
    (flow P T hw s t).symm = flow P T hw t s :=
  (evolution P T hw).inverse s t

/-- An actual solution from every initial point, on the full closed interval. -/
theorem full_interval_solution (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (s : Parameter) (x : M.Point) :
    ∃ γ : ℝ → M.Point, γ s.val = x ∧
      FirstPathFlow.IsSolution (field P T hw) γ parameterInterval ∧
      ∀ t : Parameter, γ t.val = flow P T hw s t x := by
  refine ⟨fun t => trajectory P T hw s.val t x, ?_, trajectory_solves P T hw s x, ?_⟩
  · change trajectory P T hw s.val s.val x = x
    rw [trajectory_agrees P T hw s s]
    exact flow_initial P T hw s x
  · intro t
    exact congrFun (trajectory_agrees P T hw s t) x

theorem flow_isotopy (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (t : Parameter) :
    SmoothlyIsotopicToIdentity M (flow P T hw parameterZero t) :=
  (evolution P T hw).isotopy t

/-- The endpoint required for the manuscript arrow lambda + A beta to A beta. -/
def inverseEndpoint (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) : M.SmoothEquiv M :=
  flow P T hw parameterOne parameterZero

theorem inverseEndpoint_eq (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) :
    inverseEndpoint P T hw = (flow P T hw parameterZero parameterOne).symm :=
  (flow_inverse P T hw parameterZero parameterOne).symm

theorem inverseEndpoint_isotopy (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) :
    SmoothlyIsotopicToIdentity M (inverseEndpoint P T hw) :=
  evolution_inverse_isotopy (evolution P T hw)

/-- Literal A and both primitive endpoints, together with the proved inverse direction.
This deliberately makes no pullback or exactness assertion. -/
theorem inverseEndpoint_direction (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) :
    primitive P T parameterOne.val = T.primitive +
      LinearAlgebraChecks.radialPrimitive P (LargeCoefficient.A P T.primitive) ∧
    primitive P T parameterZero.val =
      LinearAlgebraChecks.radialPrimitive P (LargeCoefficient.A P T.primitive) ∧
    inverseEndpoint P T hw = (flow P T hw parameterZero parameterOne).symm ∧
    SmoothlyIsotopicToIdentity M (inverseEndpoint P T hw) :=
  ⟨primitive_one P T, primitive_zero P T, inverseEndpoint_eq P T hw,
    inverseEndpoint_isotopy P T hw⟩

end ExactLiouvilleComparison.ThirdPath
