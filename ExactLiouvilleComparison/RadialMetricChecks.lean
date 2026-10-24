import ExactLiouvilleComparison.RadialMetricNorm

/-! Consumers construct the compatible summand; none is accepted as input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.RadialMetricChecks
variable {d : ℕ} {M : SmoothManifold d}

/-- The constructed h is literally the metric of the radial form with the original J. -/
theorem metric_eq (P : RadialReference M) (q : RadialCoefficient P.rstar)
    (x : M.Point) (v w : M.Tangent x) :
    q.compatible.g.inner x v w =
      evalTwo (M.exteriorDerivative (LinearAlgebraChecks.radialPrimitive P q.rho)) x v
        (P.compatible.J x w) := q.metricBilin_apply x v w

/-- Native first-path consumer with the formerly missing radial compatibility
input now constructed from the coefficient hypotheses. -/
theorem first_path_linear_estimate (P : RadialReference M) (q : RadialCoefficient P.rstar)
    (T : ExactSymplecticStructure M) (hweak : WeaklyTames P.compatible T)
    (x : M.Point) {t : ℝ} (ht : 0 ≤ t) :
    M.Nondegenerate (M.exteriorDerivative T.primitive +
      t • M.exteriorDerivative (LinearAlgebraChecks.radialPrimitive P q.rho)) x ∧
    ∃ X W : q.compatible.MetricTangent x,
      (∀ v, evalTwo (M.exteriorDerivative T.primitive) x W v =
        -q.rho (P.R x) * evalOne P.exactStructure.primitive x v) ∧
      (∀ v, evalTwo (M.exteriorDerivative T.primitive +
        t • M.exteriorDerivative (LinearAlgebraChecks.radialPrimitive P q.rho)) x X v =
        -q.rho (P.R x) * evalOne P.exactStructure.primitive x v) ∧ ‖X‖ ≤ ‖W‖ :=
  LinearAlgebraChecks.first_path_linear_estimate P q.rho q.exactStructure rfl
    q.compatible (fun _ => rfl) T hweak x ht

/-- The generic decreasing coefficient supplies the manuscript metric comparison
in the native h and g metrics, including every point of the compact core. -/
theorem decreasing_metric_bounds (P : RadialReference M) (q : RadialCoefficient P.rstar)
    (hdec : ∀ r ∈ Ici (1 : ℝ), q.rhoPrime r ≤ 0) (x : M.Point) (v : M.Tangent x) :
    (q.rho (P.R x) + P.R x * q.rhoPrime (P.R x)) * P.compatible.g.inner x v v ≤
      q.compatible.g.inner x v v ∧
    q.compatible.g.inner x v v ≤ q.rho (P.R x) * P.compatible.g.inner x v v := by
  change _ ≤ q.metricBilin x v v ∧ q.metricBilin x v v ≤ _
  rw [q.metricBilin_apply]
  exact ⟨q.metricValue_lower_of_nonpos x (hdec _ (P.lower_R x)) v,
    q.metricValue_le_of_nonpos x (hdec _ (P.lower_R x)) v⟩

/-- Explicit consumer under generic decreasing-coefficient hypotheses. -/
theorem decreasing_first_path (P : RadialReference M) (q : RadialCoefficient P.rstar)
    (hdec : ∀ r ∈ Ici (1 : ℝ), q.rhoPrime r ≤ 0)
    (T : ExactSymplecticStructure M) (hweak : WeaklyTames P.compatible T)
    (x : M.Point) {t : ℝ} (ht : 0 ≤ t) :
    (∀ v : M.Tangent x,
      (q.rho (P.R x) + P.R x * q.rhoPrime (P.R x)) * P.compatible.g.inner x v v ≤
        q.compatible.g.inner x v v ∧
      q.compatible.g.inner x v v ≤ q.rho (P.R x) * P.compatible.g.inner x v v) ∧
    ∃ X W : q.compatible.MetricTangent x,
      (∀ v, evalTwo (M.exteriorDerivative T.primitive) x W v =
        -q.rho (P.R x) * evalOne P.exactStructure.primitive x v) ∧
      (∀ v, evalTwo (M.exteriorDerivative T.primitive +
        t • M.exteriorDerivative (LinearAlgebraChecks.radialPrimitive P q.rho)) x X v =
        -q.rho (P.R x) * evalOne P.exactStructure.primitive x v) ∧ ‖X‖ ≤ ‖W‖ :=
  ⟨decreasing_metric_bounds P q hdec x,
    (first_path_linear_estimate P q T hweak x ht).2⟩

end ExactLiouvilleComparison.RadialMetricChecks
