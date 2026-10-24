import ExactLiouvilleComparison.RadialInterpolationCoefficient

/-! Actual symplectic interpolation and its uniquely constructed pointwise
Moser vector. Smooth dependence and trajectories are not asserted here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology InnerProductSpace
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.RadialInterpolation
variable {d : ℕ} {M : SmoothManifold d} {P : RadialReference M}

/-- Additivity proved from the pinned chart definition and native extDeriv_add. -/
theorem exteriorDerivative_add {α β : M.Form 1}
    (hα : M.IsSmoothForm α) (hβ : M.IsSmoothForm β) :
    M.exteriorDerivative (α + β) = M.exteriorDerivative α + M.exteriorDerivative β := by
  funext x
  have hx := (chartAt (Model d) x).map_source (mem_chart_source (Model d) x)
  have ha := ((hα x).contDiffAt
    ((chartAt (Model d) x).open_target.mem_nhds hx)).differentiableAt (by simp)
  have hb := ((hβ x).contDiffAt
    ((chartAt (Model d) x).open_target.mem_nhds hx)).differentiableAt (by simp)
  unfold exteriorDerivative
  rw [formInChart_add, extDeriv_add ha hb]
  ext vs
  rfl

def primitive (q : RadialCoefficient P.rstar) (σ : M.Form 1) : M.Form 1 :=
  σ + q.primitive

/-- Actual parameter derivative evaluated on every native tangent vector.
At u in [0,1] this primitive is definitionally that of coefficient q₀ q₁ u hu. -/
theorem primitive_parameter_derivative (q₀ q₁ : RadialCoefficient P.rstar)
    (σ : M.Form 1) (u : ℝ) (x : M.Point) (v : M.Tangent x) :
    HasDerivAt (fun t =>
      evalOne (σ + LinearAlgebraChecks.radialPrimitive P (rho q₀ q₁ t)) x v)
      (delta q₀ q₁ (P.R x) * evalOne P.exactStructure.primitive x v) u := by
  have h := (rho_parameter_derivative q₀ q₁ u (P.R x)).mul_const
    (evalOne P.exactStructure.primitive x v)
  convert h.const_add (evalOne σ x v) using 1
  rfl

/-- Weak taming of a differential; no nondegeneracy of d sigma is included. -/
def WeakDifferential (σ : M.Form 1) : Prop :=
  ∀ x v, 0 ≤ evalTwo (M.exteriorDerivative σ) x v (P.compatible.J x v)

theorem differential_apply (q : RadialCoefficient P.rstar) (σ : M.Form 1)
    (hσ : M.IsSmoothForm σ) (x : M.Point) (v w : M.Tangent x) :
    evalTwo (M.exteriorDerivative (primitive q σ)) x v w =
      evalTwo (M.exteriorDerivative σ) x v w +
      evalTwo (M.exteriorDerivative q.primitive) x v w := by
  rw [primitive, exteriorDerivative_add hσ q.smooth_primitive]
  rfl

theorem nondegenerate (q : RadialCoefficient P.rstar) (σ : M.Form 1)
    (hσ : M.IsSmoothForm σ) (hw : WeakDifferential (P := P) σ) (x : M.Point) :
    M.Nondegenerate (M.exteriorDerivative (primitive q σ)) x := by
  intro v hv
  by_contra hn
  have he := hv (P.compatible.J x v)
  rw [differential_apply q σ hσ] at he
  have hp := q.metricValue_pos x v hn
  have hs := hw x v
  change 0 < evalTwo (M.exteriorDerivative q.primitive) x v (P.compatible.J x v) at hp
  linarith

def exactStructure (q : RadialCoefficient P.rstar) (σ : M.Form 1)
    (hσ : M.IsSmoothForm σ) (hw : WeakDifferential (P := P) σ) :
    ExactSymplecticStructure M where
  primitive := primitive q σ
  smooth_primitive := hσ.add q.smooth_primitive
  symplectic := (M.isSymplecticOn_exteriorDerivative_iff _ (hσ.add q.smooth_primitive)
    univ).2 (fun x _ => nondegenerate q σ hσ hw x)

/-- Inverse positive contraction acts on the actual covector -delta(R) beta. -/
def vector (q : RadialCoefficient P.rstar) (σ : M.Form 1)
    (hσ : M.IsSmoothForm σ) (hw : WeakDifferential (P := P) σ)
    (δ : ℝ → ℝ) (x : M.Point) : M.Tangent x :=
  q.compatible.inverseContraction (M.exteriorDerivative (primitive q σ)) x
    (nondegenerate q σ hσ hw x)
    (LinearAlgebraChecks.firstPathCovector P δ q.compatible x)

theorem vector_equation (q : RadialCoefficient P.rstar) (σ : M.Form 1)
    (hσ : M.IsSmoothForm σ) (hw : WeakDifferential (P := P) σ)
    (δ : ℝ → ℝ) (x : M.Point) (v : M.Tangent x) :
    evalTwo (M.exteriorDerivative (primitive q σ)) x (vector q σ hσ hw δ x) v =
      -δ (P.R x) * evalOne P.exactStructure.primitive x v :=
  q.compatible.inverseContraction_equation _ x (nondegenerate q σ hσ hw x) _ v

theorem vector_unique (q : RadialCoefficient P.rstar) (σ : M.Form 1)
    (hσ : M.IsSmoothForm σ) (hw : WeakDifferential (P := P) σ)
    (δ : ℝ → ℝ) (x : M.Point) (v : M.Tangent x)
    (hv : ∀ w, evalTwo (M.exteriorDerivative (primitive q σ)) x v w =
      -δ (P.R x) * evalOne P.exactStructure.primitive x w) :
    v = vector q σ hσ hw δ x := by
  apply q.compatible.flatLinear_injective _ x (nondegenerate q σ hσ hw x)
  ext w
  exact (hv w).trans (vector_equation q σ hσ hw δ x w).symm

theorem vector_eq_zero (q : RadialCoefficient P.rstar) (σ : M.Form 1)
    (hσ : M.IsSmoothForm σ) (hw : WeakDifferential (P := P) σ)
    (δ : ℝ → ℝ) (x : M.Point) (hδ : δ (P.R x) = 0) :
    vector q σ hσ hw δ x = 0 := by
  apply (nondegenerate q σ hσ hw x)
  intro w
  rw [vector_equation, hδ, neg_zero, zero_mul]

/-- Exactly the norm induced by the delivered rho metric, not a chart norm. -/
theorem energy (q : RadialCoefficient P.rstar) (σ : M.Form 1)
    (hσ : M.IsSmoothForm σ) (hw : WeakDifferential (P := P) σ)
    (δ : ℝ → ℝ) (x : M.Point) (hx : P.rstar < P.R x) :
    let X := vector q σ hσ hw δ x
    @norm (q.compatible.MetricTangent x) _ X ^ 2 +
      evalTwo (M.exteriorDerivative σ) x X (P.compatible.J x X) =
      -P.c * δ (P.R x) * M.scalarDerivative P.R x X := by
  dsimp only
  let X := vector q σ hσ hw δ x
  have he := vector_equation q σ hσ hw δ x (P.compatible.J x X)
  rw [differential_apply q σ hσ] at he
  have hb := P.radial_identity x hx (P.compatible.J x X)
  rw [P.compatible.square] at hb
  have hd : M.scalarDerivative P.R x (-X) = -M.scalarDerivative P.R x X := map_neg _ X
  rw [hd] at hb
  have hn : @norm (q.compatible.MetricTangent x) _ X ^ 2 =
      evalTwo (M.exteriorDerivative q.primitive) x X (P.compatible.J x X) := by
    rw [← real_inner_self_eq_norm_sq]
    exact q.compatible.metric_inner_eq x X X
  change @norm (q.compatible.MetricTangent x) _ X ^ 2 + _ = _
  rw [hn]
  rw [hb] at he
  nlinarith

end ExactLiouvilleComparison.RadialInterpolation
