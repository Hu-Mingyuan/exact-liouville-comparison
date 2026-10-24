import ExactLiouvilleComparison.FirstPathFlow
import ExactLiouvilleComparison.FirstPathFlowChecks

/-! Consumers of the constructed first-path evolution; no flow is an input. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.FirstPathFlowFinalChecks
variable {d : ℕ} {M : SmoothManifold d}

/-- The chosen evolution obeys the literal first-path ODE at every parameter,
including 0 and 1, for every starting parameter and initial point. -/
theorem native_ode (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    {C : ℝ} (hC : 0 < C) (K : Set M.Point) (hK : IsCompact K)
    (hb : ∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * G.B (P.R x))
    (s t : Parameter) (x : M.Point) :
    let H := FirstPathFlow.evolution P G T hw hC K hK hb
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
      (fun u => H.extension s.val u x) parameterInterval t.val
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (FirstPath.X P G T hw (H.extension s.val t.val x) t.val t.property.1)) :=
  (FirstPathFlow.evolution P G T hw hC K hK hb).solves s x |>.2 t.val t.property t.property

/-- Forward and backward transport are actual inverse maps; the time-one map
is smoothly isotopic to identity. The compact exception is still arbitrary. -/
theorem inverse_and_isotopy (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    {C : ℝ} (hC : 0 < C) (K : Set M.Point) (hK : IsCompact K)
    (hb : ∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * G.B (P.R x)) :
    let H := FirstPathFlow.evolution P G T hw hC K hK hb
    (∀ (s t : Parameter) x, H.map t s (H.map s t x) = x) ∧
      SmoothlyIsotopicToIdentity M (H.map parameterZero parameterOne) := by
  dsimp only
  let H := FirstPathFlow.evolution P G T hw hC K hK hb
  refine ⟨?_, H.isotopy parameterOne⟩
  intro s t x
  exact (H.compose s t s x).trans (H.initial s x)

/-- The unchanged manuscript GrowthAtInfinity input produces a witness and
actual evolution of the corresponding literal X, with endpoint chart ODE. -/
theorem growth_consumer (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) (hg : GrowthAtInfinity P.compatible T P.R 1) :
    ∃ G : AdmissibleGrowth 1,
      Nonempty (FirstPathFlow.Evolution (fun t x => FirstPath.X P G T hw x t.val t.property.1)) :=
  FirstPathFlow.firstPathFlow_of_growth P T hw hg
end ExactLiouvilleComparison.FirstPathFlowFinalChecks
