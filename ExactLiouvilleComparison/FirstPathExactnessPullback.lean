import ExactLiouvilleComparison.FirstPathExactnessInputs
import ExactLiouvilleComparison.MoserExactnessPullback

/-! Unconditional first-path pullback differentiation at the original hypotheses. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.FirstPathExactness
variable {d : ℕ} {M : SmoothManifold d}

theorem pullbackDerivative (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    {C : ℝ} (hC : 0 < C) (K : Set M.Point) (hK : IsCompact K)
    (hb : ∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * G.B (P.R x)) :
    MoserExactness.PullbackDerivative (primitive P G T)
      (FirstPathFlow.evolution P G T hw hC K hK hb) :=
  MoserExactness.pullbackDerivative _ (primitive_smoothFamily P G T)
    (field_smooth P G T hw) (field_equation P G T hw) _

theorem endpoint_integral (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    {C : ℝ} (hC : 0 < C) (K : Set M.Point) (hK : IsCompact K)
    (hb : ∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * G.B (P.R x))
    (x : M.Point) (v : M.Tangent x) :
    let E := FirstPathFlow.evolution P G T hw hC K hK hb
    evalOne (M.pullback M (E.map parameterZero parameterOne) (primitive P G T 1)) x v =
      evalOne (primitive P G T 0) x v +
        ∫ t in (0 : ℝ)..1, MoserExactness.derivativeIntegrand (primitive P G T) E x v t :=
  MoserExactness.endpoint_integral _ (primitive_smoothFamily P G T)
    (field_smooth P G T hw) (field_equation P G T hw) _ x v

end ExactLiouvilleComparison.FirstPathExactness
