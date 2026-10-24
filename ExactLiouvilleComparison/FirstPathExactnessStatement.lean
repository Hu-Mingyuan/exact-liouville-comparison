import ExactLiouvilleComparison.MoserExactnessStatement

noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.FirstPathExactness
variable {d : ℕ} {M : SmoothManifold d}

/-- Literally λ + t k(R) β, with the already delivered coefficient. -/
def primitive (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (t : ℝ) : M.Form 1 :=
  T.primitive + t • LinearAlgebraChecks.radialPrimitive P (SmallCoefficient.k G P.rstar)

/-- No assumed flow, exactness, regularity or new completeness hypotheses.
This uses the actual delivered FirstPathFlow.evolution at the original hypotheses. -/
def Target : Prop :=
  ∀ (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    (C : ℝ) (hC : 0 < C) (K : Set M.Point) (hK : IsCompact K)
    (hb : ∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * G.B (P.R x)),
    MoserExactness.PullbackDerivative (primitive P G T)
      (FirstPathFlow.evolution P G T hw hC K hK hb) ∧
    MoserExactness.Endpoint (primitive P G T)
      (FirstPathFlow.evolution P G T hw hC K hK hb)
end ExactLiouvilleComparison.FirstPathExactness
