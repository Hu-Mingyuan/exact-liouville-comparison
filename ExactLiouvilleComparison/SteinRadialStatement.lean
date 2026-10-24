import ExactLiouvilleComparison.Statement

/-! Bounded Stein radial obligation. This definition is a statement, not a proof. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.SteinRadial

/-- The literal exhaustion and its induced-metric estimate, followed by the
radial package with the original structures and fixed constants. The input `P`
is the separately owned intermediate Stein reference, not an extra hypothesis
of the source-level Stein comparison. -/
def Target : Prop :=
  ∀ (d N : ℕ) (M : SmoothManifold d) (i : ProperComplexEmbedding M N)
    (P : SteinReference i),
    ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ (steinRadius i) ∧
    IsProperMap (steinRadius i) ∧
    (∀ x, 1 ≤ steinRadius i x) ∧
    (∀ x, (P.compatible.dualNorm x
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) (steinRadius i) x)) ^ 2 ≤
      4 * (steinRadius i x - Real.exp 1)) ∧
    ∃ Q : RadialReference M,
      Q.exactStructure = P.exactStructure ∧ HEq Q.compatible P.compatible ∧
      Q.R = steinRadius i ∧ Q.c = (1 / 4 : ℝ) ∧ Q.rstar = 2

end ExactLiouvilleComparison.SteinRadial
