import ExactLiouvilleComparison.CylindricalCompatibilityBridges
import ExactLiouvilleComparison.CylindricalCompatibilityEndTransport
import ExactLiouvilleComparison.CylindricalCompatibilityRelativeSection

/-! Native consumers of the partial prerequisites, not existence claims. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ExactLiouvilleComparison.CylindricalCompatibility.Checks

example {d : ℕ} {D : LiouvilleDomain d} (C : Completion D) (P : ContactData D)
    (y : D.domain.boundary.Point) (t : ℝ) (v : D.domain.boundary.Tangent y) (s : ℝ) :
    endTangentJ C P y t
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
        C.endMap (y, t) (v, s)) =
      mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
        C.endMap (y, t) (P.J y v + s • P.reeb y, -evalOne (alpha D) y v) :=
  endTangentJ_formula C P y t (v, s)

example (hc : ContactExistenceTarget) (he : ExtensionTarget) : ConsumerTarget :=
  consumer_of_existence (existence_of_contact_and_extension hc he)

end ExactLiouvilleComparison.CylindricalCompatibility.Checks

#eval IO.println "CYLINDRICAL_COMPATIBILITY_CONSUMERS_COMPLETE"
