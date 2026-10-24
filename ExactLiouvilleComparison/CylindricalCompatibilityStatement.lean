import ExactLiouvilleComparison.Statement

/-! Specifications for the supporting assertion immediately before cor:liouville.
These are construction obligations, not proofs of existence or extension. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set

namespace ExactLiouvilleComparison.CylindricalCompatibility

/-- The actual boundary primitive, on the native boundary tangent bundle. -/
abbrev alpha {d : ℕ} (D : LiouvilleDomain d) : D.domain.boundary.Form 1 :=
  D.domain.boundaryForm D.liouville.primitive

/-- Prescribed smooth compatible contact data. `J` is the zero extension on
the Reeb line of the complex structure on `ker alpha`. All identities refer
to the actual boundary exterior derivative. No global structure is an input. -/
structure ContactData {d : ℕ} (D : LiouvilleDomain d) where
  reeb : (y : D.domain.boundary.Point) → D.domain.boundary.Tangent y
  smooth_reeb : D.domain.boundary.IsSmoothVectorField reeb
  normalized : ∀ y, evalOne (alpha D) y (reeb y) = 1
  kernel : ∀ y v,
    evalTwo (D.domain.boundary.exteriorDerivative (alpha D)) y (reeb y) v = 0
  J : (y : D.domain.boundary.Point) →
    D.domain.boundary.Tangent y →L[ℝ] D.domain.boundary.Tangent y
  smooth_J : SmoothEndomorphism D.domain.boundary J
  annihilate_reeb : ∀ y, J y (reeb y) = 0
  horizontal : ∀ y v, evalOne (alpha D) y (J y v) = 0
  square : ∀ y v, J y (J y v) = -v + evalOne (alpha D) y v • reeb y
  invariant : ∀ y v w,
    evalTwo (D.domain.boundary.exteriorDerivative (alpha D)) y (J y v) (J y w) =
      evalTwo (D.domain.boundary.exteriorDerivative (alpha D)) y v w
  positive : ∀ y v, evalOne (alpha D) y v = 0 → v ≠ 0 →
    0 < evalTwo (D.domain.boundary.exteriorDerivative (alpha D)) y v (J y v)

/-- Full end formula, at every nonnegative logarithmic time including zero.
Here `r = exp t`, so the time direction is `r ∂r`. -/
def Extends {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    (P : ContactData D) (A : CompatibleStructure (completionReference C)) : Prop :=
  ∀ y t, 0 ≤ t → ∀ (v : D.domain.boundary.Tangent y) (s : ℝ),
    A.J (C.endMap (y, t))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
        C.endMap (y, t) (v, s)) =
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
      C.endMap (y, t) (P.J y v + s • P.reeb y, -evalOne (alpha D) y v)

/-- Existence of some cylindrical compatible structure; no chosen J is assumed. -/
def ExistenceTarget : Prop :=
  ∀ (d : ℕ) (D : LiouvilleDomain d) (C : Completion D),
    ∃ A : CompatibleStructure (completionReference C), Nonempty (CylindricalStructure C A)

/-- Extension of arbitrary prescribed compatible contact data, not merely a
choice of some end structure. The output includes the explicit smooth metric
`g(v,w) = d beta(v,Jw)` through the unchanged `CompatibleStructure`. -/
def ExtensionTarget : Prop :=
  ∀ (d : ℕ) (D : LiouvilleDomain d) (C : Completion D) (P : ContactData D),
    ∃ A : CompatibleStructure (completionReference C), Extends C P A

/-- Separate nonvacuity obligation for the contact input to extension. -/
def ContactExistenceTarget : Prop :=
  ∀ (d : ℕ) (D : LiouvilleDomain d) (C : Completion D), Nonempty (ContactData D)

/-- Consumer scope: choose J before T, retaining exactly the original weak
taming and existential end-growth assumptions. -/
def ConsumerTarget : Prop :=
  ∀ (d : ℕ) (D : LiouvilleDomain d) (C : Completion D),
    ∃ A : CompatibleStructure (completionReference C),
      Nonempty (CylindricalStructure C A) ∧
      ∀ T : ExactSymplecticStructure C.ambient.manifold,
        WeaklyTames A T →
        (∃ B : AdmissibleGrowth 1, ∃ C₀ : ℝ, 0 < C₀ ∧
          ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ y t, t₀ ≤ t →
            A.inverseNorm T (C.endMap (y, t)) ≤ C₀ * B.B (Real.exp t)) →
        ExactComparison C.ambient.manifold T.primitive C.ambient.primitive

end ExactLiouvilleComparison.CylindricalCompatibility
