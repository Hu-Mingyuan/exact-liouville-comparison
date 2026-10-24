import ExactLiouvilleComparison.Geometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Basic

/-! The four manuscript targets are Props, not proved theorems. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set Filter

namespace ExactLiouvilleComparison

/-- Values below the specified endpoint are irrelevant. Smoothness includes
the endpoint, using the native within-set derivative convention. -/
structure AdmissibleGrowth (lower : ℝ) where
  B : ℝ → ℝ
  smooth : ContDiffOn ℝ ∞ B (Ici lower)
  positive : ∀ r ∈ Ici lower, 0 < B r
  dominates : ∀ r ∈ Ici lower, r ≤ B r
  divergent : Tendsto (fun b : ℝ => ∫ r in lower..b, r / (B r) ^ 2) atTop atTop

structure RadialReference {d : ℕ} (M : SmoothManifold d) where
  exactStructure : ExactSymplecticStructure M
  compatible : CompatibleStructure exactStructure
  R : M.Point → ℝ
  smooth_R : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ R
  proper_R : IsProperMap R
  lower_R : ∀ x, 1 ≤ R x
  c : ℝ
  positive_c : 0 < c
  rstar : ℝ
  one_lt_rstar : 1 < rstar
  radial_identity : ∀ x, rstar < R x → ∀ v,
    evalOne exactStructure.primitive x v = -c * M.scalarDerivative R x (compatible.J x v)
  radial_bound : ∀ x, rstar < R x →
    c * (compatible.dualNorm x (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) R x)) ^ 2 ≤ R x

def WeaklyTames {d : ℕ} {M : SmoothManifold d}
    {S : ExactSymplecticStructure M} (A : CompatibleStructure S)
    (T : ExactSymplecticStructure M) : Prop :=
  ∀ x v, 0 ≤ evalTwo (M.exteriorDerivative T.primitive) x v (A.J x v)

/-- Only the inverse-form bound has a compact-set exception. -/
def GrowthAtInfinity {d : ℕ} {M : SmoothManifold d}
    {S : ExactSymplecticStructure M} (A : CompatibleStructure S)
    (T : ExactSymplecticStructure M) (R : M.Point → ℝ) (lower : ℝ) : Prop :=
  ∃ B : AdmissibleGrowth lower, ∃ C : ℝ, 0 < C ∧
    ∃ K : Set M.Point, IsCompact K ∧ ∀ x, x ∉ K → A.inverseNorm T x ≤ C * B.B (R x)

/-- Manuscript thm:main. No completeness or primitive-growth input. -/
def MainTarget : Prop :=
  ∀ (d : ℕ) (M : SmoothManifold d) (P : RadialReference M)
    (T : ExactSymplecticStructure M),
    WeaklyTames P.compatible T →
    GrowthAtInfinity P.compatible T P.R 1 →
    ExactComparison M T.primitive P.exactStructure.primitive

/-- Manuscript cor:two, with independent growth witnesses for both forms. -/
def CommonReferenceTarget : Prop :=
  ∀ (d : ℕ) (M : SmoothManifold d) (P : RadialReference M)
    (T₁ T₂ : ExactSymplecticStructure M),
    WeaklyTames P.compatible T₁ → GrowthAtInfinity P.compatible T₁ P.R 1 →
    WeaklyTames P.compatible T₂ → GrowthAtInfinity P.compatible T₂ P.R 1 →
    ExactComparison M T₁.primitive T₂.primitive

/-- Complete specialization keeps the actual prescribed primitive and its flow. -/
def CompleteLiouvilleComparisonTarget : Prop :=
  ∀ (d : ℕ) (M : SmoothManifold d) (P : RadialReference M)
    (_ : CompletePrimitive M P.exactStructure.primitive)
    (T : ExactSymplecticStructure M) (_ : CompletePrimitive M T.primitive),
    WeaklyTames P.compatible T → GrowthAtInfinity P.compatible T P.R 1 →
    ExactComparison M T.primitive P.exactStructure.primitive

def completionReference {d : ℕ} {D : LiouvilleDomain d} (C : Completion D) :
    ExactSymplecticStructure C.ambient.manifold where
  primitive := C.ambient.primitive
  smooth_primitive := C.ambient.smooth_primitive
  symplectic := C.ambient.symplectic

/-- The cylindrical structure in logarithmic radius t = log r.
The formula includes J(r∂r)=Reeb and an r-independent complex structure
on the contact distribution. It asserts no radial exhaustion or comparison. -/
structure CylindricalStructure {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    (A : CompatibleStructure (completionReference C)) where
  reeb : (y : D.domain.boundary.Point) → D.domain.boundary.Tangent y
  contactJ : (y : D.domain.boundary.Point) →
    D.domain.boundary.Tangent y →L[ℝ] D.domain.boundary.Tangent y
  reeb_normalized : ∀ y,
    evalOne (D.domain.boundaryForm D.liouville.primitive) y (reeb y) = 1
  reeb_kernel : ∀ y v,
    evalTwo (D.domain.boundary.exteriorDerivative
      (D.domain.boundaryForm D.liouville.primitive)) y (reeb y) v = 0
  contactJ_reeb : ∀ y, contactJ y (reeb y) = 0
  contactJ_horizontal : ∀ y v,
    evalOne (D.domain.boundaryForm D.liouville.primitive) y (contactJ y v) = 0
  cylindrical : ∀ y t, 0 ≤ t → ∀ (v : D.domain.boundary.Tangent y) (s : ℝ),
    A.J (C.endMap (y, t))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
        C.endMap (y, t) (v, s)) =
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d))
      C.endMap (y, t)
      (contactJ y v + s • reeb y, -evalOne (D.domain.boundaryForm D.liouville.primitive) y v)

/-- Manuscript cor:liouville. The new primitive is not assumed complete.
The reference is an actual complete marked end of a compact Liouville domain. -/
def FiniteTypeTarget : Prop :=
  ∀ (d : ℕ) (D : LiouvilleDomain d) (C : Completion D)
    (A : CompatibleStructure (completionReference C)), CylindricalStructure C A →
    ∀ T : ExactSymplecticStructure C.ambient.manifold,
    WeaklyTames A T →
    (∃ B : AdmissibleGrowth 1, ∃ C₀ : ℝ, 0 < C₀ ∧
      ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ y t, t₀ ≤ t →
        A.inverseNorm T (C.endMap (y, t)) ≤ C₀ * B.B (Real.exp t)) →
    ExactComparison C.ambient.manifold T.primitive C.ambient.primitive

/-- Source data for a proper holomorphic embedding, expressed on the native
real tangent bundle by its complex structure and Cauchy–Riemann equation.
No symplectic structure, metric, radial estimate or flow is an input. -/
structure ProperComplexEmbedding {d : ℕ} (M : SmoothManifold d) (N : ℕ) where
  J : (x : M.Point) → M.Tangent x →L[ℝ] M.Tangent x
  smooth_J : SmoothEndomorphism M J
  square : ∀ x v, J x (J x v) = -v
  map : M.Point → EuclideanSpace ℂ (Fin N)
  smooth : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) ∞ map
  embedding : Topology.IsEmbedding map
  proper : IsProperMap map
  immersion : ∀ x, Function.Injective
    (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) map x)
  complex_linear : ∀ x v,
    mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) map x (J x v) =
      Complex.I • (show EuclideanSpace ℂ (Fin N) from
        mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) map x v)

def steinRadius {d N : ℕ} {M : SmoothManifold d}
    (i : ProperComplexEmbedding M N) (x : M.Point) : ℝ :=
  Real.exp 1 + ‖i.map x‖ ^ 2

/-- The reference data to be CONSTRUCTED from the embedding. The identities fix
beta, J and the metric to the manuscript's data. No comparison conclusion,
flow, radial inequality or primitive-growth estimate is included. -/
structure SteinReference {d N : ℕ} {M : SmoothManifold d}
    (i : ProperComplexEmbedding M N) where
  exactStructure : ExactSymplecticStructure M
  compatible : CompatibleStructure exactStructure
  complex_eq : compatible.J = i.J
  primitive_eq : ∀ x v, evalOne exactStructure.primitive x v =
    -(1 / 4 : ℝ) * M.scalarDerivative (steinRadius i) x (i.J x v)
  induced_metric : ∀ x v w, compatible.g.inner x v w =
    @inner ℝ (EuclideanSpace ℂ (Fin N)) _
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x v)
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, EuclideanSpace ℂ (Fin N))) i.map x w)

/-- Explicit unproved construction obligation. A definition of this Prop does
not construct the reference and does not discharge any geometric proof. -/
def SteinReferenceConstructionTarget : Prop :=
  ∀ (d N : ℕ) (M : SmoothManifold d) (i : ProperComplexEmbedding M N),
    Nonempty (SteinReference i)

/-- The packaged conditional comparison, separated from source coverage. -/
def PackagedSteinTarget : Prop :=
  ∀ (d N : ℕ) (M : SmoothManifold d) (i : ProperComplexEmbedding M N)
    (P : SteinReference i) (T : ExactSymplecticStructure M),
    WeaklyTames P.compatible T →
    GrowthAtInfinity P.compatible T (steinRadius i) (Real.exp 1) →
    ExactComparison M T.primitive P.exactStructure.primitive

/-- Full source-level cor:stein target. Reference construction is an OUTPUT,
prior to quantifying the other primitive; it is not an extra hypothesis.
The construction and comparison remain unproved. -/
def SteinTarget : Prop :=
  ∀ (d N : ℕ) (M : SmoothManifold d) (i : ProperComplexEmbedding M N),
    ∃ P : SteinReference i, ∀ T : ExactSymplecticStructure M,
      WeaklyTames P.compatible T →
      GrowthAtInfinity P.compatible T (steinRadius i) (Real.exp 1) →
      ExactComparison M T.primitive P.exactStructure.primitive

/-- A logical assembly bridge only: both geometric obligations are hypotheses.
This theorem proves neither reference construction nor comparison. -/
theorem steinTarget_of_construction_and_packaged
    (construction : SteinReferenceConstructionTarget) (comparison : PackagedSteinTarget) :
    SteinTarget := by
  intro d N M i
  obtain ⟨P⟩ := construction d N M i
  exact ⟨P, comparison d N M i P⟩

/-- Source coverage is a necessary part of the full Stein target. -/
theorem steinTarget_requires_construction (h : SteinTarget) :
    SteinReferenceConstructionTarget := by
  intro d N M i
  obtain ⟨P, _⟩ := h d N M i
  exact ⟨P⟩

/-- All four manuscript statements, including source-level Stein construction.
This is the full proof obligation, not a proved theorem. -/
def ManuscriptTarget : Prop :=
  MainTarget ∧ FiniteTypeTarget ∧ SteinTarget ∧ CommonReferenceTarget

end ExactLiouvilleComparison
