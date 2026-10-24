import ExactLiouvilleComparison.FirstPathChecks
import ExactLiouvilleComparison.RadialInterpolationChecks
import FsFltz.Geometry.FamilyLiouvilleNeighborhood

/-! Bounded statement gate only. These propositions are specifications, not proofs. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.MoserRegularity
variable {d : ℕ} {M : SmoothManifold d}

/-- A single extension is native jointly smooth at each required parameter-space point.
There is no uniform negative-time strip or off-interval nondegeneracy assumption. -/
def NativeJoint (Z : Parameter → (x : M.Point) → M.Tangent x) : Prop :=
  ∃ E : ℝ → (x : M.Point) → M.Tangent x,
    (∀ t : Parameter, E t.val = Z t) ∧
    ∀ p : ℝ × M.Point, p.1 ∈ parameterInterval →
      ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
        (fun q : ℝ × M.Point =>
          (⟨q.2, E q.1 q.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)) p

/-- Positive contraction for an arbitrary form and covector family. -/
def InverseBridgeTarget : Prop :=
  ∀ (omega : ℝ → M.Form 2) (α : ℝ → M.Form 1),
    M.IsSmoothFormFamily omega → M.IsSmoothFormFamily α →
    (∀ t ∈ parameterInterval, ∀ x, M.Nondegenerate (omega t) x) →
    ∃ Z : Parameter → (x : M.Point) → M.Tangent x,
      NativeJoint Z ∧ ∀ t x,
        (∀ w, evalTwo (omega t.val) x (Z t x) w = evalOne (α t.val) x w) ∧
        ∀ v : M.Tangent x, (∀ w, evalTwo (omega t.val) x v w = evalOne (α t.val) x w) → v = Z t x

def firstField (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    (t : Parameter) (x : M.Point) : M.Tangent x := FirstPath.X P G T hw x t.val t.property.1

def interpolationField (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ) (hw : RadialInterpolation.WeakDifferential (P := P) σ)
    (t : Parameter) (x : M.Point) : M.Tangent x :=
  RadialInterpolation.vector (RadialInterpolation.coefficient q₀ q₁ t.val t.property)
    σ hσ hw (RadialInterpolation.delta q₀ q₁) x

def FirstTarget (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T) : Prop :=
  NativeJoint (firstField P G T hw) ∧
  ∀ K : Set M.Point, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
    ∀ t : Parameter, ∀ x ∈ K,
      |M.scalarDerivative (FirstPath.exhaustion P G) x (firstField P G T hw t x)| ≤ C

/-- Actual time derivative plus actual spatial derivative of Q_u(R). -/
def barrierRate (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (Z : Parameter → (x : M.Point) → M.Tangent x) (t : Parameter) (x : M.Point) : ℝ :=
  RadialInterpolation.delta q₀ q₁ (P.R x) * P.R x +
    M.scalarDerivative (fun y => RadialInterpolation.Q q₀ q₁ t.val (P.R y)) x (Z t x)

def InterpolationTarget (P : RadialReference M) (q₀ q₁ : RadialCoefficient P.rstar)
    (σ : M.Form 1) (hσ : M.IsSmoothForm σ) (hw : RadialInterpolation.WeakDifferential (P := P) σ) : Prop :=
  NativeJoint (interpolationField P q₀ q₁ σ hσ hw) ∧
  ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ t : Parameter, ∀ x, P.R x ≤ P.rstar →
    M.scalarDerivative P.R x (interpolationField P q₀ q₁ σ hσ hw t x) ≤ C₀ ∧
    -C₁ ≤ barrierRate P q₀ q₁ (interpolationField P q₀ q₁ σ hσ hw) t x

end ExactLiouvilleComparison.MoserRegularity
