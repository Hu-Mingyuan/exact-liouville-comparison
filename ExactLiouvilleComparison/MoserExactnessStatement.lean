import ExactLiouvilleComparison.FirstPathFlow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Bounded contracts for manuscript eq:exactness. These definitions are statements,
not proofs. All geometry is the pinned native geometry; no exactness is input data. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.MoserExactness
variable {d : ℕ} {M : SmoothManifold d}

/-- The literal scalar μₜ(Xₜ) pulled back by the identity-start evolution. -/
def contractionAlong (mu : ℝ → M.Form 1)
    {Z : Parameter → (x : M.Point) → M.Tangent x}
    (E : FirstPathFlow.Evolution Z) (t : Parameter) (x : M.Point) : ℝ :=
  evalOne (mu t.val) (E.map parameterZero t x) (Z t (E.map parameterZero t x))

/-- The literal interval integral. Values outside [0,1] are set to zero solely
because intervalIntegral takes an all-real function; they do not affect H. -/
def gauge (mu : ℝ → M.Form 1)
    {Z : Parameter → (x : M.Point) → M.Tangent x}
    (E : FirstPathFlow.Evolution Z) (x : M.Point) : ℝ := by
  classical
  exact ∫ t in (0 : ℝ)..1, if ht : t ∈ parameterInterval then
    contractionAlong mu E ⟨t, ht⟩ x else 0

/-- The actual Moser equation, with the positive contraction convention.
The time derivative holds the base point and tangent vector fixed. -/
def Equation (mu : ℝ → M.Form 1)
    (Z : Parameter → (x : M.Point) → M.Tangent x) : Prop :=
  ∀ (t : Parameter) (x : M.Point) (v : M.Tangent x),
    evalTwo (M.exteriorDerivative (mu t.val)) x (Z t x) v =
      -deriv (fun u => evalOne (mu u) x v) t.val

/-- Analytic Cartan identity after substituting the Moser equation, including
one-sided derivatives at both endpoints. The pullback uses the actual mfderiv. -/
def PullbackDerivative (mu : ℝ → M.Form 1)
    {Z : Parameter → (x : M.Point) → M.Tangent x}
    (E : FirstPathFlow.Evolution Z) : Prop :=
  ∀ (t : Parameter) (x : M.Point) (v : M.Tangent x),
    HasDerivWithinAt
      (fun u => evalOne (M.pullback M (E.extension 0 u) (mu u)) x v)
      (M.scalarDerivative (contractionAlong mu E t) x v) parameterInterval t.val

/-- Full time-dependent Cartan formula before Moser cancellation. -/
def CartanDerivative (mu : ℝ → M.Form 1)
    {Z : Parameter → (x : M.Point) → M.Tangent x}
    (E : FirstPathFlow.Evolution Z) : Prop :=
  ∀ (t : Parameter) (x : M.Point) (v : M.Tangent x),
    let y := E.map parameterZero t x
    let w := mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (E.map parameterZero t) x v
    HasDerivWithinAt
      (fun u => evalOne (M.pullback M (E.extension 0 u) (mu u)) x v)
      (deriv (fun u => evalOne (mu u) y w) t.val +
        evalTwo (M.exteriorDerivative (mu t.val)) y (Z t y) w +
        M.scalarDerivative (contractionAlong mu E t) x v) parameterInterval t.val

/-- Cartan is to be proved from smooth families and the actual evolution ODE. -/
def CartanTarget : Prop :=
  ∀ (mu : ℝ → M.Form 1), M.IsSmoothFormFamily mu →
    ∀ (Z : Parameter → (x : M.Point) → M.Tangent x),
      M.IsSmoothIntervalVectorFieldFamily Z →
        ∀ E : FirstPathFlow.Evolution Z, CartanDerivative mu E

/-- Required endpoint conclusions for the explicitly defined integral gauge. -/
def Endpoint (mu : ℝ → M.Form 1)
    {Z : Parameter → (x : M.Point) → M.Tangent x}
    (E : FirstPathFlow.Evolution Z) : Prop :=
  ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ (gauge mu E) ∧
  (∀ x v, evalOne (M.pullback M (E.map parameterZero parameterOne) (mu 1)) x v =
    evalOne (mu 0) x v + M.scalarDerivative (gauge mu E) x v) ∧
  M.pullback M (E.map parameterZero parameterOne) (M.exteriorDerivative (mu 1)) =
    M.exteriorDerivative (mu 0)

/-- Generic bounded exactness contract. The field/evolution are legitimate inputs
here; the first-path application below must construct/discharge them. Smoothness
means an actual open extension, not pointwise smooth slices or formal operations. -/
def Target : Prop :=
  ∀ (mu : ℝ → M.Form 1), M.IsSmoothFormFamily mu →
    ∀ (Z : Parameter → (x : M.Point) → M.Tangent x),
      M.IsSmoothIntervalVectorFieldFamily Z → Equation mu Z →
        ∀ E : FirstPathFlow.Evolution Z, PullbackDerivative mu E ∧ Endpoint mu E
end ExactLiouvilleComparison.MoserExactness
