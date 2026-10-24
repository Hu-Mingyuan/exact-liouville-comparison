import ExactLiouvilleComparison.ThirdPathEndpoints
import ExactLiouvilleComparison.ThirdPathExhaustion
import ExactLiouvilleComparison.FirstPathFlow

/-! Actual third-path evolution. All regularity and scalar hypotheses of the
continuation theorem are discharged for the literal delivered coefficient A. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.ThirdPath
variable {d : ℕ} {M : SmoothManifold d}

theorem evolution_exists (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) :
    Nonempty (FirstPathFlow.Evolution (field P T hw)) := by
  obtain ⟨E, heq, Ω, hΩ, hstrip, hE⟩ :=
    ODE.native_open_of_interval_family (field P T hw) (field_intervalSmooth P T hw)
  obtain ⟨D, hD, hb⟩ := exhaustion_global_bound P (field_joint P T hw)
    (field_norm_le_one P T hw)
  have hbound : ∀ t ∈ parameterInterval, ∀ x,
      |M.scalarDerivative (exhaustion P) x (E t x)| ≤ D := by
    intro t ht x
    have he := congrFun (heq ⟨t, ht⟩) x
    change E t x = field P T hw ⟨t, ht⟩ x at he
    rw [he]
    exact hb ⟨t, ht⟩ x
  have hfields : (fun t : Parameter => E t.val) = field P T hw := funext heq
  simpa only [hfields] using FirstPathFlow.evolution_of_scalar_bound E hΩ hstrip hE
    (exhaustion P) (exhaustion_smooth P) (exhaustion_proper P)
    (exhaustion_bddBelow P) hD hbound

/-- A chosen actual evolution, justified by the proved existence theorem. -/
def evolution (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) : FirstPathFlow.Evolution (field P T hw) :=
  Classical.choice (evolution_exists P T hw)

/-- Every field of the independently reviewed output contract is constructed. -/
def construction (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T) : Construction P T where
  field := field P T hw
  smooth_primitive := primitive_family P T
  symplectic := symplectic P T hw
  equation := field_equation P T hw
  unique_field := field_unique P T hw
  joint := field_joint P T hw
  norm_bound := field_norm_bound P T hw
  ratio_le_one := ratio_le_one P T
  exterior_bound := fun s x hx =>
    exhaustion_exterior_bound P x hx _ (field_norm_le_one P T hw s x)
  smooth_exhaustion := exhaustion_smooth P
  proper_exhaustion := exhaustion_proper P
  lower_exhaustion := exhaustion_lower P
  core_bound := exhaustion_core_bound P (field_joint P T hw)
  global_bound := exhaustion_global_bound P (field_joint P T hw) (field_norm_le_one P T hw)
  evolution := evolution P T hw
  inverse_isotopy := evolution_inverse_isotopy (evolution P T hw)

/-- The bounded third-path target, with no assumed field, trajectory or evolution. -/
theorem thirdPathFlow : Target (M := M) := by
  intro P T hw
  exact ⟨construction P T hw⟩

end ExactLiouvilleComparison.ThirdPath
