import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationStatement

/-! The empty-base and rank-zero cases of the reviewed native contract. -/
noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace ExactLiouvilleComparison.CylindricalCompatibility.Normalization

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  [IsManifold IB ∞ B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle ∞ F E IB]

/-- On an empty base the actual zero section supplies normalization. -/
theorem normalization_of_isEmpty [IsEmpty B] (omega : SymplecticForm IB F E)
    (h : ContMDiffRiemannianMetric IB ∞ F E) : NormalizationTarget IB F E omega h := by
  refine ⟨fun _ ↦ 0, ?_, ?_, ?_⟩
  · exact contMDiff_zeroSection ℝ (fun x ↦ E x →L[ℝ] E x)
  · intro x
    exact isEmptyElim x
  · intro x
    exact isEmptyElim x

/-- Zero fibers require no choice of a positive-rank normalizing formula. -/
theorem normalization_of_subsingleton_fibers [∀ x, Subsingleton (E x)]
    (omega : SymplecticForm IB F E) (h : ContMDiffRiemannianMetric IB ∞ F E) :
    NormalizationTarget IB F E omega h := by
  refine ⟨fun _ ↦ 0, contMDiff_zeroSection ℝ (fun x ↦ E x →L[ℝ] E x), ?_, ?_⟩
  · intro x
    refine ⟨fun _ ↦ Subsingleton.elim _ _, ?_, ?_⟩
    · intro v w
      have hv : v = 0 := Subsingleton.elim _ _
      have hw : w = 0 := Subsingleton.elim _ _
      simp [hv, hw]
    · intro v hv
      exact (hv (Subsingleton.elim _ _)).elim
  · intro x J₀ _ _
    ext v
    exact Subsingleton.elim _ _

/-- A zero-dimensional model has zero-dimensional native fibers via actual
bundle trivializations, including for a nontrivial base. -/
theorem normalization_of_subsingleton_model [Subsingleton F]
    (omega : SymplecticForm IB F E) (h : ContMDiffRiemannianMetric IB ∞ F E) :
    NormalizationTarget IB F E omega h := by
  let (x : B) : Subsingleton (E x) :=
    (trivializationAt F E x).linearEquivAt ℝ x
      (mem_baseSet_trivializationAt F E x) |>.injective.subsingleton
  exact normalization_of_subsingleton_fibers omega h

/-- The rank-zero branch, expressed with native module dimension. -/
theorem normalization_of_finrank_zero (hF : Module.finrank ℝ F = 0)
    (omega : SymplecticForm IB F E) (h : ContMDiffRiemannianMetric IB ∞ F E) :
    NormalizationTarget IB F E omega h := by
  let : Subsingleton F := Module.finrank_zero_iff.mp hF
  exact normalization_of_subsingleton_model omega h

end ExactLiouvilleComparison.CylindricalCompatibility.Normalization
