import ExactLiouvilleComparison.CorollaryComparisonStatement

/-! Applications to the literal Stein reference; no additional geometric inputs. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.SteinComparison
variable {d N : ℕ} {M : SmoothManifold d}

/-- The radial package uses the original induced Euclidean metric verbatim. -/
theorem radial_inner_eq (i : ProperComplexEmbedding M N) (P : SteinReference i)
    (x : M.Point) (v w : M.Tangent x) :
    (SteinRadial.reference i P).compatible.g.inner x v w = P.compatible.g.inner x v w := rfl

/-- The covector's operator norm uses exactly the same g. -/
theorem radial_dualNorm_eq (i : ProperComplexEmbedding M N) (P : SteinReference i)
    (x : M.Point) (l : M.Tangent x →L[ℝ] ℝ) :
    (SteinRadial.reference i P).compatible.dualNorm x l = P.compatible.dualNorm x l := rfl

/-- In particular the hypothesis is not silently changed to a chart norm. -/
theorem radial_inverseNorm_eq (i : ProperComplexEmbedding M N) (P : SteinReference i)
    (T : ExactSymplecticStructure M) (x : M.Point) :
    (SteinRadial.reference i P).compatible.inverseNorm T x = P.compatible.inverseNorm T x := rfl

theorem radial_weaklyTames_iff (i : ProperComplexEmbedding M N) (P : SteinReference i)
    (T : ExactSymplecticStructure M) :
    WeaklyTames (SteinRadial.reference i P).compatible T ↔ WeaklyTames P.compatible T := Iff.rfl

/-- Discharge properness and the lower bound in the delivered growth consumer. -/
theorem growth (i : ProperComplexEmbedding M N) (P : SteinReference i)
    (T : ExactSymplecticStructure M)
    (hg : GrowthAtInfinity P.compatible T (steinRadius i) (Real.exp 1)) :
    GrowthAtInfinity (SteinRadial.reference i P).compatible T (SteinRadial.reference i P).R 1 :=
  SteinGrowth.steinRadius_growth i P T (SteinRadial.radius_proper i)
    (SteinRadial.radius_lower i) hg

/-- Every packaged reference, with every admissible growth function. -/
theorem packagedSteinTarget : PackagedSteinTarget := by
  intro d N M i P T hw hg
  exact MainComparison.mainTarget d M (SteinRadial.reference i P) T hw (growth i P T hg)

/-- The reference is the delivered construction from the embedding alone. -/
theorem constructedSteinTarget : CorollaryComparison.ConstructedSteinTarget := by
  intro d N M i T
  exact packagedSteinTarget d N M i (SteinReferenceConstruction.reference i) T

/-- Source-level cor:stein: reference construction is an output, before T. -/
theorem steinTarget : SteinTarget := by
  intro d N M i
  exact ⟨SteinReferenceConstruction.reference i,
    packagedSteinTarget d N M i (SteinReferenceConstruction.reference i)⟩

/-- Expose the actual delivered Moser endpoint and gauge for the literal
extension of B and compact enlargement, without assuming any comparison. -/
theorem comparisonWitness (i : ProperComplexEmbedding M N) (P : SteinReference i)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    (B : AdmissibleGrowth (Real.exp 1)) {C : ℝ} (hC : 0 < C)
    (K : Set M.Point) (hK : IsCompact K)
    (hb : ∀ x, x ∉ K → P.compatible.inverseNorm T x ≤ C * B.B (steinRadius i x)) :
    let Q := SteinRadial.reference i P
    let G := SteinGrowth.extend B
    let K' := SteinGrowth.enlargedException (steinRadius i) K
    let hK' := SteinGrowth.enlargedException_compact
      (SteinRadial.radius_proper i) (SteinRadial.radius_lower i) hK
    let hb' := SteinGrowth.estimate_outside_enlarged P.compatible T (steinRadius i) B C K hb
    ExactComparisonAlgebra.Witness M T.primitive P.exactStructure.primitive
      (MainComparison.comparisonMap Q G T hw hC K' hK' hb')
      (MainComparison.comparisonGauge Q G T hw hC K' hK' hb') :=
  MainComparison.comparisonWitness (SteinRadial.reference i P) (SteinGrowth.extend B) T hw hC
    (SteinGrowth.enlargedException (steinRadius i) K)
    (SteinGrowth.enlargedException_compact
      (SteinRadial.radius_proper i) (SteinRadial.radius_lower i) hK)
    (SteinGrowth.estimate_outside_enlarged P.compatible T (steinRadius i) B C K hb)

end ExactLiouvilleComparison.SteinComparison
