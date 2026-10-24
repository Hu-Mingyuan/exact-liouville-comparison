import ExactLiouvilleComparison.FirstPathChecks

noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.FirstPathConsumer
open FirstPath SmallCoefficient
variable {d : ℕ} {M : SmoothManifold d}

theorem norm_is_metric {S : ExactSymplecticStructure M} (A : CompatibleStructure S)
    (x : M.Point) (v : M.Tangent x) :
    tangentNorm A x v = Real.sqrt (A.g.inner x v v) := rfl

theorem explicit_metrics (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    (x : M.Point) (t : ℝ) (ht : t ∈ Icc 0 1) :
    tangentNorm (coefficient P G).compatible x (X P G T hw x t ht.1) ≤
      tangentNorm (coefficient P G).compatible x (W P G T x) ∧
    tangentNorm P.compatible x (X P G T hw x t ht.1) ≤
      Real.sqrt (k G P.rstar (P.R x) / m G P.rstar (P.R x)) *
        tangentNorm P.compatible x (W P G T x) :=
  ⟨X_h_bound P G T hw x t ht.1, X_g_bound P G T hw x t ht.1⟩

theorem tail_both (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    (x : M.Point) (t : ℝ) (ht : t ∈ Icc 0 1) {C : ℝ} (hC : 0 < C)
    (hx : P.rstar + 1 ≤ P.R x)
    (hb : P.compatible.inverseNorm T x ≤ C * G.B (P.R x)) :
    |M.scalarDerivative P.R x (X P G T hw x t ht.1)| ≤
      Real.sqrt 2 * C * b0 G P.rstar * (G.B (P.R x)) ^ 2 * S G (P.R x) / P.R x ∧
    |M.scalarDerivative (exhaustion P G) x (X P G T hw x t ht.1)| ≤
      Real.sqrt 2 * C * b0 G P.rstar :=
  ⟨firstestimate P G T hw x t ht.1 hC hx hb, firstproper P G T hw x t ht.1 hC hx hb⟩

end ExactLiouvilleComparison.FirstPathConsumer
#check ExactLiouvilleComparison.FirstPathChecks.coefficient_core
#check ExactLiouvilleComparison.FirstPathChecks.unique_native_solution
#check ExactLiouvilleComparison.FirstPathChecks.zero_parameter
#check ExactLiouvilleComparison.FirstPathChecks.growth_consumer
#print axioms ExactLiouvilleComparison.FirstPathConsumer.norm_is_metric
#print axioms ExactLiouvilleComparison.FirstPathConsumer.explicit_metrics
#print axioms ExactLiouvilleComparison.FirstPathConsumer.tail_both
#check ExactLiouvilleComparison.FirstPathConsumer.norm_is_metric
#check ExactLiouvilleComparison.FirstPathConsumer.explicit_metrics
#check ExactLiouvilleComparison.FirstPathConsumer.tail_both
#eval IO.println "FIRST_PATH_CONSUMER_COMPLETE"
