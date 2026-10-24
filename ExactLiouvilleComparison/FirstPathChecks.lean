import ExactLiouvilleComparison.FirstPathEstimate

/-! Generic consumers of the actual accepted interfaces. No flow conclusions. -/
noncomputable section
open scoped Manifold ContDiff Topology
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold Set
namespace ExactLiouvilleComparison.FirstPathChecks
variable {d : ℕ} {M : SmoothManifold d}
open FirstPath SmallCoefficient

/-- Both coefficient endpoints and the compact core use the delivered scalar function. -/
theorem coefficient_core (P : RadialReference M) (G : AdmissibleGrowth 1)
    (r : ℝ) (hr : r ∈ Icc 1 P.rstar) :
    (coefficient P G).rho r = 1 ∧ (coefficient P G).rhoPrime r = 0 ∧
      m G P.rstar r = 1 := by
  have hk := k_eq_one G hr.1 hr.2
  have hp := kprime_zero G hr.1 hr.2
  exact ⟨hk, hp, by simp only [m, hk, hp, mul_zero, add_zero]⟩

theorem unique_native_solution (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T)
    (x : M.Point) (t : ℝ) (ht : t ∈ Icc 0 1) :
    ∃! v : M.Tangent x, ∀ w, evalTwo (form P G T t) x v w =
      -k G P.rstar (P.R x) * evalOne P.exactStructure.primitive x w :=
  ⟨X P G T hw x t ht.1, X_equation P G T hw x t ht.1,
    fun v hv => X_unique P G T hw x t ht.1 v hv⟩

/-- The t=0 vector is the constructed inverse contraction W. -/
theorem zero_parameter (P : RadialReference M) (G : AdmissibleGrowth 1)
    (T : ExactSymplecticStructure M) (hw : WeaklyTames P.compatible T) (x : M.Point) :
    X P G T hw x 0 le_rfl = W P G T x ∧
      ∀ v, evalTwo (M.exteriorDerivative T.primitive) x (X P G T hw x 0 le_rfl) v =
        -k G P.rstar (P.R x) * evalOne P.exactStructure.primitive x v := by
  refine ⟨X_zero P G T hw x, ?_⟩
  rw [X_zero]
  exact W_equation P G T x

/-- Accepted compact-exception growth supplies the exterior bound. The conclusion
does not assert smoothness of X, compact-core bounds, or ODE completeness. -/
theorem growth_consumer (P : RadialReference M) (T : ExactSymplecticStructure M)
    (hw : WeaklyTames P.compatible T)
    (hg : GrowthAtInfinity P.compatible T P.R 1) :
    ∃ (G : AdmissibleGrowth 1) (C : ℝ), 0 < C ∧
      ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ (exhaustion P G) ∧
      IsProperMap (exhaustion P G) ∧ BddBelow (range (exhaustion P G)) ∧
      ∃ L : Set M.Point, IsCompact L ∧
        ∀ x, x ∉ L → ∀ t (ht : t ∈ Icc 0 1),
          |M.scalarDerivative (exhaustion P G) x (X P G T hw x t ht.1)| ≤
            Real.sqrt 2 * C * b0 G P.rstar := by
  obtain ⟨G, C, hC, K, hK, hb⟩ := hg
  obtain ⟨L, hL, _, hbound⟩ := exterior_estimate P G T hw hC K hK hb
  exact ⟨G, C, hC, exhaustion_smooth P G, exhaustion_proper P G,
    exhaustion_bddBelow P G, L, hL, fun x hx t ht => hbound x hx t ht.1⟩

end ExactLiouvilleComparison.FirstPathChecks
