import ExactLiouvilleComparison.CylindricalCompatibilityContactBundleAtlas

noncomputable section
open Bundle
open scoped Manifold ContDiff
open FsFltz.Geometry FsFltz.Geometry.SmoothManifold
open ExactLiouvilleComparison.CylindricalCompatibility.ContactBundle

-- Low-dimensional domains are included; no boundary point is requested.
example (D : LiouvilleDomain 0) : ∃ P : Prebundle D, AtlasProperties D P :=
  atlas_exists 0 D
example (D : LiouvilleDomain 1) : ∃ P : Prebundle D, AtlasProperties D P :=
  atlas_exists 1 D

-- The native model really specializes to rank zero.
example (D : LiouvilleDomain 2) :
    let P := Atlas.prebundle D
    letI := P.totalSpaceTopology
    letI := P.toFiberBundle
    letI := P.toVectorBundle
    ContMDiffVectorBundle ∞ (Model 0) (Fiber D) 𝓘(ℝ, Model 1) :=
  Atlas.prebundle_smooth D

-- Arbitrary source and base map: no smoothness assumption on f is added.
example (d n : ℕ) (D : LiouvilleDomain d) (N : SmoothManifold n)
    (f : N.Point → D.domain.boundary.Point) (s : (z : N.Point) → Fiber D (f z)) :
    let P := Atlas.prebundle D
    letI := P.totalSpaceTopology
    letI := P.toFiberBundle
    letI := P.toVectorBundle
    ContMDiff 𝓘(ℝ, Model n)
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, Model (d - 2))) ∞
      (fun z ↦ TotalSpace.mk' (Model (d - 2)) (f z) (s z)) ↔
    ContMDiff 𝓘(ℝ, Model n)
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, Model (d - 1))) ∞
      (fun z ↦ TotalSpace.mk' (Model (d - 1)) (f z)
        (s z : D.domain.boundary.Tangent (f z))) :=
  Atlas.smooth_restriction_iff D n N f s

-- The exact reviewed proposition is the conclusion, without an extra input.
#check @atlas_exists
#check @Atlas.atlasProperties
#check @Atlas.prebundle
#check @Atlas.inclusion_smooth
#check @Atlas.smooth_restriction_iff
#print axioms Atlas.kernelProjection
#print axioms Atlas.kernelProjection_coe
#print axioms Atlas.kernelProjection_self
#print axioms Atlas.kernelProjection_subtype
#print axioms Atlas.kernelProjection_comp_coe
#print axioms Atlas.kernelEquiv
#print axioms Atlas.kernelEquiv_apply
#print axioms Atlas.kernelEquiv_symm_apply
#print axioms Atlas.kernelCongr
#print axioms Atlas.kernelCongr_coe
#print axioms Atlas.kernelCongr_symm_coe
#print axioms Atlas.covector
#print axioms Atlas.coefficient
#print axioms Atlas.coefficient_eq_chart
#print axioms Atlas.coefficient_smooth
#print axioms Atlas.coefficient_chart_apply
#print axioms Atlas.fiberChartEquiv
#print axioms Atlas.transverse
#print axioms Atlas.transverse_nonzero
#print axioms Atlas.modelEquiv
#print axioms Atlas.chartDomain
#print axioms Atlas.chartDomain_open
#print axioms Atlas.mem_chartDomain
#print axioms Atlas.fixedProjection
#print axioms Atlas.reconstruction
#print axioms Atlas.reconstruction_smooth
#print axioms Atlas.coordinate
#print axioms Atlas.coordinateEquiv
#print axioms Atlas.coordinateEquiv_apply
#print axioms Atlas.coordinateEquiv_symm_ambient
#print axioms Atlas.pretrivialization
#print axioms Atlas.pretrivialization_linear
#print axioms Atlas.pretrivialization_symm
#print axioms Atlas.pretrivialization_isInducing
#print axioms Atlas.transition
#print axioms Atlas.transition_smooth
#print axioms Atlas.transition_apply
#print axioms Atlas.prebundle
#print axioms Atlas.prebundle_isContMDiff
#print axioms Atlas.prebundle_smooth
#print axioms Atlas.reconstruction_coordinate
#print axioms Atlas.native_symmL
#print axioms Atlas.inclusion_coordinates
#print axioms Atlas.inclusion_smooth
#print axioms Atlas.smooth_restriction_iff
#print axioms Atlas.atlasProperties
#print axioms atlas_exists
