import ExactLiouvilleComparison

/-! The public entry point must expose proof terms for the original targets. -/
open ExactLiouvilleComparison

example : MainTarget := MainComparison.mainTarget
example : ManuscriptTarget := ManuscriptComparison.manuscriptTarget
example : CompleteLiouvilleComparisonTarget :=
  ManuscriptComparison.completeLiouvilleComparisonTarget
example : CylindricalCompatibility.ExistenceTarget :=
  CylindricalCompatibility.existenceTarget
example : CylindricalCompatibility.ExtensionTarget :=
  CylindricalCompatibility.extensionTarget
example : CylindricalCompatibility.ConsumerTarget :=
  CylindricalCompatibility.consumerTarget

#check CylindricalCompatibility.extension_of_prescribed_kernel
#check NativeIntegration.constructedComparison
#check NativeIntegration.prescribedExtension
example : ManuscriptTarget := NativeIntegration.manuscript
example : CylindricalCompatibility.ExistenceTarget := NativeIntegration.allDimensions
example : CylindricalCompatibility.ExtensionTarget := NativeIntegration.everyPrescribedEnd
