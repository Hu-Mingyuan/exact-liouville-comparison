import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationSqrt
open Lean Elab Command in
run_cmd do
  for n in [``ExactLiouvilleComparison.NormalizationSqrt.contDiffOn_sqrt_posDef, ``ExactLiouvilleComparison.NormalizationSqrt.contDiffOn_sqrt_comp, ``ExactLiouvilleComparison.NormalizationSqrt.contDiffOn_inverse_sqrt_comp, ``ExactLiouvilleComparison.NormalizationSqrt.contDiff_sqrt_comp, ``ExactLiouvilleComparison.NormalizationSqrt.contDiff_inverse_sqrt_comp, ``ExactLiouvilleComparison.NormalizationSqrt.relative_sqrt_contract, ``ExactLiouvilleComparison.NormalizationSqrt.sqrt_composition_contract, ``ExactLiouvilleComparison.NormalizationSqrt.inverse_sqrt_composition_contract, ``ExactLiouvilleComparison.NormalizationSqrt.SylvesterContract, ``ExactLiouvilleComparison.NormalizationSqrt.RelativeSqrtContract, ``ExactLiouvilleComparison.NormalizationSqrt.SqrtCompositionContract, ``ExactLiouvilleComparison.NormalizationSqrt.InverseSqrtCompositionContract, ``ExactLiouvilleComparison.NormalizationSqrt.sylvester, ``ExactLiouvilleComparison.NormalizationSqrt.sylvester_apply, ``ExactLiouvilleComparison.NormalizationSqrt.sylvester_injective, ``ExactLiouvilleComparison.NormalizationSqrt.sylvesterEquiv, ``ExactLiouvilleComparison.NormalizationSqrt.sylvesterEquiv_apply, ``ExactLiouvilleComparison.NormalizationSqrt.sylvester_contract, ``ExactLiouvilleComparison.NormalizationSqrt.hasFDerivAt_sq] do
    let info ← getConstInfo n
    let ty ← liftTermElabM do PrettyPrinter.ppExpr info.type
    let line := s!"{n} : {ty.pretty}"
    logInfo (s!"SQRT_TYPE_ASCII {line.toList.map Char.toNat}")
#eval IO.println "NORMALIZATION_SQRT_TYPES_COMPLETE"
