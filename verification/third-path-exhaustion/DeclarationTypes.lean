import ExactLiouvilleComparison.ThirdPathExhaustion
open Lean Elab Command in
run_cmd do
  for n in [``ExactLiouvilleComparison.ThirdPath.exhaustion_smooth, ``ExactLiouvilleComparison.ThirdPath.exhaustion_lower, ``ExactLiouvilleComparison.ThirdPath.exhaustion_bddBelow, ``ExactLiouvilleComparison.ThirdPath.exhaustion_proper, ``ExactLiouvilleComparison.ThirdPath.exhaustion_derivative, ``ExactLiouvilleComparison.ThirdPath.exhaustion_exterior_bound, ``ExactLiouvilleComparison.ThirdPath.exhaustion_core_bound, ``ExactLiouvilleComparison.ThirdPath.exhaustion_global_bound] do
    let info ← getConstInfo n
    let ty ← liftTermElabM do PrettyPrinter.ppExpr info.type
    let line := s!"{n} : {ty.pretty}"
    logInfo (s!"SCALAR_TYPE_ASCII {line.toList.map Char.toNat}")
#eval IO.println "THIRD_PATH_SCALAR_TYPES_COMPLETE"
