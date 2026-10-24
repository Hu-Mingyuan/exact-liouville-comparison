import ExactLiouvilleComparison.ThirdPathEndpoints
set_option pp.universes true
set_option pp.fullNames true
open Lean Elab Command in
run_cmd do
  let mut lines : Array String := #[]
  for n in [``ExactLiouvilleComparison.ThirdPath.primitive, ``ExactLiouvilleComparison.ThirdPath.exhaustion, ``ExactLiouvilleComparison.ThirdPath.Construction, ``ExactLiouvilleComparison.ThirdPath.Target, ``ExactLiouvilleComparison.ThirdPath.coefficient, ``ExactLiouvilleComparison.ThirdPath.primitive_smooth, ``ExactLiouvilleComparison.ThirdPath.primitive_family, ``ExactLiouvilleComparison.ThirdPath.form, ``ExactLiouvilleComparison.ThirdPath.differential_eq, ``ExactLiouvilleComparison.ThirdPath.form_apply, ``ExactLiouvilleComparison.ThirdPath.form_family, ``ExactLiouvilleComparison.ThirdPath.energy_lower, ``ExactLiouvilleComparison.ThirdPath.nondegenerate, ``ExactLiouvilleComparison.ThirdPath.symplectic, ``ExactLiouvilleComparison.ThirdPath.field, ``ExactLiouvilleComparison.ThirdPath.field_equation_form, ``ExactLiouvilleComparison.ThirdPath.field_equation, ``ExactLiouvilleComparison.ThirdPath.field_unique, ``ExactLiouvilleComparison.ThirdPath.field_joint, ``ExactLiouvilleComparison.ThirdPath.field_intervalSmooth, ``ExactLiouvilleComparison.ThirdPath.field_norm_bound, ``ExactLiouvilleComparison.ThirdPath.ratio_le_one, ``ExactLiouvilleComparison.ThirdPath.field_norm_le_one, ``ExactLiouvilleComparison.ThirdPath.primitive_zero, ``ExactLiouvilleComparison.ThirdPath.primitive_one, ``ExactLiouvilleComparison.ThirdPath.primitive_parameter_derivative, ``ExactLiouvilleComparison.ThirdPath.isotopy_symm, ``ExactLiouvilleComparison.ThirdPath.evolution_inverse_isotopy] do
    let info ← getConstInfo n
    let ty ← liftTermElabM do PrettyPrinter.ppExpr info.type
    let line := s!"{n} : {ty.pretty}"
    lines := lines.push line
  let some out ← liftIO (IO.getEnv "THIRD_PATH_TYPE_OUTPUT") | throwError "Missing type output path"
  liftIO <| IO.FS.writeFile out (String.intercalate "\n" lines.toList ++ "\n")
#eval IO.println "THIRD_INPUT_TYPES_COMPLETE"
