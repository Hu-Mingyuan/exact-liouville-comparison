import ExactLiouvilleComparison.CylindricalCompatibilityNormalizationConsumers
set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
set_option pp.deepTerms true
open Lean Elab Command in
run_cmd do
  let names ← (← getEnv).constants.foldM (init := (#[] : Array Name)) fun ns n _ => do
    if (`ExactLiouvilleComparison.NormalizationAlgebra).isPrefixOf n ||
        (`ExactLiouvilleComparison.NormalizationSqrt).isPrefixOf n ||
        (`ExactLiouvilleComparison.CylindricalCompatibility.Normalization).isPrefixOf n ||
        n.toString.startsWith "_private.ExactLiouvilleComparison.CylindricalCompatibilityNormalization" then
      return ns.push n
    return ns
  let names := names.qsort (fun a b => a.toString < b.toString)
  let some out ← liftIO (IO.getEnv "NORMALIZATION_BUNDLE_AUDIT_OUTPUT") | throwError "Missing output path"
  let mut lines : Array String := #[]
  for n in names do
    let axioms ← Lean.collectAxioms n
    lines := lines.push (n.toString ++ "\t" ++
      String.intercalate "," (axioms.toList.map Name.toString))
  liftIO <| IO.FS.writeFile out (String.intercalate "\n" lines.toList ++ "\n")
#eval IO.println "NORMALIZATION_BUNDLE_AXIOMS_COMPLETE"
