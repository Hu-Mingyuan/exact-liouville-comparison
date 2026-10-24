import ExactLiouvilleComparison.FiniteTypeRadialMetricChecks
set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
set_option pp.deepTerms true
open Lean Elab Command in
run_cmd do
  let names ← (← getEnv).constants.foldM (init := (#[] : Array Name)) fun ns n _ => do
    if (`ExactLiouvilleComparison.FiniteTypeRadialMetric).isPrefixOf n ||
        n.toString.startsWith "_private.ExactLiouvilleComparison.FiniteTypeRadialMetric" then
      return ns.push n
    return ns
  let names := names.qsort (fun a b => a.toString < b.toString)
  let some out ← liftIO (IO.getEnv "FINITE_TYPE_RADIAL_METRIC_AUDIT_OUTPUT") | throwError "Missing output path"
  let mut lines : Array String := #[]
  for n in names do
    let axioms ← Lean.collectAxioms n
    lines := lines.push (n.toString ++ "\t" ++
      String.intercalate "," (axioms.toList.map Name.toString))
  liftIO <| IO.FS.writeFile out (String.intercalate "\n" lines.toList ++ "\n")
#eval IO.println "FINITE_TYPE_RADIAL_METRIC_AXIOMS_COMPLETE"
