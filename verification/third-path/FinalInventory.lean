import ExactLiouvilleComparison.ThirdPathFlowConsumers
set_option pp.universes true
set_option pp.fullNames true
open Lean Elab Command in
run_cmd do
  let names ← (← getEnv).constants.foldM (init := (#[] : Array Name)) fun ns n _ => do
    if (`ExactLiouvilleComparison.ThirdPath).isPrefixOf n ||
        n.toString.startsWith "_private.ExactLiouvilleComparison.ThirdPath" then
      return ns.push n
    return ns
  let names := names.qsort (fun a b => a.toString < b.toString)
  let some out ← liftIO (IO.getEnv "THIRD_PATH_AUDIT_OUTPUT") | throwError "Missing output path"
  let mut lines : Array String := #[]
  for n in names do
    let info ← getConstInfo n
    let ty ← liftTermElabM do PrettyPrinter.ppExpr info.type
    lines := lines.push s!"{n} : {ty.pretty}"
  liftIO <| IO.FS.writeFile out (String.intercalate "\n" lines.toList ++ "\n")
  liftIO <| IO.FS.writeFile (out ++ ".names")
    (String.intercalate "\n" (names.toList.map Name.toString) ++ "\n")
#eval IO.println "THIRD_FINAL_INVENTORY_COMPLETE"
