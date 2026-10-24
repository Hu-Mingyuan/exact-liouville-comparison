import ExactLiouvilleComparison.FirstPathExactness
set_option pp.all true
open Lean Elab Command in
run_cmd do
  let names ← (← getEnv).constants.foldM (init := (#[] : Array Name)) fun ns n _ => do
    let s := n.toString
    if s.startsWith "ExactLiouvilleComparison.MoserExactness" ||
        s.startsWith "ExactLiouvilleComparison.FirstPathExactness" ||
        s.startsWith "_private.ExactLiouvilleComparison.MoserExactness" ||
        s.startsWith "_private.ExactLiouvilleComparison.FirstPathExactness" then
      return ns.push n
    return ns
  let names := names.qsort (fun a b => a.toString < b.toString)
  let some out ← liftIO (IO.getEnv "MOSER_FINAL_AUDIT_DIR") | throwError "Missing audit output path"
  liftIO <| IO.FS.createDirAll (out ++ "/types")
  for n in names do
    let info ← getConstInfo n
    let ty ← liftTermElabM do PrettyPrinter.ppExpr info.type
    liftIO <| IO.FS.writeFile (out ++ "/types/" ++ n.toString ++ ".txt") s!"{n} : {ty.pretty}\n"
    elabCommand (← `(command| #print axioms $(mkIdent n)))
  liftIO <| IO.FS.writeFile (out ++ "/names.txt")
    (String.intercalate "\n" (names.toList.map Name.toString) ++ "\n")
#eval IO.println "MOSER_FINAL_AUDIT_COMPLETE"
