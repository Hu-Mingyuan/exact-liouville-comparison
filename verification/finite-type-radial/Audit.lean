import ExactLiouvilleComparison.FiniteTypeRadialConsumers
set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.maxSteps 1000000
set_option pp.deepTerms true

open Lean Elab Command in
run_cmd do
  let names ← (← getEnv).constants.foldM (init := (#[] : Array Name)) fun ns n _ => do
    if n.toString.startsWith "ExactLiouvilleComparison.FiniteTypeRadial" ||
        n.toString.startsWith "_private.ExactLiouvilleComparison.FiniteTypeRadial" then
      return ns.push n
    return ns
  let names := names.qsort (fun a b => a.toString < b.toString)
  let some out ← liftIO (IO.getEnv "FINITE_TYPE_RADIAL_AUDIT_OUTPUT") |
    throwError "Missing FINITE_TYPE_RADIAL_AUDIT_OUTPUT"
  let mut types : Array String := #[]
  let mut axioms : Array String := #[]
  let mut readable : Array String := #[]
  for n in names do
    let info ← getConstInfo n
    let ty ← liftTermElabM do PrettyPrinter.ppExpr info.type
    types := types.push s!"{n} : {ty.pretty}"
    let tyReadable ← liftTermElabM do
      withOptions (fun o => o.setBool `pp.explicit false) do PrettyPrinter.ppExpr info.type
    readable := readable.push s!"{n} : {tyReadable.pretty}"
    let ax ← Lean.collectAxioms n
    axioms := axioms.push (n.toString ++ "\t" ++
      String.intercalate "," (ax.toList.map Name.toString))
  liftIO <| IO.FS.writeFile (out ++ ".types") (String.intercalate "\n" types.toList ++ "\n")
  liftIO <| IO.FS.writeFile (out ++ ".readable") (String.intercalate "\n" readable.toList ++ "\n")
  liftIO <| IO.FS.writeFile (out ++ ".axioms") (String.intercalate "\n" axioms.toList ++ "\n")
  liftIO <| IO.FS.writeFile (out ++ ".names")
    (String.intercalate "\n" (names.toList.map Name.toString) ++ "\n")
#eval IO.println "FINITE_TYPE_RADIAL_AUDIT_COMPLETE"
