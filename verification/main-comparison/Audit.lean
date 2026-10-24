import ExactLiouvilleComparison.MainComparison
set_option pp.all true
set_option pp.maxSteps 10000000
open Lean Elab Command in
run_cmd do
  let names ← (← getEnv).constants.foldM (init := (#[] : Array Name)) fun ns n _ => do
    let s := n.toString
    if s.startsWith "ExactLiouvilleComparison.MainComparison" ||
        s.startsWith "_private.ExactLiouvilleComparison.MainComparison" ||
        s.startsWith "_private.ExactLiouvilleComparison.RemainingPathExactness" then
      return ns.push n
    return ns
  let interfaces := #[``ExactLiouvilleComparison.MainTarget,
    ``ExactLiouvilleComparison.ExactComparison,
    ``ExactLiouvilleComparison.ExactComparisonAlgebra.Witness,
    ``ExactLiouvilleComparison.SmoothlyIsotopicToIdentity,
    ``ExactLiouvilleComparison.RadialReference,
    ``ExactLiouvilleComparison.AdmissibleGrowth,
    ``ExactLiouvilleComparison.GrowthAtInfinity,
    ``ExactLiouvilleComparison.WeaklyTames,
    ``ExactLiouvilleComparison.CompatibleStructure,
    ``ExactLiouvilleComparison.CompatibleStructure.dualNorm,
    ``ExactLiouvilleComparison.CompatibleStructure.inverseNorm,
    ``ExactLiouvilleComparison.MoserExactness.moserExactness,
    ``ExactLiouvilleComparison.MoserExactness.Endpoint,
    ``ExactLiouvilleComparison.MoserExactness.Equation,
    ``ExactLiouvilleComparison.MoserExactness.gauge,
    ``ExactLiouvilleComparison.FirstPathExactness.firstPathExactness,
    ``ExactLiouvilleComparison.FirstPathExactness.exactComparison,
    ``ExactLiouvilleComparison.ThirdPath.thirdPathFlow,
    ``ExactLiouvilleComparison.ThirdPath.evolution,
    ``ExactLiouvilleComparison.RadialInterpolationFlow.evolution,
    ``ExactLiouvilleComparison.FirstPathFlow.Evolution,
    ``ExactLiouvilleComparison.ExactComparisonAlgebra.Witness.comp,
    ``ExactLiouvilleComparison.ExactComparisonAlgebra.Witness.symm]
  let names := (names ++ interfaces).qsort (fun a b => a.toString < b.toString)
  let some out ← liftIO (IO.getEnv "MAIN_COMPARISON_AUDIT_DIR") | throwError "Missing output path"
  liftIO <| IO.FS.createDirAll (out ++ "/types")
  for n in names do
    let info ← getConstInfo n
    let ty ← liftTermElabM do PrettyPrinter.ppExpr info.type
    liftIO <| IO.FS.writeFile (out ++ "/types/" ++ n.toString ++ ".txt") s!"{n} : {ty.pretty}\n"
    elabCommand (← `(command| #print axioms $(mkIdent n)))
  liftIO <| IO.FS.writeFile (out ++ "/names.txt")
    (String.intercalate "\n" (names.toList.map Name.toString) ++ "\n")
#eval IO.println "MAIN_COMPARISON_AUDIT_COMPLETE"
