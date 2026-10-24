import ExactLiouvilleComparison.CorollaryComparisonConsumers
set_option pp.all true
set_option pp.maxSteps 10000000
open Lean Elab Command in
run_cmd do
  let prefixes := #["ExactLiouvilleComparison.CorollaryComparison",
    "ExactLiouvilleComparison.SteinComparison",
    "ExactLiouvilleComparison.CommonReferenceComparison"]
  let names ← (← getEnv).constants.foldM (init := (#[] : Array Name)) fun ns n _ => do
    let s := n.toString
    if prefixes.any (fun p => s.startsWith p || s.startsWith ("_private." ++ p)) then
      return ns.push n
    return ns
  let interfaces := #[``ExactLiouvilleComparison.PackagedSteinTarget,
    ``ExactLiouvilleComparison.SteinTarget,
    ``ExactLiouvilleComparison.CommonReferenceTarget,
    ``ExactLiouvilleComparison.MainTarget,
    ``ExactLiouvilleComparison.ProperComplexEmbedding,
    ``ExactLiouvilleComparison.SteinReference,
    ``ExactLiouvilleComparison.steinRadius,
    ``ExactLiouvilleComparison.ExactSymplecticStructure,
    ``ExactLiouvilleComparison.CompatibleStructure,
    ``ExactLiouvilleComparison.CompatibleStructure.MetricTangent,
    ``ExactLiouvilleComparison.CompatibleStructure.covector,
    ``ExactLiouvilleComparison.CompatibleStructure.dualNorm,
    ``ExactLiouvilleComparison.CompatibleStructure.inverseContraction,
    ``ExactLiouvilleComparison.CompatibleStructure.inverseNorm,
    ``ExactLiouvilleComparison.RadialReference,
    ``ExactLiouvilleComparison.WeaklyTames,
    ``ExactLiouvilleComparison.AdmissibleGrowth,
    ``ExactLiouvilleComparison.GrowthAtInfinity,
    ``ExactLiouvilleComparison.ExactComparison,
    ``ExactLiouvilleComparison.SmoothlyIsotopicToIdentity,
    ``ExactLiouvilleComparison.ExactComparisonAlgebra.Witness,
    ``ExactLiouvilleComparison.MainComparison.mainTarget,
    ``ExactLiouvilleComparison.MainComparison.comparisonMap,
    ``ExactLiouvilleComparison.MainComparison.comparisonGauge,
    ``ExactLiouvilleComparison.MainComparison.comparisonWitness,
    ``ExactLiouvilleComparison.SteinReferenceConstruction.reference,
    ``ExactLiouvilleComparison.SteinReferenceConstruction.construction,
    ``ExactLiouvilleComparison.SteinReferenceConstruction.checkedConstruction,
    ``ExactLiouvilleComparison.SteinRadial.reference,
    ``ExactLiouvilleComparison.SteinRadial.metric_norm_eq,
    ``ExactLiouvilleComparison.SteinRadial.radius_dualNorm_sq,
    ``ExactLiouvilleComparison.SteinGrowth.extend,
    ``ExactLiouvilleComparison.SteinGrowth.extend_eq,
    ``ExactLiouvilleComparison.SteinGrowth.scalarTarget,
    ``ExactLiouvilleComparison.SteinGrowth.witnessTarget,
    ``ExactLiouvilleComparison.SteinGrowth.growthTarget,
    ``ExactLiouvilleComparison.SteinGrowth.steinConsumerTarget,
    ``ExactLiouvilleComparison.SteinGrowth.steinRadius_growth,
    ``ExactLiouvilleComparison.SteinGrowth.estimate_outside_enlarged,
    ``ExactLiouvilleComparison.ExactComparisonAlgebra.Witness.commonReference,
    ``ExactLiouvilleComparison.ExactComparison.commonReference]
  let names := (names ++ interfaces).qsort (fun a b => a.toString < b.toString)
  let some out ← liftIO (IO.getEnv "COROLLARIES_AUDIT_DIR") | throwError "Missing output path"
  liftIO <| IO.FS.createDirAll (out ++ "/types")
  for n in names do
    let info ← getConstInfo n
    let ty ← liftTermElabM do PrettyPrinter.ppExpr info.type
    liftIO <| IO.FS.writeFile (out ++ "/types/" ++ n.toString ++ ".txt") s!"{n} : {ty.pretty}\n"
    elabCommand (← `(command| #print axioms $(mkIdent n)))
  liftIO <| IO.FS.writeFile (out ++ "/names.txt")
    (String.intercalate "\n" (names.toList.map Name.toString) ++ "\n")
#eval IO.println "COROLLARIES_AUDIT_COMPLETE"
