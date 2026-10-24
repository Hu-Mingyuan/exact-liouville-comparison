import ExactLiouvilleComparison.ManuscriptComparisonConsumers
set_option pp.all true
set_option pp.maxSteps 10000000

open Lean Elab Command in
run_cmd do
  let prefixes := #["ExactLiouvilleComparison.FiniteTypeComparison",
    "ExactLiouvilleComparison.ManuscriptComparison"]
  let owned ← (← getEnv).constants.foldM (init := (#[] : Array Name)) fun ns n _ => do
    if prefixes.any (fun p => n.toString.startsWith p ||
        n.toString.startsWith ("_private." ++ p)) then return ns.push n
    return ns
  let interfaces := #[``ExactLiouvilleComparison.MainTarget,
    ``ExactLiouvilleComparison.FiniteTypeTarget, ``ExactLiouvilleComparison.SteinTarget,
    ``ExactLiouvilleComparison.CommonReferenceTarget, ``ExactLiouvilleComparison.ManuscriptTarget,
    ``ExactLiouvilleComparison.CompleteLiouvilleComparisonTarget,
    ``ExactLiouvilleComparison.ExactSymplecticStructure,
    ``ExactLiouvilleComparison.CompatibleStructure,
    ``ExactLiouvilleComparison.CompatibleStructure.MetricTangent,
    ``ExactLiouvilleComparison.CompatibleStructure.metricCore,
    ``ExactLiouvilleComparison.CompatibleStructure.Dual,
    ``ExactLiouvilleComparison.CompatibleStructure.covector,
    ``ExactLiouvilleComparison.CompatibleStructure.dualNorm,
    ``ExactLiouvilleComparison.CompatibleStructure.flatLinear,
    ``ExactLiouvilleComparison.CompatibleStructure.flatEquiv,
    ``ExactLiouvilleComparison.CompatibleStructure.inverseContraction,
    ``ExactLiouvilleComparison.CompatibleStructure.inverseNorm,
    ``ExactLiouvilleComparison.SmoothEndomorphism,
    ``ExactLiouvilleComparison.RadialReference, ``ExactLiouvilleComparison.WeaklyTames,
    ``ExactLiouvilleComparison.AdmissibleGrowth, ``ExactLiouvilleComparison.GrowthAtInfinity,
    ``ExactLiouvilleComparison.CylindricalStructure, ``ExactLiouvilleComparison.completionReference,
    ``ExactLiouvilleComparison.ProperComplexEmbedding, ``ExactLiouvilleComparison.SteinReference,
    ``ExactLiouvilleComparison.steinRadius,
    ``ExactLiouvilleComparison.ExactComparison, ``ExactLiouvilleComparison.SmoothlyIsotopicToIdentity,
    ``ExactLiouvilleComparison.MainComparison.mainTarget,
    ``ExactLiouvilleComparison.MainComparison.comparisonMap,
    ``ExactLiouvilleComparison.MainComparison.comparisonGauge,
    ``ExactLiouvilleComparison.MainComparison.comparisonWitness,
    ``ExactLiouvilleComparison.FiniteTypeRadial.reference,
    ``ExactLiouvilleComparison.FiniteTypeRadial.constructedRadius,
    ``ExactLiouvilleComparison.FiniteTypeRadial.Radius,
    ``ExactLiouvilleComparison.FiniteTypeRadial.Radius.toReference,
    ``ExactLiouvilleComparison.FiniteTypeRadial.reference_growth,
    ``ExactLiouvilleComparison.FiniteTypeRadial.growth_witness,
    ``ExactLiouvilleComparison.SteinComparison.steinTarget,
    ``ExactLiouvilleComparison.SteinReferenceConstruction.reference,
    ``ExactLiouvilleComparison.SteinComparison.growth,
    ``ExactLiouvilleComparison.CommonReferenceComparison.commonReferenceTarget,
    ``FsFltz.Geometry.SmoothManifold, ``FsFltz.Geometry.LiouvilleDomain,
    ``FsFltz.Geometry.CompactDomain, ``FsFltz.Geometry.BoundaryDefiningFunction,
    ``FsFltz.Geometry.LiouvilleStructure, ``FsFltz.Geometry.Completion,
    ``FsFltz.Geometry.CompleteLiouvilleManifold, ``FsFltz.Geometry.CompletePrimitive,
    ``FsFltz.Geometry.CompleteLiouvilleFlow,
    ``FsFltz.Geometry.CompletePrimitive.toCompleteLiouvilleManifold,
    ``FsFltz.Geometry.SmoothManifold.Form, ``FsFltz.Geometry.SmoothManifold.Tangent,
    ``FsFltz.Geometry.SmoothManifold.SmoothEquiv,
    ``FsFltz.Geometry.SmoothManifold.SmoothEmbedding,
    ``FsFltz.Geometry.SmoothManifold.IsSmoothForm,
    ``FsFltz.Geometry.SmoothManifold.IsSmoothVectorField,
    ``FsFltz.Geometry.SmoothManifold.IsSymplecticOn,
    ``FsFltz.Geometry.SmoothManifold.Nondegenerate,
    ``FsFltz.Geometry.SmoothManifold.LiouvilleEquation,
    ``FsFltz.Geometry.SmoothManifold.liouvilleVector,
    ``FsFltz.Geometry.SmoothManifold.formInChart,
    ``FsFltz.Geometry.SmoothManifold.vectorInChart,
    ``FsFltz.Geometry.SmoothManifold.chartTangentMap,
    ``FsFltz.Geometry.SmoothManifold.exteriorDerivative,
    ``FsFltz.Geometry.SmoothManifold.pullback,
    ``FsFltz.Geometry.SmoothManifold.scalarDerivative,
    ``FsFltz.Geometry.SmoothManifold.evalOne, ``FsFltz.Geometry.SmoothManifold.evalTwo,
    ``Flow, ``Diffeomorph]
  let mut names := owned ++ interfaces
  -- Structure constructors expose every field, including ODE/metric assumptions.
  for n in interfaces do
    match ← getConstInfo n with
    | .inductInfo info => names := names ++ info.ctors.toArray
    | _ => pure ()
  names := (names.toList.eraseDups.toArray).qsort (fun a b => a.toString < b.toString)
  let some out ← liftIO (IO.getEnv "MANUSCRIPT_AUDIT_DIR") | throwError "Missing audit output path"
  liftIO <| IO.FS.createDirAll (out ++ "/types")
  liftIO <| IO.FS.createDirAll (out ++ "/definitions")
  let mut axioms : Array String := #[]
  for n in names do
    let info ← getConstInfo n
    let ty ← liftTermElabM do PrettyPrinter.ppExpr info.type
    liftIO <| IO.FS.writeFile (out ++ "/types/" ++ n.toString ++ ".txt") s!"{n} : {ty.pretty}\n"
    if interfaces.contains n then
      match info with
      | .defnInfo d =>
        let body ← liftTermElabM do PrettyPrinter.ppExpr d.value
        liftIO <| IO.FS.writeFile (out ++ "/definitions/" ++ n.toString ++ ".txt")
          s!"{n} := {body.pretty}\n"
      | _ => pure ()
    let ax ← Lean.collectAxioms n
    axioms := axioms.push (n.toString ++ "\t" ++ String.intercalate "," (ax.toList.map Name.toString))
  liftIO <| IO.FS.writeFile (out ++ "/axioms.tsv") (String.intercalate "\n" axioms.toList ++ "\n")
  liftIO <| IO.FS.writeFile (out ++ "/names.txt")
    (String.intercalate "\n" (names.toList.map Name.toString) ++ "\n")
#eval IO.println "MANUSCRIPT_AUDIT_COMPLETE"
