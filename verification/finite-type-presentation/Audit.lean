import ExactLiouvilleComparison.FiniteTypePresentationConsumers
set_option pp.all true
set_option pp.maxSteps 10000000

open Lean Elab Command in
run_cmd do
  let prefixes := #["ExactLiouvilleComparison.FiniteTypePresentation"]
  let owned ← (← getEnv).constants.foldM (init := (#[] : Array Name)) fun ns n _ => do
    if prefixes.any (fun p => n.toString.startsWith p ||
        n.toString.startsWith ("_private." ++ p)) then return ns.push n
    return ns
  let interfaces := #[``FsFltz.Geometry.IntrinsicLiouville.exists_completion_from_native,
    ``FsFltz.Geometry.IntrinsicLiouville.exists_liouvilleStructure_from_native,
    ``FsFltz.Geometry.IntrinsicLiouville.Form,
    ``FsFltz.Geometry.IntrinsicLiouville.IsLocallyExtendibleForm,
    ``FsFltz.Geometry.IntrinsicLiouville.Nondegenerate,
    ``FsFltz.Geometry.IntrinsicLiouville.exteriorDerivative,
    ``FsFltz.Geometry.IntrinsicLiouville.liouvilleVector,
    ``FsFltz.Geometry.IntrinsicLiouville.contraction_liouvilleVector,
    ``FsFltz.Geometry.IntrinsicBoundary.Point,
    ``FsFltz.Geometry.IntrinsicBoundary.smoothManifold,
    ``FsFltz.Geometry.IntrinsicBoundary.restrictForm,
    ``FsFltz.Geometry.IntrinsicCompletionGluing.completion,
    ``FsFltz.Geometry.IntrinsicCompletionGluing.compactDomain,
    ``FsFltz.Geometry.IntrinsicCompletionGluing.completeAmbient,
    ``FsFltz.Geometry.IntrinsicCompletionGluing.completeFlow,
    ``FsFltz.Geometry.IntrinsicCompletionGluing.original,
    ``FsFltz.Geometry.IntrinsicCompletionGluing.outwardEndMap,
    ``FsFltz.Geometry.IntrinsicCompletionGluing.boundaryOrbitMap_eq_outwardEndMap,
    ``FsFltz.Geometry.IntrinsicCompletionGluing.boundaryForm_eq_restrictForm,
    ``FsFltz.Geometry.IntrinsicCompletionGluing.completion_original_end_primitive,
    ``ExactLiouvilleComparison.FiniteTypeComparison.finiteTypeTarget,
    ``ExactLiouvilleComparison.FiniteTypeComparison.NativeConclusion,
    ``ExactLiouvilleComparison.FiniteTypeComparison.native_of_exactComparison,
    ``ExactLiouvilleComparison.FiniteTypeTarget,
    ``ExactLiouvilleComparison.ExactSymplecticStructure,
    ``ExactLiouvilleComparison.CompatibleStructure,
    ``ExactLiouvilleComparison.CompatibleStructure.MetricTangent,
    ``ExactLiouvilleComparison.CompatibleStructure.metricCore,
    ``ExactLiouvilleComparison.CompatibleStructure.Dual,
    ``ExactLiouvilleComparison.CompatibleStructure.covector,
    ``ExactLiouvilleComparison.CompatibleStructure.dualNorm,
    ``ExactLiouvilleComparison.CompatibleStructure.inverseContraction,
    ``ExactLiouvilleComparison.CompatibleStructure.inverseNorm,
    ``ExactLiouvilleComparison.WeaklyTames,
    ``ExactLiouvilleComparison.AdmissibleGrowth,
    ``ExactLiouvilleComparison.CylindricalStructure,
    ``ExactLiouvilleComparison.completionReference,
    ``ExactLiouvilleComparison.ExactComparison,
    ``ExactLiouvilleComparison.SmoothlyIsotopicToIdentity,
    ``FsFltz.Geometry.SmoothManifold,
    ``FsFltz.Geometry.SmoothManifold.Form,
    ``FsFltz.Geometry.SmoothManifold.Tangent,
    ``FsFltz.Geometry.SmoothManifold.exteriorDerivative,
    ``FsFltz.Geometry.SmoothManifold.pullback,
    ``FsFltz.Geometry.SmoothManifold.scalarDerivative,
    ``FsFltz.Geometry.LiouvilleDomain, ``FsFltz.Geometry.CompactDomain,
    ``FsFltz.Geometry.LiouvilleStructure, ``FsFltz.Geometry.Completion,
    ``FsFltz.Geometry.CompleteLiouvilleManifold, ``FsFltz.Geometry.CompleteLiouvilleFlow,
    ``Flow, ``Diffeomorph]
  let mut names := owned ++ interfaces
  -- Structure constructors expose every field, including ODE/metric assumptions.
  for n in interfaces do
    match ← getConstInfo n with
    | .inductInfo info => names := names ++ info.ctors.toArray
    | _ => pure ()
  names := (names.toList.eraseDups.toArray).qsort (fun a b => a.toString < b.toString)
  let some out ← liftIO (IO.getEnv "FINITE_TYPE_PRESENTATION_AUDIT_DIR") | throwError "Missing audit output path"
  liftIO <| IO.FS.createDirAll (out ++ "/types")
  liftIO <| IO.FS.createDirAll (out ++ "/definitions")
  liftIO <| IO.FS.writeFile (out ++ "/modules.txt")
    (String.intercalate "\n" ((← getEnv).header.moduleNames.toList.map Name.toString) ++ "\n")
  let mut axioms : Array String := #[]
  for n in names do
    let info ← getConstInfo n
    let ty ← liftTermElabM do PrettyPrinter.ppExpr info.type
    liftIO <| IO.FS.writeFile (out ++ "/types/" ++ n.toString ++ ".txt") s!"{n} : {ty.pretty}\n"
    if interfaces.contains n || owned.contains n then
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
#eval IO.println "FINITE_TYPE_PRESENTATION_AUDIT_COMPLETE"
