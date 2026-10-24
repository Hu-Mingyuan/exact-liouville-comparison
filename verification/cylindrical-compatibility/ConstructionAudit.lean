import ExactLiouvilleComparison.CylindricalCompatibilityFinalChecks
import ExactLiouvilleComparison.CylindricalCompatibilityBridges
import ExactLiouvilleComparison.CylindricalCompatibilityContactBundleAudit

/-! Source-bound transitive audit and lossless native declaration inventory. -/
set_option maxHeartbeats 2000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleName (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => env.mainModule
  let allOwned ← env.constants.foldM (init := (#[] : Array Name)) fun ns n _ => do
    if (moduleName n).toString.startsWith "ExactLiouvilleComparison.CylindricalCompatibility" &&
        moduleName n != `ExactLiouvilleComparison.CylindricalCompatibilityContactBundleAudit then
      return ns.push n
    return ns
  let newModules := #["FormBridge", "TransportSmooth", "ProductSmooth", "MetricPairing",
    "BasinSmooth", "Extension", "", "FinalChecks"] |>.map ("ExactLiouvilleComparison.CylindricalCompatibility" ++ ·)
  let inventory := allOwned.filter (fun n => newModules.contains (moduleName n).toString)
  let interfaces := #[``ExactLiouvilleComparison.CylindricalCompatibility.ContactData,
    ``ExactLiouvilleComparison.SmoothEndomorphism,
    ``Bundle.ContMDiffRiemannianMetric,
    ``exists_contMDiffSection_forall_mem_convex_of_local,
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
  let interfaces := interfaces ++ #[
    ``ExactLiouvilleComparison.CylindricalCompatibility.ExistenceTarget,
    ``ExactLiouvilleComparison.CylindricalCompatibility.ExtensionTarget,
    ``ExactLiouvilleComparison.CylindricalCompatibility.ConsumerTarget,
    ``ExactLiouvilleComparison.CylindricalCompatibility.Extends,
    ``ExactLiouvilleComparison.CylindricalCompatibility.endTangentEquiv,
    ``ExactLiouvilleComparison.CylindricalCompatibility.endTangentJ,
    ``ExactLiouvilleComparison.CylindricalCompatibility.Normalization.SymplecticForm,
    ``ExactLiouvilleComparison.CylindricalCompatibility.Normalization.Compatible,
    ``ExactLiouvilleComparison.CylindricalCompatibility.Normalization.tangent_normalization,
    ``ExactLiouvilleComparison.CylindricalCompatibility.RelativeMetric.exists_relative_metric,
    ``ExactLiouvilleComparison.CylindricalCompatibility.RelativeMetric.ofSPD,
    ``mfderiv, ``ContMDiff]
  let mut roots := interfaces
  for n in interfaces do
    match ← getConstInfo n with
    | .inductInfo info => roots := roots ++ info.ctors.toArray
    | _ => pure ()
    if let some st := getStructureInfo? env n then
      for field in st.fieldNames do
        if let some proj := getProjFnForField? env n field then roots := roots.push proj
  let names := ((allOwned ++ roots).toList.eraseDups.toArray).qsort (fun a b => a.toString < b.toString)
  let inventory := ((inventory ++ roots).toList.eraseDups.toArray).qsort (fun a b => a.toString < b.toString)
  let some out ← liftIO (IO.getEnv "CYLINDRICAL_CONSTRUCTION_AUDIT_DIR") | throwError "Missing output directory"
  liftIO <| IO.FS.createDirAll out
  liftIO <| IO.FS.writeFile (out ++ "/modules.txt")
    (String.intercalate "\n" (env.header.moduleNames.toList.map Name.toString) ++ "\n")
  let mut axioms : Array String := #[]
  for n in names do
    let ax ← Lean.collectAxioms n
    unless ax.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "Disallowed axioms for {n}: {ax}"
    axioms := axioms.push (n.toString ++ "\t" ++ String.intercalate "," (ax.toList.map Name.toString))
  liftIO <| IO.FS.writeFile (out ++ "/axioms.tsv") (String.intercalate "\n" axioms.toList ++ "\n")
  liftIO <| IO.FS.writeFile (out ++ "/names.txt")
    (String.intercalate "\n" (names.toList.map Name.toString) ++ "\n")
  let output ← liftIO <| IO.FS.Handle.mk (out ++ "/declarations.jsonl") .write
  let mut state : ContactBundleAudit.State := {}
  liftIO <| IO.FS.createDirAll (out ++ "/metadata-expressions")
  for n in inventory do
    let info ← getConstInfo n
    let body := match info with | .defnInfo _ => true | _ => false
    let metadata := (Expr.find? Expr.isMData info.type).isSome ||
      (body && (info.value?.map (fun e => (Expr.find? Expr.isMData e).isSome)).getD false)
    if metadata then
      if info.type.hasMVar || info.type.hasFVar || info.type.hasLooseBVars then
        throwError "Nonclosed elaborated type for {n}"
      let path := "metadata-expressions/" ++ n.toString ++ ".expr"
      let typeText := "DECL " ++ n.toString ++ "\nNAME_EXPR " ++ reprStr n ++
        "\nLEVEL_PARAMS " ++ reprStr info.levelParams ++ "\nTYPE_EXPR " ++ reprStr info.type
      let text := if body then
        match info.value? with
        | some v => typeText ++ "\nVALUE_EXPR " ++ reprStr v
        | none => typeText
        else typeText
      liftIO <| IO.FS.writeFile (out ++ "/" ++ path) text
      let record := Json.mkObj [("declaration", toJson (reprStr n)),
        ("display_name", toJson n.toString), ("encoding", toJson "native-repr"),
        ("level_params", toJson (reprStr info.levelParams)), ("raw_path", toJson path),
        ("type_root", Json.null), ("value_root", Json.null),
        ("has_value", toJson (body && info.value?.isSome))]
      liftIO <| output.putStrLn record.compress
      liftIO output.flush
    else
      state ← liftIO <| ContactBundleAudit.declaration output info body state
  liftIO <| IO.FS.writeFile (out ++ "/inventory.txt")
    (String.intercalate "\n" (inventory.toList.map Name.toString) ++ "\n")
#eval IO.println "CYLINDRICAL_CONSTRUCTION_AUDIT_COMPLETE"
