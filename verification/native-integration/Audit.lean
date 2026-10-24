import ExactLiouvilleComparison.NativeIntegration
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
    if (moduleName n).toString.startsWith "ExactLiouvilleComparison" &&
        moduleName n != `ExactLiouvilleComparison.CylindricalCompatibilityContactBundleAudit then
      return ns.push n
    return ns
  let inventory := allOwned.filter (fun n =>
    (moduleName n).toString.startsWith "ExactLiouvilleComparison.NativeIntegration")
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
  let interfaces := interfaces ++ #[
    ``ExactLiouvilleComparison.FiniteTypePresentation.fromNative,
    ``ExactLiouvilleComparison.FiniteTypePresentation.QuotientData,
    ``ExactLiouvilleComparison.FiniteTypePresentation.QuotientData.completed,
    ``ExactLiouvilleComparison.FiniteTypePresentation.QuotientData.Identifications,
    ``ExactLiouvilleComparison.FiniteTypePresentation.QuotientData.ComparisonFor,
    ``ExactLiouvilleComparison.FiniteTypePresentation.QuotientData.comparisonFor,
    ``ExactLiouvilleComparison.FiniteTypePresentation.LocalOutward,
    ``ExactLiouvilleComparison.FiniteTypePresentation.nativeTarget,
    ``ExactLiouvilleComparison.CylindricalCompatibility.existenceTarget,
    ``ExactLiouvilleComparison.CylindricalCompatibility.extensionTarget,
    ``ExactLiouvilleComparison.CylindricalCompatibility.extension_of_prescribed_kernel,
    ``ExactLiouvilleComparison.CylindricalCompatibility.FinalChecks.native_consumer,
    ``ExactLiouvilleComparison.ManuscriptComparison.manuscriptTarget,
    ``ExactLiouvilleComparison.ManuscriptComparison.completeLiouvilleComparisonTarget,
    ``ExactLiouvilleComparison.ManuscriptComparisonConsumers.completeNative,
    ``ExactLiouvilleComparison.ManuscriptTarget,
    ``ExactLiouvilleComparison.CompleteLiouvilleComparisonTarget,
    ``FsFltz.Geometry.CompletePrimitive,
    ``FsFltz.Geometry.IntrinsicLiouville.exists_completion_from_native,
    ``FsFltz.Geometry.IntrinsicLiouville.exists_liouvilleStructure_from_native]
  let mut roots := interfaces
  for n in interfaces do
    match ← getConstInfo n with
    | .inductInfo info => roots := roots ++ info.ctors.toArray
    | _ => pure ()
    if let some st := getStructureInfo? env n then
      for field in st.fieldNames do
        if let some proj := getProjFnForField? env n field then roots := roots.push proj
  -- Definition-assumption closure of the integrated public types. Follow native
  -- project/FsFltz types and computational bodies, including structure fields.
  -- The unchanged foundational Mathlib/core interfaces are source-bound below.
  let mut closure := (inventory ++ roots).toList.eraseDups.toArray
  let mut seen : NameSet := {}
  let mut external : NameSet := {}
  let mut i := 0
  while i < closure.size do
    let n := closure[i]!
    i := i + 1
    if seen.contains n then continue
    seen := seen.insert n
    let info ← getConstInfo n
    let mut refs := info.type.getUsedConstants
    if let .defnInfo d := info then refs := refs ++ d.value.getUsedConstants
    if let .inductInfo d := info then refs := refs ++ d.ctors.toArray
    if let some st := getStructureInfo? env n then
      for field in st.fieldNames do
        if let some proj := getProjFnForField? env n field then refs := refs.push proj
    for r in refs do
      let m := (moduleName r).toString
      if m.startsWith "ExactLiouvilleComparison" || m.startsWith "FsFltz" then
        unless seen.contains r || closure.contains r do closure := closure.push r
      else external := external.insert r
  let inventory := closure.qsort (fun a b => a.toString < b.toString)
  let names := ((allOwned ++ inventory).toList.eraseDups.toArray).qsort (fun a b => a.toString < b.toString)
  let some out ← liftIO (IO.getEnv "NATIVE_INTEGRATION_AUDIT_DIR") | throwError "Missing output directory"
  liftIO <| IO.FS.createDirAll out
  liftIO <| IO.FS.writeFile (out ++ "/modules.txt")
    (String.intercalate "\n" (env.header.moduleNames.toList.map Name.toString) ++ "\n")
  liftIO <| IO.FS.writeFile (out ++ "/external-definition-boundary.txt")
    (String.intercalate "\n" (external.toList.map Name.toString) ++ "\n")
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
#eval IO.println "NATIVE_INTEGRATION_AUDIT_COMPLETE"
