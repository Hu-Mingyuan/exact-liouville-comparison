import ExactLiouvilleComparison.ODEContinuation
#check ExactLiouvilleComparison.ODE.exists_bounded_smooth_compact_cutoff
#check ExactLiouvilleComparison.ODE.contMDiff_cutoff_field
#check ExactLiouvilleComparison.ODE.scalar_bound_cutoff
#check ExactLiouvilleComparison.ODE.finiteIntervalExistence
#print ExactLiouvilleComparison.ODE.FiniteIntervalExistenceTarget
example {d : ℕ} {M : FsFltz.Geometry.SmoothManifold d} :
    ExactLiouvilleComparison.ODE.FiniteIntervalExistenceTarget (M := M) :=
  ExactLiouvilleComparison.ODE.finiteIntervalExistence
#eval IO.println "ODE_CONTINUATION_TYPES_COMPLETE"
