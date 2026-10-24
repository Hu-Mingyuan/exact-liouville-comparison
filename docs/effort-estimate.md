# Early dependency and effort estimate

Status: provisional engineering estimate, 2026-10-23; not a proof claim or an accepted roadmap. Statement mission 35518290-ed35-47a8-a227-c5d55b1c117f retains integration. No graph changes are proposed by this document. Objective revision 1 is unchanged.

Inspection pins: FsFltz 1a3d387cfacc746e25aad31e5b27b1803103e7cb; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; Lean 4.34.1. Inspected FsFltz Geometry/Smooth, Liouville, FixedAmbient, ExteriorDerivative, and Mathlib Geometry/Manifold/IntegralCurve/{ExistUnique,UniformTime}, Analysis/InnerProductSpace/Defs, and Geometry/Manifold/VectorBundle/Riemannian.

## Evidence and critical path

FsFltz already supplies actual native tangent forms, chart exterior differentiation, square-zero, naturality of exterior differentiation, complete all-real-time Liouville flow data, and domain completion presentations. Mathlib supplies inner-product norms, finite-dimensional duality, proper maps, interval integration, smooth maps/diffeomorphisms, and local manifold integral-curve existence and uniqueness. These are useful ingredients; none inspected is the four-path global comparison theorem.

The revised inspection resolves one investigation gap: pinned FsFltz CollarSmoothEvolution proves joint smooth dependence for actual all-real autonomous solutions and for time-dependent solutions through every initial time. These are reusable proved results, not missing general theory. The cluster snapshot at 2c239b0c03922a1549f18ee3a45a8e0ca25bb28c demonstrates how finite-time compact confinement, FsFltz uniform compact local lifetimes and native uniqueness construct all-real solutions and both inverse flow laws for its specialized field. See the source-bound reuse table and verification/cluster-access.json; access is resolved.

The remaining ODE work is globalization for the manuscript's time-dependent Moser fields, including interval extension/reparametrization needed to meet the existing smooth-dependence theorem's all-real hypotheses, and inverse endpoint assembly. Parameterized pullback/Cartan identities, smooth integration of the primitive correction and isotopy concatenation still need suitable interfaces or new proofs. The R1 review also exposed a concrete application gap: the symplectic/metric reference must be constructed from arbitrary source embedding data, with g equal to the pulled-back Euclidean metric. The revised full Stein target includes this unproved construction as an output. Native Riemannian bundles and explicit metric-fiber/inverse operators are already reused in the statement.

Critical path: accepted faithful statements and norm bridges → parameterized smooth geometry/ODE continuation and exactness → radial compactness bounds for four paths → composition/inversion and corollaries → independent full-proof review, audit and final exposition. Linear algebra and coefficient estimates can be developed independently after the statement gate. No comparison proof has begun.

## Ranges

Allow 9–13 substantial stages, approximately 15,000–50,000 new hand-written Lean lines, excluding all dependencies and generated files. Allow approximately 4–16 weeks of elapsed work with sustained availability of two work slots and one reserved review slot. These are broad planning ranges, not measured throughput or delivery commitments; unresolved globalization, parameterized exactness and Stein construction could exceed the upper range. Queue outages and maintainer response time are additional risks.

| Work | Approximate new Lean lines | Principal uncertainty |
| --- | ---: | --- |
| Statement gate, metric/native definition bridges and consumers | 600–2,500 | Corollary presentation fidelity and review repairs |
| Reusable manifold/ODE and parameterized forms infrastructure | 8,000–28,000 | Adapt existing smooth dependence; globalization, Cartan, integration on parameters |
| Manuscript linear algebra, radial metrics, coefficients and estimates | 4,000–12,000 | Locally finite majorant construction and sharp radial bounds |
| Four-path assembly, exactness and three corollaries | 2,000–5,000 | Cylinder/Stein bridges and isotopy composition |
| Review-driven repairs and interface/audit consumers | 400–2,500 | Uncovered semantic gaps |

The approximate total rounds these overlapping ranges; it is not the sum of independent confidence intervals. A reasonable stage grouping is: statement/review; metric algebra; parameterized differential forms; adapt pinned smooth ODE dependence; properness continuation; radial interpolation; coefficient construction; four-path estimates; exact endpoint assembly; applications; final audit/exposition, with adjacent stages combinable or splittable.

Re-estimate after independent statement review, after locating/constructing the smooth-flow interface, and after the first complete path is formalized. Keep all manuscript assumptions and conclusions regardless of estimate. Final PDFs and GitHub publication occur only after full Lean acceptance, outside this statement mission.

Review update: the ranges remain 9–13 stages, 15,000–50,000 new Lean lines and 4–16 weeks. Discovering existing smooth-dependence results narrows one uncertainty but does not measure the remaining globalization/exactness work sufficiently to justify smaller numerical bounds. The capacity authorization now permits three work slots plus one maintenance slot, but current memory safeguards and actual scheduling still govern use; the stated elapsed range retains its explicit two-work/one-review scenario and is not automatically rescaled. No roadmap graph edits or proof acceptance are claimed.
