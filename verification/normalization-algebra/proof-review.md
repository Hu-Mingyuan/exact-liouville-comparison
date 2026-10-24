# Independent final proof review: normalization algebra

Reviewer: independent `contract_review` agent, 2026-10-24.
Mission: `30bfbe32-1f63-42e8-8279-88f994bffb09`, revision 1.
Verdict: **APPROVED within the finite real matrix normalization algebra scope.**
No blocking mathematical, statement-fidelity, native-interface, or axiom-closure
defect was found in the reviewed snapshot.

This review certifies the explicit normalization's compatibility, recovery,
arbitrary invertible coordinate naturality, and native coordinate consumers.
It does not certify smooth dependence, tangent-bundle assembly, extension of
the cylindrical almost complex structure, or the Liouville comparison theorem.

## Snapshot and independent verification

The original reviewed statement is byte-for-byte unchanged. I read all six
scoped Lean modules, the crosswalk, the proof guide, the verification script,
the inventory and audit programs, the generated endpoint types and axiom
records, and the final receipt. I also compared the relevant declarations to
the native pinned definitions inspected in the pre-proof review.

The following SHA-256 hashes identify the reviewed files; the common Lean
filename prefix is
`ExactLiouvilleComparison/CylindricalCompatibilityNormalizationAlgebra`.

| File suffix or path | SHA-256 |
| --- | --- |
| `Statement.lean` | `9089c2951c21eaa757f5a739bb1f6d976512c659855706638832896f64b26ecc` |
| `.lean` | `f07d9f699e0f4f671e621c961638733582d7fed75beccabf9def5613048bb2ac` |
| `Recovery.lean` | `00f543999f099df620a0f2cb03d5d086c5290cc9f4844367ee501c16ef9bff02` |
| `Naturality.lean` | `a563c9891cf09041060e8e3e9be7317bb1aab7099db652fa53b240bee052ed62` |
| `Native.lean` | `fa3b6bf275babfcacc6e95ad33987c56fce151005efc3d906ea7a962a4c58566` |
| `Checks.lean` | `611fbcf3877937e35bb804ca521764064a0dd3bd245c5f854d1b464b98091a14` |
| `docs/normalization-algebra-crosswalk.md` | `6f92381c2f2c08bfb3bb1dfc357b46bff764f334fad1afa4fb9013a10976d56a` |
| `docs/normalization-algebra-proof.md` | `68b81cdf7981a918d0727366961eb0819053d0041df2e54a8bf184ebafb9af54` |
| `scripts/verify-normalization-algebra.py` | `4a163c31d72a647f3081553ed1d880d6c76ed75783dae680fc3ec2d2a3989309` |
| `verification/normalization-algebra/Inventory.lean` | `c3e51a2bed1eb137002e1dcd2bba21802a2848406b056be608c5a232217686fa` |
| `verification/normalization-algebra/Axioms.lean` | `e32745107950762f3d520257df0db2fb3b84e8e063d7fca358980be3d83b23b9` |
| `verification/normalization-algebra/statement-review.md` | `e5016243e9df135ffbaa3ec64b418324eaa0046a936f64cf6b71f0bbba339eff` |
| `verification/normalization-algebra/receipt.json` | `918629f2ef13c86e119515db0c435ce2580a59eb16b28d737c57013a7671aaa4` |

The final receipt records three successful managed checks with return code
zero and `snapshot_verified=true`, all sharing source fingerprint
`8613d88e061ec91b0dfb672a2bb9d5a5ffa8cc26eb3638fc152a080145df6350`:

1. `lake build ExactLiouvilleComparison.CylindricalCompatibilityNormalizationAlgebraChecks`.
2. `lake env lean verification/normalization-algebra/Inventory.lean`.
3. `lake env lean verification/normalization-algebra/Axioms.lean`.

The recorded toolchain is Lean 4.34.1. Pins are Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` and FsFltz
`1a3d387cfacc746e25aad31e5b27b1803103e7cb`.

I independently recomputed every source and generated-file hash in the receipt:
all matched the current files. I independently checked the name-set equality
between the inventory, axiom table and receipt, inclusion of all 74 named
source declarations, absence of the type-printer omission marker, and the
axiom allowlist for all 123 recorded elaborated declarations. I did not run
a competing Lean build; build execution evidence is the inspected managed
receipt, while the proof and artifact-consistency review is independent.

Generated artifact SHA-256 hashes:

| Artifact | SHA-256 |
| --- | --- |
| `types.txt` | `09f1ad4193397ef7a3a21980ccc100068b4b9314da4a1255f19e2c3480d68bb8` |
| `types.txt.names` | `274a71bbeba3155acb3dde289fcbb2d9faac93d17b2582ce9827d0bef037a333` |
| `axioms.tsv` | `e8eb019bd5edd44de0e9a3b8becb7ccdd395428816fe0801308c5bfeb36ff62b` |

## Mathematical proof findings

**Compatibility is constructed from the original assumptions.**
Positive definiteness of `G` gives the actual CFC root `H`, its positivity,
invertibility and square identity. Skew symmetry and invertibility of `W`
give these properties for `K=-H⁻¹WH⁻¹` and positive definiteness of
`-K²=KᵀK`. `polarRoot_posDef`, `polarRoot_sq` and `polarRoot_commute` establish
the actual `Q=sqrt(-K²)` properties. Commutation is a native CFC consequence
of the polynomial relation, not a new assumption.

`polar_factor_sq` and `polar_factor_metric` are ordinary internal algebra
lemmas taking their identities explicitly. Their uses in the public proof
discharge every such premise using the preceding CFC theorems. There is no
circular certificate in `normalize_compatible`, and `normalize` itself still
takes only `G` and `W`. The proof obtains `J²=-1` and the identity
`WJ=HQH`; positive definiteness of that induced metric gives the strict
inequality, and symmetry plus `J²=-1` gives `JᵀWJ=W`.

**Recovery is stronger than the reviewed target.**
`normalize_recovery` needs only `G.PosDef`, `J²=-1` and `G=WJ`.
It proves `W=-GJ`, `K=HJH⁻¹`, `K²=-1`, hence `Q=1`, then cancels the
metric-root factors. It neither assumes the desired normalization equality
nor presupposes a polar decomposition. `recoveryContract` legitimately
specializes this stronger result to the original reviewed assumptions.

**Naturality covers arbitrary GL changes of both tensors.**
`whitening_orthogonal` first proves `UᵀU=1` for
`U=HP(sqrt(PᵀGP))⁻¹`, from positivity and invertibility. Finite square-matrix
algebra supplies `UUᵀ=1`. Only this orthogonal `U` enters
`sqrt_pull_orthogonal`; the original arbitrary `P` is never treated as a
star equivalence. The positive branch uses native `CFC.sqrt_unique` and
positive-semidefinite congruence. The nonpositive branch correctly transports
failure of nonnegativity through the inverse congruence and uses the CFC
total-function convention. Thus its stronger total statement is also sound.
`skew_pull`, `polarRoot_pull`, and `inv_pull_orthogonal` establish transport
of the literal factors; the final cancellations produce exactly
`normalize(PᵀGP,PᵀWP)=P⁻¹ normalize(G,W) P`. Both inputs transform, and there
is no positivity or orientation restriction on the determinant of `P`.

**All finite ranks are retained.**
The actual endpoint types quantify `n : Nat`, with no `Nonempty`, nontriviality,
evenness, or positive-rank parameter. `zero_rank_admissible` proves that the
zero-rank matrices meet all original hypotheses, including `IsUnit`;
`zero_rank_compatible` applies the general construction to them.
`normalize_rank_zero` records the unique endomorphism. The canonical-plane
consumer proves the correct sign `normalize 1 [[0,1],[-1,0]]=[[0,-1],[1,0]]`
by evaluating the recovery theorem, so the development is not solely vacuous
zero-rank reasoning. Odd positive rank has no invertible skew input, as
expected mathematically.

**The three original targets now have actual proof producers.**
`normalizationContract`, `recoveryContract`, and `naturalityContract` have
exactly the unchanged target proposition types and specialize the substantive
public theorems. The consumer examples invoke those producers, rather than
taking the target propositions as assumptions. The generated endpoint types
confirm the intended quantifiers and premise lists.

## Native bridges and consumer assessment

`form_isAlt` derives native bilinear alternation from skew symmetry;
`form_nondegenerate_iff` proves equivalence with native bilinear nondegeneracy
through determinant/invertibility APIs. `form_pull` proves the actual
congruence evaluation law. `associated_operator_equation` checks the sign in
`g(Av,w)=omega(v,w)` for `A=-G⁻¹W`, and
`skew_eq_whitened_operator` proves its whitening relation.

`endomorphism` and `continuousForm` are native Mathlib continuous linear
maps built from finite-dimensional linear maps. Their evaluation bridges
are literal definitional equalities. `normalize_native` proves the three
pointwise compatibility properties using those maps; the native naturality
and recovery consumers evaluate the actual formula. No disconnected geometry
or arbitrary form operations replace these native objects.

The explicit metric is `form G`. The ambient finite-coordinate topology is
used to package continuity; no estimate silently substitutes its norm for the
metric norm. There are no norm estimates in this mission. These consumers are
an honest coordinate interface for the later native tangent-bundle work;
they do not themselves assert an assembled smooth field or supply a manifold
extension. The proof guide states this boundary correctly.

## Trust, reproduction, and publication boundary

`Axioms.lean` uses Lean's transitive `collectAxioms` on actual environment
constants in the normalization namespace, including generated helpers, and
the matching private-name prefix. The script compares those names against
the full inventory and the named source declarations. All 123 entries have
axiom sets contained in `{propext, Classical.choice, Quot.sound}`. The actual
public endpoints, literal construction definitions, generated helpers and
native consumers are present. The three anonymous examples are direct
applications of the audited contract theorems and also compile with `Checks`.
There is no source admission, custom axiom, trust-altering shortcut, or
unproved certificate premise in the reviewed proof modules.

The reproduction script checks the pinned revisions, unchanged statement and
manuscript hashes, source stability, matching verified fingerprints, complete
type output, declaration coverage and the axiom allowlist. Its inventory
printer was corrected during the verification run to expose proof arguments;
the final receipt and hashes above refer to the corrected successful run.
The proof source did not change during that correction. A future script run
requires the configured managed `horizon-lean-check` environment; this review
does not claim it is a standalone substitute for that environment.

I independently read all six scoped library files and the crosswalk from local
git object `78ee4ed0f31bba9875889335131c5e48cc6c41f1` using `git show` and
compared their bytes with the audited working-tree files. Every comparison
matched. Thus the mathematical source verdict also binds to those seven files
at that exact commit. The final proof guide, script, inventory formatting and
audit artifacts are the later files hashed above, not claimed to be present
in that earlier commit.

This is a source-hash-bound acceptance of the algebra prerequisite. The final
private publication commit containing the complete evidence bundle must be
bound separately by checking these same file bytes; no unverified remote
publication is certified here.
No public GitHub upload, full project acceptance, smooth normalization result,
or complete Liouville theorem follows from this bounded verdict. The only file
written by this final review is this report; the pre-proof review is preserved.
