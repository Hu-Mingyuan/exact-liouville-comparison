# Exact Liouville comparison

Lean formalization of exact symplectic comparison under weak taming. The central conclusion is a diffeomorphism, smoothly isotopic to the identity, and a smooth real function satisfying

$$F^*\lambda=\beta+dh.$$

The project also constructs cylindrical compatible almost-complex structures on a Liouville completion and extends prescribed compatible contact-distribution data over its compact core.

The combined Lean formalization was accepted at `e994427720c4af8d3915d86609c6fe0538f7c031`. This delivery preserves all 191 mathematical source files exactly. The final library build, public consumers, and thirteen final-root axiom checks passed separately; see the [verification receipt](verification/publication/receipt.json). Both PDFs include the cylindrical construction and prescribed extension and have been rendered and checked against the Lean statements.

## Read the mathematics

- [Target theorem (PDF)](target-theorem.pdf): definitions, hypotheses, norms, quantifiers, and comparison results.
- [Proof blueprint (PDF)](proof-blueprint.pdf): the geometric argument, continuation estimates, exactness, and applications.
- [Theorem guide](docs/target-theorem.md): comparison and the additional cylindrical existence and prescribed-extension statements.
- [Proof-to-code map](docs/proof-blueprint.md): proof steps and their actual Lean implementations.
- [Verification guide](verification/README.md): reproducible checks, allowed axioms, and exact-source evidence.

Editable LaTeX sources are in [docs/tex](docs/tex). The statement PDF has seven pages and the proof PDF has fourteen pages.

## What the comparison theorem assumes

Let $\Omega=d\beta$ and $\omega=d\lambda$ be symplectic forms on the same smooth manifold. The general theorem uses a given smooth $\Omega$-compatible almost-complex structure $J$ and its actual Riemannian metric

$$g(v,w)=\Omega(v,Jw).$$

It assumes a smooth proper function $R\geq1$, constants $c>0$ and $r_*>1$, and the following identities and estimates outside $R\leq r_*$:

$$\beta=-c\,dR\circ J,\qquad c\|dR\|_{g^*}^{\,2}\leq R.$$

The target form satisfies **weak** taming, $\omega(v,Jv)\geq0$ everywhere. There is a smooth positive function $B$ on $[1,\infty)$ with

$$B(r)\geq r,\qquad \int_1^\infty\frac{r}{B(r)^2}\,dr=\infty,$$

and a constant $C>0$ and compact set $K$ such that

$$\|(\omega^\flat)^{-1}\|_{g^*\to g}(x)\leq C B(R(x))\quad(x\notin K).$$

The conclusion includes the exact primitive identity above, hence $F^*\omega=\Omega$, and a smooth identity isotopy with smoothly varying inverses. The compact exception belongs to the growth bound; weak taming is global. The norms are those of the displayed $g$.

This general exact-symplectic theorem assumes neither completeness of either primitive's Liouville field nor a growth bound on $\lambda$ itself. When a result uses a **complete Liouville structure**, its prescribed all-real-time smooth flow is included explicitly in the data.

## Additional results

- **Finite-type comparison:** applies the theorem to an actual Liouville completion with its constructed radial reference.
- **Cylindrical existence:** constructs a smooth compatible $J$ before choosing the target form. Weak taming and the original growth bound on that target remain hypotheses.
- **Prescribed extension:** extends a given smooth $d\alpha$-compatible structure on $\ker\alpha$, preserving it on the entire end, including the seam $r=1$. The output metric is exactly $d\beta(\cdot,J\cdot)$.
- **Stein reference:** constructs the reference from a proper complex embedding represented by native real smooth, immersion, and Cauchy–Riemann data.
- **Common reference:** compares two target forms relative to the same reference, with independent growth witnesses.

## Definitions, statements, and proofs

All declaration names below are relative to `ExactLiouvilleComparison`.

| Role | File | What to look for |
| --- | --- | --- |
| Native objects and norms | [Geometry.lean](ExactLiouvilleComparison/Geometry.lean) | Exact symplectic structures, compatible $J$, metric and norms, exact comparison and isotopy |
| Quantified comparison statements | [Statement.lean](ExactLiouvilleComparison/Statement.lean) | `MainTarget`, `FiniteTypeTarget`, `SteinTarget`, `CommonReferenceTarget` |
| General comparison proof | [MainComparison.lean](ExactLiouvilleComparison/MainComparison.lean) | `MainComparison.mainTarget` |
| Applications and assembly | [ManuscriptComparison.lean](ExactLiouvilleComparison/ManuscriptComparison.lean) | `ManuscriptComparison.manuscriptTarget` and `completeLiouvilleComparisonTarget` |
| Cylindrical contracts | [CylindricalCompatibilityStatement.lean](ExactLiouvilleComparison/CylindricalCompatibilityStatement.lean) | `ExistenceTarget`, `ExtensionTarget`, `ConsumerTarget` |
| Prescribed global extension | [CylindricalCompatibilityExtension.lean](ExactLiouvilleComparison/CylindricalCompatibilityExtension.lean) | `CylindricalCompatibility.extensionTarget` |
| Cylindrical existence and application | [CylindricalCompatibility.lean](ExactLiouvilleComparison/CylindricalCompatibility.lean) | `existenceTarget`, `consumerTarget`, `extension_of_prescribed_kernel` in `CylindricalCompatibility` |
| Native use of the result | [CylindricalCompatibilityFinalChecks.lean](ExactLiouvilleComparison/CylindricalCompatibilityFinalChecks.lean) | Diffeomorphism/isotopy conclusion and dimension-zero/empty-boundary cases |
| Integrated native construction | [NativeIntegration.lean](ExactLiouvilleComparison/NativeIntegration.lean) | `constructedComparison`, `prescribedExtension`: the same native quotient, constructed reference, and comparison |

A target defined as a `Prop` states a goal. The proof declarations listed above inhabit those propositions. The [default library entry point](ExactLiouvilleComparison.lean) imports the proof assemblies.

## Repository layout

```text
ExactLiouvilleComparison.lean       Default proof imports
ExactLiouvilleComparison/           Definitions, statements, and Lean proofs
target-theorem.pdf                 Mathematical statements
proof-blueprint.pdf                Mathematical proof
docs/target-theorem.md             Statement and assumption guide
docs/proof-blueprint.md            Proof-to-code map
docs/tex/                         Editable LaTeX
scripts/                          Verification and document tools
verification/                     Consumers, audits, reviews, and receipts
.github/workflows/                CI configuration
lean-toolchain                    Pinned Lean version
lake-manifest.json                Exact dependency revisions
```

## Reproduce the checks

With Elan, Git, and Python 3 installed, run from the repository root:

```sh
bash scripts/fetch-cache.sh
python3 scripts/verify.py
```

The cache command uses the locked dependency revisions. The verifier builds the library and final consumer, checks that mathematical sources match the accepted snapshot, and rejects unexpected transitive axioms. The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. See the [verification guide](verification/README.md) for the distinction between this final-root check and the broader development audits.

| Dependency | Pinned revision |
| --- | --- |
| Lean | `leanprover/lean4:v4.34.1` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| FsFltz | `1a3d387cfacc746e25aad31e5b27b1803103e7cb` |

## Attribution and scope

The mathematical source is the supplied manuscript *Exact comparison of Liouville forms under weak taming*, identified in [docs/sources.json](docs/sources.json). The exposition follows the actual formalized definitions and proofs.

[Bohan Fang's FsFltz](https://github.com/bohanfang/fs-fltz-minimal) is an unmodified pinned dependency, licensed upstream under Apache-2.0, using native Mathlib geometry. The project follows the separate theorem/proof/verification organization of [cluster-skeleton](https://github.com/Hu-Mingyuan/cluster-skeleton).

See [NOTICES.md](NOTICES.md) for dependency licensing and source attribution.

The delivery is intended as a private source repository. No website deployment is configured.
