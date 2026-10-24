# Verify the formalization

From the repository root on Linux or Ubuntu under WSL, with Elan (`lake` on `PATH`), Git, Python 3, and Bash 4 or newer installed:

```sh
bash scripts/fetch-cache.sh
python3 scripts/verify.py
```

The first command obtains dependency sources and compiled caches at the revisions in `lake-manifest.json`. The verifier uses ordinary Lake and performs:

```sh
lake --rehash build ExactLiouvilleComparison
lake env lean verification/FinalConsumer.lean
lake env lean verification/PublicationAxioms.lean
```

Success ends with `PUBLICATION_INTERFACE_VERIFIED`. The [CI workflow](../.github/workflows/lean.yml) runs the same commands.

## What is checked

- All 191 mathematical Lean files match the SHA-256 manifest in [accepted-library.json](accepted-library.json).
- The toolchain is Lean 4.34.1, and every dependency checkout is clean and matches its pinned revision.
- The default library import builds, and [FinalConsumer.lean](FinalConsumer.lean) applies the actual proof terms for the comparison, its applications, cylindrical existence, prescribed extension, and native quotient integration.
- [PublicationAxioms.lean](PublicationAxioms.lean) checks thirteen final theorem roots and all their transitive axiom dependencies. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Missing audit results or additional axioms fail verification; this excludes `sorryAx` and custom axioms in these proofs.
- All 199 compilation inputs retain the same hashes throughout verification.

The theorem statements are defined as propositions; the consumer checks use their completed proof terms. See the [definition guide](../docs/definition-comparison.md) for the mathematical meaning of the hypotheses and the [proof map](../docs/proof-blueprint.md) for their implementations.

## Included verification evidence

The [receipt](publication/receipt.json) and its three logs are the actual ordinary-Lake output of [successful CI run 40055251963](https://github.com/Hu-Mingyuan/exact-liouville-comparison/actions/runs/40055251963):

- [build.log](publication/build.log): library compilation.
- [consumer.log](publication/consumer.log): final theorem consumers.
- [axioms.log](publication/axioms.log): thirteen transitive axiom checks.

The receipt binds every compilation input and each log by SHA-256. All those input hashes match the delivered files. Re-running the verifier replaces these four files with the new result, including its status, toolchain, dependency revisions, source hashes, and axiom sets.

The [document check](document-check.json) records the exact PDF and LaTeX hashes, comparison with the Lean statements and proofs, and visual inspection of all 21 pages. The mathematical definitions and proof terms remain directly available for inspection in the source.
