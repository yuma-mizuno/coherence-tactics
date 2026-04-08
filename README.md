# Coherence Tactics for Monoidal Categories and Bicategories in Lean

This is a manual for mathlib's coherence tactics: `monoidal` for monoidal categories and `bicategory` for bicategories.

## Setup

```bash
lake exe cache get
lake build
```

## Generate docs

```bash
lake exe coherence-tactics-docs
```

The generated HTML is written to `_out/html-multi/`.

## GitHub Pages

This repository includes a GitHub Pages workflow at
[`./.github/workflows/deploy_github_pages.yml`](./.github/workflows/deploy_github_pages.yml).
On pushes to `main` or `master`, it builds the manual and publishes `_out/html-multi/` as the
Pages artifact.

## Citation

```bibtex
@misc{CoherenceTacticsLean,
  author = {Yuma Mizuno},
  title = {Coherence Tactics for Monoidal Categories and Bicategories in Lean},
  year = {2026},
}
```
