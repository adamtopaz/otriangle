# Otriangle

Lean formalization project with a
[Verso Blueprint](https://github.com/leanprover/verso-blueprint) for Yuichiro
Hoshi's *Introduction to Mono-anabelian Geometry*.

The source PDF, layout-preserving text extraction, and page images are kept in
`source/`. See `source/README.md` for the extraction commands.

## Build

Update dependencies once after cloning:

```bash
lake update
```

Build the Lean project and render the Blueprint site:

```bash
./scripts/ci-pages.sh
```

The rendered site is written to `_out/site/html-multi/`. For a local preview,
run:

```bash
python3 -m http.server --directory _out/site/html-multi 8000
```

The standard Blueprint query commands remain available, for example
`lake exe vbp query metadata` and `lake exe vbp check`.

## GitHub Pages

The included Pages workflow builds the Blueprint on pull requests and deploys
it from pushes to `main` or `master`. In the repository settings, select
**GitHub Actions** as the Pages source.
