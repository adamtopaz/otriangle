# Source material

- `hoshi.pdf`: Yuichiro Hoshi, *Introduction to Mono-anabelian Geometry*.
- `hoshi.txt`: layout-preserving text extracted from the PDF.
- `hoshi-page-NN.png`: 150 DPI raster image of page `NN`.

The derived files can be regenerated from the source PDF with Poppler:

```bash
pdftotext -layout source/hoshi.pdf source/hoshi.txt
pdftoppm -png -r 150 source/hoshi.pdf source/hoshi-page
```
