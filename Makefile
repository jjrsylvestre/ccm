SOURCES = \
  $(wildcard src/*.ptx) $(wildcard src/*.tex) \
  $(wildcard src/*/*.ptx) $(wildcard src/*/*.tex) \
  $(wildcard src/*/*/*.ptx) $(wildcard src/*/*/*.tex) \
  $(wildcard src/*/*/*/*.ptx) $(wildcard src/*/*/*/*.tex)
# I think that's as deep as things go...

BRANDLOGO=AUG-Colour.png
ROOTDOCNAME=book
SERVEPORT=8082
BUILDDIR=${XDG_RUNTIME_DIR}/pretext/ccm
PRETEXT=/opt/pretext/pretext/pretext
ROOT_XMLID=book-calculus-concepts-modelling
#PRETEXT=./pretext/pretext/pretext

.PHONY: ptx validate-xml \
  html html-images html-image-pdfs html-fonts html-all html-serve \
  clean ptx-clean html-clean html-images-clean \
  help list

list: help
help:
	@echo "== TARGETS ==============="
	@echo "> validate-xml       : Check for XML syntax/format errors. (Does not validate against PTX schema.)"
	@echo "> html-all           : Perform all steps necessary to create HTML version of the activity set."
	@echo "> html               : Output (only) HTML files containing all worksheets."
	@echo "> html-images        : Create SVG image files to accompany the html output."
	@echo "> html-image-pdfs    : Create PDF image files for the html output."
	@echo "                       (to feed to scripts/image-widths.sh)"
	@echo "> html-fonts         : Copy STIX2Text fonts into the HTML build directory."
	@echo "> html-serve         : Fire up a simple Python web server to locally host the HTML output."
	@echo "> latex              : Output (only) LaTeX file containing all worksheets."
	@echo "> ptx                : Only preprocess source to create a single XML file in PTX format."
	@echo "> clean              : Remove all output files."
	@echo "> ptx-clean          : Remove preprocessed PTX output."
	@echo "> html-clean         : Remove all HTML output."
	@echo "> html-images-clean  : Remove all accomanying SVG files."
	@echo "== PARAMETERS ============"
	@echo "> BUILDDIR   : Root directory for all output files. [Default: $(BUILDDIR)]"
	@echo "> BRANDLOGO  : Filename of institutional logo. Needs to exist in images/. [Default: $(BRANDLOGO)]"
	@echo "> PRETEXT : Path to pretext compilation script [Default: $(PRETEXT)]"
	@echo "> SERVEPORT  : Local port on which to serve HTML output when using the html-serve target. [Default: $(SERVEPORT)]"


html-all: html html-images html-fonts

clean: ptx-clean html-clean html-images-clean

ptx-clean:
	@-rm -f ${BUILDDIR}/ptx/.sentinal
	@-rm -f ${BUILDDIR}/ptx/${ROOTDOCNAME}.ptx
html-clean:
	@-rm -f ${BUILDDIR}/html/.sentinal
	@-rm -f ${BUILDDIR}/html/*.html
	@-rm -f ${BUILDDIR}/html/knowl/*.html
	@-rm -f ${BUILDDIR}/html/knowl/index/*.html
	@-rm -f ${BUILDDIR}/html/knowl/xref/*.html
	@-rm -f ${BUILDDIR}/html/lunr-pretext-search-index.js
	@-rm -f ${BUILDDIR}/html/ccm.css
html-images-clean:
	@-rm -f ${BUILDDIR}/html/images/.sentinal
	@-rm -f ${BUILDDIR}/html/images/*.svg
	@-rm -f ${BUILDDIR}/image-pdfs/*.pdf

ptx: ${BUILDDIR}/ptx/${ROOTDOCNAME}.ptx preprocess.xsl
html: ${BUILDDIR}/html/.sentinal html-out.xml
html-images: ${BUILDDIR}/html/images/.sentinal
html-image-pdfs: ${BUILDDIR}/image-pdfs/.sentinal
latex: ${BUILDDIR}/latex/${ROOTDOCNAME}.tex

${BUILDDIR}/ptx/${ROOTDOCNAME}.ptx: $(SOURCES) | validate-xml
	@echo "Consolidating document into one PTX file, output will be placed in build/ptx..."
	@mkdir -p ${BUILDDIR}/ptx
	@ln -sf --no-dereference ${BUILDDIR} build
	@echo "...calling xsltproc..."
	@xsltproc \
	  --xinclude \
	  --output ${BUILDDIR}/ptx/${ROOTDOCNAME}.ptx \
	  ./preprocess.xsl src/${ROOTDOCNAME}.ptx
	@touch ${BUILDDIR}/ptx/.sentinal
	@echo "...DONE"

${BUILDDIR}/html/.sentinal: ${BUILDDIR}/ptx/${ROOTDOCNAME}.ptx
	@echo "Converting PTX to HTML..."
	@-rm -f ${BUILDDIR}/html/.sentinal
	@mkdir -p ${BUILDDIR}/html/knowl
	@ln -sf --no-dereference ${BUILDDIR} build
	@echo "...calling pretext to compile PreTeXt document"
	@$(PRETEXT) \
	  --verbose \
	  --component all \
	  --format html \
	  --publisher html-out.xml \
	  --parameters \
	    html.css.extra ccm.css \
	  --directory ${BUILDDIR}/html \
	  ${BUILDDIR}/ptx/${ROOTDOCNAME}.ptx
	@sed -i \
	  -e 's/scale: 0\.[0-9]*,//' \
	  -e 's/mtextInheritFont: true/mtextInheritFont: true, matchFontHeight: true/' \
	  ${BUILDDIR}/html/*.html
	@echo "...copying css style customizations"
	@cp css/ccm.css ${BUILDDIR}/html/
	@touch ${BUILDDIR}/html/.sentinal
	@echo "...DONE"
	@echo "Now call:"
	@echo "   make html-images  (to build SVG images)"
	@echo "   make html-serve   (to serve the output locally for previewing)"

${BUILDDIR}/html/images/.sentinal: ${BUILDDIR}/ptx/${ROOTDOCNAME}.ptx
	@echo "Generating SVG files for HTML output..."
	@mkdir -p ${BUILDDIR}/html/images
	@ln -sf --no-dereference ${BUILDDIR} build
	@-rm -f ${BUILDDIR}/html/images/.sentinal
	@echo "...calling pretext to generate images"
	@$(PRETEXT) \
	  --verbose \
	  --component latex-image \
	  --format svg \
	  --restrict ${ROOT_XMLID} \
	  --directory ${BUILDDIR}/html/images \
	  ${BUILDDIR}/ptx/${ROOTDOCNAME}.ptx
	@echo "...copying institution logo"
	@-cp images/${BRANDLOGO} ${BUILDDIR}/html/images
	@touch ${BUILDDIR}/html/images/.sentinal
	@echo "...DONE"

${BUILDDIR}/image-pdfs/.sentinal: ${BUILDDIR}/ptx/${ROOTDOCNAME}.ptx
	@echo "Generating PDF files for HTML output images..."
	@mkdir -p ${BUILDDIR}/image-pdfs
	@ln -sf --no-dereference ${BUILDDIR} build
	@-rm -f ${BUILDDIR}/image-pdfs/.sentinal
	@echo "...calling pretext to generate images"
	@$(PRETEXT) \
	  --verbose \
	  --component latex-image \
	  --format pdf \
	  --restrict ${ROOT_XMLID} \
	  --directory ${BUILDDIR}/image-pdfs \
	  ${BUILDDIR}/ptx/${ROOTDOCNAME}.ptx
	@touch ${BUILDDIR}/image-pdfs/.sentinal
	@echo "...DONE"
	@echo "Now call:"
	@echo "   ./scripts/image-widths.sh build/image-pdfs/*.pdf   (to calculate width attributes for ptx source)"

html-fonts: \
  ${BUILDDIR}/html/fonts/STIXTwoText-Bold.woff2 \
  ${BUILDDIR}/html/fonts/STIXTwoText-BoldItalic.woff2 \
  ${BUILDDIR}/html/fonts/STIXTwoText-Italic.woff2 \
  ${BUILDDIR}/html/fonts/STIXTwoText-Medium.woff2 \
  ${BUILDDIR}/html/fonts/STIXTwoText-MediumItalic.woff2 \
  ${BUILDDIR}/html/fonts/STIXTwoText-Regular.woff2 \
  ${BUILDDIR}/html/fonts/STIXTwoText-SemiBold.woff2 \
  ${BUILDDIR}/html/fonts/STIXTwoText-SemiBoldItalic.woff2
#   ${BUILDDIR}/html/fonts/STIXTwoMath-Regular.woff2

${BUILDDIR}/html/fonts/%.woff2: stixfonts/fonts/static_otf_woff2/%.woff2
	@mkdir -p ${BUILDDIR}/html/fonts
	-cp $< ${BUILDDIR}/html/fonts/

${BUILDDIR}/latex/${ROOTDOCNAME}.tex: ${BUILDDIR}/ptx/${ROOTDOCNAME}.ptx
	@echo "Converting PTX to LATEX for version: ${*}..."
	@mkdir -p ${BUILDDIR}/latex
	@ln -sf --no-dereference ${BUILDDIR} build
	@echo "...calling pretext to compile PreTeXt document"
	@${PRETEXT} \
	  --XSL style-latex.xsl \
	  --component all \
	  --format latex \
	  --publisher latex-out.xml \
	  --directory ${BUILDDIR}/latex \
	  ${BUILDDIR}/ptx/${ROOTDOCNAME}.ptx
	@echo "...applying adjustments from ./make.d/latex/"
	@./make.d/latex/fourier-font.sh ${BUILDDIR}/latex/${ROOTDOCNAME}.tex
#	@./make.d/latex/page-breaks.sh ${BUILDDIR}/latex/${ROOTDOCNAME}.tex
	@echo "...DONE"

html-serve:
	@./scripts/serve.py ${BUILDDIR}/html $(SERVEPORT) 2>/dev/null

validate-xml: $(SOURCES)
	@echo "Validating xml..."
	@xmllint --xinclude src/${ROOTDOCNAME}.ptx | xmllint --noout -
	@echo "...DONE"
