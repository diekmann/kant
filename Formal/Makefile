pdf:
	echo "running Isabelle locally to build the proof document"
	mkdir -p output
	/home/corny/Downloads/Isabelle2021-1/bin/isabelle build -v -c -D . -o document=pdf

browserinfo:
	# from https://github.com/ekpyron/AOT/blob/develop/.github/workflows/pages.yml
	echo "running hermetic isabelle docker to just build the browser info"
	mkdir -p browseroutput
	chmod 777 browseroutput/
	# image seems not to ship lualatex, so we don't build the document.
	docker run -v "$(PWD):/home/isabelle/build:rw" makarius/isabelle:Isabelle2021-1 build -v -D /home/isabelle/build -o browser_info -P /home/isabelle/build/browseroutput -e
	# then open browseroutput/Unsorted/Kant/index.html

gh-pages: browserinfo
	mkdir -p public
	cp -r browseroutput/Unsorted/Kant ./public/
