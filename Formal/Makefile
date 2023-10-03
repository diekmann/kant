browserinfo:
	# from https://github.com/ekpyron/AOT/blob/develop/.github/workflows/pages.yml
	echo "running hermetic isabelle docker to just build the browser info"
	mkdir -p browseroutput
	chmod 777 browseroutput/
	mkdir -p output
	chmod 777 output/
	# use image makarius/isabelle:Isabelle2021-1 and document=false for a lightweight build without proof document.
	docker run -v "$(PWD):/home/isabelle/build:rw" makarius/isabelle:Isabelle2023_X11_Latex build -v -D /home/isabelle/build -o document=pdf -o browser_info -P /home/isabelle/build/browseroutput -e
	# then open browseroutput/Unsorted/Kant/index.html

gh-pages: browserinfo
	mkdir -p public
	cp -r browseroutput/Unsorted/Kant ./public/
	cp output/outline.pdf ./public/

clean:
	rm -rf browseroutput
	rm -rf output
	rm -rf public
