ISABELLE = /home/corny/Downloads/Isabelle2021-1/bin/isabelle


pdf:
	echo "running Isabelle locally to build the proof document"
	mkdir -p output
	echo "add -c for a clean build"
	cd Formal; $(ISABELLE) build -v -D . -c -o document=pdf

slidesonly:
	echo "only slides"
	mkdir -p slides/output
	$(ISABELLE) build -v -D . -o document=pdf Slides

clean:
	rm -rf Formal/browseroutput/
	rm -rf Formal/output/
	rm -rf slides/output/

