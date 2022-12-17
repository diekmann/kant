ISABELLE = /home/corny/Downloads/Isabelle2022/bin/isabelle


pdf:
	echo "running Isabelle locally to build the proof document"
	echo "add -c for a clean build"
	cd Formal; $(ISABELLE) build -v -D . -o document=pdf

clean:
	rm -rf Formal/browseroutput/
	rm -rf Formal/output/

