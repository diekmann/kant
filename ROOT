session Slides in slides = HOL +
  (* Based on HOL instead of session Kant to make it easier to edit both simultaneously. *)
  (* pass document=pdf via iabelle build command line *)
  (* document_build = "pdflatex" instead of lualatex, since lualated does not render umlauts *)
  options [document_output = "output", document_build = "pdflatex", document_echo, document_logo = "_", document_variants = "slides=/proof,/ML"]
  directories
    "../Formal"
  theories [document = false]
    "../Formal/ExecutableHelper"
    "../Formal/Percentage"
    "../Formal/BeispielPerson"
    "../Formal/Gesetz"
    "../Formal/Handlung"
    "../Formal/Kant"
    "../Formal/Steuern"
  theories [show_question_marks = false]
    Slides
  document_files
    "root.tex"
