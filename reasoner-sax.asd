(defsystem "reasoner-sax"
  :description "Reasoner plus XML, RDF/XML (de)serialization (Allegro SAX parser)."
  :licence "GPL"
  :author "William Hounslow"
  :depends-on ("reasoner-xml")
  :pathname "src"
  :components ((:file "xmlis")))