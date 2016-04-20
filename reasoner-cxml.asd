(defsystem "reasoner-cxml"
  :description "Reasoner plus XML, RDF/XML (de)serialization plus parser."
  :licence "GPL"
  :author "William Hounslow"
  :depends-on ("reasoner-xml" "cxml")
  :pathname "src"
  :components ((:file "xmlis")))