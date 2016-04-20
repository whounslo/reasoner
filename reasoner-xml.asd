(defsystem "reasoner-xml"
  :description "Reasoner plus XML, RDF/XML (de)serialization."
  :licence "GPL"
  :author "William Hounslow"
  :depends-on ("reasoner")
  :pathname "src"
  :serial t
  :components ((:file "xmlnames")
               (:file "deserial")
               (:file "serial")
               (:file "datatype")
               (:file "triple")))