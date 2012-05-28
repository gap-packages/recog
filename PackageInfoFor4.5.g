#############################################################################
##  
##  PackageInfo.g for the package 'recogbase'
##                                                            Max Neunhoeffer
##                                                                Akos Seress
##  (created from Frank Luebeck's PackageInfo.g template file)
##  
#############################################################################

SetPackageInfo( rec(
PackageName := "recogbase",
Subtitle := "A framework for group recognition",
Version := "1.2",
Date := "28/05/2012",  # not yet released
ArchiveURL := "http://www-groups.mcs.st-and.ac.uk/~neunhoef/Computer/Software/Gap/recogbasefor4.5/recogbase-1.2_for4.5",
ArchiveFormats := ".tar.gz",
Persons := [
  rec( 
    LastName      := "Neunhoeffer",
    FirstNames    := "Max",
    IsAuthor      := true,
    IsMaintainer  := true,
    Email         := "neunhoef@mcs.st-and.ac.uk",
    WWWHome       := "http://www-groups.mcs.st-and.ac.uk/~neunhoef/",
    PostalAddress := Concatenation( [
                       "School of Mathematics and Statistics\n",
                       "Mathematical Institute\n",
                       "North Haugh\n",
                       "St Andrews, Fife KY16 9SS\n",
                       "Scotland, UK" ] ),
    Place         := "St Andrews",
    Institution   := "University of St Andrews"
  ),
  rec( 
    LastName      := "Seress",
    FirstNames    := "Akos",
    IsAuthor      := true,
    IsMaintainer  := true,
    Email         := "akos@math.ohio-state.edu",
    WWWHome       := "http://www.math.ohio-state.edu/~akos/",
    PostalAddress := Concatenation( [
                       "Akos Seress\n",
                       "714 Math Tower\n",
                       "231 W 18th ave\n",
                       "Columbus, OH  43210\n",
                       "USA" ] ),
    Place         := "Columbus",
    Institution   := "Ohio-state University at Columbus"
  )
],

##  Status information. Currently the following cases are recognized:
##    "accepted"      for successfully refereed packages
##    "deposited"     for packages for which the GAP developers agreed 
##                    to distribute them with the core GAP system
##    "dev"           for development versions of packages 
##    "other"         for all other packages
##
Status := "deposited",
##  You must provide the next two entries if and only if the status is 
##  "accepted" because is was successfully refereed:
# format: 'name (place)'
# CommunicatedBy := "Mike Atkinson (St. Andrews)",
#CommunicatedBy := "",
# format: mm/yyyy
# AcceptDate := "08/1999",
#AcceptDate := "",
README_URL := 
  "http://www-groups.mcs.st-and.ac.uk/~neunhoef/Computer/Software/Gap/recogbase/README.recogbase",
PackageInfoURL := 
  "http://www-groups.mcs.st-and.ac.uk/~neunhoef/Computer/Software/Gap/recogbasefor4.5/PackageInfo.g",
AbstractHTML := "<b>Warning:</b> This package is still under development and \
this version is to be considered a working, but preliminary one. <p/> \
This package provides a framework to implement group \
recognition methods in a generic way. In particular, it is suitable \
for permutation groups, matrix groups, projective groups and blackbox \
groups. The accompanying <span class=\"pkgname\">recog</span> package \
contains the necessary methods for actual recognition.",
PackageWWWHome := "http://www-groups.mcs.st-and.ac.uk/~neunhoef/Computer/Software/Gap/recogbase.html",

PackageDoc := rec(
  BookName  := "recogbase",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "recogbase - a framework for group recognition",
  Autoload  := true
),


Dependencies := rec(
  GAP := ">=4.5",
  NeededOtherPackages := [["GAPDoc", ">= 1.5"],
                          ["Forms", ">= 1.2"],["genss", ">= 1.3"],
                          ["Orb", ">= 4.3"], ["FactInt", ">= 1.5.2"],
                          ["AtlasRep", ">= 1.4.0"]],
  SuggestedOtherPackages := [["recog", ">= 1.2"]],
  ExternalConditions := []
),

AvailabilityTest := ReturnTrue,
Autoload := false,
Keywords := ["group recognition", "matrix group recognition",
"permutation group", "black box group", "composition tree", 
"Aschbacher classes", "method selection"]

));


