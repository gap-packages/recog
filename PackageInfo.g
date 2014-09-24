#############################################################################
##  
##  PackageInfo.g for the package `recogbase'
##

SetPackageInfo( rec(

PackageName := "recogbase",
Subtitle := "A framework for group recognition",
Version := "1.2.3",
Date := "24/09/2014", # dd/mm/yyyy format

##  Information about authors and maintainers.
Persons := [
  rec( 
    LastName      := "Neunhöffer",
    FirstNames    := "Max",
    IsAuthor      := true,
    IsMaintainer  := false,
    Email         := "max@9hoeffer.de",
    WWWHome       := "http://www-groups.mcs.st-and.ac.uk/~neunhoef",
    PostalAddress := Concatenation( [
                       "Gustav-Freytag-Straße 40\n",
                       "50354 Hürth\n",
                       "Germany" ] ),
    #Place         := "St Andrews",
    #Institution   := "University of St Andrews"
  ),
  rec( 
    LastName      := "Seress",
    FirstNames    := "Ákos",
    IsAuthor      := true,
    IsMaintainer  := false,
  ),
  rec(
    LastName      := "Horn",
    FirstNames    := "Max",
    IsAuthor      := false,
    IsMaintainer  := true,
    Email         := "max.horn@math.uni-giessen.de",
    WWWHome       := "http://www.quendi.de/math",
    PostalAddress := Concatenation(
                       "AG Algebra\n",
                       "Mathematisches Institut\n",
                       "Justus-Liebig-Universität Gießen\n",
                       "Arndtstraße 2\n",
                       "35392 Gießen\n",
                       "Germany" ),
    Place         := "Gießen",
    Institution   := "Justus-Liebig-Universität Gießen"
  ),
],

##  Status information. Currently the following cases are recognized:
##    "accepted"      for successfully refereed packages
##    "deposited"     for packages for which the GAP developers agreed 
##                    to distribute them with the core GAP system
##    "dev"           for development versions of packages 
##    "other"         for all other packages
##
# Status := "accepted",
Status := "deposited",

##  You must provide the next two entries if and only if the status is 
##  "accepted" because is was successfully refereed:
# format: 'name (place)'
# CommunicatedBy := "Mike Atkinson (St. Andrews)",
#CommunicatedBy := "",
# format: mm/yyyy
# AcceptDate := "08/1999",
#AcceptDate := "",

PackageWWWHome := "http://gap-system.github.io/recogbase/",
README_URL     := Concatenation(~.PackageWWWHome, "README"),
PackageInfoURL := Concatenation(~.PackageWWWHome, "PackageInfo.g"),
ArchiveURL     := Concatenation("https://github.com/gap-system/recogbase/",
                                "releases/download/v", ~.Version,
                                "/recogbase-", ~.Version),
ArchiveFormats := ".tar.gz .tar.bz2",

AbstractHTML := "<b>Warning:</b> This package is still under development and \
this version is to be considered a working, but preliminary one. <p/> \
This package provides a framework to implement group \
recognition methods in a generic way. In particular, it is suitable \
for permutation groups, matrix groups, projective groups and blackbox \
groups. The accompanying <span class=\"pkgname\">recog</span> package \
contains the necessary methods for actual recognition.",

PackageDoc := rec(
  BookName  := "recogbase",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "A framework for group recognition",
),

Dependencies := rec(
  GAP := ">=4.4.12",
  NeededOtherPackages := [
    ["GAPDoc", ">= 1.2"],
    ["Forms", ">= 1.2"],
    ["genss", ">= 1.3"],
    ["Orb", ">= 3.4"],
    ["FactInt", ">= 1.5.2"],
    ["AtlasRep", ">= 1.4.0"],
  ],
  SuggestedOtherPackages := [
    ["recog", ">= 1.0"]
  ],
  ExternalConditions := []
),

AvailabilityTest := ReturnTrue,

##  *Optional*, but recommended: path relative to package root to a file which 
##  contains as many tests of the package functionality as sensible.
#TestFile := "tst/testall.g",

##  *Optional*: Here you can list some keyword related to the topic 
##  of the package.
Keywords := ["group recognition", "matrix group recognition",
"permutation group", "black box group", "composition tree", 
"Aschbacher classes", "method selection"],

AutoDoc := rec(
    TitlePage := rec(
        Copyright := Concatenation(
                    "&copyright; 2005-2014 by Max Neunhöffer and Ákos Seress<P/>\n",
                    "\n",
                    "This package may be distributed under the terms and conditions of the\n",
                    "GNU Public License Version 3 or (at your option) any later version.\n"
                ),
    )
),

));


