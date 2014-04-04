#############################################################################
##  
##  PackageInfo.g for the package `recog'                     
##                                                            Max Neunhoeffer
##                                                                Akos Seress
##                                                                     et al.
##  

##  With a new release of the package at least the entries .Version, .Date and
##  .ArchiveURL must be updated.

RecogsFunnyNameFormatterFunction := function(st)
  if Length(st) = 0 then 
      return st;
  else
      return Concatenation(" (",st,")");
  fi;
end;
RecogsFunnyWWWURLFunction := function(re)
  if IsBound(re.WWWHome) then
      return re.WWWHome;
  else
      return "";
  fi;
end;

SetPackageInfo( rec(

PackageName := "recog",
Subtitle := "A collection of group recognition methods",
Version := "1.2.2",
Date := "04/04/2014", # dd/mm/yyyy format

##  Information about authors and maintainers.
Persons := [
  rec( 
    LastName      := "Neunhoeffer",
    FirstNames    := "Max",
    IsAuthor      := true,
    IsMaintainer  := false,
    Email         := "neunhoef@mcs.st-and.ac.uk",
    WWWHome       := "http://www-groups.mcs.st-and.ac.uk/~neunhoef",
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
    IsMaintainer  := false,
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
  ),
  rec( 
    LastName      := "Ankaralioglu",
    FirstNames    := "Nurullah",
    IsAuthor      := true,
    IsMaintainer  := false,
    Email         := "ankarali@atauni.edu.tr",
  ),
  rec( 
    LastName      := "Brooksbank",
    FirstNames    := "Peter",
    IsAuthor      := true,
    IsMaintainer  := false,
    Email         := "pbrooksb@bucknell.edu",
    WWWHome       := "http://www.facstaff.bucknell.edu/pbrooksb/",
    PostalAddress := Concatenation( [
                       "Peter A. Brooksbank\n",
                       "Mathematics Department\n",
                       "Bucknell University\n",
                       "Lewisburg, PA 17837\n",
                       "USA" ] ),
    Place         := "Lewisburg",
    Institution   := "Bucknell University"
  ),
  rec(
    LastName      := "Celler",
    FirstNames    := "Frank",
    IsAuthor      := true,
    IsMaintainer  := false,
    Email         := "frank@celler.de",
    WWWHome       := "http://www.celler.de/",
    Place         := "Aachen",
    Institution   := "Lehrstuhl D fuer Mathematik, RWTH Aachen",
  ),
  rec(
    LastName      := "Howe",
    FirstNames    := "Stephen",
    IsAuthor      := true,
    IsMaintainer  := false,
    PostalAddress := "Unknown",
  ),
  rec( 
    LastName      := "Law",
    FirstNames    := "Maska",
    IsAuthor      := true,
    IsMaintainer  := false,
    Email         := "maska@maths.uwa.edu.au",
    #WWWHome       := "http://www.maths.uwa.edu.au/~maska/",
    PostalAddress := Concatenation( [
                       "Maska Law\n",
                       "University of Western Australia\n",
                       "School of Mathematics and Statistics\n",
                       "35 Stirling Highway\n",
                       "Crawley 6009\n",
                       "Western Australia" ] ),
    Place         := "Perth",
    Institution   := "University of Western Australia"
  ),
  rec( 
    LastName      := "Linton",
    FirstNames    := "Steve",
    IsAuthor      := true,
    IsMaintainer  := false,
    Email         := "sal@cs.st-andrews.ac.uk",
    WWWHome       := "http://www-circa.mcs.st-and.ac.uk/~sal/",
    PostalAddress := Concatenation( [
                       "School of Computer Science\n",
                       "Jack Cole Building\n",
                       "North Haugh\n",
                       "St Andrews, Fife KY16 9SX\n",
                       "Scotland, UK" ] ),
    Place         := "St Andrews",
    Institution   := "University of St Andrews"
  ),
  rec(
    LastName      := "Malle",
    FirstNames    := "Gunter",
    IsAuthor      := true,
    IsMaintainer  := false,
    Email         := "malle@mathematik.uni-kl.de",
    WWWHome       := "http://www.mathematik.uni-kl.de/~malle/",
    Place         := "Kaiserslautern",
    Institution   := "Universitaet Kaiserslautern",
  ),
  rec( 
    LastName      := "Niemeyer",
    FirstNames    := "Alice",
    IsAuthor      := true,
    IsMaintainer  := false,
    Email         := "alice@maths.uwa.edu.au",
    WWWHome       := "http://www.maths.uwa.edu.au/~alice/",
    PostalAddress := Concatenation( [
                       "Alice C. Niemeyer\n",
                       "University of Western Australia\n",
                       "School of Mathematics and Statistics\n",
                       "35 Stirling Highway\n",
                       "Crawley 6009\n",
                       "Western Australia" ] ),
    Place         := "Perth",
    Institution   := "University of Western Australia"
  ),
  rec(
    LastName      := "O'Brien",
    FirstNames    := "Eamonn",
    IsAuthor      := true,
    IsMaintainer  := false,
    Email         := "obrien@math.auckland.ac.nz",
    WWWHome       := "http://www.math.auckland.ac.nz/~obrien/",
    Place         := "Auckland",
    Institution   := "University of Auckland",
  ),
  rec(
    LastName      := "Roney-Dougal",
    FirstNames    := "Colva M.",
    IsAuthor      := true,
    IsMaintainer  := false,
    Email         := "colva@mcs.st-and.ac.uk",
    WWWHome       := "http://www-groups.mcs.st-and.ac.uk/~colva",
    PostalAddress := Concatenation( [
                       "School of Mathematics and Statistics\n",
                       "Mathematical Institute\n",
                       "North Haugh\n",
                       "St Andrews, Fife KY16 9SS\n",
                       "Scotland, UK" ] ),
    Place         := "St Andrews",
    Institution   := "University of St Andrews"
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

PackageWWWHome := "http://neunhoef.github.io/recog/",
README_URL     := Concatenation(~.PackageWWWHome, "README"),
PackageInfoURL := Concatenation(~.PackageWWWHome, "PackageInfo.g"),
ArchiveURL     := Concatenation("https://github.com/neunhoef/recog/",
                                "releases/download/v", ~.Version,
                                "/recog-", ~.Version),
ArchiveFormats := ".tar.gz .tar.bz2",

##  Here you  must provide a short abstract explaining the package content 
##  in HTML format (used on the package overview Web page) and an URL 
##  for a Webpage with more detailed information about the package
##  (not more than a few lines, less is ok):
##  Please, use '<span class="pkgname">GAP</span>' and
##  '<span class="pkgname">MyPKG</span>' for specifing package names.
##  
AbstractHTML := 
  "<b>Warning:</b> This package is still under development and \
   this version is to be considered a working, but preliminary one. <p/> \
   This packages contains a collection of methods for the \
   constructive recognition of groups. It is mostly intended for \
   permutation groups, matrix groups and projective groups.",

PackageDoc := rec(
  BookName  := "recog",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "A collection of group recognition methods",
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
    ["recogbase", ">= 1.0"],
  ],
  SuggestedOtherPackages := [],
  ExternalConditions := []
),

##  The LoadPackage mechanism can produce a default banner from the info
##  in this file. If you are not happy with it, you can provide a string
##  here that is used as a banner. GAP decides when the banner is shown and
##  when it is not shown. *optional* (note the ~-syntax in this example)
BannerString := Concatenation(
  "----------------------------------------------------------------------",
  "-------\n",
  "Loading  recog ", ~.Version, " - methods for constructive recognition\n\n",
  "by ", ~.Persons[1].FirstNames, " ", ~.Persons[1].LastName,
        " (", ~.Persons[1].WWWHome, ") and\n",
  "   ", ~.Persons[2].FirstNames, " ", ~.Persons[2].LastName,
        " (", ~.Persons[2].WWWHome, ")\n",
  "with contributed code by:\n",
  Concatenation(Concatenation(List(~.Persons{[3..Length(~.Persons)-1]},
       p->["     ",p.FirstNames," ",p.LastName,
       RecogsFunnyNameFormatterFunction(
         RecogsFunnyWWWURLFunction(p)),",\n"]))),
  " and ",~.Persons[Length(~.Persons)].FirstNames," ",
  ~.Persons[Length(~.Persons)].LastName,
  RecogsFunnyNameFormatterFunction(
    RecogsFunnyWWWURLFunction(~.Persons[Length(~.Persons)])),".\n",
  "-----------------------------------------------------------------------",
  "------\n"
),

AvailabilityTest := ReturnTrue,

##  *Optional*, but recommended: path relative to package root to a file which 
##  contains as many tests of the package functionality as sensible.
#TestFile := "tst/TestAll.g",
## Currently, due to the Monte-Carlo nature of our algorithms and other
## technical details, this is not a proper GAP test file.

##  *Optional*: Here you can list some keyword related to the topic 
##  of the package.
Keywords := ["matrix group recognition", "group recognition", "methods"]

));
Unbind(RecogsFunnyNameFormatterFunction);
Unbind(RecogsFunnyWWWURLFunction);

