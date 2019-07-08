#############################################################################
##
##  PackageInfo.g for the package `recog'
##

SetPackageInfo( rec(

PackageName := "recog",
Subtitle := "A collection of group recognition methods",
Version := "1.3.2dev",
Date := "09/07/2019", # dd/mm/yyyy format
License := "GPL-3.0-or-later",

##  Information about authors and maintainers.
Persons := [
  rec(
    LastName      := "Neunhöffer",
    FirstNames    := "Max",
    IsAuthor      := true,
    IsMaintainer  := false,
    Email         := "max@9hoeffer.de",
  ),
  rec(
    LastName      := "Seress",
    FirstNames    := "Ákos",
    IsAuthor      := true,
    IsMaintainer  := false,
  ),
  rec(
    LastName      := "Ankaralioglu",
    FirstNames    := "Nurullah",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "ankarali@atauni.edu.tr",
  ),
  rec(
    LastName      := "Brooksbank",
    FirstNames    := "Peter",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "pbrooksb@bucknell.edu",
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
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "frank@celler.de",
    Place         := "Aachen",
    Institution   := "Lehrstuhl D für Mathematik, RWTH Aachen",
  ),
  rec(
    LastName      := "Howe",
    FirstNames    := "Stephen",
    IsAuthor      := false,
    IsMaintainer  := false,
    PostalAddress := "Unknown",
  ),
  rec(
    LastName      := "Law",
    FirstNames    := "Maska",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "maska@maths.uwa.edu.au",
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
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "sal@cs.st-andrews.ac.uk",
    WWWHome       := "http://www-groups.dcs.st-and.ac.uk/~sal/",
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
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "malle@mathematik.uni-kl.de",
    WWWHome       := "https://www.mathematik.uni-kl.de/~malle/",
    Place         := "Kaiserslautern",
    Institution   := "Universität Kaiserslautern",
  ),
  rec(
    LastName      := "Niemeyer",
    FirstNames    := "Alice",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "alice.niemeyer@mathb.rwth-aachen.de",
    WWWHome       := "http://www.math.rwth-aachen.de/~Alice.Niemeyer/",
    PostalAddress := Concatenation( [
                       "Lehrstuhl B für Mathematik\n",
                       "RWTH Aachen University\n",
                       "Pontdriesch 10-16\n",
                       "52062 Aachen\n",
                       "Germany" ] ),
    Place         := "Aachen",
    Institution   := "RWTH Aachen University"
  ),
  rec(
    LastName      := "O'Brien",
    FirstNames    := "Eamonn",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "e.obrien@auckland.ac.nz",
    WWWHome       := "https://www.math.auckland.ac.nz/~obrien/",
    Place         := "Auckland",
    Institution   := "University of Auckland",
  ),
  rec(
    LastName      := "Roney-Dougal",
    FirstNames    := "Colva M.",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "colva@mcs.st-and.ac.uk",
    WWWHome       := "http://www-groups.dcs.st-and.ac.uk/~colva",
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
    LastName      := "Horn",
    FirstNames    := "Max",
    IsAuthor      := false,
    IsMaintainer  := true,
    Email         := "max.horn@uni-siegen.de",
    WWWHome       := "https://www.quendi.de/math",
    PostalAddress := Concatenation(
                       "Department Mathematik\n",
                       "Universität Siegen\n",
                       "Walter-Flex-Straße 3\n",
                       "57072 Siegen\n",
                       "Germany" ),
    Place         := "Siegen",
    Institution   := "Universität Siegen"
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

SourceRepository := rec(
    Type := "git",
    URL := Concatenation( "https://github.com/gap-packages/", ~.PackageName ),
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),
PackageWWWHome  := Concatenation( "https://gap-packages.github.io/", ~.PackageName ),
README_URL      := Concatenation( ~.PackageWWWHome, "/README.md" ),
PackageInfoURL  := Concatenation( ~.PackageWWWHome, "/PackageInfo.g" ),
ArchiveURL      := Concatenation( ~.SourceRepository.URL,
                                 "/releases/download/v", ~.Version,
                                 "/", ~.PackageName, "-", ~.Version ),
ArchiveFormats := ".tar.gz .tar.bz2",

##  Here you  must provide a short abstract explaining the package content
##  in HTML format (used on the package overview Web page) and an URL
##  for a Webpage with more detailed information about the package
##  (not more than a few lines, less is ok):
##  Please, use '<span class="pkgname">GAP</span>' and
##  '<span class="pkgname">MyPKG</span>' for specifing package names.
##
AbstractHTML := """
    <p><b>Warning:</b> This package is still under development and
    this version is to be considered a working, but preliminary one.</p>

    <p>This package contains a collection of methods for the
    constructive recognition of groups. It is mostly intended for
    permutation groups, matrix groups and projective groups.</p>
    """,

PackageDoc := rec(
  BookName  := "recog",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "A collection of group recognition methods",
),

Dependencies := rec(
  GAP := ">=4.9",
  NeededOtherPackages := [
    ["Forms", ">= 1.2"],
    ["genss", ">= 1.3"],
    ["Orb", ">= 3.4"],
    ["FactInt", ">= 1.5.2"],
    ["AtlasRep", ">= 1.4.0"],
  ],
  SuggestedOtherPackages := [],
  ExternalConditions := []
),

AvailabilityTest := ReturnTrue,
TestFile := "tst/testall.g",

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
