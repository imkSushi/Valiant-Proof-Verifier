// See https://aka.ms/new-console-template for more information

using ValiantParser;
using ValiantProofVerifier;
using ValiantProver.Modules;
using static ValiantProver.Modules.ImpliesTheorems;

var kernel = new Kernel();
var parser = Theory.Parser;

var printer = new PrettyPrinter.PrettyPrinter(parser, kernel);
//printer.Activate();

TopLevel.Load();

var eq = parser.ParseTerm("p = q = r"); // (p = q) = r i.e. = (= p q) r

var p = kernel.Assume(parser.ParseTerm("p :bool"));
var qImpP = AddImpliesAssumption(p, parser.ParseTerm("q :bool"));
var pImpQImpP = Discharge(parser.ParseTerm("p :bool"), qImpP);

var generalise = ForAllTheorems.Generalise(Theory.Reflexivity(parser.ParseTerm("p")), parser.ParseTerm("p"));
//new PrettyPrinter.DetailedPrinter().Activate();

var exists = ExistsTheorems.Exists(parser.ParseTerm(@"\p :bool . p"), TruthTheorems.Truth);

var exists2 = ExistsTheorems.Exists(parser.ParseTerm(@"\p . ! q . q -> p"), ForAllTheorems.Generalise(AddImpliesAssumption(TruthTheorems.Truth, parser.ParseTerm("q: bool")), parser.ParseTerm("q :bool")));

Console.WriteLine(pImpQImpP);
Console.WriteLine(exists);
Console.WriteLine(exists2);