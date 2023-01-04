// See https://aka.ms/new-console-template for more information

using ValiantParser;
using ValiantProofVerifier;
using ValiantProver.Modules;
using static ValiantProver.Modules.ImpliesTheorems;

var kernel = new Kernel();
var parser = new Parser(kernel);

var printer = new PrettyPrinter.PrettyPrinter(parser, kernel);
printer.Activate();

TopLevel.Load();

var eq = parser.ParseTerm("p = q = r"); // (p = q) = r i.e. = (= p q) r

var p = kernel.Assume(parser.ParseTerm("p :bool"));
var qImpP = AddImpliesAssumption(p, parser.ParseTerm("q :bool"));
var pImpQImpP = Discharge(parser.ParseTerm("p :bool"), qImpP);

Console.WriteLine(pImpQImpP);