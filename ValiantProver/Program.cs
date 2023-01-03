// See https://aka.ms/new-console-template for more information

using ValiantParser;
using ValiantProofVerifier;
using ValiantProver;

var kernel = new Kernel();
var parser = new PrattParser(kernel);
var utility = new Utility(kernel);
var utilThm = new UtilityTheorems(kernel, utility, parser);

var left = parser.ParseTerm("a:bool = b");
var thm = utilThm.CommutativityEquality(left);
Console.WriteLine(thm);