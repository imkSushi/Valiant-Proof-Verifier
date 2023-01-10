using System.Diagnostics.CodeAnalysis;
using ValiantBasics;
using ValiantParser.Inference;
using ValiantProofVerifier;

namespace ValiantParser;

public sealed class Parser
{
    
    private Lexer _lexer = new();
    private TypeInferer _typeInferer = new();
    private List<Token> _tokens = new();
    private Kernel _kernel;
    private int _index;
    private HashSet<string> _suspendedKeywords = new();


    public Term ParseTerm(string term)
    {
        return TryParseTerm(term).Deconstruct(out var result, out var error) ? result : throw new ParsingException(error);
    }
    
    public Result<Term> TryParseTerm(string term)
    {
        _index = 0;
        if (!Lex(term, out var error))
            return error;
        
        if (!ParsePrecedence(InfixPrecedence.NotNone).Deconstruct(out var result, out error))
            return error;
        
        if (!_typeInferer.InferType(result).Deconstruct(out var typedOutput, out error))
            return error;
        
        if (!typedOutput.TryMakeTerm(_kernel).Deconstruct(out var output, out error))
            return error;
        
        return output;
    }

    private bool Lex(string term, [MaybeNullWhen(true)] out string error)
    {
        _tokens = _lexer.Lex(term).ToList();
        return CheckTokensForErrors(out error);
    }

    private bool CheckTokensForErrors([MaybeNullWhen(true)] out string error)
    {
        error = null;
        var errors = _tokens.Where(token => token is ErrorToken).Cast<ErrorToken>().Select(token => token.Message).ToList();
        if (!errors.Any()) 
            return true;
        
        error = string.Join("\n", errors);
        return false;
    }

    public Parser(Kernel kernel)
    {
        _kernel = kernel;
    }
    
    private Dictionary<string,Func<Result<InfTerm>>> _customPrefixRules = new();

    private Func<Result<InfTerm>>? TryGetPrefixRule(Token token)
    {
        return token switch
        {
            IdentifierToken { Value: var name } => () => Identifier(name),
            KeywordToken("(")         => Grouping,
            KeywordToken("\\")        => Lambda,
            KeywordToken("$")         => Escape,
            KeywordToken(var keyword) => !_suspendedKeywords.Contains(keyword) && _customPrefixRules.TryGetValue(keyword, out var output) ? output : null,
            _                         => null
        };
    }

    private Dictionary<string, (Func<InfTerm, Result<InfTerm>> rule, InfixPrecedence precedence)> _customInfixRules = new();

    private (Func<InfTerm, Result<InfTerm>> rule, InfixPrecedence precedence)? TryGetInfixRule(Token token)
    {
        return token switch
        {
            IdentifierToken { Value: var name } => (left => Combination(left, name), InfixPrecedence.Combination),
            KeywordToken("$")                   => (Escape, InfixPrecedence.Combination),
            KeywordToken("(")                   => (Grouping, InfixPrecedence.Combination),
            KeywordToken {Value: var keyword} when _suspendedKeywords.Contains(keyword) => null,
            KeywordToken {Value: var keyword} when _customInfixRules.TryGetValue(keyword, out var output) =>  output,
            _                                   => null
        };
    }
    
    public bool TryRegisterInfixRule(string keyword, string constant, int precedence, bool leftAssociative)
    {
        if (!_kernel.TryGetConstantType(constant, out var constantType))
            return false;

        var fakeType = FakeType.FromType(constantType);
        if (fakeType is not TyApp { Name: "fun", Args: [_, TyApp { Name: "fun" }] })
            return false;

        if (_customInfixRules.ContainsKey(keyword))
            return false;
        
        if (!_lexer.TryAddKeyword(keyword))
            return false;

        var term = new InfConst(constant, InfType.FromType(constantType, false));
        
        _customInfixRules[keyword] = (delegate(InfTerm left)
        {
            _index++;
            if (!Combination(term, left).Deconstruct(out var leftCombination, out var error))
                return error;

            if (!ParsePrecedence((InfixPrecedence)(leftAssociative ? precedence + 1 : precedence)).Deconstruct(out var rightTerm, out error))
                return error;

            return Combination(leftCombination, rightTerm);
        }, (InfixPrecedence)precedence);

        _customPrefixRules[keyword] = () => Identifier(keyword);
        return true;
    }

    public bool TryRegisterPrefixRule(string keyword, string constant, int arity)
    {
        if (arity < 0)
            return false;
        
        if (!_kernel.TryGetConstantType(constant, out var constantType))
            return false;
        
        if (_customPrefixRules.ContainsKey(keyword))
            return false;
        
        if (!_lexer.TryAddKeyword(keyword))
            return false;
        
        _customPrefixRules[keyword] = delegate
        {
            if (!Identifier(constant).Deconstruct(out var app, out var error))
                return error;
            
            for (var i = 0; i < arity; i++)
            {
                var startIndex = _index;

                if (!ParsePrecedence(InfixPrecedence.Combination).IsSuccess(out var arg))
                {
                    _index = startIndex;

                    return app;
                }

                if (!Combination(app, arg).IsSuccess(out var newApp))
                {
                    _index = startIndex;

                    return app;
                }
                
                app = newApp;
            }
            
            return app;
        };

        _customInfixRules[keyword] = (delegate(InfTerm left)
        {
            if (!Identifier(constant).Deconstruct(out var app, out var error))
                return error;

            if (!ParsePrecedence(InfixPrecedence.Combination).Deconstruct(out var right, out error))
                return error;
            
            if (!Combination(app, right).Deconstruct(out var rightCombination, out error))
                return error;
            
            return Combination(left, rightCombination);
        }, InfixPrecedence.Combination);
        return true;
    }

    public bool TryRegisterLambdaRule(string keyword, string constant)
    {
        if (!_kernel.TryGetConstantType(constant, out var constantType))
            return false;

        var fakeType = FakeType.FromType(constantType);
        if (fakeType is not TyApp { Name: "fun", Args: [_, _] })
            return false;

        if (_customPrefixRules.ContainsKey(keyword))
            return false;
        
        if (!_lexer.TryAddKeyword(keyword))
            return false;

        var term = new InfConst(constant, InfType.FromType(constantType, false));
        
        _customPrefixRules[keyword] = () => Lambda(term);
        return true;
    }
    
    public void DeregisterInfixRule(string keyword)
    {
        _customInfixRules.Remove(keyword);
        _lexer.RemoveKeyword(keyword);
    }
    
    public void SuspendInfixRule(string keyword)
    {
        _suspendedKeywords.Add(keyword);
        _lexer.RemoveKeyword(keyword);
    }
    
    public void ResumeInfixRule(string keyword)
    {
        _suspendedKeywords.Remove(keyword);
        _lexer.AddKeyword(keyword);
    }

    public Result<int> TryGetInfixPrecedence(string keyword)
    {
        if (!_customInfixRules.TryGetValue(keyword, out var output))
            return $"Keyword {keyword} is not registered as an infix rule";
        
        return (int) output.precedence;
    }

    private Result<InfTerm> Grouping(InfTerm arg)
    {
        if (!Grouping().Deconstruct(out var result, out var error))
            return error;

        return new InfComb(arg, result);
    }

    private Func<Result<Type>>? TryGetTypeRule(Token token)
    {
        return token switch
        {
            KeywordToken(":") => TypeApplication,
            KeywordToken("'") => TypeVariable,
            _                                  => null
        };
    }

    private Result<InfTerm> ParsePrecedence(InfixPrecedence precedence)
    {
        if (!GetPrefixRule().Deconstruct(out var prefixRule, out var error))
            return error;

        if (!prefixRule().Deconstruct(out var output, out error))
            return error;

        while (precedence <= GetInfixPrecedence())
        {
            var (infixFunction, _) = TryGetInfixRule(Current())!.Value;
            
            if (!infixFunction(output).Deconstruct(out output, out error))
                return error;
        }
        
        return output;
    }

    private Result<Func<Result<InfTerm>>> GetPrefixRule()
    {
        return TryGetPrefixRule(Current()).Deconstruct(out var output)
            ? output
            : $"Unexpected token: {_tokens[_index]}";
    }

    private InfixPrecedence GetInfixPrecedence()
    {
        return TryGetInfixRule(Current()).Deconstruct(out var output)
            ? output!.Value.precedence
            : (InfixPrecedence.None);
    }

    private Token Current()
    {
        return _tokens[_index];
    }

    private Result<InfTerm> Grouping()
    {
        _index++;
        if (!Expression().Deconstruct(out var result, out var error))
            return error;
        
        if (!MatchKeyword(")"))
            return $"Expected ')', got {Current()}";
        
        return result;
    }
    
    private bool MatchKeyword(string keyword)
    {
        if (Current() is not KeywordToken(var value) || value != keyword) 
            return false;
        
        _index++;
        return true;
    }

    private Result<InfTerm> Expression()
    {
        return ParsePrecedence(InfixPrecedence.NotNone);
    }

    private Result<InfTerm> Identifier(string name)
    {
        _index++;
        return _kernel.ConstantExists(name) ? Constant(name) : Variable(name);
    }

    private Result<InfTerm> Constant(string name)
    {
        if (Current() is not KeywordToken { Value: ":" or "'" })
            return new InfConst(name, InfType.FromType(_kernel.GetConstantType(name), false));
        
        if (!Type().Deconstruct(out var type, out var error))
            return error;
            
        return new InfConst(name, InfType.FromType(type, true));
    }

    private Result<InfTerm> Variable(string name)
    {
        if (Current() is not KeywordToken { Value: ":" or "'" })
            return new InfVar(name, InfType.FromType(Kernel.Aty, false));

        if (!Type().Deconstruct(out var type, out var error))
            return error;
        
        return new InfVar(name, InfType.FromType(type, true));
    }
    
    private Result<Func<Result<Type>>> GetTypeRule()
    {
        return TryGetTypeRule(Current()).Deconstruct(out var output)
            ? output
            : $"Invalid type prefix: {Current()}";
    }

    private Result<Type> Type()
    {
        if (!GetTypeRule().Deconstruct(out var typeRule, out var error))
            return error;

        _index++;
        return typeRule();
    }

    private Result<Type> TypeApplication()
    {
        var name = Current().Value;
        if (!_kernel.TryGetArity(name, out var arity))
            return $"Undefined type application: {name}";
        
        _index++;
        var args = new Type[arity];
        for (var i = 0; i < arity; i++)
        {
            if (!Type().Deconstruct(out var arg, out var error))
                return error;
            
            args[i] = arg;
        }
        
        return _kernel.MakeType(name, args);
    }

    private Result<Type> TypeVariable()
    {
        var name = Current().Value;
        _index++;
        return _kernel.MakeType(name);
    }

    private Result<InfTerm> Lambda()
    {
        return Lambda(null);
    }

    private Result<InfTerm> Lambda(InfTerm? modifier)
    {
        var variables = new List<InfVar>();
        string? error;
        _index++;
        
        var startIndex = _index;
        
        while (Current() is IdentifierToken { Value: var name })
        {
            _index++;
            if (!Variable(name).Deconstruct(out var variable, out error))
                return error;

            variables.Add((InfVar) variable);
        }
        
        if (variables.Count == 0)
        {
            if (modifier == null) 
                return "Expected at least one variable in lambda expression";
            
            _index = startIndex;
            return modifier;
        }

        if (!MatchKeyword("."))
        {
            if (modifier == null)
                return $"Expected '.', got {Current()}";
            
            _index = startIndex;
            return modifier;
        }

        if (!Expression().Deconstruct(out var body, out error))
            return error;
        
        for (var i = variables.Count - 1; i >= 0; i--)
        {
            body = modifier == null
                ? new InfAbs(variables[i], body)
                : new InfComb(modifier, new InfAbs(variables[i], body));
        }
        
        return body;
    }

    private Result<InfTerm> Escape()
    {
        _index++;
        if (Current() is not IdentifierToken {Value: var name})
            return $"Expected identifier, got {Current()}";
        
        return Variable(name);
    }

    private Result<InfTerm> Escape(InfTerm left)
    {
        _index++;
        if (Current() is not IdentifierToken {Value: var name})
            return $"Expected identifier, got {Current()}";
        
        if (!Variable(name).Deconstruct(out var right, out var error))
            return error;
        return Combination(left, right);
    }

    private Result<InfTerm> Combination(InfTerm left, string name)
    {
        if (!Identifier(name).Deconstruct(out var right, out var error))
            return error;
        
        return Combination(left, right);
    }

    private Result<InfTerm> Combination(InfTerm left, InfTerm right)
    {
        return new InfComb(left, right);
    }

    private enum InfixPrecedence
    {
        None = int.MinValue,
        NotNone = int.MinValue + 1,
        Combination = 60,
        Highest = int.MaxValue,
    }
}