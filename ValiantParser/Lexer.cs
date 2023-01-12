using System.Text;

namespace ValiantParser;

internal sealed class Lexer
{
    private List<string> _keywords = new()
    {
        "'",
        ":",
        "\\",
        ".",
        "(",
        ")",
        "$"
    };

    internal HashSet<string> GetKeywords() => _keywords.ToHashSet();
    internal bool TryAddKeyword(string keyword)
    {
        if (_keywords.Contains(keyword))
            return false;
        
        _keywords.Add(keyword);
        
        return true;
    }

    internal void AddKeyword(string keyword)
    {
        TryAddKeyword(keyword);
    }
    
    internal void RemoveKeyword(string keyword)
    {
        _keywords.Remove(keyword);
    }
    
    internal IEnumerable<Token> Lex(string expression)
    {
        var index = 0;
        Token? cachedNextToken = null;

        void SkipWhitespace()
        {
            while (index < expression.Length && expression[index] is ' ' or '\t' or '\n' or '\r')
            {
                index++;
            }
        }
        
        Token NextToken()
        {
            if (cachedNextToken != null)
            {
                var output = cachedNextToken;
                cachedNextToken = null;
                return output;
            }

            if (expression[index] == '"')
                return NextQuotedToken();
            
            var start = index;

            var str = "";
            var validKeywordParts = new HashSet<(int keyword, int indexStart)>();
            (int keyword, int indexStart)? latestValidKeyword = null;

            while (index < expression.Length)
            {
                var c = expression[index];
                if (c is ' ' or '\t' or '\r' or '\n' or '"')
                    break;
                
                if (c is < '!' or > '~')
                {
                    return new ErrorToken($"Invalid character '{c}'");
                }

                var index1 = index;
                validKeywordParts.RemoveWhere(tuple => c != _keywords[tuple.keyword][index1 - tuple.indexStart]);

                if (latestValidKeyword == null)
                {
                    for (var i = 0; i < _keywords.Count; i++)
                    {
                        var keyword = _keywords[i];
                    
                        if (keyword[0] == c)
                        {
                            validKeywordParts.Add((i, index));
                        }
                    }
                }
                else if (validKeywordParts.Count == 0)
                    break;
                
                var validKeywords = validKeywordParts.Where(tuple => _keywords[tuple.keyword].Length == index - tuple.indexStart + 1).ToList();

                if (validKeywords.Any())
                {
                    var (newKeyword, newIndexStart) = validKeywords.MinBy(tuple => tuple.indexStart);
                    validKeywordParts.RemoveWhere(tuple => tuple.indexStart > newIndexStart);
                    validKeywordParts.Remove((newKeyword, newIndexStart));
                    latestValidKeyword = (newKeyword, newIndexStart);
                        
                    if (validKeywordParts.Count == 0)
                        break;
                }
                
                if (latestValidKeyword == null)
                    str += c;
                
                index++;
            }

            if (latestValidKeyword == null) 
                return new IdentifierToken(str);
            
            var (outputKeyword, outputStartIndex) = latestValidKeyword.Value;
            index = outputStartIndex + _keywords[outputKeyword].Length;
            if (outputStartIndex == start)
                return new KeywordToken(_keywords[outputKeyword]);

            cachedNextToken = new KeywordToken(_keywords[outputKeyword]);

            return new IdentifierToken(str[..(outputStartIndex - start)]);
        }
        
        Token NextQuotedToken()
        {
            index++;
            var start = index;
            while (index < expression.Length)
            {
                var c = expression[index];
                if (c == '"')
                {
                    if (index == start)
                        return new ErrorToken("Empty quoted identifier");
                    var str = expression[start..index];
                    index++;
                    return new IdentifierToken(str);
                }

                if (c is < '!' or > '~')
                    return new ErrorToken($"Invalid character '{c}'");

                index++;
            }
            
            return new ErrorToken("Unterminated quoted identifier");
        }
        
        SkipWhitespace();
        while (index < expression.Length || cachedNextToken != null)
        {
            yield return NextToken();
            SkipWhitespace();
        }

        yield return new EndOfExpressionToken();
    }
}

internal record Token(string Value);

internal record IdentifierToken(string Value) : Token(Value)
{
    public override string ToString()
    {
        return $"Identifier: {Value}";
    }
}

internal record KeywordToken(string Value) : Token(Value)
{
    public override string ToString()
    {
        return $"Custom: {Value}";
    }
}

internal record ErrorToken(string Message) : Token(Message)
{
    public override string ToString()
    {
        return $"Error: {Message}";
    }
}

internal record EndOfExpressionToken() : Token("\0")
{
    public override string ToString()
    {
        return "End of expression";
    }
}