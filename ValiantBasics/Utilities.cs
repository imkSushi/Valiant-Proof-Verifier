using System.Diagnostics.CodeAnalysis;

namespace ValiantBasics;

public static class Utilities
{
    private static IEnumerable<string> NewTypeNameGenerator()
    {
        for (var length = 1;; length++)
        {
            foreach (var str in StringProvider(length))
            {
                yield return str;
            }
        }
        // ReSharper disable once IteratorNeverReturns
    }

    private static IEnumerable<char> LetterProvider()
    {
        for (var c = 'a'; c <= 'z'; c++)
        {
            yield return c;
        }
        
        for (var c = 'A'; c <= 'Z'; c++)
        {
            yield return c;
        }
        
        for (var c = '0'; c <= '9'; c++)
        {
            yield return c;
        }
    }

    private static IEnumerable<string> StringProvider(int length)
    {
        switch (length)
        {
            case > 1:
                foreach (var letter in LetterProvider())
                {
                    foreach (var suffix in StringProvider(length - 1))
                    {
                        yield return letter + suffix;
                    }
                }
                break;
            case 1:
                foreach (var c in LetterProvider())
                {
                    yield return c.ToString();
                }
                break;
            case 0:
                yield return "";
                break;
            default:
                throw new ArgumentOutOfRangeException(nameof(length), length, "Length must be greater than or equal to 0");
        }
    }

    public class NewNameTypeGenerator : IDisposable
    {
        private IEnumerator<string> _generator = NewTypeNameGenerator().GetEnumerator();

        public string Next()
        {
            _generator.MoveNext();
            return _generator.Current;
        }

        public void Dispose()
        {
            _generator.Dispose();
        }
    }
    
    public static bool Deconstruct<T>(this T? nullable, [MaybeNullWhen(false)] out T value)
    {
        value = nullable;
        return value != null;
    }
    
    public static bool Unique<T>(this IEnumerable<T> enumerable)
    {
        var hashSet = new HashSet<T>();
        return enumerable.All(value => hashSet.Add(value));
    }
}