using System.Diagnostics.CodeAnalysis;

namespace ValiantBasics;

public class Result<T>
{
    private bool _success;
    private string _message = null!;
    private T _value = default!;
    
    public Result(string message)
    {
        _success = false;
        _message = message;
    }
    
    public Result(T value)
    {
        _success = true;
        _value = value;
    }
    
    public bool Deconstruct([MaybeNullWhen(false)] out T value, [MaybeNullWhen(true)] out string message)
    {
        value = _value;
        message = _message;
        return _success;
    }
    
    public bool IsError([MaybeNullWhen(false)] out string error)
    {
        error = _message;
        return !_success;
    }
    
    public bool IsSuccess([MaybeNullWhen(true)] out T value)
    {
        value = _value;
        return _success;
    }

    public bool IsError()
    {
        return !_success;
    }
    
    public bool IsSuccess()
    {
        return _success;
    }
    
    public static implicit operator Result<T>(string error) => new(error);
    public static implicit operator Result<T>(T value) => new(value);
}