namespace ValiantProver.Modules;

public static class TopLevel
{
    public static void Load() { }

    static TopLevel()
    {
        TautologyEvaluator.Load();
    }
}