# Persona Samples

`default-profile.json` contains a balanced starter profile that mirrors the expectations of the `/ae:persona` command suite. Import it with:

```bash
pnpm ae persona import samples/persona/default-profile.json
```

Profiles follow the `PersonaProfile` schema (see `src/utils/persona-manager.ts`). Duplicate the file to create project-specific personas.
