export function capitalize(str: string): string {
  return str.charAt(0).toUpperCase() + str.slice(1);
}

function generatePhoenixModule(funcName: string, behaviors: string[]): string {
  const moduleName = capitalize(funcName);
  let implementation = `defmodule MyAppWeb.${moduleName}Controller do\n`;
  implementation += '  use MyAppWeb, :controller\n\n';

  implementation += '  @doc """\n';
  implementation += `  ${moduleName} action\n`;
  implementation += '  """\n';
  implementation += `  def ${funcName}(conn, _params) do\n`;

  for (const behavior of behaviors) {
    implementation += `    # ${behavior}\n`;
  }

  implementation += '    # TODO: Implement based on tests\n';
  implementation += '    json(conn, %{message: "not implemented"})\n';
  implementation += '  end\n';
  implementation += 'end\n';

  return implementation;
}

function generateElixirFunction(funcName: string, behaviors: string[], framework?: string): string {
  if (framework === 'phoenix') {
    return generatePhoenixModule(funcName, behaviors);
  }

  let implementation = `defmodule ${capitalize(funcName)} do\n`;
  implementation += '  @moduledoc """\n';
  implementation += `  ${capitalize(funcName)} module\n`;
  implementation += '  """\n\n';

  implementation += '  @doc """\n';
  implementation += `  Main function for ${funcName}\n`;
  implementation += '  """\n';
  implementation += `  def ${funcName}(args) do\n`;

  for (const behavior of behaviors) {
    implementation += `    # ${behavior}\n`;
  }

  implementation += '    # TODO: Implement based on tests\n';
  implementation += '    {:ok, "not implemented"}\n';
  implementation += '  end\n';
  implementation += 'end\n';

  return implementation;
}

function generateTSFunction(funcName: string, behaviors: string[]): string {
  let implementation = `export function ${funcName}(...args: any[]): any {\n`;

  for (const behavior of behaviors) {
    if (behavior.includes('return')) {
      implementation += `  // ${behavior}\n`;
    }
  }

  implementation += '  // TODO: Implement based on tests\n';
  implementation += '  return {};\n';
  implementation += '}\n';

  return implementation;
}

function generatePythonFunction(funcName: string, behaviors: string[]): string {
  let implementation = `def ${funcName}(*args, **kwargs):\n`;
  implementation += `    """${capitalize(funcName)} function"""\n`;

  for (const behavior of behaviors) {
    implementation += `    # ${behavior}\n`;
  }

  implementation += '    # TODO: Implement based on tests\n';
  implementation += '    return {}\n';

  return implementation;
}

function generateRustFunction(funcName: string, behaviors: string[]): string {
  let implementation = `pub fn ${funcName}() -> Result<(), Box<dyn std::error::Error>> {\n`;

  for (const behavior of behaviors) {
    implementation += `    // ${behavior}\n`;
  }

  implementation += '    // TODO: Implement based on tests\n';
  implementation += '    Ok(())\n';
  implementation += '}\n';

  return implementation;
}

function generateGoFunction(funcName: string, behaviors: string[]): string {
  let implementation = `func ${capitalize(funcName)}() error {\n`;

  for (const behavior of behaviors) {
    implementation += `    // ${behavior}\n`;
  }

  implementation += '    // TODO: Implement based on tests\n';
  implementation += '    return nil\n';
  implementation += '}\n';

  return implementation;
}

export function generateFunctionImplementation(
  funcName: string,
  behaviors: string[],
  language: string,
  framework?: string,
): string {
  switch (language) {
    case 'elixir':
      return generateElixirFunction(funcName, behaviors, framework);
    case 'typescript':
    case 'javascript':
      return generateTSFunction(funcName, behaviors);
    case 'python':
      return generatePythonFunction(funcName, behaviors);
    case 'rust':
      return generateRustFunction(funcName, behaviors);
    case 'go':
      return generateGoFunction(funcName, behaviors);
    default:
      return generateTSFunction(funcName, behaviors);
  }
}

export function getFileExtension(language: string): string {
  const extensions: Record<string, string> = {
    typescript: 'ts',
    javascript: 'js',
    python: 'py',
    elixir: 'ex',
    rust: 'rs',
    go: 'go',
  };
  return extensions[language] || 'ts';
}

export function getTestExtension(language: string): string {
  const extensions: Record<string, string> = {
    typescript: 'test.ts',
    javascript: 'test.js',
    python: 'test.py',
    elixir: '_test.exs',
    rust: 'rs',
    go: 'test.go',
  };
  return extensions[language] || 'test.ts';
}

export function getSourceDirectory(language: string): string {
  const directories: Record<string, string> = {
    typescript: 'src',
    javascript: 'src',
    python: 'src',
    elixir: 'lib',
    rust: 'src',
    go: '.',
  };
  return directories[language] || 'src';
}

export function getTestDirectory(language: string): string {
  const directories: Record<string, string> = {
    typescript: 'tests',
    javascript: 'tests',
    python: 'tests',
    elixir: 'test',
    rust: 'tests',
    go: '.',
  };
  return directories[language] || 'tests';
}
