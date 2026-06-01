import { afterEach, beforeEach, describe, expect, test } from 'vitest';
import * as fs from 'fs/promises';
import * as path from 'path';
import { MCPPluginManager, type PluginManifest } from '../../../src/utils/mcp-plugin-manager.js';

const fileSymlinkType = process.platform === 'win32' ? 'file' : undefined;
const directorySymlinkType = process.platform === 'win32' ? 'junction' : 'dir';

describe('MCPPluginManager path safety', () => {
  let workspaceRoot: string;
  let projectRoot: string;

  beforeEach(async () => {
    workspaceRoot = path.join(
      process.cwd(),
      'artifacts',
      'testing',
      'test-tmp',
      `mcp-plugin-manager-${process.pid}-${Date.now()}-${Math.random().toString(16).slice(2)}`
    );
    projectRoot = path.join(workspaceRoot, 'project');
    await fs.mkdir(projectRoot, { recursive: true });
  });

  afterEach(async () => {
    await fs.rm(workspaceRoot, { recursive: true, force: true });
  });

  async function writePlugin(
    pluginsRoot: string,
    directoryName: string,
    manifest: Partial<PluginManifest>,
    moduleContent = 'export async function initialize() {}\n'
  ): Promise<string> {
    const pluginDirectory = path.join(pluginsRoot, directoryName);
    await fs.mkdir(pluginDirectory, { recursive: true });

    const completeManifest: PluginManifest = {
      name: 'safe-plugin',
      version: '1.0.0',
      main: 'index.mjs',
      ...manifest
    };

    await fs.writeFile(path.join(pluginDirectory, 'plugin.json'), JSON.stringify(completeManifest, null, 2));
    await fs.writeFile(path.join(pluginDirectory, 'index.mjs'), moduleContent);
    return path.join(pluginDirectory, 'plugin.json');
  }

  test('loads plugins from the actual scanned directory instead of recomputing paths from manifest.name', async () => {
    const pluginsRoot = path.join(projectRoot, 'plugins');
    const manifestPath = await writePlugin(pluginsRoot, 'actual-directory', {
      name: 'safe-plugin',
      main: 'index.mjs'
    });

    const manager = new MCPPluginManager(projectRoot);
    const results = await manager.loadPluginsFromDirectory(pluginsRoot);

    expect(results).toHaveLength(1);
    expect(results[0]?.success).toBe(true);
    expect(results[0]?.plugin?.filePath).toBe(manifestPath);
    expect(manager.getPlugin('safe-plugin')?.filePath).toBe(manifestPath);
  });

  test('discovery filters invalid manifests by default but can expose them when validation is skipped', async () => {
    const pluginsRoot = path.join(projectRoot, 'plugins');
    await writePlugin(pluginsRoot, 'valid-plugin', {
      name: 'valid-plugin',
      main: 'index.mjs'
    });
    await writePlugin(pluginsRoot, 'invalid-plugin', {
      name: '../invalid',
      main: 'index.mjs'
    });

    const manager = new MCPPluginManager(projectRoot);

    const defaultDiscovery = await manager.discoverPlugins({ searchPaths: [pluginsRoot], includeDevPlugins: true });
    expect(defaultDiscovery.map((plugin) => plugin.name).sort()).toEqual(['valid-plugin']);

    const skipValidationDiscovery = await manager.discoverPlugins({
      searchPaths: [pluginsRoot],
      includeDevPlugins: true,
      skipValidation: true
    });
    expect(skipValidationDiscovery.map((plugin) => plugin.name).sort()).toEqual(['../invalid', 'valid-plugin']);
  });

  test('directory loading returns per-plugin load errors for invalid manifests instead of silently skipping them', async () => {
    const pluginsRoot = path.join(projectRoot, 'plugins');
    await writePlugin(pluginsRoot, 'invalid-plugin', {
      name: '../invalid',
      main: 'index.mjs'
    });

    const manager = new MCPPluginManager(projectRoot);
    const results = await manager.loadPluginsFromDirectory(pluginsRoot);

    expect(results).toHaveLength(1);
    expect(results[0]?.success).toBe(false);
    expect(results[0]?.error).toContain('Invalid plugin manifest');
  });

  test('allows nested manifest main paths when they remain inside the plugin directory', async () => {
    const pluginsRoot = path.join(projectRoot, 'plugins');
    const pluginDirectory = path.join(pluginsRoot, 'nested-main-plugin');
    await fs.mkdir(path.join(pluginDirectory, 'dist'), { recursive: true });
    const manifestPath = path.join(pluginDirectory, 'plugin.json');
    await fs.writeFile(
      manifestPath,
      JSON.stringify({ name: 'nested-main-plugin', version: '1.0.0', main: 'dist/index.mjs' }, null, 2)
    );
    await fs.writeFile(path.join(pluginDirectory, 'dist', 'index.mjs'), 'export async function initialize() {}\n');

    const manager = new MCPPluginManager(projectRoot);
    const result = await manager.loadPlugin(
      { name: 'nested-main-plugin', version: '1.0.0', main: 'dist/index.mjs' },
      manifestPath
    );

    expect(result.success).toBe(true);
    expect(result.plugin?.manifest.name).toBe('nested-main-plugin');
  });

  test.each([
    '../evil',
    'bad/name',
    'bad\\name',
    'BadName',
    'bad name',
    '.hidden',
    'a'.repeat(81)
  ])('rejects unsafe manifest plugin name %s before module loading', async (unsafeName) => {
    const pluginsRoot = path.join(projectRoot, 'plugins');
    const manifestPath = await writePlugin(pluginsRoot, 'unsafe-name-plugin', {
      name: unsafeName,
      main: 'index.mjs'
    });

    const manager = new MCPPluginManager(projectRoot);
    const result = await manager.loadPlugin(
      { name: unsafeName, version: '1.0.0', main: 'index.mjs' },
      manifestPath
    );

    expect(result.success).toBe(false);
    expect(result.error).toContain('Invalid plugin manifest');
  });

  test.each([
    '../outside.mjs',
    './index.mjs',
    '/absolute/index.mjs',
    'C:\\temp\\plugin.js',
    'nested/../index.mjs',
    'index.ts',
    'index.json'
  ])('rejects unsafe manifest main path %s before module loading', async (unsafeMain) => {
    const pluginsRoot = path.join(projectRoot, 'plugins');
    const manifestPath = await writePlugin(pluginsRoot, 'unsafe-main-plugin', {
      name: 'unsafe-main-plugin',
      main: unsafeMain
    });

    const manager = new MCPPluginManager(projectRoot);
    const result = await manager.loadPlugin(
      { name: 'unsafe-main-plugin', version: '1.0.0', main: unsafeMain },
      manifestPath
    );

    expect(result.success).toBe(false);
    expect(result.error).toContain('Invalid plugin manifest');
  });

  test('rejects symlinked plugin main files that resolve outside the plugin directory', async () => {
    const pluginsRoot = path.join(projectRoot, 'plugins');
    const pluginDirectory = path.join(pluginsRoot, 'symlink-plugin');
    const outsideDirectory = path.join(workspaceRoot, 'outside');
    await fs.mkdir(pluginDirectory, { recursive: true });
    await fs.mkdir(outsideDirectory, { recursive: true });

    const outsideModule = path.join(outsideDirectory, 'outside.mjs');
    await fs.writeFile(outsideModule, 'export async function initialize() {}\n');
    await fs.writeFile(
      path.join(pluginDirectory, 'plugin.json'),
      JSON.stringify({ name: 'symlink-plugin', version: '1.0.0', main: 'index.mjs' }, null, 2)
    );
    await fs.symlink(outsideModule, path.join(pluginDirectory, 'index.mjs'), fileSymlinkType);

    const manager = new MCPPluginManager(projectRoot);
    const result = await manager.loadPlugin(
      { name: 'symlink-plugin', version: '1.0.0', main: 'index.mjs' },
      path.join(pluginDirectory, 'plugin.json')
    );

    expect(result.success).toBe(false);
    expect(result.error).toContain('resolves outside the plugin directory');
  });

  test('creates plugin templates only inside the approved project tree and serializes generated code strings', async () => {
    const targetDir = path.join(projectRoot, 'plugins');
    const manager = new MCPPluginManager(projectRoot);

    await manager.createPluginTemplate('new-plugin', targetDir);

    const pluginDirectory = path.join(targetDir, 'new-plugin');
    await expect(fs.stat(path.join(pluginDirectory, 'plugin.json'))).resolves.toBeDefined();
    await expect(fs.stat(path.join(pluginDirectory, 'README.md'))).resolves.toBeDefined();

    const generatedCode = await fs.readFile(path.join(pluginDirectory, 'index.js'), 'utf8');
    expect(generatedCode).toContain('console.log("new-plugin plugin initialized");');
    expect(generatedCode).toContain('path: "/new-plugin/hello"');
    expect(generatedCode).toContain('message: "Hello from new-plugin plugin!"');
  });

  test('allows relative template target directories inside the project root', async () => {
    const manager = new MCPPluginManager(projectRoot);

    await manager.createPluginTemplate('relative-plugin', 'plugins');

    await expect(fs.stat(path.join(projectRoot, 'plugins', 'relative-plugin', 'plugin.json'))).resolves.toBeDefined();
  });

  test.each(['../evil', 'bad/name', 'bad\\name', "bad'name", 'BadName', 'bad name'])(
    'rejects unsafe template plugin name %s before writing files',
    async (unsafeName) => {
      const targetDir = path.join(projectRoot, 'plugins');
      const manager = new MCPPluginManager(projectRoot);

      await expect(manager.createPluginTemplate(unsafeName, targetDir)).rejects.toThrow(/Plugin template name/);

      const entries = await fs.readdir(targetDir).catch(() => []);
      expect(entries).toEqual([]);
    }
  );

  test('rejects plugin template target directories outside the project root', async () => {
    const manager = new MCPPluginManager(projectRoot);
    const outsideTarget = path.join(workspaceRoot, 'outside-target');

    await expect(manager.createPluginTemplate('safe-plugin', outsideTarget)).rejects.toThrow(/project root/);

    await expect(fs.stat(path.join(outsideTarget, 'safe-plugin'))).rejects.toMatchObject({ code: 'ENOENT' });
  });

  test('rejects plugin template target symlinks that resolve outside the project root', async () => {
    const outsideTarget = path.join(workspaceRoot, 'outside-target');
    const symlinkTarget = path.join(projectRoot, 'plugins-link');
    await fs.mkdir(outsideTarget, { recursive: true });
    await fs.symlink(outsideTarget, symlinkTarget, directorySymlinkType);

    const manager = new MCPPluginManager(projectRoot);

    await expect(manager.createPluginTemplate('safe-plugin', symlinkTarget)).rejects.toThrow(/outside the project root/);

    const entries = await fs.readdir(outsideTarget);
    expect(entries).toEqual([]);
  });

  test('rejects pre-existing symlinked plugin template output files before overwriting them', async () => {
    const targetDir = path.join(projectRoot, 'plugins');
    const pluginDirectory = path.join(targetDir, 'safe-plugin');
    const outsideTarget = path.join(workspaceRoot, 'outside-plugin-json');
    await fs.mkdir(pluginDirectory, { recursive: true });
    await fs.writeFile(outsideTarget, 'outside content');
    await fs.symlink(outsideTarget, path.join(pluginDirectory, 'plugin.json'), fileSymlinkType);

    const manager = new MCPPluginManager(projectRoot);

    await expect(manager.createPluginTemplate('safe-plugin', targetDir)).rejects.toThrow(/symbolic link|ELOOP/);
    await expect(fs.readFile(outsideTarget, 'utf8')).resolves.toBe('outside content');
  });

  test('rejects symlinked implementation output files without following the final symlink', async () => {
    const targetDir = path.join(projectRoot, 'plugins');
    const pluginDirectory = path.join(targetDir, 'safe-plugin');
    const outsideTarget = path.join(workspaceRoot, 'outside-index');
    await fs.mkdir(pluginDirectory, { recursive: true });
    await fs.writeFile(outsideTarget, 'outside content');
    await fs.symlink(outsideTarget, path.join(pluginDirectory, 'index.js'), fileSymlinkType);

    const manager = new MCPPluginManager(projectRoot);

    await expect(manager.createPluginTemplate('safe-plugin', targetDir)).rejects.toThrow(/symbolic link|ELOOP/);
    await expect(fs.readFile(outsideTarget, 'utf8')).resolves.toBe('outside content');
  });
});
