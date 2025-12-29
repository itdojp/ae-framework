/**
 * Tests for SBOM Generator
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { SBOMGenerator, type SBOMGeneratorOptions, type SBOM } from '../../src/security/sbom-generator.js';
import * as fs from 'fs/promises';

// Mock fs module
vi.mock('fs/promises');
const { mockGlob } = vi.hoisted(() => ({
  mockGlob: vi.fn()
}));
vi.mock('glob', () => ({
  glob: mockGlob,
}));

const mockFs = vi.mocked(fs);

describe('SBOMGenerator', () => {
  let generator: SBOMGenerator;
  let options: SBOMGeneratorOptions;

  beforeEach(() => {
    vi.clearAllMocks();
    
    options = {
      projectRoot: '/test/project',
      outputPath: '/test/project/sbom.json',
      includeDevDependencies: false,
      includeLicenses: true,
      includeHashes: true,
      includeVulnerabilities: false,
      format: 'json',
    };

    generator = new SBOMGenerator(options);
  });

  describe('Basic SBOM Generation', () => {
    it('should generate a valid SBOM structure', async () => {
      // Mock package.json
      const mockPackageJson = {
        name: 'test-project',
        version: '1.0.0',
        dependencies: {
          'express': '^4.18.0',
          'lodash': '^4.17.0',
        },
        devDependencies: {
          'jest': '^29.0.0',
        },
        author: 'Test Author',
      };

      // Mock package-lock.json
      const mockPackageLock = {
        packages: {
          'node_modules/express': {
            version: '4.18.2',
            description: 'Fast, unopinionated, minimalist web framework',
            license: 'MIT',
            homepage: 'http://expressjs.com/',
            repository: {
              url: 'git+https://github.com/expressjs/express.git',
            },
          },
          'node_modules/lodash': {
            version: '4.17.21',
            description: 'Lodash modular utilities.',
            license: 'MIT',
          },
        },
      };

      mockFs.readFile.mockImplementation((filePath: string) => {
        const pathStr = filePath.toString();
        if (pathStr.endsWith('package.json')) {
          return Promise.resolve(JSON.stringify(mockPackageJson));
        }
        if (pathStr.endsWith('package-lock.json')) {
          return Promise.resolve(JSON.stringify(mockPackageLock));
        }
        return Promise.reject(new Error('File not found'));
      });

      mockGlob.mockResolvedValue([]);

      const sbom = await generator.generate();

      expect(sbom).toBeDefined();
      expect(sbom.bomFormat).toBe('CycloneDX');
      expect(sbom.specVersion).toBe('1.4');
      expect(sbom.serialNumber).toMatch(/^urn:uuid:/);
      expect(sbom.version).toBe(1);
      expect(sbom.metadata).toBeDefined();
      expect(sbom.components).toBeDefined();
    });

    it('should include proper metadata', async () => {
      mockFs.readFile.mockImplementation((filePath: string) => {
        const pathStr = filePath.toString();
        if (pathStr.endsWith('package.json')) {
          return Promise.resolve(JSON.stringify({
            name: 'test-project',
            author: 'Test Author',
          }));
        }
        return Promise.reject(new Error('File not found'));
      });

      mockGlob.mockResolvedValue([]);

      const sbom = await generator.generate();

      expect(sbom.metadata.timestamp).toBeDefined();
      expect(sbom.metadata.tools).toHaveLength(1);
      expect(sbom.metadata.tools[0].name).toBe('SBOM Generator');
      expect(sbom.metadata.authors).toContain('Test Author');
    });

    it('should extract package dependencies correctly', async () => {
      const mockPackageJson = {
        dependencies: {
          'express': '^4.18.0',
          'lodash': '^4.17.0',
        },
      };

      const mockPackageLock = {
        packages: {
          'node_modules/express': {
            version: '4.18.2',
            description: 'Express framework',
            license: 'MIT',
          },
          'node_modules/lodash': {
            version: '4.17.21',
            description: 'Lodash utilities',
            license: 'MIT',
          },
        },
      };

      mockFs.readFile.mockImplementation((filePath: string) => {
        const pathStr = filePath.toString();
        if (pathStr.endsWith('package.json')) {
          return Promise.resolve(JSON.stringify(mockPackageJson));
        }
        if (pathStr.endsWith('package-lock.json')) {
          return Promise.resolve(JSON.stringify(mockPackageLock));
        }
        return Promise.reject(new Error('File not found'));
      });

      mockGlob.mockResolvedValue([]);

      const sbom = await generator.generate();

      const expressComponent = sbom.components.find(c => c.name === 'express');
      const lodashComponent = sbom.components.find(c => c.name === 'lodash');

      expect(expressComponent).toBeDefined();
      expect(expressComponent?.version).toBe('4.18.2');
      expect(expressComponent?.type).toBe('library');
      expect(expressComponent?.purl).toBe('pkg:npm/express@4.18.2');
      expect(expressComponent?.licenses).toContain('MIT');

      expect(lodashComponent).toBeDefined();
      expect(lodashComponent?.version).toBe('4.17.21');
    });

    it('should include dev dependencies when requested', async () => {
      const optionsWithDev = { ...options, includeDevDependencies: true };
      const generatorWithDev = new SBOMGenerator(optionsWithDev);

      const mockPackageJson = {
        dependencies: {
          'express': '^4.18.0',
        },
        devDependencies: {
          'jest': '^29.0.0',
        },
      };

      const mockPackageLock = {
        packages: {
          'node_modules/express': {
            version: '4.18.2',
            license: 'MIT',
          },
          'node_modules/jest': {
            version: '29.5.0',
            license: 'MIT',
          },
        },
      };

      mockFs.readFile.mockImplementation((filePath: string) => {
        const pathStr = filePath.toString();
        if (pathStr.endsWith('package.json')) {
          return Promise.resolve(JSON.stringify(mockPackageJson));
        }
        if (pathStr.endsWith('package-lock.json')) {
          return Promise.resolve(JSON.stringify(mockPackageLock));
        }
        return Promise.reject(new Error('File not found'));
      });

      mockGlob.mockResolvedValue([]);

      const sbom = await generatorWithDev.generate();

      const jestComponent = sbom.components.find(c => c.name === 'jest');
      expect(jestComponent).toBeDefined();
      expect(jestComponent?.version).toBe('29.5.0');
    });
  });

  describe('File Handling', () => {
    it('should extract application files when requested', async () => {
      mockFs.readFile.mockResolvedValue('{}');
      
      // Mock glob to return some files
      mockGlob.mockResolvedValue([
        '/test/project/src/index.ts',
        '/test/project/src/utils.ts',
      ]);

      // Mock fs.stat
      mockFs.stat.mockResolvedValue({
        isFile: () => true,
        size: 1024,
      } as any);

      const sbom = await generator.generate();

      const fileComponents = sbom.components.filter(c => c.type === 'file');
      expect(fileComponents.length).toBeGreaterThan(0);
      
      const indexFile = fileComponents.find(c => c.name === 'src/index.ts');
      expect(indexFile).toBeDefined();
      expect(indexFile?.type).toBe('file');
    });

    it('should generate file hashes when requested', async () => {
      const optionsWithHashes = { ...options, includeHashes: true };
      const generatorWithHashes = new SBOMGenerator(optionsWithHashes);

      mockFs.readFile.mockImplementation((filePath: string) => {
        const pathStr = filePath.toString();
        if (pathStr.endsWith('package.json')) {
          return Promise.resolve('{}');
        }
        if (pathStr.endsWith('/test/project/src/index.ts')) {
          return Promise.resolve(Buffer.from('console.log("Hello World");'));
        }
        return Promise.reject(new Error('File not found'));
      });

      mockGlob.mockResolvedValue(['/test/project/src/index.ts']);

      mockFs.stat.mockResolvedValue({
        isFile: () => true,
        size: 1024,
      } as any);

      const sbom = await generatorWithHashes.generate();

      const fileComponent = sbom.components.find(c => c.name === 'src/index.ts');
      expect(fileComponent?.hashes).toBeDefined();
      expect(fileComponent?.hashes).toHaveLength(2); // SHA-256 and SHA-1
      expect(fileComponent?.hashes?.[0].algorithm).toBe('SHA-256');
      expect(fileComponent?.hashes?.[1].algorithm).toBe('SHA-1');
    });
  });

  describe('Output Formats', () => {
    it('should generate JSON format by default', async () => {
      mockFs.readFile.mockResolvedValue('{}');
      mockGlob.mockResolvedValue([]);

      const sbom = await generator.generate();
      expect(typeof sbom).toBe('object');
    });

    it('should save SBOM to file', async () => {
      mockFs.readFile.mockResolvedValue('{}');
      mockGlob.mockResolvedValue([]);
      mockFs.writeFile.mockResolvedValue(undefined);

      const outputPath = await generator.generateAndSave();

      expect(mockFs.writeFile).toHaveBeenCalledWith(
        options.outputPath,
        expect.stringContaining('"bomFormat": "CycloneDX"'),
        'utf8'
      );
      expect(outputPath).toBe(options.outputPath);
    });
  });

  describe('Error Handling', () => {
    it('should handle missing package.json gracefully', async () => {
      mockFs.readFile.mockRejectedValue(new Error('File not found'));
      mockGlob.mockResolvedValue([]);

      const sbom = await generator.generate();

      expect(sbom).toBeDefined();
      expect(sbom.components).toBeDefined();
      // Should still generate SBOM even without package.json
    });

    it('should handle missing package-lock.json gracefully', async () => {
      mockFs.readFile.mockImplementation((filePath: string) => {
        const pathStr = filePath.toString();
        if (pathStr.endsWith('package.json')) {
          return Promise.resolve(JSON.stringify({
            dependencies: { 'express': '^4.18.0' }
          }));
        }
        return Promise.reject(new Error('File not found'));
      });

      mockGlob.mockResolvedValue([]);

      const sbom = await generator.generate();

      expect(sbom).toBeDefined();
      const expressComponent = sbom.components.find(c => c.name === 'express');
      expect(expressComponent).toBeDefined();
      expect(expressComponent?.version).toBe('^4.18.0'); // Should use version from package.json
    });

    it('should handle glob errors gracefully', async () => {
      mockFs.readFile.mockResolvedValue('{}');
      mockGlob.mockRejectedValue(new Error('Glob error'));

      const sbom = await generator.generate();

      expect(sbom).toBeDefined();
      // Should still generate SBOM without application files
    });
  });

  describe('Serial Number Generation', () => {
    it('should generate unique serial numbers', async () => {
      mockFs.readFile.mockResolvedValue('{}');
      mockGlob.mockResolvedValue([]);

      const sbom1 = await generator.generate();
      const sbom2 = await generator.generate();

      expect(sbom1.serialNumber).toMatch(/^urn:uuid:/);
      expect(sbom2.serialNumber).toMatch(/^urn:uuid:/);
      expect(sbom1.serialNumber).not.toBe(sbom2.serialNumber);
    });
  });

  describe('License Extraction', () => {
    it('should extract licenses from package lock', async () => {
      const mockPackageJson = {
        dependencies: { 'test-package': '^1.0.0' }
      };

      const mockPackageLock = {
        packages: {
          'node_modules/test-package': {
            version: '1.0.0',
            license: 'MIT',
          },
        },
      };

      mockFs.readFile.mockImplementation((filePath: string) => {
        const pathStr = filePath.toString();
        if (pathStr.endsWith('package.json')) {
          return Promise.resolve(JSON.stringify(mockPackageJson));
        }
        if (pathStr.endsWith('package-lock.json')) {
          return Promise.resolve(JSON.stringify(mockPackageLock));
        }
        return Promise.reject(new Error('File not found'));
      });

      mockGlob.mockResolvedValue([]);

      const sbom = await generator.generate();
      const component = sbom.components.find(c => c.name === 'test-package');
      
      expect(component?.licenses).toContain('MIT');
    });

    it('should handle complex license structures', async () => {
      const mockPackageJson = {
        dependencies: { 'test-package': '^1.0.0' }
      };

      const mockPackageLock = {
        packages: {
          'node_modules/test-package': {
            version: '1.0.0',
            licenses: [
              { type: 'MIT' },
              { type: 'Apache-2.0' }
            ],
          },
        },
      };

      mockFs.readFile.mockImplementation((filePath: string) => {
        const pathStr = filePath.toString();
        if (pathStr.endsWith('package.json')) {
          return Promise.resolve(JSON.stringify(mockPackageJson));
        }
        if (pathStr.endsWith('package-lock.json')) {
          return Promise.resolve(JSON.stringify(mockPackageLock));
        }
        return Promise.reject(new Error('File not found'));
      });

      mockGlob.mockResolvedValue([]);

      const sbom = await generator.generate();
      const component = sbom.components.find(c => c.name === 'test-package');
      
      expect(component?.licenses).toContain('MIT');
      expect(component?.licenses).toContain('Apache-2.0');
    });
  });
});
