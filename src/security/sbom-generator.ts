/**
 * Software Bill of Materials (SBOM) Generator
 * Generates comprehensive SBOMs for security and compliance
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import { glob } from 'glob';
import * as crypto from 'crypto';

export interface SBOMComponent {
  name: string;
  version: string;
  type: 'library' | 'framework' | 'application' | 'container' | 'file' | 'operating-system';
  supplier?: string;
  author?: string;
  description?: string;
  licenses?: string[];
  cpe?: string;
  purl?: string;
  hashes?: {
    algorithm: string;
    value: string;
  }[];
  externalReferences?: {
    type: string;
    url: string;
  }[];
  dependencies?: string[];
  vulnerabilities?: {
    id: string;
    severity: 'low' | 'medium' | 'high' | 'critical';
    description?: string;
    references?: string[];
  }[];
}

export interface SBOMMetadata {
  timestamp: string;
  tools: {
    vendor: string;
    name: string;
    version: string;
  }[];
  authors: string[];
  supplier?: string;
}

export interface SBOM {
  bomFormat: string;
  specVersion: string;
  serialNumber: string;
  version: number;
  metadata: SBOMMetadata;
  components: SBOMComponent[];
  dependencies?: {
    ref: string;
    dependsOn?: string[];
  }[];
  vulnerabilities?: {
    bom_ref: string;
    id: string;
    source?: {
      name: string;
      url: string;
    };
    ratings?: {
      source?: string;
      score?: number;
      severity?: string;
      method?: string;
    }[];
    cwes?: number[];
    description?: string;
    advisories?: {
      title?: string;
      url?: string;
    }[];
  }[];
}

export interface SBOMGeneratorOptions {
  projectRoot: string;
  outputPath?: string;
  includeDevDependencies?: boolean;
  includeLicenses?: boolean;
  includeHashes?: boolean;
  includeVulnerabilities?: boolean;
  format?: 'json' | 'xml';
  customComponents?: SBOMComponent[];
}

export class SBOMGenerator {
  private options: Required<SBOMGeneratorOptions>;

  constructor(options: SBOMGeneratorOptions) {
    this.options = {
      outputPath: path.join(options.projectRoot, 'sbom.json'),
      includeDevDependencies: false,
      includeLicenses: true,
      includeHashes: true,
      includeVulnerabilities: false,
      format: 'json',
      customComponents: [],
      ...options,
    };
  }

  /**
   * Generate complete SBOM
   */
  public async generate(): Promise<SBOM> {
    const components: SBOMComponent[] = [];

    // Add package dependencies
    const packageComponents = await this.extractPackageDependencies();
    components.push(...packageComponents);

    // Add custom components
    components.push(...this.options.customComponents);

    // Add application files
    const fileComponents = await this.extractApplicationFiles();
    components.push(...fileComponents);

    // Generate metadata
    const metadata = await this.generateMetadata();

    const sbom: SBOM = {
      bomFormat: 'CycloneDX',
      specVersion: '1.4',
      serialNumber: this.generateSerialNumber(),
      version: 1,
      metadata,
      components,
    };

    // Add dependencies if available
    const dependencies = await this.extractDependencyGraph(components);
    if (dependencies.length > 0) {
      sbom.dependencies = dependencies;
    }

    // Add vulnerabilities if requested
    if (this.options.includeVulnerabilities) {
      sbom.vulnerabilities = await this.extractVulnerabilities(components);
    }

    return sbom;
  }

  /**
   * Generate and save SBOM to file
   */
  public async generateAndSave(): Promise<string> {
    const sbom = await this.generate();
    const content = this.options.format === 'json' 
      ? JSON.stringify(sbom, null, 2)
      : this.convertToXML(sbom);

    await fs.writeFile(this.options.outputPath, content, 'utf8');
    return this.options.outputPath;
  }

  /**
   * Extract package dependencies from package.json and package-lock.json
   */
  private async extractPackageDependencies(): Promise<SBOMComponent[]> {
    const components: SBOMComponent[] = [];

    try {
      // Read package.json
      const packageJsonPath = path.join(this.options.projectRoot, 'package.json');
      const packageJson = JSON.parse(await fs.readFile(packageJsonPath, 'utf8'));

      // Read package-lock.json for detailed version info
      let packageLock: any = {};
      try {
        const packageLockPath = path.join(this.options.projectRoot, 'package-lock.json');
        packageLock = JSON.parse(await fs.readFile(packageLockPath, 'utf8'));
      } catch {
        // package-lock.json might not exist
      }

      // Process dependencies
      const deps = {
        ...packageJson.dependencies || {},
        ...(this.options.includeDevDependencies ? packageJson.devDependencies || {} : {}),
      };

      for (const [name, version] of Object.entries(deps)) {
        const lockInfo = packageLock.packages?.[`node_modules/${name}`] || {};
        const resolvedVersion = lockInfo.version || (version as string);

        const component: SBOMComponent = {
          name,
          version: resolvedVersion,
          type: 'library',
          description: lockInfo.description,
          licenses: this.options.includeLicenses ? this.extractLicenses(lockInfo) : undefined,
          purl: `pkg:npm/${name}@${resolvedVersion}`,
          externalReferences: [
            {
              type: 'website',
              url: `https://www.npmjs.com/package/${name}`,
            },
          ],
        };

        if (lockInfo.homepage) {
          component.externalReferences?.push({
            type: 'website',
            url: lockInfo.homepage,
          });
        }

        if (lockInfo.repository?.url) {
          component.externalReferences?.push({
            type: 'vcs',
            url: lockInfo.repository.url,
          });
        }

        components.push(component);
      }
    } catch (error) {
      console.warn('Failed to extract package dependencies:', error);
    }

    return components;
  }

  /**
   * Extract application files
   */
  private async extractApplicationFiles(): Promise<SBOMComponent[]> {
    const components: SBOMComponent[] = [];

    try {
      const patterns = [
        'src/**/*.{ts,js,tsx,jsx}',
        'dist/**/*.{js,css}',
        'public/**/*',
        '*.{ts,js,json}',
      ];

      for (const pattern of patterns) {
        const files = await glob(pattern, { 
          cwd: this.options.projectRoot,
          absolute: true,
        });

        for (const file of files) {
          const stats = await fs.stat(file);
          if (stats.isFile()) {
            const relativePath = path.relative(this.options.projectRoot, file);
            const component: SBOMComponent = {
              name: relativePath,
              version: '1.0.0', // Application version
              type: 'file',
              description: `Application file: ${relativePath}`,
            };

            if (this.options.includeHashes) {
              component.hashes = await this.generateFileHashes(file);
            }

            components.push(component);
          }
        }
      }
    } catch (error) {
      console.warn('Failed to extract application files:', error);
    }

    return components;
  }

  /**
   * Generate metadata section
   */
  private async generateMetadata(): Promise<SBOMMetadata> {
    let packageJson: any = {};
    try {
      const packageJsonPath = path.join(this.options.projectRoot, 'package.json');
      packageJson = JSON.parse(await fs.readFile(packageJsonPath, 'utf8'));
    } catch {
      // package.json might not exist
    }

    return {
      timestamp: new Date().toISOString(),
      tools: [
        {
          vendor: 'AE Framework',
          name: 'SBOM Generator',
          version: '1.0.0',
        },
      ],
      authors: packageJson.author ? [packageJson.author] : ['AE Framework'],
      supplier: packageJson.author || 'AE Framework',
    };
  }

  /**
   * Extract dependency graph
   */
  private async extractDependencyGraph(components: SBOMComponent[]): Promise<{ ref: string; dependsOn?: string[] }[]> {
    const dependencies: { ref: string; dependsOn?: string[] }[] = [];

    try {
      const packageLockPath = path.join(this.options.projectRoot, 'package-lock.json');
      const packageLock = JSON.parse(await fs.readFile(packageLockPath, 'utf8'));

      if (packageLock.packages) {
        for (const [packagePath, packageInfo] of Object.entries(packageLock.packages)) {
          if (packagePath === '' || !(packageInfo as any).dependencies) continue;

          const packageName = packagePath.replace('node_modules/', '');
          const dependsOn = Object.keys((packageInfo as any).dependencies || {});

          if (dependsOn.length > 0) {
            dependencies.push({
              ref: packageName,
              dependsOn,
            });
          }
        }
      }
    } catch (error) {
      console.warn('Failed to extract dependency graph:', error);
    }

    return dependencies;
  }

  /**
   * Extract vulnerabilities (placeholder for vulnerability scanning integration)
   */
  private async extractVulnerabilities(components: SBOMComponent[]): Promise<any[]> {
    // This would integrate with vulnerability databases like:
    // - NPM audit
    // - GitHub Advisory Database
    // - OSV (Open Source Vulnerabilities)
    // - Snyk
    // - CVE databases

    const vulnerabilities: any[] = [];

    // Placeholder implementation
    for (const component of components) {
      if (component.type === 'library') {
        // Mock vulnerability check
        if (Math.random() < 0.1) { // 10% chance for demonstration
          vulnerabilities.push({
            bom_ref: component.name,
            id: `CVE-2023-${Math.floor(Math.random() * 10000).toString().padStart(4, '0')}`,
            source: {
              name: 'National Vulnerability Database',
              url: 'https://nvd.nist.gov/',
            },
            ratings: [
              {
                source: 'NVD',
                score: Math.random() * 10,
                severity: ['low', 'medium', 'high', 'critical'][Math.floor(Math.random() * 4)],
                method: 'CVSSv3',
              },
            ],
            description: `Mock vulnerability in ${component.name}`,
          });
        }
      }
    }

    return vulnerabilities;
  }

  /**
   * Extract license information
   */
  private extractLicenses(packageInfo: any): string[] {
    const licenses: string[] = [];

    if (packageInfo.license) {
      if (typeof packageInfo.license === 'string') {
        licenses.push(packageInfo.license);
      } else if (Array.isArray(packageInfo.license)) {
        licenses.push(...packageInfo.license);
      }
    }

    if (packageInfo.licenses && Array.isArray(packageInfo.licenses)) {
      for (const license of packageInfo.licenses) {
        if (typeof license === 'string') {
          licenses.push(license);
        } else if (license.type) {
          licenses.push(license.type);
        }
      }
    }

    return [...new Set(licenses)]; // Remove duplicates
  }

  /**
   * Generate file hashes
   */
  private async generateFileHashes(filePath: string): Promise<{ algorithm: string; value: string }[]> {
    const content = await fs.readFile(filePath);
    
    return [
      {
        algorithm: 'SHA-256',
        value: crypto.createHash('sha256').update(content).digest('hex'),
      },
      {
        algorithm: 'SHA-1',
        value: crypto.createHash('sha1').update(content).digest('hex'),
      },
    ];
  }

  /**
   * Generate serial number for SBOM
   */
  private generateSerialNumber(): string {
    const timestamp = new Date().toISOString().replace(/[:.]/g, '');
    const random = crypto.randomBytes(8).toString('hex');
    return `urn:uuid:${timestamp}-${random}`;
  }

  /**
   * Convert SBOM to XML format (CycloneDX XML)
   */
  private convertToXML(sbom: SBOM): string {
    // Simplified XML conversion - in production, use a proper XML library
    let xml = '<?xml version="1.0" encoding="UTF-8"?>\n';
    xml += `<bom xmlns="http://cyclonedx.org/schema/bom/1.4" version="${sbom.version}" serialNumber="${sbom.serialNumber}">\n`;
    
    // Metadata
    xml += '  <metadata>\n';
    xml += `    <timestamp>${sbom.metadata.timestamp}</timestamp>\n`;
    xml += '    <tools>\n';
    for (const tool of sbom.metadata.tools) {
      xml += `      <tool>\n`;
      xml += `        <vendor>${this.escapeXML(tool.vendor)}</vendor>\n`;
      xml += `        <name>${this.escapeXML(tool.name)}</name>\n`;
      xml += `        <version>${this.escapeXML(tool.version)}</version>\n`;
      xml += `      </tool>\n`;
    }
    xml += '    </tools>\n';
    xml += '  </metadata>\n';

    // Components
    xml += '  <components>\n';
    for (const component of sbom.components) {
      xml += `    <component type="${component.type}">\n`;
      xml += `      <name>${this.escapeXML(component.name)}</name>\n`;
      xml += `      <version>${this.escapeXML(component.version)}</version>\n`;
      if (component.description) {
        xml += `      <description>${this.escapeXML(component.description)}</description>\n`;
      }
      if (component.purl) {
        xml += `      <purl>${this.escapeXML(component.purl)}</purl>\n`;
      }
      xml += '    </component>\n';
    }
    xml += '  </components>\n';

    xml += '</bom>\n';
    return xml;
  }

  /**
   * Escape XML characters
   */
  private escapeXML(text: string): string {
    return text
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#39;');
  }
}