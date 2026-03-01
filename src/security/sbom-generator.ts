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

interface PackageLockEntry {
  version?: string;
  description?: string;
  homepage?: string;
  repository?: {
    url?: string;
  };
  dependencies?: Record<string, string>;
  license?: string | string[];
  licenses?: Array<string | { type?: string }>;
}

interface PackageLockFile {
  packages?: Record<string, PackageLockEntry>;
}

interface PackageJsonLike {
  dependencies?: Record<string, string>;
  devDependencies?: Record<string, string>;
  author?: string;
}

type SBOMVulnerability = NonNullable<SBOM['vulnerabilities']>[number];

interface NormalizedVulnerabilityComponent {
  bomRef: string;
  name: string;
  version: string;
  ecosystem: string;
}

interface OsvSeverity {
  type?: string;
  score?: string;
}

interface OsvReference {
  type?: string;
  url?: string;
}

interface OsvVulnerability {
  id?: string;
  summary?: string;
  details?: string;
  severity?: OsvSeverity[];
  references?: OsvReference[];
  database_specific?: {
    severity?: string;
    cwes?: string[];
  };
}

interface OsvBatchResult {
  vulns?: OsvVulnerability[];
}

interface OsvBatchResponse {
  results?: OsvBatchResult[];
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
    const dependencies = await this.extractDependencyGraph();
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
      const packageJson = JSON.parse(await fs.readFile(packageJsonPath, 'utf8')) as PackageJsonLike;

      // Read package-lock.json for detailed version info
      let packageLock: PackageLockFile = {};
      try {
        const packageLockPath = path.join(this.options.projectRoot, 'package-lock.json');
        packageLock = JSON.parse(await fs.readFile(packageLockPath, 'utf8')) as PackageLockFile;
      } catch {
        // package-lock.json might not exist
      }

      // Process dependencies
      const deps: Record<string, string> = {
        ...(packageJson.dependencies ?? {}),
        ...(this.options.includeDevDependencies ? (packageJson.devDependencies ?? {}) : {}),
      };

      for (const [name, version] of Object.entries(deps)) {
        const lockInfo = packageLock.packages?.[`node_modules/${name}`] ?? {};
        const resolvedVersion = lockInfo.version ?? version;

        const component: SBOMComponent = {
          name,
          version: resolvedVersion,
          type: 'library',
          ...(lockInfo.description ? { description: lockInfo.description } : {}),
          ...(this.options.includeLicenses ? { licenses: this.extractLicenses(lockInfo) } : {}),
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
    let packageJson: PackageJsonLike = {};
    try {
      const packageJsonPath = path.join(this.options.projectRoot, 'package.json');
      packageJson = JSON.parse(await fs.readFile(packageJsonPath, 'utf8')) as PackageJsonLike;
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
  private async extractDependencyGraph(): Promise<{ ref: string; dependsOn?: string[] }[]> {
    const dependencies: { ref: string; dependsOn?: string[] }[] = [];

    try {
      const packageLockPath = path.join(this.options.projectRoot, 'package-lock.json');
      const packageLock = JSON.parse(await fs.readFile(packageLockPath, 'utf8')) as PackageLockFile;

      if (packageLock.packages) {
        for (const [packagePath, packageInfo] of Object.entries(packageLock.packages)) {
          if (packagePath === '' || !packageInfo.dependencies) continue;

          const packageName = packagePath.replace('node_modules/', '');
          const dependsOn = Object.keys(packageInfo.dependencies);

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
   * Extract vulnerabilities from OSV using normalized component metadata.
   * Fallback behavior is non-fatal by design: warn + empty result.
   */
  private async extractVulnerabilities(components: SBOMComponent[]): Promise<SBOMVulnerability[]> {
    const normalized = this.normalizeVulnerabilityComponents(components);
    if (normalized.length === 0) {
      console.warn('[SBOM] No vulnerability-queryable components found; skipping OSV lookup.');
      return [];
    }

    const batch = await this.queryOsvBatch(normalized);
    if (!batch) return [];

    const results = Array.isArray(batch.results) ? batch.results : [];
    if (results.length !== normalized.length) {
      console.warn(
        `[SBOM] OSV response count mismatch (queries=${normalized.length}, results=${results.length}).`,
      );
    }

    const vulnerabilities: SBOMVulnerability[] = [];
    for (let i = 0; i < normalized.length; i += 1) {
      const component = normalized[i]!;
      const result = results[i];
      const vulns = Array.isArray(result?.vulns) ? result.vulns : [];
      for (const vuln of vulns) {
        vulnerabilities.push(this.mapOsvVulnerability(component, vuln));
      }
    }

    vulnerabilities.sort((a, b) => {
      if (a.bom_ref !== b.bom_ref) return a.bom_ref.localeCompare(b.bom_ref);
      return a.id.localeCompare(b.id);
    });

    return vulnerabilities;
  }

  private normalizeVulnerabilityComponents(components: SBOMComponent[]): NormalizedVulnerabilityComponent[] {
    const normalized: NormalizedVulnerabilityComponent[] = [];
    const seen = new Set<string>();

    for (const component of components) {
      if (component.type !== 'library') continue;

      const name = component.name.trim();
      const version = this.normalizeVersionForVulnerabilityQuery(component.version);
      const ecosystem = this.inferEcosystemForVulnerabilityQuery(component);

      if (!name || !version || !ecosystem) {
        continue;
      }

      const key = `${ecosystem}:${name}@${version}`;
      if (seen.has(key)) continue;
      seen.add(key);

      normalized.push({
        bomRef: component.name,
        name,
        version,
        ecosystem,
      });
    }

    return normalized;
  }

  private normalizeVersionForVulnerabilityQuery(rawVersion: string): string | null {
    const trimmed = rawVersion.trim();
    if (!trimmed) return null;
    if (/^(workspace|file|link|git):/i.test(trimmed)) return null;

    // Accept exact resolved versions and normalize common semver prefixes when lockfile is unavailable.
    const normalized = trimmed.replace(/^[~^<>=\s]+/, '').replace(/^v(?=\d)/i, '');
    if (!normalized || /[\s|*]/.test(normalized)) return null;
    return normalized;
  }

  private inferEcosystemForVulnerabilityQuery(component: SBOMComponent): string | null {
    if (component.purl?.startsWith('pkg:')) {
      const withoutPrefix = component.purl.slice(4);
      const slashIndex = withoutPrefix.indexOf('/');
      if (slashIndex > 0) {
        const purlEcosystem = withoutPrefix.slice(0, slashIndex).toLowerCase();
        switch (purlEcosystem) {
          case 'npm':
            return 'npm';
          case 'maven':
            return 'Maven';
          case 'pypi':
            return 'PyPI';
          case 'nuget':
            return 'NuGet';
          case 'crates':
            return 'crates.io';
          case 'packagist':
            return 'Packagist';
          case 'rubygems':
            return 'RubyGems';
          case 'go':
          case 'golang':
            return 'Go';
          default:
            return null;
        }
      }
    }

    // Without purl, ecosystem cannot be inferred safely.
    return null;
  }

  private async queryOsvBatch(components: NormalizedVulnerabilityComponent[]): Promise<OsvBatchResponse | null> {
    const endpoint = process.env['SBOM_OSV_ENDPOINT'] ?? 'https://api.osv.dev/v1/querybatch';
    const timeoutRaw = Number.parseInt(process.env['SBOM_OSV_TIMEOUT_MS'] ?? '10000', 10);
    const timeoutMs = Number.isFinite(timeoutRaw) && timeoutRaw > 0 ? timeoutRaw : 10000;
    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), timeoutMs);

    const body = {
      queries: components.map((component) => ({
        package: {
          ecosystem: component.ecosystem,
          name: component.name,
        },
        version: component.version,
      })),
    };

    try {
      const response = await fetch(endpoint, {
        method: 'POST',
        headers: {
          'content-type': 'application/json',
        },
        body: JSON.stringify(body),
        signal: controller.signal,
      });

      if (!response.ok) {
        const retryAfter = response.headers.get('retry-after');
        if (response.status === 429) {
          console.warn(
            `[SBOM] OSV rate-limited (HTTP 429). retry-after=${retryAfter ?? 'unknown'}s. Returning empty vulnerabilities.`,
          );
        } else {
          console.warn(`[SBOM] OSV query failed: HTTP ${response.status}. Returning empty vulnerabilities.`);
        }
        return null;
      }

      const payload = (await response.json()) as OsvBatchResponse;
      if (!payload || !Array.isArray(payload.results)) {
        console.warn('[SBOM] OSV response did not include a valid results array. Returning empty vulnerabilities.');
        return null;
      }

      return payload;
    } catch (error) {
      const reason = error instanceof Error ? error.message : String(error);
      console.warn(`[SBOM] OSV query threw an error (${reason}). Returning empty vulnerabilities.`);
      return null;
    } finally {
      clearTimeout(timeout);
    }
  }

  private mapOsvVulnerability(
    component: NormalizedVulnerabilityComponent,
    vulnerability: OsvVulnerability,
  ): SBOMVulnerability {
    const id = vulnerability.id?.trim() || 'OSV-UNKNOWN';
    const summary = vulnerability.summary?.trim();
    const details = vulnerability.details?.trim();
    const score = this.parseCvssScore(vulnerability.severity);
    const severity = this.mapSeverityFromOsv(vulnerability, score);
    const references = Array.isArray(vulnerability.references) ? vulnerability.references : [];
    const cwes = vulnerability.database_specific?.cwes
      ?.map((value) => Number.parseInt(value.replace(/^CWE-/i, ''), 10))
      .filter((value) => Number.isInteger(value));

    return {
      bom_ref: component.bomRef,
      id,
      source: {
        name: 'OSV',
        url: `https://osv.dev/vulnerability/${id}`,
      },
      ratings: [
        {
          source: 'OSV',
          ...(score !== undefined ? { score } : {}),
          severity,
          method: 'OSV',
        },
      ],
      ...(Array.isArray(cwes) && cwes.length > 0 ? { cwes } : {}),
      description: summary || details || `Vulnerability in ${component.name}@${component.version}`,
      advisories: references
        .filter((reference): reference is OsvReference & { url: string } => Boolean(reference?.url))
        .map((reference) => ({
          ...(reference.type ? { title: reference.type } : {}),
          url: reference.url,
        })),
    };
  }

  private mapSeverityFromOsv(vulnerability: OsvVulnerability, score?: number): 'low' | 'medium' | 'high' | 'critical' {
    if (score !== undefined) {
      if (score >= 9.0) return 'critical';
      if (score >= 7.0) return 'high';
      if (score >= 4.0) return 'medium';
      return 'low';
    }

    const vectorSeverity = this.parseCvssSeverityFromVector(vulnerability.severity);
    if (vectorSeverity) return vectorSeverity;

    const dbSeverity = vulnerability.database_specific?.severity?.toLowerCase();
    if (dbSeverity === 'critical') return 'critical';
    if (dbSeverity === 'high') return 'high';
    if (dbSeverity === 'medium' || dbSeverity === 'moderate') return 'medium';
    if (dbSeverity === 'low') return 'low';
    return 'medium';
  }

  private parseCvssScore(severities?: OsvSeverity[]): number | undefined {
    if (!Array.isArray(severities)) return undefined;
    for (const severity of severities) {
      const rawScore = severity.score?.trim();
      if (!rawScore) continue;
      const parsed = Number.parseFloat(rawScore);
      if (Number.isFinite(parsed)) return parsed;
    }
    return undefined;
  }

  private parseCvssSeverityFromVector(
    severities?: OsvSeverity[],
  ): 'low' | 'medium' | 'high' | 'critical' | undefined {
    if (!Array.isArray(severities)) return undefined;
    for (const severity of severities) {
      const rawScore = severity.score?.trim();
      if (!rawScore || !/^CVSS:/i.test(rawScore)) continue;

      const metrics = new Map<string, string>();
      for (const segment of rawScore.split('/').slice(1)) {
        const [key, value] = segment.split(':');
        if (!key || !value) continue;
        metrics.set(key.toUpperCase(), value.toUpperCase());
      }

      let risk = 0;
      const av = metrics.get('AV');
      if (av === 'N') risk += 1.5;
      else if (av === 'A') risk += 1.0;
      else if (av === 'L') risk += 0.5;

      if (metrics.get('AC') === 'L') risk += 1.0;
      if (metrics.get('PR') === 'N') risk += 1.0;
      else if (metrics.get('PR') === 'L') risk += 0.5;
      if (metrics.get('UI') === 'N') risk += 0.5;
      if (metrics.get('S') === 'C') risk += 1.0;

      for (const axis of ['C', 'I', 'A']) {
        const value = metrics.get(axis);
        if (value === 'H') risk += 2.0;
        else if (value === 'L') risk += 1.0;
      }

      if (risk >= 9.0) return 'critical';
      if (risk >= 7.0) return 'high';
      if (risk >= 4.0) return 'medium';
      return 'low';
    }
    return undefined;
  }

  /**
   * Extract license information
   */
  private extractLicenses(packageInfo: PackageLockEntry): string[] {
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
