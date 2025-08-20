/** @type {import('dependency-cruiser').IConfiguration} */
module.exports = {
  forbidden: [
    {
      name: 'no-circular',
      severity: 'error',
      comment: 'Circular dependencies are not allowed',
      from: {},
      to: {
        circular: true
      }
    },
    {
      name: 'no-orphans',
      severity: 'warn',
      comment: 'Modules should be reachable from the entry point',
      from: {
        orphan: true,
        pathNot: ['\\.d\\.ts$', '\\.test\\.(ts|js)$', '\\.spec\\.(ts|js)$']
      },
      to: {}
    },
    {
      name: 'no-deprecated-core',
      severity: 'warn',
      comment: 'Node.js core modules should not be deprecated',
      from: {},
      to: {
        dependencyTypes: ['core'],
        path: ['^(punycode|domain)$']
      }
    }
  ],
  options: {
    doNotFollow: {
      path: 'node_modules'
    },
    includeOnly: {
      path: '^src'
    },
    tsPreCompilationDeps: true,
    tsConfig: {
      fileName: 'tsconfig.json'
    },
    enhancedResolveOptions: {
      extensions: ['.js', '.jsx', '.ts', '.tsx', '.d.ts']
    },
    reporterOptions: {
      dot: {
        collapsePattern: 'node_modules/(@[^/]+/[^/]+|[^/]+)'
      },
      archi: {
        collapsePattern: '^src/[^/]+|node_modules/(@[^/]+/[^/]+|[^/]+)'
      }
    }
  }
};