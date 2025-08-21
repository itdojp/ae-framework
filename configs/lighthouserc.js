const fs = require('fs');
const path = require('path');

/**
 * Load quality policy from centralized configuration
 */
function loadLighthouseConfig() {
  try {
    const policyPath = path.join(process.cwd(), 'policy', 'quality.json');
    const policyContent = fs.readFileSync(policyPath, 'utf-8');
    const policy = JSON.parse(policyContent);
    
    // Get environment from NODE_ENV or default to 'ci'
    const environment = process.env.NODE_ENV === 'development' ? 'development' : 'ci';
    
    // Apply environment overrides if specified
    if (environment && policy.environments[environment]) {
      const overrides = policy.environments[environment].overrides;
      Object.entries(overrides).forEach(([overridePath, value]) => {
        const pathParts = overridePath.split('.');
        let current = policy.quality;
        
        for (let i = 0; i < pathParts.length - 1; i++) {
          current = current[pathParts[i]];
        }
        
        current[pathParts[pathParts.length - 1]] = value;
      });
    }
    
    const lighthouseGate = policy.quality.lighthouse;
    if (!lighthouseGate) {
      console.warn('⚠️  No lighthouse configuration in quality policy, using defaults');
      return getDefaultConfig();
    }
    
    console.log(`📋 Using centralized lighthouse policy (${environment} environment)`);
    console.log(`   Policy version: ${policy.version}`);
    
    return {
      ci: {
        collect: {
          staticDistDir: './apps/web/dist',
          numberOfRuns: lighthouseGate.config?.numberOfRuns || 3,
          url: lighthouseGate.config?.urls || [
            'http://localhost:3000',
            'http://localhost:3000/health'
          ]
        },
        assert: {
          assertions: {
            'categories:performance': lighthouseGate.enforcement === 'off' ? 'off' : 
              [lighthouseGate.enforcement === 'strict' ? 'error' : 'warn', 
               { minScore: (lighthouseGate.thresholds.performance || 90) / 100 }],
            'categories:accessibility': lighthouseGate.enforcement === 'off' ? 'off' : 
              [lighthouseGate.enforcement === 'strict' ? 'error' : 'warn', 
               { minScore: (lighthouseGate.thresholds.accessibility || 95) / 100 }],
            'categories:best-practices': lighthouseGate.enforcement === 'off' ? 'off' : 
              [lighthouseGate.enforcement === 'strict' ? 'error' : 'warn', 
               { minScore: (lighthouseGate.thresholds.bestPractices || 85) / 100 }],
            'categories:seo': lighthouseGate.enforcement === 'off' ? 'off' : 
              [lighthouseGate.enforcement === 'strict' ? 'error' : 'warn', 
               { minScore: (lighthouseGate.thresholds.seo || 80) / 100 }],
            'categories:pwa': lighthouseGate.thresholds.pwa === 'off' ? 'off' : 
              [lighthouseGate.enforcement === 'strict' ? 'error' : 'warn', 
               { minScore: 0.8 }]
          }
        },
        upload: {
          target: 'temporary-public-storage'
        },
        server: {
          port: 9009,
          storage: './lighthouse-reports'
        }
      }
    };
    
  } catch (error) {
    console.warn(`⚠️  Could not load quality policy for lighthouse: ${error.message}`);
    console.log('🔄 Using default lighthouse configuration');
    return getDefaultConfig();
  }
}

function getDefaultConfig() {
  return {
    ci: {
      collect: {
        staticDistDir: './apps/web/dist',
        numberOfRuns: 3,
        url: [
          'http://localhost:3000',
          'http://localhost:3000/health'
        ]
      },
      assert: {
        assertions: {
          'categories:performance': ['warn', { minScore: 0.8 }],
          'categories:accessibility': ['error', { minScore: 0.9 }],
          'categories:best-practices': ['warn', { minScore: 0.85 }],
          'categories:seo': ['warn', { minScore: 0.8 }],
          'categories:pwa': 'off'
        }
      },
      upload: {
        target: 'temporary-public-storage'
      },
      server: {
        port: 9009,
        storage: './lighthouse-reports'
      }
    }
  };
}

module.exports = loadLighthouseConfig();