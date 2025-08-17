module.exports = {
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