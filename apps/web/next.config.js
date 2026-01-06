const createNextIntlPlugin = require('next-intl/plugin');
const path = require('path');

const withNextIntl = createNextIntlPlugin();

/** @type {import('next').NextConfig} */
const nextConfig = {
  transpilePackages: ['@ae-framework/ui', '@ae-framework/design-tokens'],
  eslint: {
    dirs: ['app', 'components', 'lib'],
  },
  webpack: (config) => {
    config.resolve = config.resolve || {};
    config.resolve.alias = {
      ...(config.resolve.alias || {}),
      '@ae-framework/ui/components': path.resolve(__dirname, '../../packages/ui/src'),
    };
    return config;
  },
};

module.exports = withNextIntl(nextConfig);
