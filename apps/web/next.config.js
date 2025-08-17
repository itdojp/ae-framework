const createNextIntlPlugin = require('next-intl/plugin');

const withNextIntl = createNextIntlPlugin();

/** @type {import('next').NextConfig} */
const nextConfig = {
  experimental: {
    transpilePackages: ['@ae-framework/ui', '@ae-framework/design-tokens'],
  },
  eslint: {
    dirs: ['app', 'components', 'lib'],
  },
};

module.exports = withNextIntl(nextConfig);