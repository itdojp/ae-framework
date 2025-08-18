const { tailwindTokens } = require('@ae-framework/design-tokens/dist/tailwind');

/** @type {import('tailwindcss').Config} */
module.exports = {
  content: [
    './stories/**/*.{js,ts,jsx,tsx,mdx}',
    '../../packages/ui/src/**/*.{js,ts,jsx,tsx}',
  ],
  theme: {
    extend: tailwindTokens,
  },
  plugins: [],
};