import createMiddleware from 'next-intl/middleware';

export default createMiddleware({
  // A list of all locales that are supported
  locales: ['ja', 'en'],
  
  // Used when no locale matches
  defaultLocale: 'ja'
});

export const config = {
  // Match only internationalized pathnames
  matcher: ['/', '/(ja|en)/:path*']
};