import { getRequestConfig } from 'next-intl/server';

const locales = ['ja', 'en'] as const;
type AppLocale = (typeof locales)[number];

function isAppLocale(value: string | undefined): value is AppLocale {
  return locales.includes(value as AppLocale);
}

export default getRequestConfig(async ({ locale, requestLocale }) => {
  // Use the detected locale from the context and fall back to ja for pages
  // that render outside a locale segment.
  const requestedLocale = locale ?? await requestLocale;
  const resolvedLocale = isAppLocale(requestedLocale) ? requestedLocale : 'ja';

  return {
    locale: resolvedLocale,
    messages: (await import(`./messages/${resolvedLocale}.json`)).default,
  };
});
