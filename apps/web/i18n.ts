import { getRequestConfig } from 'next-intl/server';

export default getRequestConfig(async ({locale}) => {
  // Use the detected locale from the context
  // Default to 'ja' if no locale is provided
  const resolvedLocale = locale || 'ja';
 
  return {
    messages: (await import(`./messages/${resolvedLocale}.json`)).default
  };
});