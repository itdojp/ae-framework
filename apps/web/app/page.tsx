import { useTranslations } from 'next-intl';
import { Button } from '@ae-framework/ui';

export default function HomePage() {
  const t = useTranslations('HomePage');

  return (
    <main className="container mx-auto px-4 py-8">
      <div className="text-center">
        <h1 className="text-4xl font-bold text-gray-900 mb-4">
          {t('title')}
        </h1>
        <p className="text-xl text-gray-600 mb-8">
          {t('subtitle')}
        </p>
        <div className="space-x-4">
          <Button>{t('getStarted')}</Button>
          <Button variant="outline">{t('learnMore')}</Button>
        </div>
      </div>
      
      <div className="mt-16 grid grid-cols-1 md:grid-cols-3 gap-8">
        <div className="text-center">
          <h3 className="text-lg font-semibold mb-2">Phase 6 UI/UX</h3>
          <p className="text-gray-600">
            Automated component generation with accessibility and design tokens
          </p>
        </div>
        <div className="text-center">
          <h3 className="text-lg font-semibold mb-2">Quality Gates</h3>
          <p className="text-gray-600">
            Built-in A11y, E2E, and performance validation
          </p>
        </div>
        <div className="text-center">
          <h3 className="text-lg font-semibold mb-2">Production Ready</h3>
          <p className="text-gray-600">
            From requirements to deployment with CI/CD integration
          </p>
        </div>
      </div>
    </main>
  );
}