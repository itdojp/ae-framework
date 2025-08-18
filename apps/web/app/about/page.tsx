import { Button, Dialog, DialogContent, DialogDescription, DialogHeader, DialogTitle, DialogTrigger } from '@ae-framework/ui';

export default function AboutPage() {
  return (
    <main className="container mx-auto px-4 py-8">
      <div className="max-w-4xl">
        <h1 className="text-3xl font-bold mb-6">About ae-framework</h1>
        
        <div className="prose prose-gray max-w-none">
          <p className="text-lg text-gray-600 mb-8">
            ae-framework is a comprehensive AI-enhanced development framework that automates 
            the entire software development lifecycle from requirements analysis to production deployment.
          </p>
          
          <div className="grid grid-cols-1 md:grid-cols-2 gap-8 mb-12">
            <div>
              <h2 className="text-xl font-semibold mb-4">Phase-Based Development</h2>
              <div className="space-y-3">
                <div className="border-l-4 border-primary-500 pl-4">
                  <h3 className="font-medium">Phase 1-2: Requirements</h3>
                  <p className="text-sm text-gray-600">Intent analysis and natural language processing</p>
                </div>
                <div className="border-l-4 border-primary-500 pl-4">
                  <h3 className="font-medium">Phase 3: User Stories</h3>
                  <p className="text-sm text-gray-600">INVEST-compliant user story generation</p>
                </div>
                <div className="border-l-4 border-primary-500 pl-4">
                  <h3 className="font-medium">Phase 4-5: Modeling</h3>
                  <p className="text-sm text-gray-600">Validation and domain-driven design</p>
                </div>
                <div className="border-l-4 border-success pl-4">
                  <h3 className="font-medium">Phase 6: UI/UX</h3>
                  <p className="text-sm text-gray-600">Automated component generation with accessibility</p>
                </div>
              </div>
            </div>
            
            <div>
              <h2 className="text-xl font-semibold mb-4">Key Features</h2>
              <ul className="space-y-2">
                <li className="flex items-start">
                  <span className="inline-block w-2 h-2 bg-primary-500 rounded-full mt-2 mr-3"></span>
                  <span>Automated UI component generation from domain models</span>
                </li>
                <li className="flex items-start">
                  <span className="inline-block w-2 h-2 bg-primary-500 rounded-full mt-2 mr-3"></span>
                  <span>Built-in accessibility validation (WCAG 2.1 AA)</span>
                </li>
                <li className="flex items-start">
                  <span className="inline-block w-2 h-2 bg-primary-500 rounded-full mt-2 mr-3"></span>
                  <span>Design token integration with Figma/Sketch</span>
                </li>
                <li className="flex items-start">
                  <span className="inline-block w-2 h-2 bg-primary-500 rounded-full mt-2 mr-3"></span>
                  <span>Comprehensive quality gates and CI/CD integration</span>
                </li>
                <li className="flex items-start">
                  <span className="inline-block w-2 h-2 bg-primary-500 rounded-full mt-2 mr-3"></span>
                  <span>End-to-end testing with Playwright</span>
                </li>
                <li className="flex items-start">
                  <span className="inline-block w-2 h-2 bg-primary-500 rounded-full mt-2 mr-3"></span>
                  <span>Visual regression testing with Chromatic</span>
                </li>
              </ul>
            </div>
          </div>
          
          <div className="bg-gray-50 rounded-lg p-6 mb-8">
            <h2 className="text-xl font-semibold mb-4">Technology Stack</h2>
            <div className="grid grid-cols-2 md:grid-cols-4 gap-4">
              <div>
                <h3 className="font-medium text-sm text-gray-700 mb-2">Frontend</h3>
                <ul className="text-sm text-gray-600 space-y-1">
                  <li>Next.js 14</li>
                  <li>React 18</li>
                  <li>TypeScript</li>
                  <li>Tailwind CSS</li>
                </ul>
              </div>
              <div>
                <h3 className="font-medium text-sm text-gray-700 mb-2">UI Components</h3>
                <ul className="text-sm text-gray-600 space-y-1">
                  <li>Radix UI</li>
                  <li>shadcn/ui</li>
                  <li>Lucide Icons</li>
                  <li>CVA</li>
                </ul>
              </div>
              <div>
                <h3 className="font-medium text-sm text-gray-700 mb-2">State & Forms</h3>
                <ul className="text-sm text-gray-600 space-y-1">
                  <li>TanStack Query</li>
                  <li>React Hook Form</li>
                  <li>Zod Validation</li>
                  <li>Next Intl</li>
                </ul>
              </div>
              <div>
                <h3 className="font-medium text-sm text-gray-700 mb-2">Quality</h3>
                <ul className="text-sm text-gray-600 space-y-1">
                  <li>ESLint + A11y</li>
                  <li>Playwright</li>
                  <li>Storybook</li>
                  <li>Lighthouse CI</li>
                </ul>
              </div>
            </div>
          </div>
          
          <div className="text-center">
            <Dialog>
              <DialogTrigger asChild>
                <Button>View Technical Specifications</Button>
              </DialogTrigger>
              <DialogContent className="max-w-2xl">
                <DialogHeader>
                  <DialogTitle>Technical Specifications</DialogTitle>
                  <DialogDescription>
                    Detailed technical information about ae-framework architecture
                  </DialogDescription>
                </DialogHeader>
                <div className="mt-4 space-y-4">
                  <div>
                    <h4 className="font-medium mb-2">Browser Support</h4>
                    <p className="text-sm text-gray-600">
                      Chrome 90+, Firefox 88+, Safari 14+, Edge 90+
                    </p>
                  </div>
                  <div>
                    <h4 className="font-medium mb-2">Internationalization</h4>
                    <p className="text-sm text-gray-600">
                      Default locale: ja-JP, with support for en-US and additional locales
                    </p>
                  </div>
                  <div>
                    <h4 className="font-medium mb-2">Accessibility</h4>
                    <p className="text-sm text-gray-600">
                      WCAG 2.1 AA compliant with automated testing via axe-core
                    </p>
                  </div>
                  <div>
                    <h4 className="font-medium mb-2">Performance</h4>
                    <p className="text-sm text-gray-600">
                      Lighthouse Performance Score ≥75, Core Web Vitals optimization
                    </p>
                  </div>
                </div>
              </DialogContent>
            </Dialog>
          </div>
        </div>
      </div>
    </main>
  );
}