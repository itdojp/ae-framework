/**
 * UI/UX Task Adapter
 *
 * Provides task-oriented UI/UX generation that can be consumed by
 * UIUXAgentAdapter and direct task workflows.
 */

import { FormalAgent } from './formal-agent.js';
import type { FormalAgentConfig } from './formal-agent.js';
import type { TaskRequest, TaskResponse } from './task-types.js';
import type {
  DesignSystem,
  Prototype,
  UIComponent,
  UIUXInput,
  UIUXOutput,
  UserFlow,
  UserStory,
  Wireframe,
  WireframeComponent,
} from './interfaces/standard-interfaces.js';

type UIUXTaskType =
  | 'generate-uiux'
  | 'wireframe'
  | 'user-flow'
  | 'design-system'
  | 'accessibility'
  | 'prototype'
  | 'generic';

export interface UIUXGenerationResult {
  output: UIUXOutput;
  warnings: string[];
  qualityScore: number;
}

export class UIUXTaskAdapter {
  private agent: FormalAgent;

  constructor() {
    const config: FormalAgentConfig = {
      outputFormat: 'openapi',
      validationLevel: 'comprehensive',
      generateDiagrams: true,
      enableModelChecking: false,
    };
    this.agent = new FormalAgent(config);
  }

  async handleUIUXTask(request: TaskRequest): Promise<TaskResponse> {
    const taskType = this.classifyTask(request.description, request.prompt);
    const focus = this.describeTaskFocus(taskType);

    return {
      summary: `UI/UX task analysis complete (${taskType})`,
      analysis: [
        '# UI/UX Task Analysis',
        '',
        `- Focus: ${focus}`,
        `- Input length: ${request.prompt.length} chars`,
        '- Suggested output: wireframes, user flow, component contracts',
      ].join('\n'),
      recommendations: this.recommendByTaskType(taskType),
      nextActions: [
        'Validate personas and primary use cases',
        'Review wireframe coverage against user stories',
        'Align component contracts with domain entities',
      ],
      warnings: [],
      shouldBlockProgress: false,
    };
  }

  async generateUIUXArtifacts(input: UIUXInput): Promise<UIUXGenerationResult> {
    const warnings = this.validateInput(input);
    const requirements = this.buildRequirementSummary(input);
    try {
      await this.agent.createAPISpecification(requirements, 'openapi');
    } catch {
      // API spec generation is best-effort for hints; UI/UX artifacts should still be generated.
      warnings.push('API-style endpoint inference failed; continuing with UI/UX artifact generation');
    }

    const components = this.generateUIComponents(input);
    const output: UIUXOutput = {
      wireframes: this.generateWireframes(input),
      userFlows: this.generateUserFlows(input),
      components,
      designSystem: this.generateDesignSystem(components),
      prototypes: this.generatePrototypes(input, components),
    };

    return {
      output,
      warnings,
      qualityScore: this.calculateQualityScore(output, warnings),
    };
  }

  private classifyTask(description: string, prompt: string): UIUXTaskType {
    const text = `${description} ${prompt}`.toLowerCase();

    if (text.includes('wireframe') || text.includes('ワイヤーフレーム') || text.includes('ワイアーフレーム')) {
      return 'wireframe';
    }
    if (
      text.includes('flow') ||
      text.includes('journey') ||
      text.includes('画面遷移') ||
      text.includes('画面フロー') ||
      text.includes('ユーザーフロー') ||
      text.includes('ユーザー フロー') ||
      text.includes('ユーザージャーニー') ||
      text.includes('ユーザー ジャーニー')
    ) {
      return 'user-flow';
    }
    if (text.includes('design system') || text.includes('token') || text.includes('デザインシステム')) {
      return 'design-system';
    }
    if (
      text.includes('accessibility') ||
      text.includes('a11y') ||
      text.includes('アクセシビリティ') ||
      text.includes('バリアフリー')
    ) {
      return 'accessibility';
    }
    if (text.includes('prototype') || text.includes('プロトタイプ')) {
      return 'prototype';
    }
    if (text.includes('ui') || text.includes('ux') || text.includes('screen') || text.includes('画面')) {
      return 'generate-uiux';
    }
    return 'generic';
  }

  private describeTaskFocus(taskType: UIUXTaskType): string {
    switch (taskType) {
      case 'wireframe':
        return 'Screen-level structure and key component placement';
      case 'user-flow':
        return 'Primary user journey and transition design';
      case 'design-system':
        return 'Reusable components and visual tokens';
      case 'accessibility':
        return 'A11y guardrails and keyboard/screen-reader considerations';
      case 'prototype':
        return 'Interactive transitions and clickable path definition';
      case 'generate-uiux':
        return 'End-to-end UI/UX artifact generation';
      default:
        return 'General UI/UX planning and decomposition';
    }
  }

  private recommendByTaskType(taskType: UIUXTaskType): string[] {
    switch (taskType) {
      case 'wireframe':
        return ['Define critical actions per screen', 'Keep low-fidelity first and iterate quickly'];
      case 'user-flow':
        return ['Limit each flow to one user intent', 'Define explicit alternate/error paths'];
      case 'design-system':
        return ['Normalize spacing/typography scales', 'Map domain entities to UI component contracts'];
      case 'accessibility':
        return ['Ensure semantic labels and focus order', 'Document color contrast constraints'];
      case 'prototype':
        return ['Prioritize key happy paths', 'Annotate transitions with trigger and expected feedback'];
      case 'generate-uiux':
        return ['Link each story to at least one screen', 'Keep component props traceable to domain terms'];
      default:
        return ['Provide user personas and core scenarios', 'Define expected outputs before implementation'];
    }
  }

  private validateInput(input: UIUXInput): string[] {
    const warnings: string[] = [];
    if (!input.stakeholders || input.stakeholders.length === 0) {
      warnings.push('No stakeholders provided; default persona assumptions will be used');
    }
    if (!input.userStories || input.userStories.stories.length === 0) {
      warnings.push('No user stories provided; generated artifacts may be generic');
    }
    if (!input.domainModel || input.domainModel.entities.length === 0) {
      warnings.push('No domain entities provided; component contracts may be coarse-grained');
    }
    return warnings;
  }

  private buildRequirementSummary(input: UIUXInput): string {
    const storyLines = input.userStories.stories
      .map((story) => `- ${story.title}: ${story.description}`)
      .join('\n');
    const entityLines = input.domainModel.entities
      .map((entity) => `- ${entity.name}(${entity.attributes.map((attr) => attr.name).join(', ')})`)
      .join('\n');
    return [
      'UI/UX generation requirements',
      'User stories:',
      storyLines,
      'Domain entities:',
      entityLines,
    ].join('\n');
  }

  private generateWireframes(input: UIUXInput): Wireframe[] {
    const wireframes: Wireframe[] = input.userStories.stories.map((story, index) => ({
      name: `wireframe_${story.id || index + 1}`,
      type: 'low-fidelity' as const,
      components: this.generateWireframeComponents(story),
      userFlow: story.title || `User Flow ${index + 1}`,
    }));

    wireframes.push({
      name: 'landing_page',
      type: 'high-fidelity',
      components: [
        {
          type: 'header',
          properties: { title: 'Welcome', navigation: true },
          children: [
            { type: 'logo', properties: { position: 'left' } },
            { type: 'navigation', properties: { items: ['Home', 'About', 'Contact'] } },
          ],
        },
        { type: 'hero_section', properties: { title: 'Main Heading', subtitle: 'Description' } },
        { type: 'footer', properties: { copyright: true, links: true } },
      ],
      userFlow: 'Main Landing Experience',
    });

    return wireframes;
  }

  private generateWireframeComponents(story: UserStory): WireframeComponent[] {
    const components: WireframeComponent[] = [];
    const description = story.description.toLowerCase();

    if (description.includes('login') || description.includes('auth')) {
      components.push({ type: 'form', properties: { fields: ['username', 'password'], submitButton: true } });
    }
    if (description.includes('list') || description.includes('view')) {
      components.push({ type: 'list', properties: { itemType: 'data', pagination: true } });
    }
    if (description.includes('create') || description.includes('add')) {
      components.push({ type: 'form', properties: { fields: ['title', 'description'], submitButton: true } });
    }
    if (components.length === 0) {
      components.push(
        { type: 'container', properties: { layout: 'vertical' } },
        { type: 'text', properties: { content: story.description } },
      );
    }
    return components;
  }

  private generateUserFlows(input: UIUXInput): UserFlow[] {
    const flowGroups = this.groupStoriesByFlow(input.userStories.stories);
    return Object.entries(flowGroups).map(([name, stories]) => ({
      name,
      steps: stories.map((story, index) => ({
        action: story.iWant || story.description,
        screen: `screen_${story.id || index + 1}`,
        ...(index < stories.length - 1
          ? { nextStep: `screen_${stories[index + 1]?.id || index + 2}` }
          : {}),
        conditions: story.acceptanceCriteria || [],
      })),
      triggers: stories.map((story) => story.asA || 'user'),
      outcomes: stories.map((story) => story.soThat || 'achieve goal'),
    }));
  }

  private groupStoriesByFlow(stories: UserStory[]): Record<string, UserStory[]> {
    const groups: Record<string, UserStory[]> = {
      'Authentication Flow': [],
      'Main User Flow': [],
      'Admin Flow': [],
    };

    for (const story of stories) {
      const desc = story.description?.toLowerCase() || '';
      const role = story.asA?.toLowerCase() || '';
      if (desc.includes('login') || desc.includes('register') || desc.includes('auth')) {
        groups['Authentication Flow']?.push(story);
      } else if (role.includes('admin') || desc.includes('manage')) {
        groups['Admin Flow']?.push(story);
      } else {
        groups['Main User Flow']?.push(story);
      }
    }

    return Object.fromEntries(Object.entries(groups).filter(([, entries]) => entries.length > 0));
  }

  private generateUIComponents(input: UIUXInput): UIComponent[] {
    const components: UIComponent[] = [];

    for (const entity of input.domainModel.entities) {
      components.push({
        name: `${entity.name}Card`,
        type: 'display',
        props: entity.attributes.map((attr) => ({
          name: attr.name,
          type: attr.type,
          required: attr.required,
          description: attr.description ?? '',
        })),
        states: [
          { name: 'loading', description: 'Data is being loaded', triggers: ['fetch'] },
          { name: 'loaded', description: 'Data has been loaded', triggers: ['success'] },
          { name: 'error', description: 'Error occurred', triggers: ['failure'] },
        ],
        interactions: [
          { event: 'click', action: 'view_details', feedback: 'Navigate to detail view' },
          { event: 'hover', action: 'highlight', feedback: 'Visual feedback on hover' },
        ],
      });

      components.push({
        name: `${entity.name}Form`,
        type: 'input',
        props: entity.attributes.map((attr) => ({
          name: attr.name,
          type: this.mapTypeToInputType(attr.type),
          required: attr.required,
          description: attr.description ?? '',
        })),
        states: [
          { name: 'pristine', description: 'Form not yet touched', triggers: ['init'] },
          { name: 'dirty', description: 'Form has been modified', triggers: ['input'] },
          { name: 'submitting', description: 'Form is being submitted', triggers: ['submit'] },
          { name: 'submitted', description: 'Form has been submitted', triggers: ['success'] },
        ],
        interactions: [
          { event: 'submit', action: 'validate_and_save', feedback: 'Show validation errors or success message' },
          { event: 'input', action: 'validate_field', feedback: 'Real-time validation feedback' },
        ],
      });
    }

    components.push(
      {
        name: 'NavigationHeader',
        type: 'navigation',
        props: [
          { name: 'title', type: 'string', required: true },
          { name: 'menuItems', type: 'array', required: true },
          { name: 'userProfile', type: 'object', required: false },
        ],
        states: [
          { name: 'expanded', description: 'Mobile menu expanded', triggers: ['toggle'] },
          { name: 'collapsed', description: 'Mobile menu collapsed', triggers: ['toggle'] },
        ],
        interactions: [{ event: 'menuClick', action: 'navigate', feedback: 'Navigate to selected page' }],
      },
      {
        name: 'SearchBar',
        type: 'input',
        props: [
          { name: 'placeholder', type: 'string', required: false },
          { name: 'onSearch', type: 'function', required: true },
        ],
        states: [
          { name: 'empty', description: 'No search query', triggers: ['clear'] },
          { name: 'typing', description: 'User is typing', triggers: ['input'] },
          { name: 'searching', description: 'Search in progress', triggers: ['search'] },
        ],
        interactions: [{ event: 'enter', action: 'execute_search', feedback: 'Show search results' }],
      },
    );

    return components;
  }

  private generateDesignSystem(components: UIComponent[]): DesignSystem {
    const componentLibrary: Record<string, UIComponent> = {};
    components.forEach((component) => {
      componentLibrary[component.name] = component;
    });

    return {
      colors: {
        primary: '#007bff',
        secondary: '#6c757d',
        success: '#28a745',
        danger: '#dc3545',
        warning: '#ffc107',
        info: '#17a2b8',
        light: '#f8f9fa',
        dark: '#343a40',
        white: '#ffffff',
        black: '#000000',
      },
      typography: {
        fonts: {
          primary: '-apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif',
          monospace: 'SFMono-Regular, Menlo, Monaco, Consolas, monospace',
        },
        sizes: {
          xs: '0.75rem',
          sm: '0.875rem',
          base: '1rem',
          lg: '1.125rem',
          xl: '1.25rem',
          '2xl': '1.5rem',
          '3xl': '1.875rem',
          '4xl': '2.25rem',
        },
        weights: { light: 300, normal: 400, medium: 500, semibold: 600, bold: 700 },
      },
      spacing: {
        base: 4,
        scale: { xs: 2, sm: 4, md: 8, lg: 16, xl: 24, '2xl': 32, '3xl': 48, '4xl': 64 },
      },
      components: componentLibrary,
    };
  }

  private generatePrototypes(input: UIUXInput, components: UIComponent[]): Prototype[] {
    return [
      {
        name: 'Main Application Prototype',
        type: 'interactive',
        screens: input.userStories.stories.slice(0, 5).map((story, index) => ({
          name: `screen_${story.id || index + 1}`,
          wireframe: `wireframe_${story.id || index + 1}`,
          components: components.slice(0, 3),
        })),
        interactions: [
          { from: 'screen_1', to: 'screen_2', trigger: 'button_click', transition: 'slide_right' },
          { from: 'screen_2', to: 'screen_1', trigger: 'back_button', transition: 'slide_left' },
        ],
      },
    ];
  }

  private mapTypeToInputType(type: string): string {
    const map: Record<string, string> = {
      string: 'text',
      number: 'number',
      boolean: 'checkbox',
      date: 'date',
      email: 'email',
      password: 'password',
      text: 'textarea',
    };
    return map[type.toLowerCase()] || 'text';
  }

  private calculateQualityScore(output: UIUXOutput, warnings: string[]): number {
    const screenCount = output.wireframes.length + output.prototypes.reduce((acc, item) => acc + item.screens.length, 0);
    const componentCount = output.components.length;
    const flowCount = output.userFlows.length;
    const base = Math.min(95, 40 + screenCount * 4 + componentCount * 2 + flowCount * 4);
    const penalty = Math.min(20, warnings.length * 5);
    return Math.max(50, base - penalty);
  }
}
