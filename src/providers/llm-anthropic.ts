import type { LLM } from './index.js';
import { AnthropicMsg } from '../schemas/llm.js';

type AnthropicMessage = { role: 'user' | 'system'; content: string };
type AnthropicClient = {
  messages: {
    create: (input: {
      model: string;
      max_tokens: number;
      temperature: number;
      messages: AnthropicMessage[];
    }) => Promise<unknown>;
  };
};
type AnthropicModule = { default: new (options: { apiKey?: string }) => AnthropicClient };

const isAnthropicModule = (value: unknown): value is AnthropicModule => {
  if (!value || typeof value !== 'object') {
    return false;
  }
  return 'default' in value;
};

const loadAnthropicModule = async (): Promise<AnthropicModule> => {
  const raw: unknown = await eval('import("@anthropic-ai/sdk")');
  if (!isAnthropicModule(raw)) {
    throw new Error('Anthropic SDK module did not provide a default export.');
  }
  return raw;
};

const stringifyUnknown = (value: unknown): string => {
  if (value == null) return '';
  if (typeof value === 'string') return value;
  if (typeof value === 'number' || typeof value === 'boolean') return String(value);
  if (value instanceof Error) return value.message;
  try {
    const serialized = JSON.stringify(value);
    return serialized ?? '[unserializable]';
  } catch {
    return '[unserializable]';
  }
};

const AnthropicProvider: LLM = {
  name: 'anthropic',
  async complete({ prompt, system, temperature }) {
    const mod = await loadAnthropicModule();
    const client = new mod.default({ apiKey: process.env['ANTHROPIC_API_KEY'] });
    const res: unknown = await client.messages.create({
      model: process.env['ANTHROPIC_MODEL'] ?? 'claude-3-5-sonnet-20240620',
      max_tokens: 1024,
      temperature: temperature ?? 0,
      messages: [
        ...(system ? [{ role: 'user', content: system }] : []),
        { role: 'user', content: prompt }
      ]
    });
    const parsed = AnthropicMsg.safeParse(res);
    if (parsed.success) {
      const c = Array.isArray(parsed.data.content) ? parsed.data.content[0] : parsed.data.content;
      return (c?.text ?? c ?? '').toString();
    }
    return stringifyUnknown(res);
  }
};

export default AnthropicProvider;
