import type { LLM } from './index.js';
import { AnthropicMsg } from '../schemas/llm.js';
import { extractAnthropicText, hasConstructorProperty, stringifyUnknown } from './provider-utils.js';

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

const isAnthropicModule = (value: unknown): value is AnthropicModule =>
  hasConstructorProperty(value, 'default');

const loadAnthropicModule = async (): Promise<AnthropicModule> => {
  const raw: unknown = await eval('import("@anthropic-ai/sdk")');
  if (!isAnthropicModule(raw)) {
    throw new Error('Anthropic SDK module did not provide a default export.');
  }
  return raw;
};

const AnthropicProvider: LLM = {
  name: 'anthropic',
  async complete({ prompt, system, temperature }) {
    const mod = await loadAnthropicModule();
    const apiKey = process.env['ANTHROPIC_API_KEY'];
    const client = new mod.default(apiKey ? { apiKey } : {});
    const messages: AnthropicMessage[] = [
      ...(system ? [{ role: 'user' as const, content: system }] : []),
      { role: 'user' as const, content: prompt }
    ];
    const res: unknown = await client.messages.create({
      model: process.env['ANTHROPIC_MODEL'] ?? 'claude-3-5-sonnet-20240620',
      max_tokens: 1024,
      temperature: temperature ?? 0,
      messages
    });
    const parsed = AnthropicMsg.safeParse(res);
    if (parsed.success) {
      return extractAnthropicText(parsed.data.content);
    }
    return stringifyUnknown(res);
  }
};

export default AnthropicProvider;
