import type { LLM } from './index.js';
import { OpenAIChat } from '../schemas/llm.js';

type OpenAIChatMessage = { role: 'system' | 'user'; content: string };
type OpenAIChatClient = {
  chat: {
    completions: {
      create: (input: {
        model: string;
        messages: OpenAIChatMessage[];
        temperature: number;
      }) => Promise<unknown>;
    };
  };
};
type OpenAIModule = { default: new (options: { apiKey?: string }) => OpenAIChatClient };

const isOpenAIModule = (value: unknown): value is OpenAIModule => {
  if (!value || typeof value !== 'object') {
    return false;
  }
  return 'default' in value;
};

const loadOpenAIModule = async (): Promise<OpenAIModule> => {
  const raw: unknown = await eval('import("openai")');
  if (!isOpenAIModule(raw)) {
    throw new Error('OpenAI SDK module did not provide a default export.');
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

const OpenAIProvider: LLM = {
  name: 'openai',
  async complete({ prompt, system, temperature }) {
    const mod = await loadOpenAIModule();
    const client = new mod.default({ apiKey: process.env['OPENAI_API_KEY'] });
    const res: unknown = await client.chat.completions.create({
      model: process.env['OPENAI_MODEL'] ?? 'gpt-4o-mini',
      messages: [
        ...(system ? [{ role: 'system', content: system }] : []),
        { role: 'user', content: prompt }
      ],
      temperature: temperature ?? 0
    });
    const parsed = OpenAIChat.safeParse(res);
    return parsed.success ? parsed.data.choices[0].message.content : stringifyUnknown(res);
  }
};

export default OpenAIProvider;
