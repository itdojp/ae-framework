import type { LLM } from './index.js';
import { OpenAIChat } from '../schemas/llm.js';
import { hasConstructorProperty, stringifyUnknown } from './provider-utils.js';

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

const isOpenAIModule = (value: unknown): value is OpenAIModule =>
  hasConstructorProperty(value, 'default');

const loadOpenAIModule = async (): Promise<OpenAIModule> => {
  const raw: unknown = await eval('import("openai")');
  if (!isOpenAIModule(raw)) {
    throw new Error('OpenAI SDK module did not provide a default export.');
  }
  return raw;
};

const OpenAIProvider: LLM = {
  name: 'openai',
  async complete({ prompt, system, temperature }) {
    const mod = await loadOpenAIModule();
    const apiKey = process.env['OPENAI_API_KEY'];
    const client = new mod.default(apiKey ? { apiKey } : {});
    const messages: OpenAIChatMessage[] = [
      ...(system ? [{ role: 'system' as const, content: system }] : []),
      { role: 'user' as const, content: prompt }
    ];
    const res: unknown = await client.chat.completions.create({
      model: process.env['OPENAI_MODEL'] ?? 'gpt-4o-mini',
      messages,
      temperature: temperature ?? 0
    });
    const parsed = OpenAIChat.safeParse(res);
    return parsed.success ? parsed.data.choices[0].message.content : stringifyUnknown(res);
  }
};

export default OpenAIProvider;
