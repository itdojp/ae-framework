import type { LLM } from './index.js';
import { AnthropicMsg } from '../schemas/llm.js';

const AnthropicProvider: LLM = {
  name: 'anthropic',
  async complete({ prompt, system, temperature }) {
    const mod: any = await eval('import("@anthropic-ai/sdk")');
    const client = new mod.default({ apiKey: process.env.ANTHROPIC_API_KEY });
    const res: unknown = await client.messages.create({
      model: process.env.ANTHROPIC_MODEL ?? 'claude-3-5-sonnet-20240620',
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
    return String(res ?? '');
  }
};

export default AnthropicProvider;