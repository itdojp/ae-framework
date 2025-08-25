import type { LLM } from './index.js';

const AnthropicProvider: LLM = {
  name: 'anthropic',
  async complete({ prompt, system, temperature }) {
    const mod: any = await eval('import("@anthropic-ai/sdk")');
    const client = new mod.default({ apiKey: process.env.ANTHROPIC_API_KEY });
    const res = await client.messages.create({
      model: process.env.ANTHROPIC_MODEL ?? 'claude-3-5-sonnet-20240620',
      max_tokens: 1024,
      temperature: temperature ?? 0,
      messages: [
        ...(system ? [{ role: 'user', content: system }] : []),
        { role: 'user', content: prompt }
      ]
    });
    const c = Array.isArray(res?.content) ? res.content[0] : res?.content;
    return (c?.text ?? c ?? '').toString();
  }
};

export default AnthropicProvider;