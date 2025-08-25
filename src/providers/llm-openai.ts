import type { LLM } from './index.js';

const OpenAIProvider: LLM = {
  name: 'openai',
  async complete({ prompt, system, temperature }) {
    const mod: any = await eval('import("openai")');
    const client = new mod.default({ apiKey: process.env.OPENAI_API_KEY });
    const res = await client.chat.completions.create({
      model: process.env.OPENAI_MODEL ?? 'gpt-4o-mini',
      messages: [
        ...(system ? [{ role: 'system', content: system }] : []),
        { role: 'user', content: prompt }
      ],
      temperature: temperature ?? 0
    });
    return res?.choices?.[0]?.message?.content ?? '';
  }
};

export default OpenAIProvider;