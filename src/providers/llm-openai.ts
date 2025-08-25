import type { LLM } from './index.js';
import { OpenAIChat } from '../schemas/llm.js';

const OpenAIProvider: LLM = {
  name: 'openai',
  async complete({ prompt, system, temperature }) {
    const mod: any = await eval('import("openai")');
    const client = new mod.default({ apiKey: process.env.OPENAI_API_KEY });
    const res: unknown = await client.chat.completions.create({
      model: process.env.OPENAI_MODEL ?? 'gpt-4o-mini',
      messages: [
        ...(system ? [{ role: 'system', content: system }] : []),
        { role: 'user', content: prompt }
      ],
      temperature: temperature ?? 0
    });
    const parsed = OpenAIChat.safeParse(res);
    return parsed.success ? parsed.data.choices[0].message.content : String(res ?? '');
  }
};

export default OpenAIProvider;