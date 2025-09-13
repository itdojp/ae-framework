import type { LLM } from './index.js';
import { GeminiResp } from '../schemas/llm.js';

const GeminiProvider: LLM = {
  name: 'gemini',
  async complete({ prompt, system, temperature }) {
    const mod: any = await eval('import("@google/generative-ai")');
    const client = new mod.GoogleGenerativeAI(process.env['GEMINI_API_KEY']);
    const model = client.getGenerativeModel({ model: process.env['GEMINI_MODEL'] ?? 'gemini-1.5-pro' });
    const res: unknown = await model.generateContent([
      ...(system ? [{ text: system }] : []),
      { text: prompt }
    ], { generationConfig: { temperature: temperature ?? 0 } } as any);
    const parsed = GeminiResp.safeParse(res);
    if (parsed.success) {
      // SDK差異を吸収して文字列へ
      const out = (parsed.data.response?.text?.() ?? parsed.data.response?.candidates?.[0]?.content?.parts?.[0]?.text ?? '').toString();
      return out;
    }
    return String(res ?? '');
  }
};

export default GeminiProvider;
