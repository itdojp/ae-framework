import type { LLM } from './index.js';

const GeminiProvider: LLM = {
  name: 'gemini',
  async complete({ prompt, system, temperature }) {
    const mod: any = await eval('import("@google/generative-ai")');
    const client = new mod.GoogleGenerativeAI(process.env.GEMINI_API_KEY);
    const model = client.getGenerativeModel({ model: process.env.GEMINI_MODEL ?? 'gemini-1.5-pro' });
    const res = await model.generateContent([
      ...(system ? [{ text: system }] : []),
      { text: prompt }
    ], { generationConfig: { temperature: temperature ?? 0 } } as any);
    // SDK差異を吸収して文字列へ
    const out = (res?.response?.text?.() ?? res?.response?.candidates?.[0]?.content?.parts?.[0]?.text ?? '').toString();
    return out;
  }
};

export default GeminiProvider;