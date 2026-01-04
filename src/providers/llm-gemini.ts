import type { LLM } from './index.js';
import { GeminiResp } from '../schemas/llm.js';

type GeminiContentPart = { text: string };
type GeminiGenerationConfig = { temperature?: number };
type GeminiModel = {
  generateContent: (
    parts: GeminiContentPart[],
    options?: { generationConfig?: GeminiGenerationConfig }
  ) => Promise<unknown>;
};
type GeminiClient = {
  getGenerativeModel: (input: { model: string }) => GeminiModel;
};
type GeminiModule = {
  GoogleGenerativeAI: new (apiKey?: string) => GeminiClient;
};

const isGeminiModule = (value: unknown): value is GeminiModule => {
  if (!value || typeof value !== 'object') {
    return false;
  }
  return 'GoogleGenerativeAI' in value;
};

const loadGeminiModule = async (): Promise<GeminiModule> => {
  const raw: unknown = await eval('import("@google/generative-ai")');
  if (!isGeminiModule(raw)) {
    throw new Error('Gemini SDK module did not provide GoogleGenerativeAI.');
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

const GeminiProvider: LLM = {
  name: 'gemini',
  async complete({ prompt, system, temperature }) {
    const mod = await loadGeminiModule();
    const client = new mod.GoogleGenerativeAI(process.env['GEMINI_API_KEY']);
    const model = client.getGenerativeModel({ model: process.env['GEMINI_MODEL'] ?? 'gemini-1.5-pro' });
    const res: unknown = await model.generateContent([
      ...(system ? [{ text: system }] : []),
      { text: prompt }
    ], { generationConfig: { temperature: temperature ?? 0 } });
    const parsed = GeminiResp.safeParse(res);
    if (parsed.success) {
      // SDK差異を吸収して文字列へ
      const out = (parsed.data.response?.text?.() ?? parsed.data.response?.candidates?.[0]?.content?.parts?.[0]?.text ?? '').toString();
      return out;
    }
    return stringifyUnknown(res);
  }
};

export default GeminiProvider;
