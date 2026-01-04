import type { LLM } from './index.js';
import { GeminiResp } from '../schemas/llm.js';
import { extractGeminiText, hasConstructorProperty, stringifyUnknown } from './provider-utils.js';

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

const isGeminiModule = (value: unknown): value is GeminiModule =>
  hasConstructorProperty(value, 'GoogleGenerativeAI');

const loadGeminiModule = async (): Promise<GeminiModule> => {
  const raw: unknown = await eval('import("@google/generative-ai")');
  if (!isGeminiModule(raw)) {
    throw new Error('Gemini SDK module did not provide GoogleGenerativeAI.');
  }
  return raw;
};

const GeminiProvider: LLM = {
  name: 'gemini',
  async complete({ prompt, system, temperature }) {
    const mod = await loadGeminiModule();
    const client = new mod.GoogleGenerativeAI(process.env['GEMINI_API_KEY']);
    const model = client.getGenerativeModel({ model: process.env['GEMINI_MODEL'] ?? 'gemini-1.5-pro' });
    const parts: GeminiContentPart[] = [
      ...(system ? [{ text: system }] : []),
      { text: prompt }
    ];
    const res: unknown = await model.generateContent(parts, { generationConfig: { temperature: temperature ?? 0 } });
    const parsed = GeminiResp.safeParse(res);
    if (parsed.success) {
      // SDK差異を吸収して文字列へ
      return extractGeminiText(parsed.data.response);
    }
    return stringifyUnknown(res);
  }
};

export default GeminiProvider;
