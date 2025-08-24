import type { LLM } from './index';

const Gemini: LLM = {
  name: 'gemini',
  async complete({ prompt, system, temperature = 0.7 }) {
    try {
      const { GoogleGenerativeAI } = await import('@google/generative-ai');
      const genAI = new GoogleGenerativeAI(process.env.GEMINI_API_KEY!);
      
      const model = genAI.getGenerativeModel({ 
        model: 'gemini-pro',
        generationConfig: {
          temperature,
          maxOutputTokens: 1000
        }
      });

      const fullPrompt = system ? `${system}\n\n${prompt}` : prompt;
      const result = await model.generateContent(fullPrompt);
      const response = await result.response;
      
      return response.text() || '[no response]';
    } catch (error) {
      throw new Error(`Gemini API error: ${error instanceof Error ? error.message : 'Unknown error'}`);
    }
  }
};

export default Gemini;