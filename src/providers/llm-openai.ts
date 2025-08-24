import type { LLM } from './index';

const OpenAI: LLM = {
  name: 'openai',
  async complete({ prompt, system, temperature = 0.7 }) {
    try {
      const { OpenAI: OpenAISDK } = await import('openai');
      const client = new OpenAISDK({
        apiKey: process.env.OPENAI_API_KEY
      });

      const messages: Array<{ role: 'system' | 'user'; content: string }> = [];
      if (system) {
        messages.push({ role: 'system', content: system });
      }
      messages.push({ role: 'user', content: prompt });

      const response = await client.chat.completions.create({
        model: 'gpt-3.5-turbo',
        messages,
        temperature,
        max_tokens: 1000
      });

      return response.choices[0]?.message?.content || '[no response]';
    } catch (error) {
      throw new Error(`OpenAI API error: ${error instanceof Error ? error.message : 'Unknown error'}`);
    }
  }
};

export default OpenAI;