import type { LLM } from './index';

const Anthropic: LLM = {
  name: 'anthropic',
  async complete({ prompt, system, temperature = 0.7 }) {
    try {
      const { Anthropic: AnthropicSDK } = await import('@anthropic-ai/sdk');
      const client = new AnthropicSDK({
        apiKey: process.env.ANTHROPIC_API_KEY
      });

      const response = await client.messages.create({
        model: 'claude-3-sonnet-20240229',
        max_tokens: 1000,
        temperature,
        system,
        messages: [{ role: 'user', content: prompt }]
      });

      return response.content[0].type === 'text' 
        ? response.content[0].text 
        : '[non-text response]';
    } catch (error) {
      throw new Error(`Anthropic API error: ${error instanceof Error ? error.message : 'Unknown error'}`);
    }
  }
};

export default Anthropic;