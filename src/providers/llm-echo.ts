import type { LLM } from './index';

const Echo: LLM = {
  name: 'echo',
  async complete({ prompt, system }) {
    const prefix = system ? `[system: ${system}] ` : '';
    return `[echo] ${prefix}${prompt}`;
  }
};

export default Echo;