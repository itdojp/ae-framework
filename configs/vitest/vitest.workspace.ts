import { defineWorkspace } from 'vitest/config';
import { rootTestConfig, projectConfigs } from '../vitest.config.ts';

const rootProject = {
  test: {
    name: 'root',
    ...rootTestConfig,
  },
};

export default defineWorkspace([
  rootProject,
  ...projectConfigs,
]);
