import { defineWorkspace } from 'vitest/config';
import { rootTestConfig, projectConfigs } from './configs/vitest.config.ts';

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
