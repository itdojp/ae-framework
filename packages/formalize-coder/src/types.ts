export type FormalPlanMetadata = {
  source: string;
  generatedAt: string;
  model?: {
    name: string;
    version?: string;
  };
};

export type FormalPlanRequirement = {
  id: string;
  text: string;
};

export type FormalPlanVariable = {
  name: string;
  type: string;
  description?: string;
  domain?: string;
};

export type FormalPlanConstant = {
  name: string;
  type: string;
  description?: string;
  value?: string;
};

export type FormalPlanAction = {
  name: string;
  tla: string;
  description?: string;
  preconditions?: string[];
  effects?: string[];
};

export type FormalPlanFormula = {
  name: string;
  tla: string;
  description?: string;
};

export type FormalPlan = {
  schemaVersion: string;
  metadata: FormalPlanMetadata;
  requirements?: FormalPlanRequirement[];
  variables: FormalPlanVariable[];
  constants?: FormalPlanConstant[];
  actions: FormalPlanAction[];
  invariants: FormalPlanFormula[];
  liveness?: FormalPlanFormula[];
  assumptions?: FormalPlanFormula[];
};
