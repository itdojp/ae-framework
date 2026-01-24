export type SamplingOptions = {
  temperature: number;
};

export const samplingProfiles: Record<string, SamplingOptions> = {
  deterministic: {
    temperature: 0,
  },
  balanced: {
    temperature: 0.2,
  },
};

export const samplingDefaults = samplingProfiles.balanced;
