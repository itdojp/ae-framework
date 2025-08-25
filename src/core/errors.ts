export type AppError =
  | { code: 'E_EXEC'; step: string; detail?: string }
  | { code: 'E_PARSE'; step: string; detail?: string }
  | { code: 'E_TIMEOUT'; step: string; ms: number }
  | { code: 'E_CONFIG'; key: string; detail?: string };