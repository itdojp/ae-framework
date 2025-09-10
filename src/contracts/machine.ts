// State-machine skeleton (to be refined)
export type State = 'Init' | 'Next' | 'Done'
export function next(state: State): State {
  return state === 'Init' ? 'Next' : 'Done'
}

