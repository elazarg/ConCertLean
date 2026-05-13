/- Port of execution/theories/Circulation.v -/

import ConCert.Utils.Extras
import ConCert.Execution.Blockchain
import ConCert.Execution.Finite

namespace ConCert.Execution.Circulation

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Finite
open ConCert.Utils.Extras

variable [Base : ChainBase] [Finite Base.Address]

def circulation (env : @Environment Base) : Int :=
  sumZ env.env_account_balances (Finite.elements (T := Base.Address))

axiom address_reorganize :
  ∀ {a b : Base.Address},
    a ≠ b →
    ∃ suf, List.Perm ([a, b] ++ suf) (Finite.elements (T := Base.Address))

axiom eval_action_from_to_same :
  ∀ {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)}
    (eval : ActionEvaluation pre act post new_acts),
    ActionEvaluation.eval_from eval = ActionEvaluation.eval_to eval →
    circulation post = circulation pre

axiom eval_action_circulation_unchanged :
  ∀ {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)},
    ActionEvaluation pre act post new_acts → circulation post = circulation pre

axiom circulation_proper :
  ∀ (e1 e2 : @Environment Base),
    EnvironmentEquiv e1 e2 → circulation e1 = circulation e2

axiom circulation_add_new_block :
  ∀ (header : @BlockHeader Base) (env : @Environment Base),
    circulation (add_new_block_to_env header env) =
      circulation env + header.block_reward

axiom step_circulation :
  ∀ {prev next : @ChainState Base} (step : ChainStep prev next),
    circulation next.toEnvironment =
      (match step with
       | .step_block hdr _ _ _ _ _ => circulation prev.toEnvironment + hdr.block_reward
       | _ => circulation prev.toEnvironment)

axiom chain_trace_circulation :
  ∀ {state : @ChainState Base}
    (trace : ConCert.Execution.ChainedList.ChainedList ChainStep empty_state state),
    circulation state.toEnvironment =
      sumZ (fun h => @BlockHeader.block_reward Base h)
           (ConCert.Execution.BlockchainBase.trace_blocks trace)

end ConCert.Execution.Circulation
