/- Port of utils/theories/BSEnv.v. Same as Env.v but over MetaRocq's bytestring.
   In Lean we just use `String` again; the two ports collapse. -/

import ConCert.Utils.Env

namespace ConCert.Utils.BSEnv

export ConCert.Utils.Env (Env lookup lookup_with_ind_rec lookup_with_ind lookup_i remove_by_key)

end ConCert.Utils.BSEnv
