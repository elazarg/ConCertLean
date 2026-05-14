/- Port of utils/theories/RecordUpdate.v.

The original re-exports RecordSet + its notations. -/

import ConCert.Utils.RecordSet

namespace ConCert.Utils.RecordUpdate

export ConCert.Utils.RecordSet (SetterFromGetter modify_from_getter set_from_getter)
export ConCert.Utils.RecordSet.SetterFromGetter (modify set)

end ConCert.Utils.RecordUpdate
