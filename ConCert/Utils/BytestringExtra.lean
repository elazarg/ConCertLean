/- Port of utils/theories/BytestringExtra.v. Source duplicates StringExtra.v over
   MetaRocq's bytestring; Lean has no direct bytestring analogue, so this
   module re-exports `StringExtra`. -/

import ConCert.Utils.StringExtra

namespace ConCert.Utils.BytestringExtra

export ConCert.Utils.StringExtra (
  strRev str_rev hex_of_N hex_of_nat hex_of_positive hex_of_Z Nlog2up_nat
  string_of_N string_of_nat string_of_positive string_of_Z
  replace_char remove_char starts_with starts_with_cont replace
  substring_from substring_count str_map last_index_of
  is_letter char_to_upper char_to_lower
  to_upper to_lower capitalize uncapitalize str_split lines)

end ConCert.Utils.BytestringExtra
