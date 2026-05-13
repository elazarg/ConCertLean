/- Port of utils/theories/BytestringExtra.v. Source duplicates StringExtra.v over
   MetaRocq's bytestring; in Lean we re-export StringExtra. -/

import ConCert.Utils.StringExtra

namespace ConCert.Utils.BytestringExtra

export ConCert.Utils.StringExtra (
  strRev hex_of_N hex_of_nat hex_of_Z Nlog2up_nat
  string_of_N string_of_nat string_of_positive string_of_Z
  replace_char remove_char starts_with replace
  substring_from substring_count str_map last_index_of
  is_letter char_to_upper char_to_lower
  to_upper to_lower capitalize uncapitalize str_split lines)

end ConCert.Utils.BytestringExtra
