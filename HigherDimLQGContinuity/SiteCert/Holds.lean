import HigherDimLQGContinuity.SiteCert.OfNet
import HigherDimLQGContinuity.Network.Catalogue
import HigherDimLQGContinuity.Network.SpecFinal

/-!
# The site certificate `SiteCertOfLabel` (interface I27; [C] Lemma 4.3's certificate, Part B `b:thm-sitecert`)

Packet Q7b proves `SiteCertOfLabel d` from two facts about the label network (`q7b_siteCert_of_net`): the catalogue
product bound (4.9) and, for each site data, a network constant with the properties of `b:lem-net`, `b:lem-sep` and
`b:lem-star` for every realizable label. Packet Q4 proves both (`q4_hcount`, `q4_hnet`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

/-- **The site certificate (I27)**, for every `d ≥ 3`. -/
theorem siteCert_holds {d : ℕ} (hd : 3 ≤ d) : SiteCertOfLabel d :=
  q7b_siteCert_of_net hd q4_hcount (q4_hnet (by omega))

end HigherDimLQGContinuity
