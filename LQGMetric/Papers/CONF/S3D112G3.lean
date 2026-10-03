import LQGMetric.Papers.CONF.S3D112G1
import LQGMetric.Papers.CONF.S3D112G2

/-!
# D112 packet G1: the grid claims discharged

With `confChainFull : CONFChainFull 4` (S3D112G1) and `confFullConn : CONFFullConn` (S3D112G2),
the deterministic Step 2 input (3.21) of CONF Lemma 3.6 for `fatG` holds unconditionally, and
`L36Input` follows from Lemma 3.3 for `fatG` alone (decision D112, `decisions/DEC-112.md` §2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric.CONF

open Blueprint

/-- **CONF (3.21) for `fatG`**, with the grid claims proved -/
theorem l36Step2Input_fatG' {p : CONFParams} (hc : 0 < p.c) (hδ : 0 < p.δ) (hδ8 : p.δ < 1 / 8) :
    L36Step2Input p (fatG p) :=
  l36Step2Input_fatG confChainFull confFullConn hc hδ hδ8

end LQGMetric.CONF
