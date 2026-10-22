import HigherDimLQGMetric.Thm13.ProbBdd
import HigherDimLQGMetric.Thm13.Translation
import HigherDimLQGMetric.Limits.LengthLFPP
import HigherDimLQGMetric.Limits.WeylTruncLimit
import HigherDimLQGMetric.Limits.WeylLimit

/-! The exact interface inputs used during L8 development are now supplied by L6c. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

theorem l8_length_limit_input : L8LengthLimitInput := by
  intro hL6a d ξ κ hB2 Ω _ P _ h hh μ hμ
  exact l6c_lemma31_lengthLimit hL6a ξ κ hB2 P h hh μ hμ

theorem l8_lemma36_trunc_input : L8Lemma36TruncInput := by
  intro d hd κ hκ ξ hL2c εs hεs hεt Ω _ P _ h Dh hh hlim
  exact l6c_lemma36_trunc hd κ hκ ξ hL2c εs hεs hεt P h Dh hh hlim

theorem l8_lemma36_full_input : L8Lemma36FullInput := by
  intro d hd κ hκ ξ εs hεs hεt Ω _ P _ h Dh hh hlim
  exact l6c_lemma36_full hd κ hκ ξ εs hεs hεt P h Dh hh hlim

end HigherDimLQGMetric
