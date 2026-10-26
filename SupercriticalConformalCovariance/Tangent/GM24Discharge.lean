import SupercriticalConformalCovariance.Tangent.Fixed
import SupercriticalConformalCovariance.GM24.Closed

/-!
# Discharging input (I4), GM Lemma 2.4 (2.6)

the proof of Gwynne–Miller Lemma 2.4's continuation proves (2.6) on centred disks with no remaining inputs
(`SupercriticalConformalCovariance.GM24.tendsto_tvDist_gm24_closed`, `GM24/Closed.lean:89`). Its statement is verbatim the
body of `GMLemma24TV`.
-/

set_option autoImplicit false

namespace SupercriticalConformalCovariance.Tangent

theorem gmLemma24TV_holds : GMLemma24TV := by
  intro U φ α hopen hzeroU hexhaust hd hinj hzero hα hder Ω _ P _ h hh f hf1 hrot hnorm B R hB hR
    hFB
  exact SupercriticalConformalCovariance.GM24.tendsto_tvDist_gm24_closed hopen hzeroU hexhaust hd hinj hzero hα hder hh hf1 hrot
    hnorm hB hR hFB

end SupercriticalConformalCovariance.Tangent
