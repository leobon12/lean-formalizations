import HigherDimLQGMetric.Sec6.Prop62
import HigherDimLQGMetric.Amplify.Main

/-!
# The §6 package with Lemma 6.1 discharged

Packet S6b. `sec6Package` takes [S] Lemma 6.1 (`FineFieldAmplification`) as a hypothesis (packet
interface pattern); S5b's `fineFieldAmplification_of_lower_pair` proves it for the lower pair of two
sharp weak assignments with the a.s. lower comparison `c_* D ≤ D̃`, `0 < pstar ≤ 1`. This corollary
combines the two.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- **The §6 package without the Lemma 6.1 hypothesis** (S5b's `fineFieldAmplification_of_lower_pair`
discharges it). -/
theorem sec6Package_of_sharp (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    {cs Cs c0 c1 c2 aL A₀L ℓL β₀L pstar : ℝ}
    (hcs : 0 < cs) (hcs1 : cs < c1) (hc12 : c1 < c2) (hc2Cs : c2 < Cs)
    (hcomp : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ᵐ ω ∂P, ∀ u v : Rd d, cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
          (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v))
    (hℓL : 0 < ℓL) (hβ₀L : 0 < β₀L) (hpstar : 0 < pstar) (hpstar1 : pstar ≤ 1)
    (hfreq : FrequencyLemma d ξ Q Dt D cs⁻¹ aL A₀L ℓL β₀L pstar)
    (h10 : cs⁻¹ - aL / A₀L * (cs⁻¹ - c1⁻¹) < c0⁻¹) :
    TrapFamily d ξ Q D Dt cs Cs c1 aL A₀L ℓL β₀L pstar ∧ ConfigLocal d ξ Q D Dt ∧
      ∀ m : ℕ, Cor63 d ξ Q D Dt cs c0 c1 aL A₀L ℓL β₀L pstar m := by
  have hFFA : FineFieldAmplification d ξ Q D Dt cs c1 c2 aL A₀L ℓL β₀L pstar := by
    refine fineFieldAmplification_of_lower_pair hd hξ hQ hD hDt hcs (hcs.trans hcs1) hℓL hc12
      hpstar hpstar1 ?_
    intro Ω _ P _ h hh
    exact (hcomp P h hh).mono fun ω hω u v => (hω u v).1
  exact sec6Package hd hξ hQ hD hDt hcs hcs1 hc12 hc2Cs hcomp hℓL hβ₀L hpstar hfreq h10 hFFA

end HigherDimLQGMetric
