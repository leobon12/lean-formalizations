/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmTMean
import InteractingSLE.Spec.Supplement.GW2TqCond

/-!
# GW2's open lines: below the cap, the physical clock is below the version's cap; the stage shape as a domain

Packet PROVE-GW2-STAGEMEAN, R121 round (helpers of the Claim(k) step):

* `min_lt_of_clockX_lt_capX`: at ROOTX's corrected instance, `clockX t < capX` gives
  `min (physClockX (T + t)) V < V` (one sample);
* **`ae_compl_eq_dom_root0`**: on the history's success and the good set, below the version's cap, the complement of
  the corrected union at stage time `u` is the domain of GB6's relative chart moved by the version to `capA u`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Psm

open Restart Exist Exist.Staged Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rd
  GW2Rz GW2Sde Supp8 Supp8.GB6

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **Below the stage cap the physical clock is below the version's cap** (one sample). -/
theorem min_lt_of_clockX_lt_capX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (ch : GW2Sdh.SchedChoice Ω) {ω : Ω} (hV : V ω ≠ ⊤) {t : ℝ≥0}
    (hlt : (GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω <
      (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω) :
    min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + t) ω) (V ω) < V ω := by
  have hstartne : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω ≠ ⊤ :=
    ne_top_of_le_ne_top hV (min_le_right _ _)
  by_contra hcon
  push Not at hcon
  have h1 : V ω - stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω ≤
      min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + t) ω) (V ω) -
        stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω :=
    tsub_le_tsub_right hcon _
  have h2 : (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω =
      V ω - stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω := by
    show V ω - ((stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω).toNNReal :
      ℝ≥0∞) = _
    rw [ENNReal.coe_toNNReal hstartne]
  have h3 : (GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω =
      min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + t) ω) (V ω) -
        stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω := rfl
  have hlt' := hlt
  rw [h2, h3] at hlt'
  exact absurd (lt_of_lt_of_le hlt' h1) (lt_irrefl _)

/-- **The complement of the corrected union below the cap is the domain of the version's moved relative chart**
(root `0`, on the history's success and the good set). -/
theorem ae_compl_eq_dom_root0 (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hr0 : rootPt r.1 = 0) (hs0 : 0 < c.s) {GT : Set Ω}
    (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hv : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V) :
    ∀ᵐ ω ∂c.P, ω ∈ GT → oldSuccess c r l ω → ∀ u : ℝ≥0,
      min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + u) ω) (V ω) < V ω →
      H \ GW2Sdi.schedUnionS c r l a u ω = ((stgChart (RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) (fun q => R q ω)
        (capA (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) u ω)).dom : Set ℂ) := by
  filter_upwards [ae_shape_root0 c r l a hr0 hs0 hGT hv] with ω h hωG hsucc u hlt
  rw [h hωG hsucc u hlt, GW2Rd.dom_stgChart (RelSafeS.isConformal_relChart _) (hv.2.1 ω) (hv.2.2.1 ω)]

end InteractingSLE.Theorem14.GW2Psm
