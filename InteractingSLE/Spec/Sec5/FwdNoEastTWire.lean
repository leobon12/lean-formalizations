/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm1415CurrentRegularity
import InteractingSLE.Spec.Sec5.Aux61UnionKLocal
import InteractingSLE.Spec.Sec5.Aux61ActCut

/-!
# Theorem 1.5's target-component (E1) below the critical gap: the wiring through Theorem 1.3

Packet PROVE-T15-FWDNOEAST. Theorem 1.5's expanded assembly (`Wire.theorem15Statement_late_expanded`,
PROVE-WIRE-T1415) takes `Aux61Kernel.FwdNoEastCrosscutTgtQOn.{u} smallGap` and its universe-`0` copy as inputs
(`smallGap κ θ₁ θ₂ := ¬ Prop51G.IsLargeGap κ θ₁ θ₂`). Theorem 1.5 may use Theorems 1.2–1.3 (R48: it is not an input of
them). Here:

* `fwdNoEastCrosscutTgtQOn_restrict`: (E1) on all angle pairs gives (E1) on every regime;
* **`fwdNoEastCrosscutTgtQOn_smallGap_of_thm13_window`**: (E1) below the critical gap from Theorem 1.3 (which
  supplies the counterflow regularity `Prop51Q.CfLineRegularQStatement`,
  `Wire.cfLineRegularQStatement_of_theorem13_current`, in place of Zhan's Part A) and AUX61-R23's single named
  input `RestartWindowNullQOn` below the critical gap;
* **`fwdNoEastCrosscutTgtQOn_smallGap_of_thm13_localCover`**: the same from the fibre-local cover of PROVE-AUX61-FIBK
  (`Aux61UnionK.GluedLocalCoverOn`) and the negative-side reference avoidance (`Aux61Cov.R5NegStatement`), the form in
  which the restart comparison is being closed (PROVE-AUX61-CHARTLOC / -MEAN / -UNIONLOC, PROVE-TWOMARK).

The physical marked local set (P) of that route at the glued stop is supplied for Theorem 1.5 by counterflow
determination (Theorem 1.2), in `FwdNoEastTWalls`.

Conditional helpers with distinct names; they replace no source theorem. They are downstream of Theorem 1.3 and must
never be fed back into the Section 5 inputs of Theorems 1.2–1.3 (R48).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Sec5.FwdNoEastT

open Prop51G Aux61Kernel

/-- **(E1) on all angle pairs gives (E1) on every regime** (the regime is only a hypothesis of `GluedQ`). -/
theorem fwdNoEastCrosscutTgtQOn_restrict {G : ℝ → ℝ → ℝ → Prop}
    (h : FwdNoEastCrosscutTgtQOn.{u} fun _ _ _ => True) : FwdNoEastCrosscutTgtQOn.{u} G := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 _ hb ha Ω mΩ P _ hf η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  exact h κ hκ hκ4 a b θ₁ θ₂ h12 trivial hb ha P hf η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs

/-- **Theorem 1.5's (E1) below the critical gap from Theorem 1.3 and the restart comparison at one window** (below
the critical gap; the large-gap regime is proved, `restartWindowNullQOn_largeGap`). -/
theorem fwdNoEastCrosscutTgtQOn_smallGap_of_thm13_window (h13 : Exist.Theorem13Statement.{u})
    (hsmall : RestartWindowNullQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :
    FwdNoEastCrosscutTgtQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂ :=
  fwdNoEastCrosscutTgtQOn_restrict
    (fwdNoEastCrosscutTgtQOn_of_window_smallGap (Wire.cfLineRegularQStatement_of_theorem13_current h13) hsmall)

/-- **Theorem 1.5's (E1) below the critical gap from Theorem 1.3, the fibre-local cover and R5 on the negative
side.** -/
theorem fwdNoEastCrosscutTgtQOn_smallGap_of_thm13_localCover (h13 : Exist.Theorem13Statement.{u})
    (hcov : Aux61UnionK.GluedLocalCoverOn.{u}) (hneg : Aux61Cov.R5NegStatement.{u}) :
    FwdNoEastCrosscutTgtQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂ :=
  fwdNoEastCrosscutTgtQOn_restrict
    (Aux61Act.fwdNoEastCrosscutTgtQOn_of_dyCover_refWin (Wire.cfLineRegularQStatement_of_theorem13_current h13)
      (Aux61UnionK.dyCover_of_localCoverOn hcov) hneg)

/-- **Both universes at once** (the two inputs `htgt`, `htgt₀` of `Wire.theorem15Statement_late_expanded`). -/
theorem fwdNoEastCrosscutTgtQOn_smallGap_pair_of_thm13_localCover (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hcov : Aux61UnionK.GluedLocalCoverOn.{u})
    (hcov₀ : Aux61UnionK.GluedLocalCoverOn.{0}) (hneg : Aux61Cov.R5NegStatement.{u})
    (hneg₀ : Aux61Cov.R5NegStatement.{0}) :
    FwdNoEastCrosscutTgtQOn.{u} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) ∧
      FwdNoEastCrosscutTgtQOn.{0} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :=
  ⟨fwdNoEastCrosscutTgtQOn_smallGap_of_thm13_localCover h13 hcov hneg,
    fwdNoEastCrosscutTgtQOn_smallGap_of_thm13_localCover h13₀ hcov₀ hneg₀⟩

end InteractingSLE.Sec5.FwdNoEastT
