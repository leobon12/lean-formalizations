/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VcClock

/-!
# SB2(1)'s version half: continuity of the relative clock

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). For the relative clock
`Vc.clockOf γ t_L ζ` of a lift `γ` (entrance `t_L`, lifetime `ζ`):

* `clockOf_eq_sup_of_le`: from the lifetime on, the clock is the relative lifetime
  `sup {capClock γ s | t_L + s < ζ}` (this is what the `alive` field compares with the threshold);
* `clockOf_eq_zero_of_le_tL`: if the lifetime is not after the entrance, the clock vanishes identically;
* **`continuous_clockOf`**: if the capacity clock vanishes at `0` and is continuous and monotone on every
  `[0, T₁ − t_L]` with `t_L ≤ T₁ < ζ` (a record's chain at every horizon below the lifetime), the clock is continuous.

Deterministic; nothing here replaces a source statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Vd

open Vc

variable {γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {ζ : ℝ≥0∞}

/-- **From the lifetime on, the clock is the relative lifetime.** -/
theorem clockOf_eq_sup_of_le {t : ℝ≥0} (ht : ζ ≤ t) :
    clockOf γ tL ζ t = ⨆ (s : ℝ≥0) (_ : ((tL + s : ℝ≥0) : ℝ≥0∞) < ζ),
      ENNReal.ofReal (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) s) := by
  unfold clockOf
  refine le_antisymm (iSup₂_le fun s _ => iSup_le fun hs => le_iSup₂_of_le s hs le_rfl) ?_
  refine iSup₂_le fun s hs => ?_
  have h1 : tL + s ≤ t := ENNReal.coe_le_coe.1 (hs.le.trans ht)
  exact le_iSup₂_of_le s h1 (le_iSup_of_le hs le_rfl)

/-- **If the lifetime is not after the entrance, the clock vanishes.** -/
theorem clockOf_eq_zero_of_le_tL (hζ : ζ ≤ tL) (t : ℝ≥0) : clockOf γ tL ζ t = 0 := by
  refine le_antisymm (iSup₂_le fun s _ => iSup_le fun hs => ?_) zero_le
  exact absurd (hs.trans_le hζ) (not_lt.2 (ENNReal.coe_le_coe.2 le_self_add))

/-- **The relative clock is continuous** (capacity clock vanishing at `0`, continuous and monotone on every
`[0, T₁ − t_L]` with `t_L ≤ T₁ < ζ`). -/
theorem continuous_clockOf (h0 : Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) 0 = 0)
    (hloc : ∀ T₁ : ℝ≥0, tL ≤ T₁ → (T₁ : ℝ≥0∞) < ζ →
      ContinuousOn (Sec7.Lemma71C.capClock fun r : ℝ => γ r.toNNReal) (Icc 0 ((T₁ : ℝ) - tL)) ∧
        MonotoneOn (Sec7.Lemma71C.capClock fun r : ℝ => γ r.toNNReal) (Icc 0 ((T₁ : ℝ) - tL))) :
    Continuous (clockOf γ tL ζ) := by
  by_cases hζtL : ζ ≤ tL
  · have e : clockOf γ tL ζ = fun _ => 0 := funext (clockOf_eq_zero_of_le_tL hζtL)
    rw [e]; exact continuous_const
  rw [not_le] at hζtL
  refine continuous_iff_continuousAt.2 fun t => ?_
  by_cases htζ : (t : ℝ≥0∞) < ζ
  · -- before the lifetime: the clock is `ofReal (capClock γ (max (t' − t_L) 0))` near `t`
    obtain ⟨T₁, hT₁, hT₁ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (max_lt htζ hζtL)
    have htT : t < T₁ := ENNReal.coe_lt_coe.1 ((le_max_left _ _).trans_lt hT₁)
    have htLT : tL < T₁ := ENNReal.coe_lt_coe.1 ((le_max_right _ _).trans_lt hT₁)
    obtain ⟨hcont, hmono⟩ := hloc T₁ htLT.le hT₁ζ
    set inner : ℝ≥0 → ℝ := fun t' => max ((t' : ℝ) - tL) 0 with hinner
    set g : ℝ≥0 → ℝ≥0∞ := fun t' =>
      ENNReal.ofReal (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) (inner t')) with hg
    have hmaps : MapsTo inner (Iic T₁) (Icc 0 ((T₁ : ℝ) - tL)) := fun t' ht' =>
      ⟨le_max_right _ _, max_le (by have := NNReal.coe_le_coe.2 ht'; linarith)
        (by have := NNReal.coe_lt_coe.2 htLT; linarith)⟩
    have hinc : Continuous inner :=
      (NNReal.continuous_coe.sub continuous_const).max continuous_const
    have hgc : ContinuousOn g (Iic T₁) :=
      ENNReal.continuous_ofReal.comp_continuousOn (hcont.comp hinc.continuousOn hmaps)
    have hev : clockOf γ tL ζ =ᶠ[𝓝 t] g := by
      filter_upwards [Iic_mem_nhds htT] with t' ht'
      have ht'ζ : (t' : ℝ≥0∞) < ζ := (ENNReal.coe_le_coe.2 ht').trans_lt hT₁ζ
      rcases le_total t' tL with h | h
      · rw [clockOf_eq_zero_of_le h h0]
        have : inner t' = 0 := max_eq_right (by have := NNReal.coe_le_coe.2 h; linarith)
        simp only [hg, this, h0, ENNReal.ofReal_zero]
      · have hin : inner t' = (t' : ℝ) - tL := max_eq_left (by have := NNReal.coe_le_coe.2 h; linarith)
        rw [clockOf_eq h ht'ζ (hmono.mono (Icc_subset_Icc_right (by
          have := NNReal.coe_le_coe.2 ht'; linarith)))]
        simp only [hg, hin]
    exact (hgc.continuousAt (Iic_mem_nhds htT)).congr hev.symm
  · -- from the lifetime on: constant to the right, the monotone limit to the left
    rw [not_lt] at htζ
    have hζtop : ζ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top htζ
    set ζ' : ℝ≥0 := ζ.toNNReal with hζ'
    have hζc : ((ζ' : ℝ≥0) : ℝ≥0∞) = ζ := ENNReal.coe_toNNReal hζtop
    have hconst : ∀ t' : ℝ≥0, ζ' ≤ t' → clockOf γ tL ζ t' = clockOf γ tL ζ ζ' := fun t' ht' => by
      rw [clockOf_eq_sup_of_le (by rw [← hζc]; exact ENNReal.coe_le_coe.2 ht'),
        clockOf_eq_sup_of_le (by rw [hζc])]
    have hζ't : ζ' ≤ t := by rw [← ENNReal.coe_le_coe, hζc]; exact htζ
    rcases hζ't.lt_or_eq with hlt | heq
    · -- strictly after the lifetime: locally constant
      have hev : clockOf γ tL ζ =ᶠ[𝓝 t] fun _ => clockOf γ tL ζ ζ' := by
        filter_upwards [Ioi_mem_nhds hlt] with t' ht'
        exact hconst t' (le_of_lt ht')
      exact (continuousAt_const).congr hev.symm
    · -- at the lifetime
      subst heq
      refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
      · have hmono := monotone_clockOf γ tL ζ
        have htend := Monotone.tendsto_nhdsLT hmono ζ'
        have hsup : sSup (clockOf γ tL ζ '' Iio ζ') = clockOf γ tL ζ ζ' := by
          refine le_antisymm (sSup_le ?_) ?_
          · rintro _ ⟨t', ht', rfl⟩; exact hmono ht'.le
          · rw [clockOf_eq_sup_of_le (by rw [hζc])]
            refine iSup₂_le fun s hs => ?_
            have hlt' : tL + s < ζ' := by rw [← ENNReal.coe_lt_coe, hζc]; exact hs
            refine le_trans ?_ (le_sSup ⟨tL + s, hlt', rfl⟩)
            unfold clockOf
            exact le_iSup₂_of_le s le_rfl (le_iSup_of_le hs le_rfl)
        rw [hsup] at htend
        have hI : Iic ζ' = insert ζ' (Iio ζ') := Iio_insert.symm
        rw [ContinuousWithinAt, hI, nhdsWithin_insert]
        exact tendsto_sup.2 ⟨tendsto_pure_nhds _ _, htend⟩
      · exact (continuousWithinAt_const (b := clockOf γ tL ζ ζ')).congr (fun t' ht' => hconst t' ht') rfl

end InteractingSLE.Theorem14.SB.Vd
