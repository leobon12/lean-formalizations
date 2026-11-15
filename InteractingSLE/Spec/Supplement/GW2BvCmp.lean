/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BtContact
import InteractingSLE.Spec.Supplement.GW2BuExh
import InteractingSLE.Spec.Supplement.GW2FbConfig
import InteractingSLE.Spec.Supplement.GW2WmDec
import InteractingSLE.Spec.Sec6.DrivingCriterion

/-!
# Capped and uncapped stage paths agree up to the cap; the uncapped contact clause

Packet PROVE-GW2-BUF (round 19; decision D50: BUF's share of the uncapped route). At one sample, with the source
counterflow good:

* `clockX_eq_of_agree`, `hullX_eq_of_agree`: two explored drivers agreeing on `[0, t]` have the same root-`x` clock
  and re-centred relative hull at `t` (`recOf_congr_top`);
* `lt_contactX_of_agree`: two explored traces agreeing on `[0, t₁]` have their root-`x` contacts after the same times
  below `t₁` (`GW2Fb.lt_firstContactTime_of_prefix`);
* **`eqOn_of_agree_hulls`**: the comparison. Take a driver `R` generating the hulls of one explored driver `w₁` along
  its clock below a cap `V`, and a driver `Wc` generating those of `w₂` below a death clock `d`. If `w₁ = w₂` and
  their traces agree on `[0, t₁]`, then `R = Wc` on `[0, clockX w₁ t]` for every `t < t₁` before the contact with the
  clock there below `V` and `d`. This is hull uniqueness (`Sec6.eqOn_of_fwdHull_eq`) along the common clock. It is
  the capped/uncapped comparison: `w₁` is a candidate's `schedW` with a version `(R, V)` (`IsRelVersionX`), `w₂` is
  NEARIMG2's uncapped `uncW` with its canonical driver (`GW2Ni.IsCanonUX`), and `t₁ = T + cap` (NEARIMG2's
  `UncAgreeStatement`).
* **`gapVanishes_contactX_cond`**: round 17's root-`x` contact clause for a canonical driver that generates the hulls
  only below a death clock `d` (as `GW2Ni.IsCanonUX`), whenever the relative life is `≤ d`: then every time before
  the contact has its clock below `d`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.GW2Bh

open Exist Staged StagedLaw MartChar.RealFlow Supp8 Supp8.GB6 Supp8.GB6.CoordB Supp8.Q3Rel Restart GW2TipSystem
  GW2Rz

variable {Ω : Type*}

theorem clockX_eq_of_agree {x : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {w₁ w₂ : ℝ≥0 → Ω → ℝ} {ω : Ω}
    {t : ℝ≥0} (hw : ∀ u ≤ t, w₁ u ω = w₂ u ω) : clockX x s W' ζ' w₁ t ω = clockX x s W' ζ' w₂ t ω := by
  unfold clockX recPair
  rw [GW2Wm.recOf_congr_top hw]

theorem hullX_eq_of_agree {x : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {w₁ w₂ : ℝ≥0 → Ω → ℝ} {ω : Ω}
    {t : ℝ≥0} (hw : ∀ u ≤ t, w₁ u ω = w₂ u ω) : hullX x s W' ζ' w₁ t ω = hullX x s W' ζ' w₂ t ω := by
  unfold hullX recPair
  rw [GW2Wm.recOf_congr_top hw]

theorem lt_contactX_of_agree {x : ℝ} {s : ℝ≥0} {γ₁ γ₂ α : Ω → ℝ≥0 → ℂ} {ω : Ω} {t₁ t : ℝ≥0}
    (hγ : ∀ u ≤ t₁, γ₁ ω u = γ₂ ω u) (htt : t < t₁) (ht : (t : ℝ≥0∞) < contactX x s γ₁ α ω) :
    (t : ℝ≥0∞) < contactX x s γ₂ α ω :=
  GW2Fb.lt_firstContactTime_of_prefix htt (fun u hu => by simp only [hγ u hu]) ht

section Sample

variable (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) {α : Ω → ℝ≥0 → ℂ}
  (hα : IsGeneratingTrace (W · ω) ⊤ (α ω)) (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α ω u‖ < 1)

include hα hW hW0 hζ hs hx harc

/-- **The capped/uncapped comparison** at one sample: drivers generating the hulls of two explored drivers that agree
with their traces on `[0, t₁]` agree on `[0, clockX w₁ t]` for `t < t₁` before the contact with the clock there below
the cap `V` and the death clock `d`. -/
theorem eqOn_of_agree_hulls {w₁ w₂ : ℝ≥0 → Ω → ℝ} {γ₁ γ₂ : Ω → ℝ≥0 → ℂ}
    (hwc₁ : Continuous (w₁ · ω)) (hw0₁ : w₁ 0 ω = 0) (hγ₁ : IsGeneratingTrace (w₁ · ω) ⊤ (γ₁ ω))
    {t₁ : ℝ≥0} (hw : ∀ u ≤ t₁, w₁ u ω = w₂ u ω) (hγ : ∀ u ≤ t₁, γ₁ ω u = γ₂ ω u)
    {R : ℝ≥0 → ℝ} (hRc : Continuous R) (hR0 : R 0 = 0) {V : ℝ≥0∞}
    (hR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ₁ α ω → ENNReal.ofReal (clockX x s W ζ w₁ t ω) ≤ V →
      fwdHull (fun q : ℝ => R q.toNNReal) (clockX x s W ζ w₁ t ω) = hullX x s W ζ w₁ t ω)
    {Wc : ℝ≥0 → ℝ} (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) {d : ℝ≥0∞}
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ₂ α ω → ENNReal.ofReal (clockX x s W ζ w₂ t ω) < d →
      fwdHull (fun q : ℝ => Wc q.toNNReal) (clockX x s W ζ w₂ t ω) = hullX x s W ζ w₂ t ω)
    {t : ℝ≥0} (htt : t < t₁) (htc : (t : ℝ≥0∞) < contactX x s γ₁ α ω)
    (htV : ENNReal.ofReal (clockX x s W ζ w₁ t ω) ≤ V) (htd : ENNReal.ofReal (clockX x s W ζ w₁ t ω) < d) :
    ∀ u : ℝ≥0, (u : ℝ) ≤ clockX x s W ζ w₁ t ω → R u = Wc u := by
  obtain ⟨h0, hsm, hac⟩ := GW2Rz.clock_props W ζ ω hα hW hW0 hζ hs hx harc hwc₁ hw0₁ hγ₁
  set clk : ℝ≥0 → ℝ := fun t => clockX x s W ζ w₁ t ω with hclk
  have hclk0 : clk 0 = 0 := h0
  -- the hulls agree at every clock value before `t`
  have hhull : ∀ t' : ℝ≥0, t' ≤ t →
      fwdHull (fun q : ℝ => R q.toNNReal) (clk t') = fwdHull (fun q : ℝ => Wc q.toNNReal) (clk t') := by
    intro t' ht'
    have ht'c : (t' : ℝ≥0∞) < contactX x s γ₁ α ω := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht') htc
    have hmono : clk t' ≤ clk t := by
      rcases eq_or_lt_of_le ht' with h | h
      · rw [h]
      · exact (hsm ht'c htc h).le
    have hw' : ∀ u ≤ t', w₁ u ω = w₂ u ω := fun u hu => hw u (hu.trans (ht'.trans htt.le))
    have hceq : clockX x s W ζ w₁ t' ω = clockX x s W ζ w₂ t' ω := clockX_eq_of_agree hw'
    have hheq : hullX x s W ζ w₁ t' ω = hullX x s W ζ w₂ t' ω := hullX_eq_of_agree hw'
    have h2c : (t' : ℝ≥0∞) < contactX x s γ₂ α ω := lt_contactX_of_agree hγ (lt_of_le_of_lt ht' htt) ht'c
    have hV' : ENNReal.ofReal (clk t') ≤ V := (ENNReal.ofReal_le_ofReal hmono).trans htV
    have hd' : ENNReal.ofReal (clockX x s W ζ w₂ t' ω) < d := by
      rw [← hceq]
      exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hmono) htd
    show fwdHull (fun q : ℝ => R q.toNNReal) (clockX x s W ζ w₁ t' ω) =
      fwdHull (fun q : ℝ => Wc q.toNNReal) (clockX x s W ζ w₁ t' ω)
    rw [hR t' ht'c hV', hceq, hK t' h2c hd', hheq]
  -- every value in `[0, clk t]` is a clock value before `t`
  have hcont : ContinuousOn clk (Icc 0 t) :=
    hac.mono fun t' ht' => lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht'.2) htc
  have hS : 0 ≤ clk t := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
    · rw [← h, hclk0]
    · have h0c : ((0 : ℝ≥0) : ℝ≥0∞) < contactX x s γ₁ α ω := lt_of_le_of_lt (by exact_mod_cast zero_le) htc
      exact (lt_of_eq_of_lt hclk0.symm (hsm h0c htc h)).le
  have hEq : EqOn (fun q : ℝ => R q.toNNReal) (fun q : ℝ => Wc q.toNNReal) (Icc 0 (clk t)) := by
    refine Sec6.eqOn_of_fwdHull_eq (hRc.comp continuous_real_toNNReal) (hWc.comp continuous_real_toNNReal)
      (by simp [hR0]) (by simp [hWc0]) hS fun σ hσ => ?_
    obtain ⟨t', ht', hσeq⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ t) hcont
      ⟨by rw [hclk0]; exact hσ.1, hσ.2⟩
    rw [← hσeq]
    exact hhull t' ht'.2
  intro u hu
  have h : R (u : ℝ).toNNReal = Wc (u : ℝ).toNNReal := hEq ⟨u.2, hu⟩
  rwa [Real.toNNReal_coe] at h

/-- **The root-`x` contact clause for a canonical driver generating the hulls only below a death clock `d`**
(the form of NEARIMG2's `GW2Ni.IsCanonUX`), whenever the relative life is at most `d`. -/
theorem gapVanishes_contactX_cond {w : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ}
    (hwc : Continuous (w · ω)) (hw0 : w 0 ω = 0) (hγ : IsGeneratingTrace (w · ω) ⊤ (γ ω))
    (htr : Tendsto (fun t => ‖γ ω t‖) atTop atTop) {Wc : ℝ≥0 → ℝ}
    (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) {ζc : ℝ≥0∞} {ηc : ℝ≥0 → ℂ} (hη : IsGeneratingTrace Wc ζc ηc)
    {d : ℝ≥0∞}
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω → ENNReal.ofReal (clockX x s W ζ w t ω) < d →
      fwdHull (fun q : ℝ => Wc q.toNNReal) (clockX x s W ζ w t ω) = hullX x s W ζ w t ω)
    (hbdd : ∃ M : ℝ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω → clockX x s W ζ w t ω ≤ M)
    (hLζ : ENNReal.ofReal (contactLifeX x s (cfRec s W ζ ω) (w · ω) (γ ω) (α ω)) ≤ ζc)
    (hLd : ENNReal.ofReal (contactLifeX x s (cfRec s W ζ ω) (w · ω) (γ ω) (α ω)) ≤ d) :
    (baseL (rp (W · ω)) s < 0 ∧
        junctionR (rp (W · ω)) s - (relBdry (rp (W · ω)) s x).re ≤
          (ηc (contactLifeX x s (cfRec s W ζ ω) (w · ω) (γ ω) (α ω)).toNNReal).re ∧
        ∀ y : ℝ, y ≤ (ηc (contactLifeX x s (cfRec s W ζ ω) (w · ω) (γ ω) (α ω)).toNNReal).re →
          GapVanishes (rp Wc) y (contactLifeX x s (cfRec s W ζ ω) (w · ω) (γ ω) (α ω))) ∨
      (0 < baseR (rp (W · ω)) s ∧
        (ηc (contactLifeX x s (cfRec s W ζ ω) (w · ω) (γ ω) (α ω)).toNNReal).re ≤
          junctionL (rp (W · ω)) s - (relBdry (rp (W · ω)) s x).re ∧
        ∀ y : ℝ, (ηc (contactLifeX x s (cfRec s W ζ ω) (w · ω) (γ ω) (α ω)).toNNReal).re ≤ y →
          GapVanishes (fun r => -rp Wc r) (-y) (contactLifeX x s (cfRec s W ζ ω) (w · ω) (γ ω) (α ω))) := by
  obtain ⟨h0, hsm, -⟩ := GW2Rz.clock_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ
  obtain ⟨M, hM⟩ := hbdd
  refine gapVanishes_contactX W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ htr hWc hWc0 hη (fun t ht => ?_)
    ⟨M, hM⟩ hLζ
  -- before the contact the clock is below the life, hence below `d`
  have hlt := clock_lt_life (a := fun t => clockX x s W ζ w t ω) hsm hM ht
  have hnn : 0 ≤ clockX x s W ζ w t ω := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
    · rw [← h]; exact h0.ge
    · have h0c : ((0 : ℝ≥0) : ℝ≥0∞) < contactX x s γ α ω := lt_of_le_of_lt (by exact_mod_cast zero_le) ht
      exact (lt_of_eq_of_lt h0.symm (hsm h0c ht h)).le
  have hd : ENNReal.ofReal (clockX x s W ζ w t ω) < d :=
    lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnn).2 hlt) hLd
  exact hK t ht hd

end Sample

end InteractingSLE.Theorem14.GW2Bh
