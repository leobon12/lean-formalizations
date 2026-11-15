/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.NoClusterRec

/-!
# Lemma 3.4: the restart time and the separation bound

Packet PROVE-ZHAN-GT4-B2. Two ingredients of the restart in Lemma 3.4 (additional note L1491–L1495; follow-up §B.3
L1247–L1250: "let `T ≥ T₀` be the first subsequent time `X_t = x₀` … At the resulting time `T`, the centered mapped
future has exactly the original law"):

* `hitAfterT t₀`: the first time after a deterministic `t₀` at which a continuous process vanishes (PROVE-ZHAN-GT4-B's
  `hitAfter`, with `1` replaced by `t₀`);
* `eight_mul_le_sep_sq`: **the marks separate**, `8t ≤ (V_R − V_L)_t²` for a separated one-mark-per-side path (the
  chordal form of the source's growth of the gaps (E8), (E12): `∂ₜ(V_R − V_L) = 2/R + 2/L ≥ 8/(R + L)`);
* `hasAdmissiblePartialSums_one`, and the trace of the restarted driver (`TopEvent`, `topCodeSet`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

/-! ### The first time after `t₀` at which a continuous process vanishes -/

section Hit

variable {Ω : Type*}

/-- `max(Y_t, t₀ − t)`: nonpositive exactly when `t ≥ t₀` and `Y_t ≤ 0`. -/
def posAfterT (t₀ : ℝ≥0) (Y : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω => max (Y t ω) ((t₀ : ℝ) - (t : ℝ))

/-- **The first time after `t₀` at which `Y` vanishes**, as the later of the first times after `t₀` at which `Y ≤ 0`
and `−Y ≤ 0`. -/
def hitAfterT (t₀ : ℝ≥0) (Y : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  max (Sec7.firstMeet zeroProc (posAfterT t₀ Y) ζ ω) (Sec7.firstMeet zeroProc (posAfterT t₀ (-Y)) ζ ω)

theorem continuousOn_posAfterT_sub {t₀ : ℝ≥0} {Y : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous fun t => Y t ω)
    (S : Set ℝ≥0) : ContinuousOn (fun t => posAfterT t₀ Y t ω - zeroProc t ω) S :=
  ((hc.max (continuous_const.sub NNReal.continuous_coe)).sub continuous_const).continuousOn

theorem exists_firstMeet_posAfterT {t₀ : ℝ≥0} {Y : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hc : Continuous fun t => Y t ω) (hζ : ζ ω = ⊤) {t₁ : ℝ≥0} (ht₁ : t₀ ≤ t₁) (hz : Y t₁ ω ≤ 0) :
    ∃ m : ℝ≥0, Sec7.firstMeet zeroProc (posAfterT t₀ Y) ζ ω = m ∧ t₀ ≤ m ∧ Y m ω ≤ 0 ∧
      ∀ t : ℝ≥0, t₀ ≤ t → t < m → 0 < Y t ω := by
  have ht₁' : (t₁ : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  have h1 : posAfterT t₀ Y t₁ ω ≤ zeroProc t₁ ω := by
    simp only [posAfterT, zeroProc, max_le_iff]
    exact ⟨hz, by have : (t₀ : ℝ) ≤ t₁ := by exact_mod_cast ht₁
                  linarith⟩
  have hlt : Sec7.firstMeet zeroProc (posAfterT t₀ Y) ζ ω < ζ ω :=
    lt_of_le_of_lt (Sec7.firstMeet_le_of ht₁' h1) ht₁'
  obtain ⟨m, hm, -, hmV⟩ := Sec7.exists_eq_firstMeet (continuousOn_posAfterT_sub hc _) hlt
  simp only [posAfterT, zeroProc, max_le_iff] at hmV
  refine ⟨m, hm, ?_, hmV.1, fun t ht1 htm => ?_⟩
  · have : (t₀ : ℝ) ≤ m := by linarith [hmV.2]
    exact_mod_cast this
  · have h2 := (Sec7.lt_of_lt_firstMeet (W := zeroProc) (V := posAfterT t₀ Y) (ζ := ζ) (ω := ω)
      (t := t) (by rw [hm]; exact_mod_cast htm)).2
    simp only [posAfterT, zeroProc, lt_max_iff] at h2
    rcases h2 with h2 | h2
    · exact h2
    · have : (t₀ : ℝ) ≤ t := by exact_mod_cast ht1
      linarith

/-- **The hitting time after `t₀` is a zero of `Y`** (pathwise). -/
theorem exists_hitAfterT {t₀ : ℝ≥0} {Y : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (hc : Continuous fun t => Y t ω)
    (hζ : ζ ω = ⊤) {t₁ : ℝ≥0} (ht₁ : t₀ ≤ t₁) (hz : Y t₁ ω = 0) :
    ∃ m : ℝ≥0, hitAfterT t₀ Y ζ ω = m ∧ t₀ ≤ m ∧ Y m ω = 0 := by
  obtain ⟨mp, hmp, hmp1, hYp, hbp⟩ := exists_firstMeet_posAfterT hc hζ ht₁ hz.le
  have hcn : Continuous fun t => (-Y) t ω := hc.neg
  obtain ⟨mm, hmm, hmm1, hYm, hbm⟩ := exists_firstMeet_posAfterT (Y := -Y) hcn hζ ht₁ (by simp [hz])
  simp only [Pi.neg_apply, neg_nonpos] at hYm
  simp only [Pi.neg_apply, Left.neg_pos_iff] at hbm
  have hYc : Continuous fun t : ℝ≥0 => Y t ω := hc
  unfold hitAfterT
  rw [hmp, hmm]
  rcases le_total mm mp with hle | hle
  · refine ⟨mp, by rw [max_eq_left (by exact_mod_cast hle)], hmp1, ?_⟩
    obtain ⟨t, ht, hYt⟩ := intermediate_value_Icc' hle hYc.continuousOn ⟨hYp, hYm⟩
    rcases ht.2.lt_or_eq with htl | hte
    · exact absurd hYt (hbp t (hmm1.trans ht.1) htl).ne'
    · rw [← hte]; exact hYt
  · refine ⟨mm, by rw [max_eq_right (by exact_mod_cast hle)], hmm1, ?_⟩
    obtain ⟨t, ht, hYt⟩ := intermediate_value_Icc hle hYc.continuousOn ⟨hYp, hYm⟩
    rcases ht.2.lt_or_eq with htl | hte
    · exact absurd hYt (hbm t (hmp1.trans ht.1) htl).ne
    · rw [← hte]; exact hYt

end Hit

/-! ### Admissibility of one-mark-per-side words -/

/-- A one-mark-per-side word with weights `≥ κ/2 − 2` has admissible side partial sums (any positions). -/
theorem hasAdmissiblePartialSums_one {κ : ℝ} {ρL ρR xL xR : Fin 1 → ℝ} (hL : κ / 2 - 2 ≤ ρL 0)
    (hR : κ / 2 - 2 ≤ ρR 0) : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR := by
  constructor
  · rintro x - ⟨i, hi⟩
    have hf : (Finset.univ.filter fun i : Fin 1 => x < xL i) = Finset.univ := by
      ext j; rw [Fin.fin_one_eq_zero j, Fin.fin_one_eq_zero i] at *; simp [hi]
    rwa [hf, Fin.sum_univ_one]
  · rintro x - ⟨i, hi⟩
    have hf : (Finset.univ.filter fun i : Fin 1 => xR i ≤ x) = Finset.univ := by
      ext j; rw [Fin.fin_one_eq_zero j, Fin.fin_one_eq_zero i] at *; simp [hi]
    rwa [hf, Fin.sum_univ_one]

/-- A separated one-mark-per-side word is ordered. -/
theorem isOrderedForceWord_one {xL xR : Fin 1 → ℝ} (hxL : xL 0 < 0) (hxR : 0 < xR 0) :
    IsOrderedForceWord xL xR :=
  ⟨fun i j _ => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j],
    fun i => by rw [Fin.fin_one_eq_zero i]; exact hxL.le,
    fun i j _ => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j],
    fun j => by rw [Fin.fin_one_eq_zero j]; exact hxR.le⟩

/-! ### The marks separate: `8t ≤ (V_R − V_L)²` -/

theorem eight_div_le_two_div_add {R L : ℝ} (hR : 0 < R) (hL : 0 < L) : 8 / (R + L) ≤ 2 / R + 2 / L := by
  rw [div_add_div _ _ hR.ne' hL.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (R - L), mul_pos hR hL]

/-- **The marks separate** (the chordal form of (E8), (E12)): for a one-mark-per-side path with infinite lifetime whose
marks never meet the driver, `8t ≤ (V_R − V_L)_t²`. -/
theorem eight_mul_le_sep_sq {κ : ℝ} {xL xR ρL ρR : Fin 1 → ℝ} {w : ℝ≥0 → ℝ} {vL vR : Fin 1 → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ⊤)
    (hsL : ∀ t, vL 0 t < w t) (hsR : ∀ t, w t < vR 0 t) (t : ℝ≥0) :
    8 * (t : ℝ) ≤ (vR 0 t - vL 0 t) ^ 2 := by
  have hcont : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ⊤} → Continuous f := fun hf =>
    continuousOn_univ.1 (hf.mono fun t _ => ENNReal.coe_lt_top)
  have hw : Continuous fun s : ℝ => w s.toNNReal := (hcont hp.2.2.2.1).comp continuous_real_toNNReal
  have hl : Continuous fun s : ℝ => vL 0 s.toNNReal :=
    (hcont (hp.2.2.2.2.1 0)).comp continuous_real_toNNReal
  have hr : Continuous fun s : ℝ => vR 0 s.toNNReal :=
    (hcont (hp.2.2.2.2.2.1 0)).comp continuous_real_toNNReal
  set sep : ℝ≥0 → ℝ := fun u => vR 0 u - vL 0 u with hsepdef
  have hsep0 : ∀ u, 0 < sep u := fun u => by simp only [hsepdef]; linarith [hsL u, hsR u]
  have hRc : Continuous fun s : ℝ => 2 / (vR 0 s.toNNReal - w s.toNNReal) :=
    continuous_const.div (hr.sub hw) fun s => (sub_pos.2 (hsR _)).ne'
  have hLc : Continuous fun s : ℝ => 2 / (vL 0 s.toNNReal - w s.toNNReal) :=
    continuous_const.div (hl.sub hw) fun s => (sub_neg.2 (hsL _)).ne
  set G : ℝ → ℝ := fun s => 2 / (vR 0 s.toNNReal - w s.toNNReal) - 2 / (vL 0 s.toNNReal - w s.toNNReal)
    with hG
  have hGc : Continuous G := hRc.sub hLc
  have hGlow : ∀ s : ℝ, 8 / sep s.toNNReal ≤ G s := fun s => by
    have hR0 : 0 < vR 0 s.toNNReal - w s.toNNReal := sub_pos.2 (hsR _)
    have hL0 : 0 < w s.toNNReal - vL 0 s.toNNReal := sub_pos.2 (hsL _)
    have h := eight_div_le_two_div_add hR0 hL0
    have e1 : vR 0 s.toNNReal - w s.toNNReal + (w s.toNNReal - vL 0 s.toNNReal) = sep s.toNNReal := by
      simp only [hsepdef]; ring
    have e2 : 2 / (vL 0 s.toNNReal - w s.toNNReal) = -(2 / (w s.toNNReal - vL 0 s.toNNReal)) := by
      rw [← neg_sub, div_neg]
    rw [e1] at h
    simp only [hG, e2]
    linarith
  have hsepint : ∀ u : ℝ≥0, sep u = sep 0 + ∫ s in (0 : ℝ)..u, G s := fun u => by
    have h1 := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 u ENNReal.coe_lt_top 0
    have h2 := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1 u ENNReal.coe_lt_top 0
    have h10 : vR 0 0 = xR 0 := hp.2.2.1 0
    have h20 : vL 0 0 = xL 0 := hp.2.1 0
    simp only [hsepdef, hG]
    rw [intervalIntegral.integral_sub (hRc.intervalIntegrable _ _) (hLc.intervalIntegrable _ _), h10, h20]
    linarith
  have hGpos : ∀ s, 0 ≤ G s := fun s => le_trans (by have := hsep0 s.toNNReal; positivity) (hGlow s)
  have hmono : ∀ u v : ℝ≥0, u ≤ v → sep u ≤ sep v := fun u v huv => by
    rw [hsepint u, hsepint v, ← intervalIntegral.integral_add_adjacent_intervals
      (hGc.intervalIntegrable 0 u) (hGc.intervalIntegrable u v)]
    have := intervalIntegral.integral_nonneg (μ := volume) (f := G) (a := u) (b := v)
      (by exact_mod_cast huv) fun s _ => hGpos s
    linarith
  have hint : (8 / sep t) * (t : ℝ) ≤ ∫ s in (0 : ℝ)..t, G s := by
    have h := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ => 8 / sep t) (g := G)
      t.coe_nonneg intervalIntegrable_const (hGc.intervalIntegrable _ _) fun s hs => by
        refine le_trans ?_ (hGlow s)
        have hle : sep s.toNNReal ≤ sep t := hmono _ _ (by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]; exact hs.2)
        exact div_le_div_of_nonneg_left (by norm_num) (hsep0 _) hle
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
    linarith
  have ht := hsepint t
  have h0 := hsep0 0
  have hT := hsep0 t
  have : 8 * (t : ℝ) ≤ sep t * (sep t - sep 0) := by
    have := mul_le_mul_of_nonneg_left (show (8 / sep t) * (t : ℝ) ≤ sep t - sep 0 by linarith) hT.le
    rwa [← mul_assoc, mul_div_cancel₀ _ hT.ne'] at this
  show 8 * (t : ℝ) ≤ sep t ^ 2
  nlinarith

end InteractingSLE.ZhanGT4
