/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12LowProb

/-!
# Lemma G12 when the weight before the mark is `≤ −2`: the stopping times exhaust the picture

Packet PROVE-G12C. The **picture** after a restart time `q` (`LowPic`): up to a time `T_e ≤ ζ`, the inner gap
`o = V^k − W` is positive, after `q` no mark meets the driver, and the drift energy `∫_q^t D²` is at most `κC`. On a
good path with this picture, every time `t ∈ [q, T_e)` is below the stopping time `σ_n = lowStop` for all large `n`
(`exists_le_lowStop`): PROVE-G12's `σ_n` exhausts the life of the mark (`G12Core.exists_le_locG`), the inner gap and the
monitored gaps are bounded below on the compact `[0, t]`, and the cut energy at level `δ_n` is the true energy
(`lowEnergy_le_of_pic`), at most `C < C + 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

namespace G12Low

open G12 (GCoord coordG densG locG coordAtG clockAt rhoY)
open Supp8.GB5 (IsGBGood)
open GB7a Girsanov

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {k j₀ : Fin nR} {S : ℝ}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {q : ℝ≥0} {C n : ℕ}

/-- The drift difference `D = Σᵢ ρ_{i,L}/(W − V^{i,L}) + Σⱼ (ρ_{j,R} − ρ'ⱼ)/(W − V^{j,R})` of the word against the
reference, along one path. -/
def lowD (ρL : Fin nL → ℝ) (xR ρR : Fin nR → ℝ) (k j₀ : Fin nR) (S : ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ω : Ω) (s : ℝ) : ℝ :=
  (∑ i, ρL i / (W s.toNNReal ω - VL i s.toNNReal ω)) +
    ∑ j, (ρR j - lowRefW xR ρR k j₀ S j) / (W s.toNNReal ω - VR j s.toNNReal ω)

/-- **The picture after the restart time `q`** up to `T_e`: the inner gap is positive before `T_e`, after `q` no
mark meets the driver, and the drift energy after `q` is at most `κC`. -/
def LowPic (κ : ℝ) (ρL : Fin nL → ℝ) (xR ρR : Fin nR → ℝ) (k j₀ : Fin nR) (S : ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (q : ℝ≥0) (C : ℕ) (ω : Ω)
    (Te : ℝ≥0) : Prop :=
  q < Te ∧ (Te : ℝ≥0∞) ≤ ζ ω ∧ (∀ t : ℝ≥0, t < Te → W t ω < VR k t ω) ∧
    (∀ t : ℝ≥0, q ≤ t → t < Te → (∀ i, W t ω ≠ VL i t ω) ∧ ∀ j, W t ω ≠ VR j t ω) ∧
    ∀ t : ℝ≥0, q ≤ t → t < Te → ∫ s in (q : ℝ)..t, lowD ρL xR ρR k j₀ S W VL VR ω s ^ 2 ≤ κ * C

/-! ### The energy on the picture -/

section Energy

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω)

include hE hGm hGc hgood in
/-- **The cut energy is the true energy** while the monitored gaps exceed `δ_n`: on the picture it is at most
`C` up to any `s ≤` the separation time. -/
theorem lowEnergy_le_of_pic (hκ : 0 < κ) {ω : Ω} {Te : ℝ≥0}
    (hpic : LowPic κ ρL xR ρR k j₀ S W VL VR ζ q C ω Te) {s : ℝ≥0} (hsTe : s < Te)
    (hsep : (s : ℝ≥0∞) ≤ lowSep ρL xR ρR k j₀ S G W VL VR ζ q n ω)
    (hgap : ∀ r : ℝ≥0, q ≤ r → r ≤ s → ∀ j : Fin (nL + nR),
      refW nL xR ρR k j₀ S j - actW ρL ρR j ≠ 0 → G12.dlt n ≤ |W r ω - Girsanov.allMarks VL VR j r ω|) :
    lowEnergy κ ρL xR ρR k j₀ S G W VL VR ζ q n s ω ≤ C := by
  set θ := lowTheta κ ρL xR ρR k j₀ S G W VL VR ζ q n with hθdef
  have hτζ := sepTime_le_lifetime (ρ := actW ρL ρR) (ρ' := refW nL xR ρR k j₀ S) (k := Fin.natAdd nL k) (q := q)
    (W := W) (U := Girsanov.allMarks VL VR) (ζ := goodLife G ζ) (T₀ := (n : ℝ≥0)) (G12.dlt_pos n).le ω
  have hWc := continuousOn_goodLife_W hgood ω
  have hUc := fun j => continuousOn_goodLife_marks hgood j ω
  have hθp := isStronglyProgressive_lowTheta (κ := κ) (k := k) (j₀ := j₀) (S := S) (q := q) (n := n)
    hE hGm hGc hgood
  have hθ2 : IsStronglyProgressive (usualAugmentation 𝓕 P) (fun t ω => θ t ω ^ 2) := fun t => (hθp t).pow 2
  have hθb : ∀ t ω, |θ t ω ^ 2| ≤ cmpBound κ (G12.dlt n) (fun j => refW nL xR ρR k j₀ S j - actW ρL ρR j) ^ 2 :=
    fun t ω => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_lowTheta_le t ω) 2
  have hI := fun a b => intervalIntegrable_time hθ2 hθb ω a b
  -- `θ = 0` before `q`
  have hzero : ∀ r : ℝ, 0 ≤ r → r < q → r < s → θ r.toNNReal ω = 0 := fun r hr0 hrq hrs => by
    refine cmpDrift_eq_zero_of_lt_min (G12.dlt_pos n) hτζ hWc hUc (lt_min ?_ ?_)
    · refine lt_of_lt_of_le ?_ hsep
      exact_mod_cast (show r.toNNReal < s by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]; exact hrs)
    · exact_mod_cast (show r.toNNReal < q by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]; exact hrq)
  have hE0 : lowEnergy κ ρL xR ρR k j₀ S G W VL VR ζ q n s ω = ∫ r in (0 : ℝ)..s, θ r.toNNReal ω ^ 2 := rfl
  -- the integral of `θ²` over `[0, a]`, `a ≤ min(q, s)`, vanishes
  have hvan : ∀ a : ℝ, 0 ≤ a → a ≤ q → a ≤ s → ∫ r in (0 : ℝ)..a, θ r.toNNReal ω ^ 2 = 0 := fun a ha haq has => by
    have : ∫ r in (0 : ℝ)..a, θ r.toNNReal ω ^ 2 = ∫ r in (0 : ℝ)..a, (0 : ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [ae_ne_real a] with r hra hr
      rw [uIoc_of_le ha] at hr
      have hr' : r < a := lt_of_le_of_ne hr.2 hra
      rw [hzero r hr.1.le (hr'.trans_le haq) (hr'.trans_le has), zero_pow two_ne_zero]
    rw [this, intervalIntegral.integral_zero]
  rw [hE0]
  rcases le_or_gt s q with hsq | hqs
  · rw [hvan s s.coe_nonneg (by exact_mod_cast hsq) le_rfl]
    exact Nat.cast_nonneg C
  -- `q < s`: split at `q`
  have hqs' : (q : ℝ) < s := hqs
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI 0 q) (hI q s),
    hvan q q.coe_nonneg le_rfl hqs'.le, zero_add]
  -- on `(q, s)` the cut drift is the drift difference over `√κ`
  have hpt : ∀ r ∈ Ioo (q : ℝ) s, θ r.toNNReal ω ^ 2 = lowD ρL xR ρR k j₀ S W VL VR ω r ^ 2 / κ := by
    intro r hr
    have hr0 : 0 ≤ r := q.coe_nonneg.trans hr.1.le
    have hqr : q < r.toNNReal := by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]; exact hr.1
    have hrs : r.toNNReal < s := by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]; exact hr.2
    have hθr := cmpDrift_eq_of_mem (κ := κ) (σ := fun j => refW nL xR ρR k j₀ S j - actW ρL ρR j)
      (τ := lowSep ρL xR ρR k j₀ S G W VL VR ζ q n) (G12.dlt_pos n) hτζ hWc hUc hqr
      (lt_of_lt_of_le (by exact_mod_cast hrs) hsep)
    have hsq := shiftIntegrand_sq_eq (κ := κ) (ρ := actW ρL ρR) (ρ' := refW nL xR ρR k j₀ S) hκ (G12.dlt_pos n)
      (w := W r.toNNReal ω) (u := fun j => Girsanov.allMarks VL VR j r.toNNReal ω)
      (hgap r.toNNReal hqr.le hrs.le)
    rw [sum_refW_sub_actW] at hsq
    simp only [allMarks_castAdd', allMarks_natAdd', neg_sq] at hsq
    rw [hθdef, lowTheta, hθr, hsq]
    rfl
  have hDi : IntervalIntegrable (fun r => lowD ρL xR ρR k j₀ S W VL VR ω r ^ 2 / κ) volume q s :=
    (hI q s).congr_uIoo fun r hr => by
      rw [uIoo_of_le hqs'.le] at hr
      exact hpt r hr
  have heq : ∫ r in (q : ℝ)..s, θ r.toNNReal ω ^ 2 = ∫ r in (q : ℝ)..s, lowD ρL xR ρR k j₀ S W VL VR ω r ^ 2 / κ :=
    intervalIntegral.integral_congr_ae (by
      filter_upwards [ae_ne_real (s : ℝ)] with r hrs hr
      rw [uIoc_of_le hqs'.le] at hr
      exact hpt r ⟨hr.1, lt_of_le_of_ne hr.2 hrs⟩)
  rw [heq, intervalIntegral.integral_div, div_le_iff₀ hκ]
  have := hpic.2.2.2.2 s hqs.le hsTe
  linarith

end Energy

theorem dlt_lt_of_ceil_le {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : ⌈1 / c⌉₊ ≤ n) : G12.dlt n < c := by
  have h1 : 1 / c < (n : ℝ) + 1 := (Nat.le_ceil _).trans_lt (by exact_mod_cast Nat.lt_succ_of_le hn)
  unfold G12.dlt
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hc] at h1
  linarith

/-! ### Exhaustion -/

section Exhaust

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω)

include hE hGm hGc hgood in
/-- **On the picture the stopping times exhaust `[q, T_e)`.** -/
theorem exists_le_lowStop (hord : IsOrderedForceWord xL xR) (hTm : ∀ ω, Monotone fun n => T n ω)
    (hκ : 0 < κ) (hkj : k ≤ j₀) (hkjx : xR k < xR j₀) {ω : Ω} (hω : ω ∈ G) {Te : ℝ≥0}
    (hpic : LowPic κ ρL xR ρR k j₀ S W VL VR ζ q C ω Te) {t : ℝ≥0} (hqt : q ≤ t) (htTe : t < Te) :
    ∃ N, ∀ n ≥ N, t ≤ lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω := by
  classical
  obtain ⟨hqTe, hTeζ, hopos, hoff, hen⟩ := hpic
  have hF := (hgood ω hω).1.isForcePath
  have hlt : ∀ s : ℝ≥0, s ≤ t → (s : ℝ≥0∞) < ζ ω := fun s hs =>
    lt_of_lt_of_le (by exact_mod_cast hs.trans_lt htTe) hTeζ
  -- (1) PROVE-G12's localizing times
  have hlife : G11.IsMarkLife (W · ω) (VR j₀ · ω) (ζ ω) t := by
    refine ⟨hlt t le_rfl, fun u hu => ?_⟩
    exact (hopos u (hu.trans_lt htTe)).trans_le (hF.monotone_vR (hlt u hu) hkj)
  have hn : 0 < nR := Fin.pos k
  set i₀ : Fin nR := ⟨0, hn⟩
  have hi₀ : ∀ j, i₀ ≤ j := fun j => Fin.mk_le_of_le_val (Nat.zero_le _)
  have hx : xR i₀ < xR j₀ := (hord.2.2.1 (hi₀ k)).trans_lt hkjx
  obtain ⟨n₁, hn₁⟩ := G12.exists_le_locG hord hi₀ hx hTm hgood hω hlife
  -- (2) the inner gap
  obtain ⟨c₀, hc₀, hc₀le⟩ := G12.exists_pos_le_of_isCompact (isCompact_Icc (a := (0 : ℝ≥0)) (b := t))
    ⟨0, le_rfl, zero_le⟩ (((hF.continuousOn_vR k).sub hF.continuousOn_w).mono fun s hs => hlt s hs.2)
    fun s hs => sub_pos.2 (hopos s (hs.2.trans_lt htTe))
  -- (3) the monitored gaps after `q`
  have hgapj : ∀ j : Fin (nL + nR), ∃ c > 0, ∀ r ∈ Icc q t, c ≤ |W r ω - Girsanov.allMarks VL VR j r ω| := by
    intro j
    have hcj : ContinuousOn (fun r => |W r ω - Girsanov.allMarks VL VR j r ω|) (Icc q t) := by
      refine continuous_abs.comp_continuousOn ((hF.continuousOn_w.sub ?_).mono fun s hs => hlt s hs.2)
      cases j using Fin.addCases with
      | left i => simpa only [allMarks_castAdd'] using hF.continuousOn_vL i
      | right i => simpa only [allMarks_natAdd'] using hF.continuousOn_vR i
    refine G12.exists_pos_le_of_isCompact isCompact_Icc ⟨q, le_rfl, hqt⟩ hcj fun r hr => abs_pos.2 ?_
    have := hoff r hr.1 (hr.2.trans_lt htTe)
    cases j using Fin.addCases with
    | left i => rw [allMarks_castAdd']; exact sub_ne_zero.2 (this.1 i)
    | right i => rw [allMarks_natAdd']; exact sub_ne_zero.2 (this.2 i)
  choose cj hcj hcjle using hgapj
  have hne : (univ : Finset (Fin (nL + nR))).Nonempty := ⟨Fin.natAdd nL k, mem_univ _⟩
  set c₁ := (univ : Finset (Fin (nL + nR))).inf' hne cj with hc₁def
  have hc₁ : 0 < c₁ := (Finset.lt_inf'_iff hne).2 fun j _ => hcj j
  have hc₁le : ∀ j, ∀ r ∈ Icc q t, c₁ ≤ |W r ω - Girsanov.allMarks VL VR j r ω| := fun j r hr =>
    (Finset.inf'_le _ (mem_univ j)).trans (hcjle j r hr)
  refine ⟨max n₁ (max ⌈1 / c₀⌉₊ (max ⌈1 / c₁⌉₊ ⌈(t : ℝ)⌉₊)), fun n hn => ?_⟩
  have hn₁n : n₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : ⌈1 / c₀⌉₊ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₃ : ⌈1 / c₁⌉₊ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hn₄ : ⌈(t : ℝ)⌉₊ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have htn : t ≤ (n : ℝ≥0) := by
    rw [← NNReal.coe_le_coe]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hn₄)
  have hδ₀ : G12.dlt n < c₀ := dlt_lt_of_ceil_le hc₀ hn₂
  have hδ₁ : G12.dlt n < c₁ := dlt_lt_of_ceil_le hc₁ hn₃
  -- (1)
  have h1 : t ≤ locG xR j₀ G W VL VR B ζ T n ω :=
    hn₁.trans (G12.locG_mono hTm (Supp8.GB5.continuous_brownG_gb hgood) hn₁n ω)
  -- (2)
  have h2 : (t : WithTop ℝ≥0) ≤ lowOStop k G W VL VR ζ (lowDelta xR k n) ω := by
    simp only [lowOStop, hω, ↓reduceIte]
    refine Coupling.le_hitBelow fun s _ hs => ?_
    by_contra hst
    push Not at hst
    have := hc₀le s ⟨zero_le, hst.le⟩
    simp only [Pi.sub_apply] at this
    simp only [Coupling.stateAt] at hs
    have hδ : lowDelta xR k n ≤ G12.dlt n := min_le_left _ _
    linarith
  -- (3)
  have hsep : (t : ℝ≥0∞) ≤ lowSep ρL xR ρR k j₀ S G W VL VR ζ q n ω := by
    refine le_min (le_iInf₂ fun r hr => ?_) (by exact_mod_cast htn)
    by_contra hrt
    push Not at hrt
    have hrt' : r < t := by exact_mod_cast hrt
    obtain ⟨j, hj⟩ := hr.2
    have hrζ : (r : ℝ≥0∞) < goodLife G ζ ω := by
      simp only [goodLife, hω, ↓reduceIte]; exact hlt r hrt'.le
    rw [killedF, Girsanov.killed_of_lt hrζ, monGap] at hj
    rcases lt_or_ge r q with hrq | hrq
    · have : G12.dlt n < G12.dlt n + ((q : ℝ) - r) := by
        have : (r : ℝ) < q := hrq
        linarith
      exact absurd hj (not_le.2 (this.trans_le (le_max_right _ _)))
    · by_cases hm : IsMon (actW ρL ρR) (refW nL xR ρR k j₀ S) (Fin.natAdd nL k) j
      · have h3 := hc₁le j r ⟨hrq, hrt'.le⟩
        simp only [hm, ↓reduceIte] at hj
        exact absurd hj (not_le.2 (hδ₁.trans_le (h3.trans (le_max_left _ _))))
      · simp only [hm, ↓reduceIte] at hj
        have : G12.dlt n < G12.dlt n + 1 := by linarith
        exact absurd hj (not_le.2 (this.trans_le (le_max_left _ _)))
  -- (4)
  have h4 : (t : WithTop ℝ≥0) ≤ MathFin.exitTime (lowEnergy κ ρL xR ρR k j₀ S G W VL VR ζ q n) (C + 1) ω := by
    by_contra hcon
    push Not at hcon
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hcon)
    have hrt : r < t := by rw [← hr] at hcon; exact_mod_cast hcon
    obtain ⟨s, hs, hEs⟩ := (MathFin.exitTime_le_iff (continuous_lowEnergy hE hGm hGc hgood) (C + 1) r ω).1
      (by rw [← hr])
    have hst : s < t := lt_of_le_of_lt hs.2 hrt
    have hle := lowEnergy_le_of_pic hE hGm hGc hgood hκ (n := n) ⟨hqTe, hTeζ, hopos, hoff, hen⟩
      (hst.trans htTe) ((ENNReal.coe_le_coe.2 hst.le).trans hsep)
      fun r' hqr' hr's j _ => (hδ₁.trans_le (hc₁le j r' ⟨hqr', hr's.trans hst.le⟩)).le
    have hnn : 0 ≤ lowEnergy κ ρL xR ρR k j₀ S G W VL VR ζ q n s ω :=
      intervalIntegral.integral_nonneg s.coe_nonneg fun r _ => sq_nonneg _
    rw [abs_of_nonneg hnn] at hEs
    push_cast at hEs
    linarith
  have hσ := Sec2.TwoSeed.coe_capTime (locG xR j₀ G W VL VR B ζ T n)
    (fun ω => min (lowOStop k G W VL VR ζ (lowDelta xR k n) ω)
      (min (lowSep ρL xR ρR k j₀ S G W VL VR ζ q n ω : WithTop ℝ≥0)
        (MathFin.exitTime (lowEnergy κ ρL xR ρR k j₀ S G W VL VR ζ q n) (C + 1) ω))) ω
  have hfin : (t : WithTop ℝ≥0) ≤ (lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω : WithTop ℝ≥0) := by
    rw [lowStop, hσ]
    exact le_min (by exact_mod_cast h1) (le_min h2 (le_min hsep h4))
  exact_mod_cast hfin

end Exhaust

end G12Low

end Supp7

end InteractingSLE
