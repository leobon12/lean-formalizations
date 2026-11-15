/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6VersionRule
import InteractingSLE.Spec.Restart.StoppedExtendWF

/-!
# GB6: Galmarino rules on killed histories from causal path rules

Packet PROVE-GB6-HULLID. The corrected Aux. 54 (ruling R79, `Aux54.StoppedHullExtendRStatement`) needs the stop of a
stopped coupling to be `R (killed history)` for a measurable Galmarino rule `R` on `HistorySpace`. GB6's relative stops
are stopping rules of the record and of the relative driver path (`GB6Version*`: first entrance of a causal gauge).
This file turns such a path rule into a history rule:

* `sld`, `recon`: the driver path read back from a killed history (limit superior of the samples at the dyadic times
  strictly below `min t ζ`); measurable (`measurable_recon`), equal to the sampled continuous path up to the lifetime
  (`recon_eq_of_samples`), and determined by the samples before any time up to which two histories live
  (`recon_eq_recon_of_agree`);
* `IsPathRule`: a rule of (record, path) determined by the path up to its own value;
* `histRule`: the induced rule on histories, measurable (`measurable_histRule`) and Galmarino
  (`isHistGalmarino_histRule`);
* `hitRule`: the attained first time of the countable prefix test `prefixHitSet` of a causal readout; a measurable
  path rule (`measurable_hitRule`, `isPathRule_hitRule`) equal to the gauge stop on a sample read back through the stop
  (`hitRule_eq_gaugeStop`).

No probability; nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.HullId

open LawUnique Restart.StoppedExtendWF Exist.StagedLaw RelDrv RelDrv.Version

/-! ### Dyadic times strictly below a time -/

/-- The dyadic index strictly below `t > 0` at level `n`: `(⌈2ⁿ t⌉ − 1) / 2ⁿ`. -/
def sld (t : ℝ≥0) (n : ℕ) : ℕ × ℕ := (n, ⌈(2 : ℝ≥0) ^ n * t⌉₊ - 1)

theorem dyadicTime_sld_lt {t : ℝ≥0} (ht : 0 < t) (n : ℕ) : dyadicTime (sld t n) < t := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  have hx : 0 < (2 : ℝ≥0) ^ n * t := mul_pos h2 ht
  have hc : 1 ≤ ⌈(2 : ℝ≥0) ^ n * t⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hx).ne'
  show ((⌈(2 : ℝ≥0) ^ n * t⌉₊ - 1 : ℕ) : ℝ≥0) / 2 ^ n < t
  rw [div_lt_iff₀ h2]
  have hlt : ((⌈(2 : ℝ≥0) ^ n * t⌉₊ - 1 : ℕ) : ℝ≥0) + 1 < (2 : ℝ≥0) ^ n * t + 1 := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel hc]
    exact Nat.ceil_lt_add_one hx.le
  calc ((⌈(2 : ℝ≥0) ^ n * t⌉₊ - 1 : ℕ) : ℝ≥0) < (2 : ℝ≥0) ^ n * t := lt_of_add_lt_add_right hlt
    _ = t * 2 ^ n := mul_comm _ _

theorem le_dyadicTime_sld_add (t : ℝ≥0) (n : ℕ) : t ≤ dyadicTime (sld t n) + 1 / 2 ^ n := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  show t ≤ ((⌈(2 : ℝ≥0) ^ n * t⌉₊ - 1 : ℕ) : ℝ≥0) / 2 ^ n + 1 / 2 ^ n
  rw [← add_div, le_div_iff₀ h2]
  calc t * 2 ^ n = (2 : ℝ≥0) ^ n * t := mul_comm _ _
    _ ≤ (⌈(2 : ℝ≥0) ^ n * t⌉₊ : ℝ≥0) := Nat.le_ceil _
    _ ≤ ((⌈(2 : ℝ≥0) ^ n * t⌉₊ - 1 : ℕ) : ℝ≥0) + 1 := by
      rw [← Nat.cast_add_one]
      exact_mod_cast le_tsub_add

theorem tendsto_dyadicTime_sld (t : ℝ≥0) : Tendsto (fun n => dyadicTime (sld t n)) atTop (𝓝 t) := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | ht
  · subst h0
    have he : ∀ n, dyadicTime (sld 0 n) = 0 := fun n => by simp [dyadicTime, sld]
    simp only [he]
    exact tendsto_const_nhds
  have hlo : Tendsto (fun n : ℕ => t - 1 / 2 ^ n) atTop (𝓝 t) := by
    simpa only [tsub_zero] using tendsto_const_nhds.sub tendsto_one_div_two_pow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds (fun n => ?_)
    (fun n => (dyadicTime_sld_lt ht n).le)
  exact tsub_le_iff_right.2 (le_dyadicTime_sld_add t n)

theorem measurable_sld (n : ℕ) : Measurable fun t : ℝ≥0 => sld t n := by
  have hc : Measurable fun t : ℝ≥0 => ⌈(2 : ℝ≥0) ^ n * t⌉₊ :=
    (measurable_const.mul measurable_id).nat_ceil
  exact measurable_const.prodMk ((measurable_from_nat (f := fun k : ℕ => k - 1)).comp hc)

/-! ### Reading the driver path back from a killed history -/

variable {nL nR : ℕ}

/-- The time read by `recon` at `t`: `t` capped at the lifetime. -/
def reconEnd (γ : HistorySpace nL nR) (t : ℝ≥0) : ℝ≥0 := (min (t : ℝ≥0∞) γ.1).toNNReal

theorem coe_reconEnd (γ : HistorySpace nL nR) (t : ℝ≥0) : (reconEnd γ t : ℝ≥0∞) = min (t : ℝ≥0∞) γ.1 :=
  ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))

theorem reconEnd_of_le {γ : HistorySpace nL nR} {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ γ.1) : reconEnd γ t = t := by
  rw [reconEnd, min_eq_left ht, ENNReal.toNNReal_coe]

/-- **The driver path read back from a history**: at time `t`, the limit superior of the driver samples at the dyadic
times strictly below `min t ζ` (`0` when `min t ζ = 0`). Only samples strictly before the lifetime are read. -/
def recon (γ : HistorySpace nL nR) (t : ℝ≥0) : ℝ :=
  if reconEnd γ t = 0 then 0 else limsup (fun n => (γ.2 (sld (reconEnd γ t) n)).1) atTop

theorem measurable_reconEnd (t : ℝ≥0) : Measurable fun γ : HistorySpace nL nR => reconEnd γ t :=
  (measurable_const.min measurable_fst).ennreal_toNNReal

theorem measurable_recon_apply (t : ℝ≥0) : Measurable fun γ : HistorySpace nL nR => recon γ t := by
  have hS : Measurable fun x : HistorySpace nL nR × (ℕ × ℕ) => (x.1.2 x.2).1 :=
    measurable_from_prod_countable_left fun p =>
      measurable_fst.comp ((measurable_pi_apply p).comp measurable_snd)
  have hn : ∀ n : ℕ, Measurable fun γ : HistorySpace nL nR => (γ.2 (sld (reconEnd γ t) n)).1 := fun n =>
    hS.comp (measurable_id.prodMk ((measurable_sld n).comp (measurable_reconEnd t)))
  exact Measurable.ite ((measurable_reconEnd t) (measurableSet_singleton 0)) measurable_const (Measurable.limsup hn)

theorem measurable_recon : Measurable fun γ : HistorySpace nL nR => recon γ :=
  measurable_pi_iff.2 measurable_recon_apply

/-- A history whose samples before its lifetime are those of a continuous path from `0` reads back that path, frozen
at the lifetime. -/
theorem recon_eq_of_samples {γ : HistorySpace nL nR} {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : ∀ p, (dyadicTime p : ℝ≥0∞) < γ.1 → (γ.2 p).1 = w (dyadicTime p)) (t : ℝ≥0) :
    recon γ t = w (reconEnd γ t) := by
  unfold recon
  split_ifs with h0
  · rw [h0, hw0]
  · have hpos : 0 < reconEnd γ t := lt_of_le_of_ne zero_le (Ne.symm h0)
    have hle : (reconEnd γ t : ℝ≥0∞) ≤ γ.1 := (coe_reconEnd γ t).trans_le (min_le_right _ _)
    have he : (fun n => (γ.2 (sld (reconEnd γ t) n)).1) = fun n => w (dyadicTime (sld (reconEnd γ t) n)) :=
      funext fun n => hs _ ((ENNReal.coe_lt_coe.2 (dyadicTime_sld_lt hpos n)).trans_le hle)
    rw [he]
    exact ((hw.tendsto _).comp (tendsto_dyadicTime_sld _)).limsup_eq

/-- Up to the lifetime, the read-back of a sampled continuous path is the path. -/
theorem recon_eq_of_samples_of_le {γ : HistorySpace nL nR} {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : ∀ p, (dyadicTime p : ℝ≥0∞) < γ.1 → (γ.2 p).1 = w (dyadicTime p)) {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ γ.1) :
    recon γ t = w t := by
  rw [recon_eq_of_samples hw hw0 hs t, reconEnd_of_le ht]

/-- Two histories living at least until `τ` with the same samples before `τ` read back the same path on `[0, τ]`. -/
theorem recon_eq_recon_of_agree {γ γ' : HistorySpace nL nR} {τ : ℝ≥0∞} (hγ : τ ≤ γ.1) (hγ' : τ ≤ γ'.1)
    (hag : ∀ p, (dyadicTime p : ℝ≥0∞) < τ → γ.2 p = γ'.2 p) {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ τ) :
    recon γ t = recon γ' t := by
  have h1 : reconEnd γ t = t := reconEnd_of_le (ht.trans hγ)
  have h2 : reconEnd γ' t = t := reconEnd_of_le (ht.trans hγ')
  unfold recon
  rw [h1, h2]
  split_ifs with h0
  · rfl
  · have hpos : 0 < t := lt_of_le_of_ne zero_le (Ne.symm h0)
    have he : (fun n => (γ.2 (sld t n)).1) = fun n => (γ'.2 (sld t n)).1 :=
      funext fun n => by rw [hag _ ((ENNReal.coe_lt_coe.2 (dyadicTime_sld_lt hpos n)).trans_le ht)]
    rw [he]

/-- The killed history's samples are the sampled driver before the lifetime. -/
theorem killedHistory_samples {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (e : Ω → ℝ≥0∞) (ω : Ω) (p : ℕ × ℕ)
    (hp : (dyadicTime p : ℝ≥0∞) < (killedHistory W VL VR e ω).1) :
    ((killedHistory W VL VR e ω).2 p).1 = W (dyadicTime p) ω := by
  have hp' : (dyadicTime p : ℝ≥0∞) < e ω := hp
  simp only [killedHistory, hp', ↓reduceIte]

/-! ### Path rules and the induced history rules -/

/-- **A stopping rule of a record and a driver path**, determined by the path up to its own value: changing the path
after the value does not change the value. -/
def IsPathRule (ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞) : Prop :=
  ∀ (r : RecData) (w w' : ℝ≥0 → ℝ), (∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ ρ (r, w) → w u = w' u) → ρ (r, w') = ρ (r, w)

/-- **The history rule of a path rule** at the record `r`: the path rule of the read-back driver when it does not
exceed the lifetime, `⊤` otherwise. -/
def histRule (ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞) (r : RecData) (γ : HistorySpace nL nR) : ℝ≥0∞ :=
  if ρ (r, recon γ) ≤ γ.1 then ρ (r, recon γ) else ⊤

theorem measurable_histRule {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ : Measurable ρ) (r : RecData) :
    Measurable (histRule (nL := nL) (nR := nR) ρ r) := by
  have h1 : Measurable fun γ : HistorySpace nL nR => ρ (r, recon γ) :=
    hρ.comp (measurable_const.prodMk measurable_recon)
  exact Measurable.ite (measurableSet_le h1 measurable_fst) h1 measurable_const

/-- **The history rule of a path rule is Galmarino** (no continuity of the histories is needed). -/
theorem isHistGalmarino_histRule {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ : IsPathRule ρ) (r : RecData) :
    IsHistGalmarino (histRule (nL := nL) (nR := nR) ρ r) := by
  intro γ γ' _ _ hR hR' hag
  by_cases h : ρ (r, recon γ) ≤ γ.1
  · have hRγ : histRule ρ r γ = ρ (r, recon γ) := by
      simp only [histRule, h, ↓reduceIte]
    rw [hRγ] at hR' hag ⊢
    have hρ' : ρ (r, recon γ') = ρ (r, recon γ) :=
      hρ r (recon γ) (recon γ') fun u hu => recon_eq_recon_of_agree h hR' hag hu
    have h' : ρ (r, recon γ') ≤ γ'.1 := hρ' ▸ hR'
    change (if ρ (r, recon γ') ≤ γ'.1 then ρ (r, recon γ') else ⊤) = _
    rw [hρ']
    simp only [hR', ↓reduceIte]
  · have hRγ : histRule ρ r γ = ⊤ := by
      simp only [histRule, h, ↓reduceIte]
    rw [hRγ, top_le_iff] at hR
    exact (h (hR ▸ le_top)).elim

/-- On a killed history of a continuous driver from `0` whose stop is the path rule, the history rule returns the
stop. -/
theorem histRule_killedHistory {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ : IsPathRule ρ) {r : RecData} {Ω : Type*}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {e : Ω → ℝ≥0∞} {ω : Ω}
    (hW : Continuous fun t => W t ω) (hW0 : W 0 ω = 0) (he : e ω = ρ (r, fun t => W t ω)) :
    histRule ρ r (killedHistory W VL VR e ω) = e ω := by
  set γ := killedHistory W VL VR e ω with hγ
  have hγ1 : γ.1 = e ω := rfl
  have hs : ∀ p, (dyadicTime p : ℝ≥0∞) < γ.1 → (γ.2 p).1 = W (dyadicTime p) ω :=
    killedHistory_samples W VL VR e ω
  have hrec : ρ (r, recon γ) = ρ (r, fun t => W t ω) :=
    hρ r (fun t => W t ω) (recon γ) fun u hu =>
      (recon_eq_of_samples_of_le hW hW0 hs (hγ1 ▸ he ▸ hu)).symm
  have hle : ρ (r, recon γ) ≤ γ.1 := by rw [hrec, hγ1, he]
  have hR : histRule ρ r γ = ρ (r, recon γ) := by simp only [histRule, hle, ↓reduceIte]
  rw [hR, hrec, he]

/-! ### The attained first time of the countable prefix test -/

section Hit

variable (G : GaugeReadout) (ε : RecData → ℝ) (c : ℝ≥0)

/-- The infimum of the times at which the countable prefix test holds (it holds from the cap `c` on). -/
def hitInf (x : RecData × (ℝ≥0 → ℝ)) : ℝ≥0 := sInf {t | x ∈ prefixHitSet G ε c t}

open Classical in
/-- **The attained first time of the prefix test**: `hitInf` when the test holds there, `⊤` otherwise. -/
def hitRule (x : RecData × (ℝ≥0 → ℝ)) : ℝ≥0∞ :=
  if x ∈ prefixHitSet G ε c (hitInf G ε c x) then (hitInf G ε c x : ℝ≥0∞) else ⊤

variable {G ε c}

theorem mem_prefixHitSet_mono {x : RecData × (ℝ≥0 → ℝ)} {t t' : ℝ≥0} (htt : t ≤ t')
    (hx : x ∈ prefixHitSet G ε c t) : x ∈ prefixHitSet G ε c t' := by
  rcases hx with h | h
  · exact Or.inl (h.trans htt)
  · exact Or.inr fun n => (h n).imp fun q hq => ⟨hq.1.trans htt, hq.2⟩

theorem mem_prefixHitSet_cap (x : RecData × (ℝ≥0 → ℝ)) : x ∈ prefixHitSet G ε c c := Or.inl le_rfl

theorem hitInf_le_of_mem {x : RecData × (ℝ≥0 → ℝ)} {t : ℝ≥0} (hx : x ∈ prefixHitSet G ε c t) :
    hitInf G ε c x ≤ t :=
  csInf_le (OrderBot.bddBelow _) hx

theorem notMem_of_lt_hitInf {x : RecData × (ℝ≥0 → ℝ)} {t : ℝ≥0} (ht : t < hitInf G ε c x) :
    x ∉ prefixHitSet G ε c t := fun hx => (not_le.2 ht) (hitInf_le_of_mem hx)

theorem _root_.InteractingSLE.Supp8.GB6.HullId.exists_nnrat_btwn {t a : ℝ≥0} (h : t < a) :
    ∃ q : ℚ≥0, t < q ∧ (q : ℝ≥0) < a := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (t : ℝ) < a from h)
  have hq0 : (0 : ℝ) ≤ q := t.2.trans hq1.le
  have hcoe : (((q.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = q := by
    rw [coe_toNNRat_eq, Real.coe_toNNReal _ hq0]
  exact ⟨q.toNNRat, NNReal.coe_lt_coe.1 (hcoe ▸ hq1), NNReal.coe_lt_coe.1 (hcoe ▸ hq2)⟩

theorem hitInf_lt_iff (x : RecData × (ℝ≥0 → ℝ)) (a : ℝ≥0) :
    hitInf G ε c x < a ↔ ∃ q : ℚ≥0, (q : ℝ≥0) < a ∧ x ∈ prefixHitSet G ε c q := by
  constructor
  · intro h
    obtain ⟨t, ht, hta⟩ := exists_lt_of_csInf_lt ⟨c, mem_prefixHitSet_cap x⟩ h
    obtain ⟨q, htq, hqa⟩ := exists_nnrat_btwn hta
    exact ⟨q, hqa, mem_prefixHitSet_mono htq.le ht⟩
  · rintro ⟨q, hqa, hq⟩
    exact (hitInf_le_of_mem hq).trans_lt hqa

theorem measurable_hitInf (hG : ∀ t, Measurable (G t)) (hε : Measurable ε) : Measurable (hitInf G ε c) := by
  refine measurable_of_Iio fun a => ?_
  have he : hitInf G ε c ⁻¹' Iio a =
      ⋃ q : ℚ≥0, ⋃ (_ : (q : ℝ≥0) < a), {x | x ∈ prefixHitSet G ε c q} := by
    ext x
    simp only [mem_preimage, mem_Iio, hitInf_lt_iff, mem_iUnion, mem_ofPred_eq, exists_prop]
  rw [he]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => measurableSet_prefixHitSet hG hε c q

theorem measurableSet_mem_prefixHitSet_hitInf (hG : ∀ t, Measurable (G t)) (hε : Measurable ε) :
    MeasurableSet {x | x ∈ prefixHitSet G ε c (hitInf G ε c x)} := by
  have hm := measurable_hitInf (c := c) hG hε
  have he : {x | x ∈ prefixHitSet G ε c (hitInf G ε c x)} =
      {x | c ≤ hitInf G ε c x} ∪ ⋂ n : ℕ, ⋃ q : ℚ≥0,
        ({x | (q : ℝ≥0) ≤ hitInf G ε c x} ∩ {x | G q x < ε x.1 + 1 / ((n : ℝ) + 1)}) := by
    ext x
    simp only [prefixHitSet, mem_ofPred_eq, mem_union, mem_iInter, mem_iUnion, mem_inter_iff]
  rw [he]
  exact (measurableSet_le measurable_const hm).union (MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q =>
    (measurableSet_le measurable_const hm).inter
      (measurableSet_lt (hG q) ((hε.comp measurable_fst).add_const _)))

theorem measurable_hitRule (hG : ∀ t, Measurable (G t)) (hε : Measurable ε) : Measurable (hitRule G ε c) :=
  Measurable.ite (measurableSet_mem_prefixHitSet_hitInf hG hε)
    (measurable_coe_nnreal_ennreal.comp (measurable_hitInf hG hε)) measurable_const

/-- **The attained first time of the prefix test of a causal readout is a path rule.** -/
theorem isPathRule_hitRule (hG : IsCausal G) : IsPathRule (hitRule G ε c) := by
  intro r w w' hag
  by_cases hm : (r, w) ∈ prefixHitSet G ε c (hitInf G ε c (r, w))
  · have hρ : hitRule G ε c (r, w) = hitInf G ε c (r, w) := by
      simp only [hitRule, hm, ↓reduceIte]
    rw [hρ] at hag ⊢
    set τ := hitInf G ε c (r, w) with hτ
    have hiff : ∀ t ≤ τ, ((r, w) ∈ prefixHitSet G ε c t ↔ (r, w') ∈ prefixHitSet G ε c t) := fun t ht =>
      isDetUpTo_prefixHitSet hG ε c t r w w' fun u hu => hag u (ENNReal.coe_le_coe.2 (hu.trans ht))
    have hm' : (r, w') ∈ prefixHitSet G ε c τ := (hiff τ le_rfl).1 hm
    have hle : hitInf G ε c (r, w') ≤ τ := hitInf_le_of_mem hm'
    have hge : τ ≤ hitInf G ε c (r, w') := by
      refine le_csInf ⟨c, mem_prefixHitSet_cap _⟩ fun t ht => ?_
      by_contra hlt
      exact notMem_of_lt_hitInf (not_le.1 hlt) ((hiff t (not_le.1 hlt).le).2 ht)
    have heq : hitInf G ε c (r, w') = τ := le_antisymm hle hge
    have hm'' : (r, w') ∈ prefixHitSet G ε c (hitInf G ε c (r, w')) := heq ▸ hm'
    unfold hitRule
    simp only [hm'', ↓reduceIte]
    rw [heq]
  · have hρ : hitRule G ε c (r, w) = ⊤ := by
      simp only [hitRule, hm, ↓reduceIte]
    have hww : w' = w := funext fun u => (hag u (hρ ▸ le_top)).symm
    rw [hww]

/-- **On a sample read back through the gauge stop, the prefix-test rule is the gauge stop.** -/
theorem hitRule_eq_gaugeStop {r : RecData} {w : ℝ≥0 → ℝ} {g : ℝ≥0 → ℝ} (hg : Continuous g) (hc : 0 < c)
    (h0 : ε r < g 0) (hread : ∀ u ≤ gaugeStop g (ε r) c, G u (r, w) = g u) :
    hitRule G ε c (r, w) = gaugeStop g (ε r) c := by
  have hiff : ∀ t, (r, w) ∈ prefixHitSet G ε c t ↔ gaugeStop g (ε r) c ≤ t :=
    mem_prefixHitSet_iff hg hc h0 hread
  have hset : {t | (r, w) ∈ prefixHitSet G ε c t} = Ici (gaugeStop g (ε r) c) := by
    ext t
    exact hiff t
  have hinf : hitInf G ε c (r, w) = gaugeStop g (ε r) c := by
    rw [hitInf, hset, csInf_Ici]
  have hm : (r, w) ∈ prefixHitSet G ε c (hitInf G ε c (r, w)) := by
    rw [hinf]
    exact (hiff _).2 le_rfl
  unfold hitRule
  simp only [hm, ↓reduceIte]
  rw [hinf]

end Hit

end InteractingSLE.Supp8.GB6.HullId
