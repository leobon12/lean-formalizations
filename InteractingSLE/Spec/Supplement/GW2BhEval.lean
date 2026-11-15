/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BhRule
import InteractingSLE.Spec.Sec5.Prop59StageCross

/-!
# Evaluating the uncapped rule along a regular readout (S3)

Packet PROVE-GW2-BUF (S3, ruling R115). Along a path on which the causal readout `G` is a continuous antitone regular
gauge `g` (below a life `L`), and the path rule `A` takes the value `a₀`, the uncapped rule `GW2Bh.afterRule G A lev`
is the first time after `a₀` at which `g` reaches the level `ℓ = lev (min 1 (g a₀))`:

* `iSup_gaugeStop_eq`, `iSup_gaugeStop_eq_top`: the supremum over integer caps of GB6's `gaugeStop` is the first
  hitting time, or `⊤` when there is none;
* `hitRule_zero`: the cap-`0` rule is `0`;
* **`levelAt_eq`**: `levelAt G A` reads `min 1 (g a₀)`;
* **`afterRule_eq`**: the hit case (the first time `h` after `a₀` with `g h ≤ ℓ`, `h < L`);
* **`afterRule_eq_top`**: no hit and `L = ⊤`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version

/-! ### Integer caps of `gaugeStop` -/

theorem gaugeStop_eq_of_hit {g : ℝ≥0 → ℝ} (hg : Continuous g) {ε : ℝ} {h c : ℝ≥0} (hhc : h ≤ c)
    (hh : g h ≤ ε) (hlt : ∀ t < h, ε < g t) : gaugeStop g ε c = h := by
  refine le_antisymm (gaugeStop_le_of_le hhc hh) (not_lt.1 fun hlt' => ?_)
  have hm := gaugeStop_mem hg (hlt'.trans_le hhc)
  exact (not_le.2 (hlt _ hlt')) hm

theorem gaugeStop_eq_cap {g : ℝ≥0 → ℝ} (hg : Continuous g) {ε : ℝ} {c : ℝ≥0} (hlt : ∀ t ≤ c, ε < g t) :
    gaugeStop g ε c = c := by
  refine le_antisymm (gaugeStop_le g ε c) (not_lt.1 fun hlt' => ?_)
  exact (not_le.2 (hlt _ (gaugeStop_le g ε c))) (gaugeStop_mem hg hlt')

/-- The supremum over integer caps of `gaugeStop` is the first hitting time. -/
theorem iSup_gaugeStop_eq {g : ℝ≥0 → ℝ} (hg : Continuous g) {ε : ℝ} {h : ℝ≥0} (hh : g h ≤ ε)
    (hlt : ∀ t < h, ε < g t) : ⨆ n : ℕ, (gaugeStop g ε (n : ℝ≥0) : ℝ≥0∞) = h := by
  refine le_antisymm (iSup_le fun n => ?_) ?_
  · rcases le_total h (n : ℝ≥0) with hn | hn
    · rw [gaugeStop_eq_of_hit hg hn hh hlt]
    · exact ENNReal.coe_le_coe.2 ((gaugeStop_le g ε _).trans hn)
  · obtain ⟨n, hn⟩ := exists_nat_ge (h : ℝ)
    refine le_trans ?_ (le_iSup _ n)
    rw [gaugeStop_eq_of_hit hg (by exact_mod_cast hn) hh hlt]

/-- Without a hit the supremum over integer caps of `gaugeStop` is `⊤`. -/
theorem iSup_gaugeStop_eq_top {g : ℝ≥0 → ℝ} (hg : Continuous g) {ε : ℝ} (hlt : ∀ t, ε < g t) :
    ⨆ n : ℕ, (gaugeStop g ε (n : ℝ≥0) : ℝ≥0∞) = ⊤ := by
  have h : ∀ n : ℕ, (gaugeStop g ε (n : ℝ≥0) : ℝ≥0∞) = (n : ℝ≥0∞) := fun n => by
    rw [gaugeStop_eq_cap hg fun t _ => hlt t]
    rfl
  simp_rw [h]
  exact ENNReal.iSup_natCast

/-- The cap-`0` rule is `0`. -/
theorem hitRule_zero (G : GaugeReadout) (ε : RecData → ℝ) (x : RecData × (ℝ≥0 → ℝ)) :
    hitRule G ε 0 x = 0 := by
  have hinf : hitInf G ε 0 x = 0 := le_antisymm (hitInf_le_of_mem (mem_prefixHitSet_cap x)) zero_le
  have hm : x ∈ prefixHitSet G ε 0 (hitInf G ε 0 x) := Or.inl zero_le
  unfold hitRule
  rw [ite_eq_left hm, hinf]
  rfl

/-! ### The level read at `A` -/

/-- Rationals below a nonnegative real approach it. -/
theorem exists_nnrat_le_near {a : ℝ≥0} (ha : 0 < a) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℚ≥0, (q : ℝ≥0) ≤ a ∧ (a : ℝ) - δ < (q : ℝ≥0) := by
  have hlt : (a - (min (δ / 2) (a / 2)).toNNReal : ℝ≥0) < a := by
    apply tsub_lt_self ha
    exact Real.toNNReal_pos.2 (lt_min (half_pos hδ) (half_pos (by exact_mod_cast ha)))
  obtain ⟨q, h1, h2⟩ := Sec5.Prop59Stage.exists_nnrat_btwn₀ hlt
  refine ⟨q, h2.le, ?_⟩
  have h1' : ((a - (min (δ / 2) (a / 2)).toNNReal : ℝ≥0) : ℝ) < (q : ℝ≥0) := by exact_mod_cast h1
  have hle : (min (δ / 2) (a / 2)).toNNReal ≤ a := by
    refine Real.toNNReal_le_iff_le_coe.2 ((min_le_right _ _).trans ?_)
    linarith [a.2]
  rw [NNReal.coe_sub hle, Real.coe_toNNReal _ (le_min (by linarith) (by linarith [a.2]))] at h1'
  linarith [min_le_left (δ / 2) (a / 2)]

/-- **`levelAt` reads the regular gauge at `A`**, for an antitone continuous gauge. -/
theorem levelAt_eq {G : GaugeReadout} {A : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} {r : RecData} {w : ℝ≥0 → ℝ}
    {g : ℝ≥0 → ℝ} (hg : Continuous g) (hanti : Antitone g) {a₀ : ℝ≥0} (hA : A (r, w) = a₀)
    (hread : ∀ t ≤ a₀, G t (r, w) = g t) : levelAt G A (r, w) = min 1 (g a₀) := by
  have hterm : ∀ q : ℚ≥0, (if ((q : ℝ≥0) : ℝ≥0∞) ≤ A (r, w) then min 1 (G q (r, w)) else 1) =
      if (q : ℝ≥0) ≤ a₀ then min 1 (g q) else 1 := by
    intro q
    rw [hA]
    by_cases hq : (q : ℝ≥0) ≤ a₀
    · rw [ite_eq_left (ENNReal.coe_le_coe.2 hq), ite_eq_left hq, hread q hq]
    · rw [ite_eq_right (fun h => hq (ENNReal.coe_le_coe.1 h)), ite_eq_right hq]
  unfold levelAt
  simp_rw [hterm]
  have hlow : ∀ q : ℚ≥0, min 1 (g a₀) ≤ if (q : ℝ≥0) ≤ a₀ then min 1 (g q) else 1 := by
    intro q
    split_ifs with hq
    · exact min_le_min le_rfl (hanti hq)
    · exact min_le_left _ _
  have hbdd : BddBelow (range fun q : ℚ≥0 => if (q : ℝ≥0) ≤ a₀ then min 1 (g q) else 1) :=
    ⟨min 1 (g a₀), by rintro _ ⟨q, rfl⟩; exact hlow q⟩
  refine le_antisymm ?_ (le_ciInf hlow)
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ a₀) with h0 | h0
  · refine (ciInf_le hbdd 0).trans ?_
    rw [ite_eq_left (show ((0 : ℚ≥0) : ℝ≥0) ≤ a₀ by simp), ← h0]
    simp
  · refine le_of_forall_pos_lt_add fun δ hδ => ?_
    have hc : ContinuousAt (fun t => min 1 (g t)) a₀ := (continuous_const.min hg).continuousAt
    obtain ⟨η, hη, hball⟩ := Metric.continuousAt_iff.1 hc δ hδ
    obtain ⟨q, hqa, hqd⟩ := exists_nnrat_le_near h0 hη
    have hd : dist (q : ℝ≥0) a₀ < η := by
      rw [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.2 (NNReal.coe_le_coe.2 hqa))]
      linarith
    have := hball hd
    rw [Real.dist_eq] at this
    calc _ ≤ (if ((q : ℚ≥0) : ℝ≥0) ≤ a₀ then min 1 (g q) else 1) := ciInf_le hbdd q
      _ = min 1 (g q) := ite_eq_left hqa
      _ < min 1 (g a₀) + δ := by linarith [abs_lt.1 this]

/-! ### The uncapped rule along a regular readout -/

section Along

variable {G : GaugeReadout} {A : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} {lev : ℝ → ℝ} {r : RecData} {w : ℝ≥0 → ℝ}
  {g : ℝ≥0 → ℝ} {a₀ : ℝ≥0} {L : ℝ≥0∞}

/-- The normalized regular gauge. -/
def normGauge (g : ℝ≥0 → ℝ) (a₀ : ℝ≥0) (ℓ : ℝ) (t : ℝ≥0) : ℝ := if a₀ ≤ t then min 2 (g t / ℓ) else 2

theorem continuous_normGauge (hg : Continuous g) {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ2 : 2 * ℓ ≤ g a₀) :
    Continuous (normGauge g a₀ ℓ) := by
  unfold normGauge
  refine Continuous.if_le (continuous_const.min (hg.div_const ℓ)) continuous_const continuous_const
    continuous_id fun t ht => ?_
  rw [← ht]
  refine min_eq_left ?_
  rw [le_div_iff₀ hℓ]
  linarith

theorem normGauge_le_one_iff {ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ≥0) :
    normGauge g a₀ ℓ t ≤ 1 ↔ a₀ ≤ t ∧ g t ≤ ℓ := by
  unfold normGauge
  split_ifs with ht
  · constructor
    · intro h
      refine ⟨ht, ?_⟩
      rcases min_le_iff.1 h with h | h
      · norm_num at h
      · rwa [div_le_one hℓ] at h
    · rintro ⟨-, h⟩
      exact (min_le_right _ _).trans ((div_le_one hℓ).2 h)
  · constructor
    · intro h; norm_num at h
    · rintro ⟨h, -⟩; exact absurd h ht

theorem afterRead_eq (hg : Continuous g) (hanti : Antitone g) (hA : A (r, w) = a₀) (ha₀L : (a₀ : ℝ≥0∞) < L)
    (hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → G t (r, w) = g t) {t : ℝ≥0} (htL : (t : ℝ≥0∞) < L) :
    afterRead G A lev t (r, w) = normGauge g a₀ (lev (min 1 (g a₀))) t := by
  have hlevel : levelAt G A (r, w) = min 1 (g a₀) := levelAt_eq hg hanti hA fun t ht =>
    hread t ((ENNReal.coe_le_coe.2 ht).trans_lt ha₀L)
  unfold afterRead normGauge
  rw [hA, hlevel, hread t htL]
  by_cases ht : a₀ ≤ t
  · rw [ite_eq_left (ENNReal.coe_le_coe.2 ht), ite_eq_left ht]
  · rw [ite_eq_right (fun h => ht (ENNReal.coe_le_coe.1 h)), ite_eq_right ht]

/-- **The uncapped rule is the first hitting time after `a₀`**, when the hit happens before the life. -/
theorem afterRule_eq (hg : Continuous g) (hanti : Antitone g) (hA : A (r, w) = a₀)
    (hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → G t (r, w) = g t)
    (hℓ : 0 < lev (min 1 (g a₀))) (hℓ2 : 2 * lev (min 1 (g a₀)) ≤ g a₀)
    {h : ℝ≥0} (hah : a₀ ≤ h) (hhL : (h : ℝ≥0∞) < L) (hh : g h ≤ lev (min 1 (g a₀)))
    (hlt : ∀ t, a₀ ≤ t → t < h → lev (min 1 (g a₀)) < g t) :
    afterRule G A lev (r, w) = h := by
  set ℓ := lev (min 1 (g a₀)) with hℓdef
  have hn := continuous_normGauge (a₀ := a₀) hg hℓ hℓ2
  have hn0 : 1 < normGauge g a₀ ℓ 0 := by
    unfold normGauge
    split_ifs with h0
    · have : a₀ = 0 := le_antisymm h0 zero_le
      rw [← this, min_eq_left (by rw [le_div_iff₀ hℓ]; linarith)]
      norm_num
    · norm_num
  have hnh : normGauge g a₀ ℓ h ≤ 1 := (normGauge_le_one_iff hℓ h).2 ⟨hah, hh⟩
  have hnlt : ∀ t < h, 1 < normGauge g a₀ ℓ t := fun t ht => not_le.1 fun hle => by
    obtain ⟨h1, h2⟩ := (normGauge_le_one_iff hℓ t).1 hle
    exact (not_le.2 (hlt t h1 ht)) h2
  have ha₀L : (a₀ : ℝ≥0∞) < L := (ENNReal.coe_le_coe.2 hah).trans_lt hhL
  have hstop_le : ∀ n : ℕ, gaugeStop (normGauge g a₀ ℓ) 1 (n : ℝ≥0) ≤ h := fun n => by
    rcases le_total h (n : ℝ≥0) with hn' | hn'
    · exact gaugeStop_le_of_le hn' hnh
    · exact (gaugeStop_le _ _ _).trans hn'
  have hterm : ∀ n : ℕ, hitRule (afterRead G A lev) (fun _ => 1) (n : ℝ≥0) (r, w) =
      (gaugeStop (normGauge g a₀ ℓ) 1 (n : ℝ≥0) : ℝ≥0∞) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [Nat.cast_zero, hitRule_zero, le_antisymm (gaugeStop_le _ _ 0) zero_le, ENNReal.coe_zero]
    · refine hitRule_eq_gaugeStop hn (by exact_mod_cast hpos) hn0 fun u hu => ?_
      exact afterRead_eq hg hanti hA ha₀L hread ((ENNReal.coe_le_coe.2 (hu.trans (hstop_le n))).trans_lt hhL)
  unfold afterRule
  simp_rw [hterm]
  exact iSup_gaugeStop_eq hn hnh hnlt

/-- **Without a hit, the uncapped rule is `⊤`**, when the readout is regular forever. -/
theorem afterRule_eq_top (hg : Continuous g) (hanti : Antitone g) (hA : A (r, w) = a₀)
    (hread : ∀ t : ℝ≥0, G t (r, w) = g t)
    (hℓ : 0 < lev (min 1 (g a₀))) (hℓ2 : 2 * lev (min 1 (g a₀)) ≤ g a₀)
    (hlt : ∀ t, a₀ ≤ t → lev (min 1 (g a₀)) < g t) :
    afterRule G A lev (r, w) = ⊤ := by
  set ℓ := lev (min 1 (g a₀)) with hℓdef
  have hn := continuous_normGauge (a₀ := a₀) hg hℓ hℓ2
  have hn0 : 1 < normGauge g a₀ ℓ 0 := by
    unfold normGauge
    split_ifs with h0
    · have : a₀ = 0 := le_antisymm h0 zero_le
      rw [← this, min_eq_left (by rw [le_div_iff₀ hℓ]; linarith)]
      norm_num
    · norm_num
  have hnlt : ∀ t, 1 < normGauge g a₀ ℓ t := fun t => not_le.1 fun hle => by
    obtain ⟨h1, h2⟩ := (normGauge_le_one_iff hℓ t).1 hle
    exact (not_le.2 (hlt t h1)) h2
  have hterm : ∀ n : ℕ, hitRule (afterRead G A lev) (fun _ => 1) (n : ℝ≥0) (r, w) =
      (gaugeStop (normGauge g a₀ ℓ) 1 (n : ℝ≥0) : ℝ≥0∞) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [Nat.cast_zero, hitRule_zero, le_antisymm (gaugeStop_le _ _ 0) zero_le, ENNReal.coe_zero]
    · refine hitRule_eq_gaugeStop hn (by exact_mod_cast hpos) hn0 fun u _ => ?_
      exact afterRead_eq (L := ⊤) hg hanti hA ENNReal.coe_lt_top (fun t _ => hread t) ENNReal.coe_lt_top
  unfold afterRule
  simp_rw [hterm]
  exact iSup_gaugeStop_eq_top hn hnlt

end Along

end InteractingSLE.Theorem14.GW2Bh
