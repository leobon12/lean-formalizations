/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VsRec
import InteractingSLE.Spec.Supplement.Q3StopAnnounce
import InteractingSLE.Spec.Supplement.GW2GmSlit

/-!
# SB2(1)'s stop rules read from the record and the relative driver (D19)

Packet PROVE-AUX61-NOJUMP (decision D19).

* **`gaugeRead`**: the causal measurable readout `t ↦ decode r (traceAt t w)`: the record's function at the trace of
  the driver path;
* **`stopRule m`**: GB6's attained prefix-test rule `hitRule` of the readout at the record level `recLevel` and cap
  `m + 1`; **`annRules`** (Q3): its announcing rules;
* **`rules_of_readback`** (deterministic): along a driver whose readout is a continuous positive gauge `g` up to the
  gauge stop `localStop g m`, the stop rule is that stop, and the announcing rules are strictly below it with supremum
  the stop.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Vs

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp8.Q3Stop

/-- **The gauge read from a record and a driver path**: the record's function at the trace of the path. -/
def gaugeRead : GaugeReadout := fun t p => decode p.1 (LP.traceAt t p.2)

theorem isCausal_gaugeRead : IsCausal gaugeRead := fun t r w w' h => by
  simp only [gaugeRead]; rw [LP.traceAt_congr h]

theorem measurable_gaugeRead (t : ℝ≥0) : Measurable (gaugeRead t) :=
  measurable_decode.comp (measurable_fst.prodMk ((LP.measurable_traceAt t).comp measurable_snd))

/-- **The `m`-th stop rule.** -/
def stopRule (m : ℕ) : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞ := hitRule gaugeRead (recLevel gaugeRead m) (m + 1)

theorem measurable_stopRule (m : ℕ) : Measurable (stopRule m) :=
  measurable_hitRule measurable_gaugeRead (measurable_recLevel measurable_gaugeRead m)

theorem isPathRule_stopRule (m : ℕ) : IsPathRule (stopRule m) := isPathRule_hitRule isCausal_gaugeRead

/-- The trace of the zero driver at time `0` is `0`. -/
theorem traceAt_zero_zero : LP.traceAt 0 (fun _ => 0) = 0 := by
  rw [LP.traceAt_eq_of_isGeneratingTrace GW2TipSystem.Gm.isGeneratingTrace_zero_slit continuousOn_const rfl
    ENNReal.coe_lt_top]
  exact GW2TipSystem.Gm.isGeneratingTrace_zero_slit.1

theorem gaugeRead_zero_zero (r : RecData) : gaugeRead 0 (r, fun _ => 0) = decode r 0 := by
  simp only [gaugeRead, traceAt_zero_zero]

/-- **Read-back announces the coordinate stop** (deterministic): if the readout of `(r, w)` is a continuous gauge `g`
with `g 0 > 0` up to its stop `localStop g m` (and at the zero path at time `0`), then the stop rule is that stop and
the announcing rules are strictly below it, with supremum the stop. -/
theorem rules_of_readback {r : RecData} {w : ℝ≥0 → ℝ} {g : ℝ≥0 → ℝ} (hgc : Continuous g) (hg0 : 0 < g 0)
    (m : ℕ) (h0 : gaugeRead 0 (r, fun _ => 0) = g 0)
    (hrd : ∀ u ≤ localStop g m, gaugeRead u (r, w) = g u) :
    stopRule m (r, w) = (localStop g m : ℝ≥0∞) ∧
      (∀ n, annRules gaugeRead m n (r, w) < (localStop g m : ℝ≥0∞)) ∧
      ⨆ n, annRules gaugeRead m n (r, w) = (localStop g m : ℝ≥0∞) := by
  set ε := gaugeLevel (g 0) m with hεdef
  have hε0 : ε < g 0 := gaugeLevel_lt hg0 m
  have hrec : recLevel gaugeRead m r = ε := by
    change gaugeLevel (gaugeRead 0 (r, fun _ => 0)) m = _
    rw [h0]
  set T := localStop g m with hTdef
  have hT : T = gaugeStop g ε ((m : ℝ≥0) + 1) := rfl
  refine ⟨?_, ?_⟩
  · unfold stopRule
    rw [hitRule_eq_gaugeStop hgc (by positivity) (by rw [hrec]; exact hε0) fun u hu => hrd u (by
      rw [hrec] at hu; exact hu), hrec, hT]
  set εs : ℕ → ℝ := fun k => ε + (g 0 - ε) / ((k : ℝ) + 2) with hεs
  have hlev : ∀ k, annLevel gaugeRead m k r = εs k := fun k => by
    simp only [annLevel, hrec, h0, hεs]
  have hεs_gt : ∀ k, ε < εs k := fun k =>
    lt_add_of_pos_right _ (div_pos (sub_pos.2 hε0) (by positivity))
  have hεs_lt : ∀ k, εs k < g 0 := fun k => by
    have hk : (1 : ℝ) < (k : ℝ) + 2 := by
      have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      linarith
    have h2 : (g 0 - ε) / ((k : ℝ) + 2) < g 0 - ε := div_lt_self (sub_pos.2 hε0) hk
    simp only [hεs]
    linarith
  have hεs_anti : Antitone εs := fun k l hkl => by
    have : (g 0 - ε) / ((l : ℝ) + 2) ≤ (g 0 - ε) / ((k : ℝ) + 2) :=
      div_le_div_of_nonneg_left (sub_pos.2 hε0).le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hkl 2)
    simp only [hεs]
    linarith
  have hstop : ∀ k, annRule gaugeRead m k (r, w) = (gaugeStop g (εs k) (annCap m k) : ℝ≥0∞) := fun k => by
    have hle : gaugeStop g (εs k) (annCap m k) ≤ T :=
      gaugeStop_mono hgc (hεs_gt k).le (annCap_lt m k).le
    have hh : hitRule gaugeRead (annLevel gaugeRead m k) (annCap m k) (r, w) =
        gaugeStop g (annLevel gaugeRead m k r) (annCap m k) :=
      hitRule_eq_gaugeStop hgc (annCap_pos m k) (by rw [hlev]; exact hεs_lt k) fun u hu =>
        hrd u (by rw [hlev] at hu; exact hu.trans hle)
    rw [annRule, hh, hlev, min_eq_left (ENNReal.coe_le_coe.2 (gaugeStop_le _ _ _))]
  have hmono : Monotone fun k => gaugeStop g (εs k) (annCap m k) := fun k l hkl =>
    gaugeStop_mono hgc (hεs_anti hkl) (annCap_mono m hkl)
  have hrules : ∀ n, annRules gaugeRead m n (r, w) = (gaugeStop g (εs n) (annCap m n) : ℝ≥0∞) := fun n => by
    refine le_antisymm (Finset.sup_le fun k hk => ?_) ?_
    · rw [hstop]
      exact ENNReal.coe_le_coe.2 (hmono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)))
    · rw [← hstop]
      exact Finset.le_sup (f := fun k => annRule gaugeRead m k (r, w)) (Finset.self_mem_range_succ n)
  have hlt : ∀ n, gaugeStop g (εs n) (annCap m n) < T := fun n =>
    gaugeStop_lt_of_lt hgc (hεs_gt n) (hεs_lt n) (annCap_lt m n)
  refine ⟨fun n => by rw [hrules]; exact ENNReal.coe_lt_coe.2 (hlt n),
    le_antisymm (iSup_le fun n => by rw [hrules]; exact ENNReal.coe_le_coe.2 (hlt n).le) ?_⟩
  refine le_of_forall_lt fun a ha => ?_
  have ha' : a ≠ ⊤ := (ha.trans ENNReal.coe_lt_top).ne
  have htT : a.toNNReal < T := by
    rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal ha']
    exact ha
  obtain ⟨n, hn⟩ := exists_lt_gaugeStop hgc htT (εs := εs) (cs := annCap m)
    (fun δ hδ => by
      obtain ⟨N, hN⟩ := exists_div_add_two_lt (sub_pos.2 hε0).le hδ
      exact ⟨N, fun n hn => by simp only [hεs]; linarith [hN n hn]⟩)
    (fun t' ht' => exists_lt_annCap m ht')
  rw [← ENNReal.coe_toNNReal ha']
  exact (ENNReal.coe_lt_coe.2 hn).trans_le (by
    rw [← hrules]
    exact le_iSup (fun n => annRules gaugeRead m n (r, w)) n)

end InteractingSLE.Theorem14.SB.Vs
