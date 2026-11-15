/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.WordsHorizon
import InteractingSLE.Spec.Ito.FiltrationBasic

/-!
# The whole-tail comparison: transience transfers through a change of weights of finite energy

Packet PROVE-ZHAN-B4. Astra §3, "the whole-tail Girsanov localization" (`source/external/AstraIG1/
ig1_formalization_proofs.txt` L1572–L1584 and L1597–L1601; `ig1_additional_proofs.txt` §1.3, "The whole-tail change
of measure"): if the total energy of a change of weights `ρ → ρ'` is almost surely finite, an almost-sure transience
property of the reference weights transfers to the original evolution, although the two laws need not be
absolutely continuous on any finite horizon uniformly.

This file proves it without an infinite-horizon measure. For a non-transient trace there are `R` and, for every `k`,
a rational time `p ≥ k` with `‖η(p)‖ ≤ R`; for every horizon `T > p` the gaps stay above some `δ_n` on `[0, T]` and
the energy is at most some `m`, so the path lies in `lateEvent δ_n T m k R`, whose probability is at most
`(e^m)^{1/2} codeLaw ρ' (lateSet k R)^{1/2}` (`measure_lateEvent_le`), a bound independent of `T` and `n`. It tends to
`0` as `k → ∞` when the reference trace is almost surely transient (`codeLaw_lateSet_tendsto_zero`).

## Main results

* `ae_tendsto_of_changeEnergy`: the transfer, with the reference entering only through its canonical law.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Zhan

open Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart Girsanov Coupling

/-- A rational time in `[t, t + ε)`. -/
theorem exists_nnrat_near (t : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℚ≥0, t ≤ (p : ℝ≥0) ∧ ((p : ℝ≥0) : ℝ) < t + ε := by
  obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show (t : ℝ) < t + ε by linarith)
  have hq : (0 : ℚ) ≤ q := by exact_mod_cast (t.coe_nonneg.trans h1.le)
  have hc : (((q.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = q := by
    have := map_nnratCast NNReal.toRealHom q.toNNRat
    simp only [NNReal.coe_toRealHom] at this
    rw [this, show ((q.toNNRat : ℚ≥0) : ℝ) = ((q.toNNRat : ℚ) : ℝ) from (Rat.cast_nnratCast _).symm,
      Rat.coe_toNNRat q hq]
  refine ⟨q.toNNRat, ?_, by rw [hc]; exact h2⟩
  rw [← NNReal.coe_le_coe, hc]
  exact h1.le

/-- **A non-transient continuous path returns**: some disc of integer radius contains it at rational times beyond
every `k`. -/
theorem exists_late_of_not_tendsto {η : ℝ≥0 → ℂ} (hc : Continuous η)
    (h : ¬ Tendsto (fun t => ‖η t‖) atTop atTop) :
    ∃ R : ℕ, ∀ k : ℕ, ∃ p : ℚ≥0, (k : ℚ≥0) ≤ p ∧ ‖η p‖ ≤ R := by
  rw [tendsto_atTop] at h
  push Not at h
  obtain ⟨b, hb⟩ := h
  refine ⟨⌈b⌉₊, fun k => ?_⟩
  obtain ⟨t, hkt, htb⟩ := frequently_atTop.1 (not_eventually.1 hb) (k : ℝ≥0)
  push Not at htb
  have hU : ∀ᶠ s in 𝓝 t, ‖η s‖ < b := (continuous_norm.comp hc).continuousAt.eventually (gt_mem_nhds htb)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hU
  obtain ⟨p, htp, hpε⟩ := exists_nnrat_near t hε
  refine ⟨p, ?_, ?_⟩
  · have : ((k : ℚ≥0) : ℝ≥0) ≤ (p : ℝ≥0) := by
      rw [show ((k : ℚ≥0) : ℝ≥0) = (k : ℝ≥0) by norm_cast]
      exact hkt.trans htp
    exact_mod_cast this
  · have hd : dist (p : ℝ≥0) t < ε := by
      rw [NNReal.dist_eq, abs_lt]
      have : (t : ℝ) ≤ ((p : ℝ≥0) : ℝ) := by exact_mod_cast htp
      constructor <;> linarith
    exact ((hball hd).le).trans (Nat.le_ceil b)

/-- A continuous positive function has a positive lower bound `1/(n+1)` on `[0, T]`. -/
theorem exists_one_div_le_on_Iic {f : ℝ≥0 → ℝ} (hf : Continuous f) (hpos : ∀ s, 0 < f s) (T : ℝ≥0) :
    ∃ n : ℕ, ∀ s ≤ T, 1 / ((n : ℝ) + 1) ≤ f s := by
  have hK : IsCompact (Set.Icc (0 : ℝ≥0) T) := isCompact_Icc
  obtain ⟨s₀, -, hs₀⟩ := hK.exists_isMinOn ⟨0, le_rfl, zero_le⟩ hf.continuousOn
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hpos s₀)
  exact ⟨n, fun s hs => hn.le.trans (hs₀ ⟨zero_le, hs⟩)⟩

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL ρL' : Fin nL → ℝ}
  {ρR ρR' : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- The bound of one horizon tends to `0` with the late time. -/
theorem tendsto_lateBound (m : ℝ) {c : ℕ → ℝ≥0∞} (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun k => ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) * c k ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k => c k ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hc
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this
  have hne : ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) ENNReal.ofReal_ne_top
  have := ENNReal.Tendsto.const_mul h1 (Or.inr hne)
  rwa [mul_zero] at this

/-- **The whole-tail comparison.** Let `(W, V, B)` be an integrated evolution of a separated word with weights `ρ`
whose state is almost surely continuous with all gaps positive, with infinite lifetime, and let `ρ'` be other
weights such that the total energy of the change `ρ → ρ'` is almost surely finite. If the canonical law of `ρ'` from
the same start has infinite lifetime and rare late returns of its trace to every disc, then almost surely every
continuous generating trace of `W` on `[0, ∞)` tends to `∞`. -/
theorem ae_tendsto_of_changeEnergy (hκ : 0 < κ) [IsProbabilityMeasure P] (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hgood : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ W 0 ω = 0 ∧ Continuous (fun s => stateAt W VL VR s ω) ∧
      ∀ s, 0 < minGap (stateAt W VL VR s ω))
    (henergy : ∀ᵐ ω ∂P, ∃ m : ℝ, ∀ T : ℝ≥0, changeEnergy κ ρL ρL' ρR ρR' W VL VR T ω ≤ m)
    (href : codeLaw κ ρL' ρR' {x | cζ x = ⊤} (xL, xR) = 1)
    (hlate : ∀ R : ℝ, Tendsto (fun k => codeLaw κ ρL' ρR' (lateSet k R) (xL, xR)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set Good : Ω → Prop := fun ω => ζ ω = ⊤ ∧ W 0 ω = 0 ∧ Continuous (fun s => stateAt W VL VR s ω) ∧
    ∀ s, 0 < minGap (stateAt W VL VR s ω) with hGood
  set N := {ω | ¬ Good ω} with hNdef
  have hN : P N = 0 := ae_iff.1 hgood
  set G := (toMeasurable P N)ᶜ with hGdef
  have hGm : MeasurableSet[usualAugmentation 𝓕 P 0] G :=
    (Ito.measurableSet_usualAugmentation_of_null (measurableSet_toMeasurable P N)
      (by rw [measure_toMeasurable]; exact hN) 0).compl
  have hGgood : ∀ ω ∈ G, Good ω := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P N h)
  have hGc : P Gᶜ = 0 := by rw [hGdef, compl_compl, measure_toMeasurable]; exact hN
  set c : ℕ → ℕ → ℕ → ℝ≥0∞ := fun R m k =>
    ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) * codeLaw κ ρL' ρR' (lateSet k (R : ℝ)) (xL, xR) ^ (1 / 2 : ℝ)
    with hcdef
  set L : ℕ → ℕ → ℕ → ℕ → ℕ → Set Ω := fun R m k T n =>
    lateEvent κ ρL ρL' ρR ρR' G W VL VR (1 / ((n : ℝ) + 1)) (T : ℝ≥0) (m : ℝ) k (R : ℝ) with hLdef
  have hL : ∀ R m k T n, P (L R m k T n) ≤ c R m k := fun R m k T n =>
    measure_lateEvent_le hκ hsep hE𝓖 hGm (fun ω hω => (hGgood ω hω).1) (fun ω hω => (hGgood ω hω).2.2.1)
      href (by positivity) (T : ℝ≥0) (m : ℝ) k (R : ℝ)
  have hmono : ∀ R m k T, Monotone (L R m k T) := by
    intro R m k T n n' hnn' ω hω
    obtain ⟨hωG, hgap, hen, hlateω⟩ := hω
    refine ⟨hωG, fun s hs => le_trans ?_ (hgap s hs), hen, hlateω⟩
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (n : ℝ) + 1 ≤ (n' : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnn'
    exact one_div_le_one_div_of_le h1 h2
  have hU : ∀ R m k T, P (⋃ n, L R m k T n) ≤ c R m k := fun R m k T => by
    rw [(hmono R m k T).measure_iUnion]
    exact iSup_le (hL R m k T)
  set Bad : ℕ → ℕ → Set Ω := fun R m => ⋂ k : ℕ, ⋃ T₀ : ℕ, ⋂ (T : ℕ) (_ : T₀ ≤ T), ⋃ n, L R m k T n
    with hBaddef
  have hBad : ∀ R m, P (Bad R m) = 0 := by
    intro R m
    refine le_antisymm (ge_of_tendsto' (tendsto_lateBound (m : ℝ) (hlate (R : ℝ))) fun k => ?_) bot_le
    have hmT : Monotone fun T₀ : ℕ => ⋂ (T : ℕ) (_ : T₀ ≤ T), ⋃ n, L R m k T n :=
      fun T₀ T₁ h => biInter_mono (fun T hT => h.trans hT) fun _ _ => le_rfl
    calc P (Bad R m) ≤ P (⋃ T₀ : ℕ, ⋂ (T : ℕ) (_ : T₀ ≤ T), ⋃ n, L R m k T n) :=
          measure_mono (iInter_subset _ k)
      _ = ⨆ T₀ : ℕ, P (⋂ (T : ℕ) (_ : T₀ ≤ T), ⋃ n, L R m k T n) := hmT.measure_iUnion
      _ ≤ c R m k := iSup_le fun T₀ =>
          (measure_mono (biInter_subset_of_mem (le_refl T₀))).trans (hU R m k T₀)
  have hnull : P (Gᶜ ∪ {ω | ¬∃ m : ℝ, ∀ T : ℝ≥0, changeEnergy κ ρL ρL' ρR ρR' W VL VR T ω ≤ m} ∪
      ⋃ R, ⋃ m, Bad R m) = 0 :=
    measure_union_null (measure_union_null hGc (ae_iff.1 henergy))
      (measure_iUnion_null fun R => measure_iUnion_null fun m => hBad R m)
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hnull
  simp only [mem_ofPred_eq, not_forall] at hω
  obtain ⟨η, hη, hnt⟩ := hω
  by_contra hcon
  simp only [mem_union, mem_compl_iff, not_or, not_not, mem_iUnion, not_exists, mem_ofPred_eq] at hcon
  obtain ⟨⟨hωG, hωE⟩, hωB⟩ := hcon
  obtain ⟨m₀, hm₀⟩ : ∃ m : ℝ, ∀ T : ℝ≥0, changeEnergy κ ρL ρL' ρR ρR' W VL VR T ω ≤ m := by
    by_contra h
    push Not at h
    exact hωE fun x hx => by
      obtain ⟨T, hT⟩ := h x
      exact absurd (hx T) (not_le.2 hT)
  obtain ⟨hζ, hW0, hst, hpos⟩ := hGgood ω hωG
  have hηc : Continuous η := by
    rw [← continuousOn_univ]
    exact hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top
  have hWc : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ⊤} :=
    (continuous_fst.comp hst).continuousOn
  obtain ⟨R, hR⟩ := exists_late_of_not_tendsto hηc hnt
  apply hωB R ⌈m₀⌉₊
  refine mem_iInter.2 fun k => ?_
  obtain ⟨p, hkp, hpR⟩ := hR k
  refine mem_iUnion.2 ⟨⌈((p : ℝ≥0) : ℝ)⌉₊ + 1, mem_iInter₂.2 fun T hT => ?_⟩
  obtain ⟨n, hn⟩ := exists_one_div_le_on_Iic (continuous_minGap.comp hst) hpos (T : ℝ≥0)
  refine mem_iUnion.2 ⟨n, hωG, hn, (hm₀ T).trans (Nat.le_ceil m₀), p, hkp, ?_, ?_⟩
  · have h1 : ((p : ℝ≥0) : ℝ) ≤ ⌈((p : ℝ≥0) : ℝ)⌉₊ := Nat.le_ceil _
    have h2 : ((⌈((p : ℝ≥0) : ℝ)⌉₊ + 1 : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    have : ((p : ℝ≥0) : ℝ) < ((T : ℝ≥0) : ℝ) := by push_cast at h2 ⊢; linarith
    exact_mod_cast this
  · rw [LP.traceAt_eq_of_isGeneratingTrace hη hWc hW0 ENNReal.coe_lt_top]
    exact hpR

end InteractingSLE.Zhan
