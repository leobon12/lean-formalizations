/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59NodesFarPrem
import InteractingSLE.Spec.Sec5.Prop59NodesFarCore
import InteractingSLE.Spec.Sec5.Prop59StageLawProofTips

/-!
# Proposition 5.9's experiment from the killed stage law

Packet PROVE-PROP59-NODES. PROVE-PROP59T2's invariants and per-stage estimates (`Prop59StageExp`), re-proved from the
killed stage law `Prop59StageLawFarStatement` (`Prop59NodesFar`): the pieces are only local solutions before their
lifetime (killed at the first far contact), which is all the invariants use, and the two comparison premises hold in
the killed form (`Prop59NodesFarPrem`). The experiment then follows from `ae_not_isBounded_of_succ_unit`
(`Prop59NodesFarCore`).

## Main results

* `ae_pathF`, `ae_stageInvF`, `ae_mem_startsUF`: the pathwise clause and the invariants;
* **`ae_eventually_succF`**, **`le_measureReal_unitF`**: the two per-stage estimates;
* **`ae_not_isBounded_of_stageLawFar`**: almost surely on the initial event the node images are unbounded;
* **`tip0UnboundedStatement_of_stageLawFar`**, **`tipUnboundedStatement_of_stageLawFar`**: PROVE-PROP59T's
  statements from the killed law (word conditions from `IsStageInit`, as PROVE-PROP59T3).

Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Sec5.Prop59Nodes

open Prop59Stage

section Invariants

variable {κ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL₀ nR₀ : ℕ} {hnL : 0 < nL₀}
  {hnR : 0 < nR₀} {Q : Set ℝ≥0} {δ : ℕ → ℝ≥0} {G : ℕ → ℕ → ℝ≥0} {sys : StageSys Ω nL₀ nR₀} {C : Ω → Set ℂ}
  {ρL₀ : Fin nL₀ → ℝ} {ρR₀ : Fin nR₀ → ℝ}

/-- The pathwise clause of the killed stage law at every stage. -/
theorem ae_pathF (hL : Prop59StageLawFarStatement κ P hnL hnR ρL₀ ρR₀ sys) (r : ℕ → ℕ) (j : ℕ) :
    ∀ᵐ ω ∂P, ω ∈ (sys r j).R → IsOrderedForceWord ((sys r j).y ω).2.1 ((sys r j).y ω).2.2 ∧
      StrictAnti ((sys r j).y ω).2.1 ∧ StrictMono ((sys r j).y ω).2.2 ∧
      Sec2.IsSLEPathUpTo κ ((sys r j).y ω).2.1 ((sys r j).y ω).2.2 (stageρL κ ρL₀ j) (stageρR κ ρR₀ j)
        ((sys r j).W · ω) (fun i t => (sys r j).VL i t ω) (fun k t => (sys r j).VR k t ω) ((sys r j).B · ω)
        ((sys r j).ζ ω) :=
  (hL r j).1

/-- **The invariant** (`StageInv`) along the construction, from the killed law. -/
theorem ae_stageInvF (hL : Prop59StageLawFarStatement κ P hnL hnR ρL₀ ρR₀ sys)
    (hS : IsStageSystem P hnL hnR Q δ G sys C) (r : ℕ → ℕ) (j : ℕ) :
    ∀ᵐ ω ∂P, ω ∈ (sys r j).R → StageInv hnL hnR j ((sys r j).y ω) := by
  induction j with
  | zero =>
    filter_upwards [hS.init r] with ω h hω
    obtain ⟨h0, hl, hr⟩ := h hω
    refine ⟨by rw [h0]; norm_num, by rw [h0]; norm_num, fun _ => by rw [h0]; norm_num, fun h => absurd ⟨0, rfl⟩ h,
      hl, hr⟩
  | succ j ih =>
    filter_upwards [ih, ae_pathF hL r j, hS.y_next r j] with ω hinv hp hy hω
    have hωR : ω ∈ (sys r j).R ∩ succSet G hnL hnR j (sys r j) (r j) := by rw [← hS.R_succ]; exact hω
    obtain ⟨⟨hsζ, hband, -⟩, -⟩ := swT_spec hωR.2
    obtain ⟨ha1, ha2, -, -, hfl, hfr⟩ := hinv hωR.1
    have hfp := (hp hωR.1).2.2.2
    rw [hy hω]
    set s := swT G hnL hnR j (sys r j) (r j) ω with hs
    have hvl : (sys r j).VL (farL (by omega : 0 < nL₀ + j)) s ω ≤ ((sys r j).y ω).2.1 (farL (by omega)) := by
      have := hfp.vL_le_of_le zero_le hsζ (farL (by omega : 0 < nL₀ + j)); rwa [hfp.vL_zero] at this
    have hvr : ((sys r j).y ω).2.2 (farR (by omega)) ≤ (sys r j).VR (farR (by omega : 0 < nR₀ + j)) s ω := by
      have := hfp.le_vR_of_le zero_le hsζ (farR (by omega : 0 < nR₀ + j)); rwa [hfp.vR_zero] at this
    have hb : -(9 / 4) < ((sys r j).y ω).1 + (sys r j).W s ω ∧ ((sys r j).y ω).1 + (sys r j).W s ω < 9 / 4 ∧
        (Even j → ((sys r j).y ω).1 + (sys r j).W s ω < -(7 / 4)) ∧
        (¬ Even j → 7 / 4 < ((sys r j).y ω).1 + (sys r j).W s ω) := by
      by_cases hj : Even j
      · rw [band_even hj] at hband
        exact ⟨hband.1, by linarith [hband.2], fun _ => hband.2, fun h => absurd hj h⟩
      · rw [band_odd hj] at hband
        exact ⟨by linarith [hband.1], hband.2, fun h => absurd h hj, fun _ => hband.1⟩
    refine ⟨?_, ?_, fun he => ?_, fun he => ?_, ?_, ?_⟩ <;>
      simp only [nextStart_fst, nextStart_farL, nextStart_farR, ← hs]
    · exact hb.1
    · exact hb.2.1
    · have hj : ¬ Even j := fun h => (Nat.not_even_iff_odd.2 h.add_one) he
      linarith [hb.2.2.2 hj]
    · have hj : Even j := by
        by_contra h; exact he (Nat.not_even_iff_odd.1 h).add_one
      linarith [hb.2.2.1 hj]
    · linarith
    · linarith

/-- **Every stage eventually succeeds** (almost surely on `R j`, for every large grid index), from the killed law and
the killed crossing premises. -/
theorem ae_eventually_succF [IsFiniteMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hL : Prop59StageLawFarStatement κ P hnL hnR ρL₀ ρR₀ sys) (hS : IsStageSystem P hnL hnR Q δ G sys C)
    (hwL : ∀ j, Even j → IsStageWordN κ (stageρL κ ρL₀ j) (stageρR κ ρR₀ j))
    (hwR : ∀ j, ¬ Even j → IsStageWordN κ (stageρR κ ρR₀ j) (stageρL κ ρL₀ j)) (r : ℕ → ℕ) (j : ℕ) :
    ∀ᵐ ω ∂P, ω ∈ (sys r j).R → ∀ᶠ n in atTop, ω ∈ succSet G hnL hnR j (sys r j) n := by
  have hL' : 0 < nL₀ + j := by omega
  have hR' : 0 < nR₀ + j := by omega
  have hRm : MeasurableSet (sys r j).R := hS.past_le r j _ (hS.R_meas r j)
  have hpair : Measurable fun ω => ((sys r j).y ω, samp ((sys r j).W · ω) (fun i t => (sys r j).VL i t ω)
      (fun k t => (sys r j).VR k t ω) ((sys r j).ζ ω)) := (hS.meas r j).1.prodMk (hS.meas r j).2
  -- the killed comparison form with `p = 1` gives the event almost surely on `R`
  have hae : ∀ {D : Set (Start (nL₀ + j) (nR₀ + j))} {S : Set (Start (nL₀ + j) (nR₀ + j) × Samp (nL₀ + j) (nR₀ + j))},
      MeasurableSet D → MeasurableSet S →
      CompPremiseFar κ (stageρL κ ρL₀ j) (stageρR κ ρR₀ j) (farL hL') (farR hR') D S 1 →
      ∀ᵐ ω ∂P, ω ∈ (sys r j).R → (sys r j).y ω ∈ D → ((sys r j).y ω, samp ((sys r j).W · ω)
        (fun i t => (sys r j).VL i t ω) (fun k t => (sys r j).VR k t ω) ((sys r j).ζ ω)) ∈ S := by
    intro D S hD hS' hp
    have h := (hL r j).le_measure hD hS' le_rfl hp (hS.R_meas r j) subset_rfl
    rw [one_mul] at h
    set E : Set Ω := {ω | (sys r j).y ω ∈ D → ((sys r j).y ω, samp ((sys r j).W · ω)
      (fun i t => (sys r j).VL i t ω) (fun k t => (sys r j).VR k t ω) ((sys r j).ζ ω)) ∈ S} with hE
    have hEm : MeasurableSet E := by
      have : MeasurableSet {p : Start (nL₀ + j) (nR₀ + j) × Samp (nL₀ + j) (nR₀ + j) | p.1 ∈ D → p ∈ S} := by
        have e : {p : Start (nL₀ + j) (nR₀ + j) × Samp (nL₀ + j) (nR₀ + j) | p.1 ∈ D → p ∈ S} =
            (Prod.fst ⁻¹' D)ᶜ ∪ S := by ext p; simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]; tauto
        rw [e]; exact (measurable_fst hD).compl.union hS'
      exact hpair this
    have hnull : P ((sys r j).R \ E) = 0 := by
      have h3 : P ((sys r j).R ∩ E) ≤ P (sys r j).R := measure_mono inter_subset_left
      have h4 : P ((sys r j).R ∩ E) = P (sys r j).R := le_antisymm h3 h
      rw [← sdiff_self_inter, measure_sdiff inter_subset_left (hRm.inter hEm).nullMeasurableSet
        (measure_ne_top _ _), h4, tsub_self]
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hnull
    have hω' : ¬ (ω ∈ (sys r j).R → ω ∈ E) := hω
    refine ⟨?_, fun hE' => hω' fun _ => hE'⟩
    by_contra h
    exact hω' fun h' => absurd h' h
  by_cases hj : Even j
  · filter_upwards [hae (measurableSet_startsL hL' hR') (measurableSet_crossL _ _)
      (compPremiseFar_crossL hκ hκ4 hL' hR' (hwL j hj)), ae_pathF hL r j, ae_stageInvF hL hS r j, hS.clk r j]
      with ω hcr hp hinv hclk hω
    obtain ⟨hF, hxL, hxR, hfp⟩ := hp hω
    obtain ⟨ha1, ha2, hev, -, hfl, hfr⟩ := hinv hω
    have hmem : (sys r j).y ω ∈ startsL hL' hR' :=
      ⟨hF, hxL, hxR, hfl, by linarith, by linarith⟩
    obtain ⟨t, htζ, hwt, hgap⟩ := path_of_crossL (x := ((sys r j).y ω).2) hfp.continuousOn_w
      (hfp.continuousOn_vL _) (hcr hω hmem)
    refine eventually_mem_succSet hS r j hfp.continuousOn_w (hclk hω).1 (hclk hω).2 htζ ?_ fun u hu => ?_
    · simp only [hfp.w_zero, level, hj, ↓reduceIte]
      have := hev hj
      nlinarith
    · simp only [farGap, hj, ↓reduceIte]; linarith [hgap u hu]
  · filter_upwards [hae (measurableSet_startsR hL' hR') (measurableSet_crossR _ _)
      (compPremiseFar_crossR hκ hκ4 hL' hR' (hwR j hj)), ae_pathF hL r j, ae_stageInvF hL hS r j, hS.clk r j]
      with ω hcr hp hinv hclk hω
    obtain ⟨hF, hxL, hxR, hfp⟩ := hp hω
    obtain ⟨ha1, ha2, -, hodd, hfl, hfr⟩ := hinv hω
    have hmem : (sys r j).y ω ∈ startsR hL' hR' :=
      ⟨hF, hxL, hxR, hfr, by linarith, by linarith⟩
    obtain ⟨t, htζ, hwt, hgap⟩ := path_of_crossR (x := ((sys r j).y ω).2) hfp.continuousOn_w
      (hfp.continuousOn_vR _) (hcr hω hmem)
    refine eventually_mem_succSet hS r j hfp.continuousOn_w (hclk hω).1 (hclk hω).2 htζ ?_ fun u hu => ?_
    · simp only [hfp.w_zero, level, hj, ↓reduceIte]
      have := hodd hj
      nlinarith
    · simp only [farGap, hj, ↓reduceIte]; linarith [hgap u hu]

/-- **The admissible start of an even stage** (`startsU`), from the killed law. -/
theorem ae_mem_startsUF (hL : Prop59StageLawFarStatement κ P hnL hnR ρL₀ ρR₀ sys)
    (hS : IsStageSystem P hnL hnR Q δ G sys C) (r : ℕ → ℕ) {j : ℕ} (hj : ¬ Even j) :
    ∀ᵐ ω ∂P, ω ∈ (sys r (j + 2)).R → (sys r (j + 2)).y ω ∈ startsU := by
  filter_upwards [ae_pathF hL r j, ae_pathF hL r (j + 1), ae_pathF hL r (j + 2), hS.y_next r j, hS.y_next r (j + 1)]
    with ω hp0 hp1 hp2 hy0 hy1 hω
  have hω1 : ω ∈ (sys r (j + 1)).R ∩ succSet G hnL hnR (j + 1) (sys r (j + 1)) (r (j + 1)) := by
    rw [← hS.R_succ]; exact hω
  have hω0 : ω ∈ (sys r j).R ∩ succSet G hnL hnR j (sys r j) (r j) := by rw [← hS.R_succ]; exact hω1.1
  obtain ⟨⟨hs1ζ, hb1, -⟩, -⟩ := swT_spec hω1.2
  obtain ⟨⟨hs0ζ, hb0, -⟩, -⟩ := swT_spec hω0.2
  have hj1 : Even (j + 1) := (Nat.not_even_iff_odd.1 hj).add_one
  rw [band_even hj1] at hb1
  rw [band_odd hj] at hb0
  have hfp1 := (hp1 hω1.1).2.2.2
  have hfp0 := (hp0 hω0.1).2.2.2
  refine ⟨?_, ?_, (hp2 hω).1, fun k hk => ?_⟩
  · rw [hy1 hω, nextStart_fst]; exact hb1.1
  · rw [hy1 hω, nextStart_fst]; exact hb1.2
  · obtain ⟨m, rfl⟩ : ∃ m : Fin (nR₀ + (j + 1)), k = m.succ := by
      rcases Fin.eq_zero_or_eq_succ k with h0 | h
      · exact absurd (by rw [h0]; rfl) (Nat.pos_iff_ne_zero.1 hk)
      · exact h
    rw [hy1 hω, nextStart_fst, nextStart_R_succ]
    set s1 := swT G hnL hnR (j + 1) (sys r (j + 1)) (r (j + 1)) ω
    have hm1 : (sys r (j + 1)).VR m 0 ω ≤ (sys r (j + 1)).VR m s1 ω := hfp1.le_vR_of_le zero_le hs1ζ m
    rw [hfp1.vR_zero m] at hm1
    have key : 7 / 4 ≤ ((sys r (j + 1)).y ω).1 + ((sys r (j + 1)).y ω).2.2 m := by
      rw [hy0 hω1.1, nextStart_fst]
      rcases Fin.eq_zero_or_eq_succ m with h0 | ⟨m', rfl⟩
      · rw [h0, nextStart_R_zero, add_zero]; exact hb0.1.le
      · rw [nextStart_R_succ]
        have := hfp0.w_le_vR hs0ζ m'
        linarith [hb0.1]
    linarith

/-- **The unit estimate of the even stages** (Lemma 5.10 at the first passage through `0`; p. 147), from the killed
law and the killed unit premise. -/
theorem le_measureReal_unitF [IsProbabilityMeasure P] (hL : Prop59StageLawFarStatement κ P hnL hnR ρL₀ ρR₀ sys)
    (hS : IsStageSystem P hnL hnR Q δ G sys C) {p₀ : ℝ≥0∞} (hp₀1 : p₀ ≤ 1)
    (hprem : ∀ (j : ℕ) (iL : Fin (nL₀ + (j + 1))) (iR : Fin (nR₀ + (j + 1))),
      CompPremiseFar κ (stageρL κ ρL₀ (j + 1)) (stageρR κ ρR₀ (j + 1)) iL iR startsU unitSet p₀)
    (r : ℕ → ℕ) {j : ℕ} (hj : ¬ Even j) {A : Set Ω} (hA : MeasurableSet[(sys r (j + 2)).past] A) :
    p₀.toReal * P.real A ≤ P.real (A ∩ (((sys r (j + 2)).R)ᶜ ∪
      ((sys r (j + 2)).R \ succSet G hnL hnR (j + 2) (sys r (j + 2)) (r (j + 2))) ∪
      {ω | ω ∈ succSet G hnL hnR (j + 2) (sys r (j + 2)) (r (j + 2)) ∧
        1 ≤ swT G hnL hnR (j + 2) (sys r (j + 2)) (r (j + 2)) ω})) := by
  set d := sys r (j + 2) with hd
  have hRm : MeasurableSet d.R := hS.past_le r _ _ (hS.R_meas r _)
  have hpair : Measurable fun ω => (d.y ω, samp (d.W · ω) (fun i t => d.VL i t ω) (fun k t => d.VR k t ω)
      (d.ζ ω)) := (hS.meas r _).1.prodMk (hS.meas r _).2
  set E : Set Ω := {ω | d.y ω ∈ startsU → (d.y ω, samp (d.W · ω) (fun i t => d.VL i t ω)
      (fun k t => d.VR k t ω) (d.ζ ω)) ∈ unitSet} with hE
  have h := (hL r (j + 2)).le_measure measurableSet_startsU measurableSet_unitSet hp₀1 (hprem (j + 1) _ _)
    (hA.inter (hS.R_meas r _)) inter_subset_right
  -- on good samples of `A ∩ R ∩ E`, the stage aborts or spends a unit
  have hgood : ∀ᵐ ω ∂P, ω ∈ A ∩ d.R ∩ E → ω ∈ A ∩ ((d.R)ᶜ ∪ (d.R \ succSet G hnL hnR (j + 2) d (r (j + 2))) ∪
      {ω | ω ∈ succSet G hnL hnR (j + 2) d (r (j + 2)) ∧ 1 ≤ swT G hnL hnR (j + 2) d (r (j + 2)) ω}) := by
    filter_upwards [ae_mem_startsUF hL hS r hj, ae_pathF hL r (j + 2)] with ω hU hp ⟨⟨hωA, hωR⟩, hωE⟩
    refine ⟨hωA, ?_⟩
    by_cases hsc : ω ∈ succSet G hnL hnR (j + 2) d (r (j + 2))
    · refine Or.inr ⟨hsc, ?_⟩
      obtain ⟨⟨hsζ, hband, -⟩, -⟩ := swT_spec hsc
      have hodd : ¬ Even (j + 2) := fun h => hj (by simpa [Nat.even_add] using h)
      rw [band_odd hodd] at hband
      have hunit := hωE (hU hωR)
      have hfp := (hp hωR).2.2.2
      set s := swT G hnL hnR (j + 2) d (r (j + 2)) ω
      by_contra hs1
      push Not at hs1
      have hc : ContinuousAt (fun u => (d.y ω).1 + d.W u ω) s :=
        (continuousOn_const.add hfp.continuousOn_w).continuousAt ((Coupling.isOpen_setOf_coe_lt _).mem_nhds hsζ)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hc.eventually (lt_mem_nhds hband.1))
      obtain ⟨b, hsb, hbζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hsζ
      have hεn : s < s + ε.toNNReal := lt_add_of_pos_right _ (Real.toNNReal_pos.2 hε)
      obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn₀ (lt_min (ENNReal.coe_lt_coe.1 hsb) (lt_min hs1 hεn))
      have hqζ : ((q : ℝ≥0) : ℝ≥0∞) < d.ζ ω := lt_trans (by exact_mod_cast hq2.trans_le (min_le_left _ _)) hbζ
      have hq1' : ((q : ℝ≥0) : ℝ) < 1 := by
        have := hq2.trans_le ((min_le_right _ _).trans (min_le_left _ _)); exact_mod_cast this
      have hqd : dist (q : ℝ≥0) s < ε := by
        have h3 := hq2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
        rw [NNReal.dist_eq, abs_lt]
        have h4 : ((q : ℝ≥0) : ℝ) < s + ε := by
          have := (NNReal.coe_lt_coe.2 h3); rwa [NNReal.coe_add, Real.coe_toNNReal _ hε.le] at this
        constructor <;> linarith [NNReal.coe_lt_coe.2 hq1]
      have h1 := hball hqd
      have h2 := hunit q hq1' hqζ
      change (d.y ω).1 + ((samp (d.W · ω) (fun i t => d.VL i t ω) (fun k t => d.VR k t ω) (d.ζ ω)).2 q).1 < 7 / 4
        at h2
      rw [samp_snd_of_lt _ _ _ hqζ] at h2
      simp only at h1 h2
      linarith
    · exact Or.inl (Or.inr ⟨hωR, hsc⟩)
  -- the measure estimate
  set B : Set Ω := A ∩ ((d.R)ᶜ ∪ (d.R \ succSet G hnL hnR (j + 2) d (r (j + 2))) ∪
      {ω | ω ∈ succSet G hnL hnR (j + 2) d (r (j + 2)) ∧ 1 ≤ swT G hnL hnR (j + 2) d (r (j + 2)) ω}) with hB
  have h1 : P (A ∩ d.R ∩ E) ≤ P (B ∩ d.R) := by
    refine measure_mono_ae ?_
    filter_upwards [hgood] with ω hω h'
    exact ⟨hω h', h'.1.2⟩
  have h2 : A \ d.R ⊆ B \ d.R := fun ω hω => ⟨⟨hω.1, Or.inl (Or.inl hω.2)⟩, hω.2⟩
  have hsplitA : P.real A = P.real (A ∩ d.R) + P.real (A \ d.R) :=
    (measureReal_inter_add_sdiff (μ := P) (s := A) hRm).symm
  have hsplitB : P.real B = P.real (B ∩ d.R) + P.real (B \ d.R) :=
    (measureReal_inter_add_sdiff (μ := P) (s := B) hRm).symm
  have hp0 : p₀.toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hp₀1; simpa using this
  have h3 : p₀.toReal * P.real (A ∩ d.R) ≤ P.real (B ∩ d.R) := by
    have := ENNReal.toReal_mono (measure_ne_top _ _) (h.trans h1)
    rwa [ENNReal.toReal_mul] at this
  have h4 : P.real (A \ d.R) ≤ P.real (B \ d.R) := measureReal_mono h2
  rw [hsplitA, hsplitB, mul_add]
  have h5 : p₀.toReal * P.real (A \ d.R) ≤ P.real (A \ d.R) :=
    mul_le_of_le_one_left measureReal_nonneg hp0
  linarith

/-- **The alternating construction gives unbounded node images, from the killed stage law** (proof of
Proposition 5.9, pp. 143–148, with each piece used only before its first far contact). -/
theorem ae_not_isBounded_of_stageLawFar [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hL : Prop59StageLawFarStatement κ P hnL hnR ρL₀ ρR₀ sys) (hS : IsStageSystem P hnL hnR Q δ G sys C)
    (hwL : ∀ j, Even j → IsStageWordN κ (stageρL κ ρL₀ j) (stageρR κ ρR₀ j))
    (hwR : ∀ j, ¬ Even j → IsStageWordN κ (stageρR κ ρR₀ j) (stageρL κ ρL₀ j)) (r₀ : ℕ → ℕ) :
    ∀ᵐ ω ∂P, ω ∈ (sys r₀ 0).R → ¬ Bornology.IsBounded (C ω) := by
  obtain ⟨p₀, hp₀, hp₀1, hprem⟩ := exists_compPremiseFar_unit hκ hκ4 ρL₀ ρR₀
  exact ae_not_isBounded_of_succ_unit hS (ae_eventually_succF hκ hκ4 hL hS hwL hwR) hp₀ hp₀1
    (fun r j hj A hA => le_measureReal_unitF hL hS hp₀1 hprem r hj hA) r₀

/-- **The experiment from the killed law and the initial word** (`IsStageInit`, as PROVE-PROP59T3's
`ae_not_isBounded_of_pieceLaw`). -/
theorem ae_not_isBounded_of_stageLawFar_init [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hL : Prop59StageLawFarStatement κ P hnL hnR ρL₀ ρR₀ sys) (hS : IsStageSystem P hnL hnR Q δ G sys C)
    (hI : IsStageInit κ ρL₀ ρR₀) (r₀ : ℕ → ℕ) :
    ∀ᵐ ω ∂P, ω ∈ (sys r₀ 0).R → ¬ Bornology.IsBounded (C ω) :=
  ae_not_isBounded_of_stageLawFar hκ hκ4 hL hS (hwL_of_isStageInit hκ hκ4 hI) (hwR_of_isStageInit hκ hκ4 hI) r₀

end Invariants

/-! ### PROVE-PROP59T's unboundedness statements from the killed law -/

section Tips

open Prop59Tips

variable {κ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL₀ nR₀ : ℚ → ℕ}
  {hnL : ∀ r, 0 < nL₀ r} {hnR : ∀ r, 0 < nR₀ r} {ρL₀ : (r : ℚ) → Fin (nL₀ r) → ℝ}
  {ρR₀ : (r : ℚ) → Fin (nR₀ r) → ℝ} {Q : Set ℝ≥0} {δ : ℚ → ℕ → ℝ≥0} {G : ℚ → ℕ → ℕ → ℝ≥0}
  {sys : (r : ℚ) → StageSys Ω (nL₀ r) (nR₀ r)}

/-- **`Tip0UnboundedStatement` from the killed stage law** (root `0`). -/
theorem tip0UnboundedStatement_of_stageLawFar [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    {W : ℝ≥0 → Ω → ℝ} {z : ℕ → Ω → ℂ}
    (hL : ∀ r : ℚ, 0 < r → Prop59StageLawFarStatement κ P (hnL r) (hnR r) (ρL₀ r) (ρR₀ r) (sys r))
    (hS : ∀ r : ℚ, 0 < r → IsStageSystem P (hnL r) (hnR r) Q (δ r) (G r) (sys r) fun ω =>
      (ownComponentChart (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal).1 ''
        (range (fun n => z n ω) ∩ (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal)))
    (hI : ∀ r : ℚ, 0 < r → IsStageInit κ (ρL₀ r) (ρR₀ r))
    (hR0 : ∀ r : ℚ, 0 < r → ∀ᵐ ω ∂P, ω ∈ (sys r (fun _ => 0) 0).R) :
    Tip0UnboundedStatement P W z := by
  intro r hr
  filter_upwards [ae_not_isBounded_of_stageLawFar_init hκ hκ4 (hL r hr) (hS r hr) (hI r hr) (fun _ => 0),
    hR0 r hr] with ω h1 h2
  exact h1 h2

/-- **`TipUnboundedStatement` from the killed stage law** (root `z`). -/
theorem tipUnboundedStatement_of_stageLawFar [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    {W : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ} {z : Ω → ℂ} {S : Ω → Set ℂ}
    (hL : ∀ r : ℚ, 0 < r → Prop59StageLawFarStatement κ P (hnL r) (hnR r) (ρL₀ r) (ρR₀ r) (sys r))
    (hS : ∀ r : ℚ, 0 < r → IsStageSystem P (hnL r) (hnR r) Q (δ r) (G r) (sys r) fun ω =>
      (ownComponentChart (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal).1 ''
        (S ω ∩ (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal)))
    (hI : ∀ r : ℚ, 0 < r → IsStageInit κ (ρL₀ r) (ρR₀ r))
    (hR0 : ∀ r : ℚ, 0 < r → ∀ᵐ ω ∂P, (r : ℝ) < traceFirstVisit (γ ω) (z ω) → ω ∈ (sys r (fun _ => 0) 0).R) :
    TipUnboundedStatement P W γ z S := by
  intro r hr
  filter_upwards [ae_not_isBounded_of_stageLawFar_init hκ hκ4 (hL r hr) (hS r hr) (hI r hr) (fun _ => 0),
    hR0 r hr] with ω h1 h2 h3
  exact h1 (h2 h3)

end Tips

end InteractingSLE.Sec5.Prop59Nodes
