/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.CS3ProofCrossRight
import InteractingSLE.Spec.Supplement.Aux4Entrance

/-!
# The stage crossing before every bad far collision (GW2, p. 622, items 1–4; follow-up note A.3)

Packet PROVE-T14-TIP11. The near-extreme stages of GW2's exhaustion (Lemma GW2, "The central-band experiment under only
`S > −2`", `source/spec/p577-624.md` L1004–L1031, p. 622; CS3, "A positive-capacity stage before every bad far
collision", L407–L420, p. 594; follow-up note A.3, `source/external/AstraIG1/ig1_followup_a_e_audited.txt` L118–L173)
run a joint-chart word whose **attracting side may contain inadmissible original groups**: at the upper extreme the
attracting (left) original sums are `−2 + (κ/4)(S − d)` (`CS3.cs3_rL_half_pi`), which is `≤ −2` when the counterflow
sum `S` lies in `(−2, d]`; only the opposite side is admissible under `S > −2` ((GW2.3), `CS3.cs3_rR_half_pi_gt`).
Lemma GB8 (`Supp8.GB8.GB8Statement`) and PROVE-T14-TIP7's crossing lemmas (`CS3Cross.exists_lt_measure_reachEvent_left`,
`GW2TipNear.exists_buffer_eventually_lt_left`) assume **every** earlier partial sum `> −2`, so they do not apply to
these words. The source's argument (p. 622):

1. "A bad attracting group cannot collide before the driver crosses the central farther level `±(2 + 1/8)`, because its
   coordinate stays beyond `±3`."
2. "The opposite old-counterflow tail is protected." (GB7a and G12: `ae_lt_vR_last`, the proof of
   `Supp8.GB8.rightNoContactStatement`, which uses no partial sum.)
3. "On a proposed history which never crosses, no bad group collides. The complete available finite-force theorem gives
   transience. The finite-energy, whole-history comparison of GB8, with matching far heights and the changed marks
   behind compact crosscuts, excludes an entirely interior transient tail. It does not require a separated bad group to
   have weight `−2` rather than a value below `−2`." (`ae_noContact_false_far`: the proof of
   `Supp8.GB8.ae_noContact_false`, which uses no partial sum either.)
4. "Localize the strict crossing by time, driver and coordinate gap bounds. Keep all bad attracting groups and both tail
   junctions separated." (PROVE-T14-TIP7's buffers `CS3Cross.leftBuf`, `rightBuf`.)

Here the partial-sum hypothesis on the attracting side is required **only below the far cutoff** `m_L` (the designated
far labels, `i ≥ m_L`, start at most `−3`), exactly the shape of DS1's words (`Supp12.DS2.IsDS1Word`).

## Main results

* `not_threshold_far` (deterministic): a state whose far labels are strictly off the driver has no threshold;
* **`ae_exists_cross_far`**: almost surely the driver crosses `−(2 + 1/8)` before the lifetime (Theorem 1.3 as input);
* **`exists_lt_measure_reachEvent_left_far`**, **`exists_lt_measure_reachEvent_right_far`**: buffers of crossing
  probability `> 1 − δ` (A.3: "`P_{θ*}(U_{T,R,g}) → 1`");
* **`exists_buffer_eventually_lt_left_far`**, **`exists_buffer_eventually_lt_right_far`**: the near-extreme stage
  (A.3: "DS3 and Portmanteau give `lim inf_{θ → θ*} P_θ(U_{T,R,g}) ≥ P_{θ*}(U_{T,R,g}) > 1 − ε/4`"), from
  Theorem 1.3 and
  the proved DS3 (`Supp12.DSReach.ds3ReachStatement`); the limit word's admissibility below the cutoffs is read off its
  DS1 bounds.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Finset Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2TipStage

open Supp12 Supp12.DS2 Supp12.DSReach Supp8.GB8 CS3Cross

/-! ### No threshold off the far labels -/

/-- On an ordered side (`v` antitone, every mark at most `w`), the labels at `w` form an initial segment `{l ≤ k}` with
`v k = w`, so their total weight is the partial sum at a label at the driver. -/
theorem neg_two_lt_sum_filter_of {n : ℕ} {v ρ : Fin n → ℝ} {w : ℝ} (hv : Antitone v) (hle : ∀ i, v i ≤ w)
    (hps : ∀ i : Fin n, v i = w → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρ l) :
    -2 < ∑ i ∈ univ.filter (fun i => v i = w), ρ i := by
  set Z := univ.filter (fun i => v i = w) with hZ
  rcases Z.eq_empty_or_nonempty with he | hne
  · rw [he, sum_empty]; norm_num
  set k := Z.max' hne with hk
  have hkZ : v k = w := (Finset.mem_filter.1 (Z.max'_mem hne)).2
  have hZk : Z = univ.filter (fun l => l ≤ k) := by
    ext i
    simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      exact Z.le_max' i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
    · intro hik
      exact le_antisymm (hle i) (hkZ ▸ hv hik)
  rw [hZk]
  exact hps k hkZ

/-- **No threshold at a state whose far left labels are off the driver** (GW2, p. 622, item 1: "A bad attracting group
cannot collide before the driver crosses"). If every left label of index `≥ m_L` is strictly left of the driver, the
left group at the driver is an initial segment below `m_L`, of weight `> −2`; the right side is admissible. -/
theorem not_threshold_far {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hκ : 0 < κ) {mL : ℕ}
    {w₀ : ℝ} {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ} (hvL : Antitone vL₀) (hvLw : ∀ i, vL₀ i ≤ w₀)
    (hvR : Monotone vR₀) (hvRw : ∀ j, w₀ ≤ vR₀ j) (hfar : ∀ i : Fin nL, mL ≤ (i : ℕ) → vL₀ i < w₀)
    (hsR : ∑ j, ρR j = κ / 2 - 2)
    (hpsL : ∀ i : Fin nL, (i : ℕ) < mL → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    (hpsR : ∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l) :
    ¬ ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ := by
  rintro (h | h)
  · have := neg_two_lt_sum_filter_of (ρ := ρL) hvL hvLw fun i hi => by
      by_cases him : (i : ℕ) < mL
      · exact hpsL i him
      · exact absurd hi (hfar i (not_lt.1 him)).ne
    linarith
  · have := neg_two_lt_sum_filter_right (ρ := ρR) hvR hvRw hpsR fun _ _ _ => by rw [hsR]; linarith
    linarith

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-! ### The protected opposite tail and the whole-history comparison, without partial sums -/

/-- **The opposite tail is protected** (GW2, p. 622, item 2; GB8 proof, p. 523: "Lemma GB7a protects the open right
tail, and G12 protects its junction `x₊`"): the proof of `Supp8.GB8.rightNoContactStatement`, which uses only the
right total `κ/2 − 2` and the position `x₊ > 0` of the outermost right mark (no partial sum). -/
theorem ae_lt_vR_last (hκ : 0 < κ) (hκ4 : κ < 4) (hnR : 0 < nR) (hF : IsOrderedForceWord xL xR)
    (hxp : 0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩) (hsR : ∑ j, ρR j = κ / 2 - 2)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (htr : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W t ω < VR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ t ω := by
  set k : Fin nR := ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ with hk
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hlast : ∀ j, xR j ≤ xR k := fun j => hF.2.2.1 (Fin.le_iff_val_le_val.2 (by simp only [hk]; omega))
  have hfilt : ∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i = κ / 2 - 2 := by
    rw [Finset.filter_true_of_mem (fun i _ => hlast i)]
    exact hsR
  by_cases hex : ∃ j, xR j < xR k
  · classical
    set η : Ω → ℝ≥0 → ℂ := fun ω => if h : ∃ γ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ then h.choose
      else fun _ => 0 with hηdef
    have hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω) := by
      filter_upwards [htr] with ω hω
      simp only [hηdef, dite_eq_left hω]
      exact hω.choose_spec
    have hG12 := Supp7.G12Low.ae_trace_ne_right_of_exists hκ hκ4 hF hE hη hxp hex
      (by rw [hfilt]; linarith)
    have hGB : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω →
        ∀ y ∈ Set.Ioo (xR k) (xR k + n + 1), η ω t ≠ y := fun n =>
      GB7a.gb7aEvol_right GB7a.gb7aCmpInput hκ hκ4 hF hE hη (k := k)
        (by linarith [n.cast_nonneg (α := ℝ)]) (fun j hj => absurd (hlast j) (not_le.2 hj)) (by rw [hfilt])
    filter_upwards [hη, hG12, ae_all_iff.2 hGB, hE.ae_isIntegratedSLEPath] with ω hηω hg hgb hp t ht
    have hpf := hp.isForcePath
    refine w_lt_vR_of_trace_avoid hxp hpf.continuousOn_w hpf.w_zero (hpf.continuousOn_vR k)
      (fun t ht => hpf.vR_eq ht k) (fun t ht => hpf.w_le_vR ht k) hηω (fun s hs y hy => ?_) ht
    rcases hy.lt_or_eq with hy | hy
    · obtain ⟨n, hn⟩ := exists_nat_gt (y - xR k)
      exact hgb n s hs.le y ⟨hy, by linarith⟩
    · rw [← hy]
      exact hg s hs.le
  · have hco : ∀ j, xR j = xR k := fun j => le_antisymm (hlast j) (not_lt.1 fun h => hex ⟨j, h⟩)
    have hnull : P (⋃ q : ℚ, {ω | GB7a.RightCmp ρL ρR W VL VR ζ k none (κ / 2 - 2) (q : ℝ).toNNReal ω}) = 0 :=
      measure_iUnion_null fun q => GB7a.measure_rightCmp_eq_zero hκ hκ4.le hE (by simp) le_rfl _
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull, hE.ae_isIntegratedSLEPath] with ω hω hp t ht
    by_contra hcon
    obtain ⟨q, hq⟩ := exists_rightCmp_of_meet hp.isForcePath hF.2.1 hxp hco hsR ht hcon
    exact hω (Set.mem_iUnion.2 ⟨q, hq⟩)

/-- **No entirely interior transient tail avoiding the far-left mark** (GW2, p. 622, item 3): the proof of
`Supp8.GB8.ae_noContact_false` (Theorem 1.3, the protected right tail, GB8's finite-energy restart buffer and the
Aux. 108 comparison with the two-mark reference of totals `(κ − 4, κ/2 − 2)`), which uses no partial sum. -/
theorem ae_noContact_false_far (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hnL : 0 < nL)
    (hnR : 0 < nR) (hF : IsOrderedForceWord xL xR) (hxp : 0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩)
    (hsL : ∑ i, ρL i = κ - 4) (hsR : ∑ j, ρR j = κ / 2 - 2)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ → (∀ t : ℝ≥0, VL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ t ω < W t ω) → False := by
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have h13ω := h13 hκ hF hE
  have htr : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ := by
    filter_upwards [h13ω] with ω h using ⟨h.2.choose, h.2.choose_spec.1⟩
  have hR := ae_lt_vR_last hκ hκ4 hnR hF hxp hsR hE htr
  have hnull : ∀ᵐ ω ∂P, ∀ p : ℚ≥0, ∀ m : ℕ, 0 < p → ¬ (((p : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      0 < Zhan.minGap (Coupling.stateAt W VL VR p ω) ∧
      EnergySep κ ρL (refW nL (κ - 4)) ρR (refW nR (κ / 2 - 2)) m (fun t => W ((p : ℝ≥0) + t) ω - W p ω)
        (fun i t => VL i ((p : ℝ≥0) + t) ω - W p ω) (fun j t => VR j ((p : ℝ≥0) + t) ω - W p ω)
        (ζ ω - (p : ℝ≥0))) := by
    rw [ae_all_iff]; intro p; rw [ae_all_iff]; intro m
    by_cases hp : 0 < p
    · have hp' : (0 : ℝ≥0) < (p : ℝ≥0) := by exact_mod_cast hp
      have h0 := measure_restart_energySep_eq_zero referenceSwallowStatement.{0} hκ hκ4 hnL hnR hE (p : ℝ≥0) hp'
        (m : ℝ)
      rw [ae_iff]
      refine measure_mono_null (fun ω hω => ?_) h0
      simp only [not_imp, not_not, mem_ofPred_eq] at hω
      exact hω.2
    · exact Eventually.of_forall fun _ h => absurd h hp
  filter_upwards [hE.2.2.2.2, h13ω, hR, hnull] with ω hp h13ω' hRω hnullω
  intro hζ hL
  obtain ⟨-, η, hη, htrη⟩ := h13ω'
  have htr' := htrη hζ
  rw [hζ] at hη hp
  obtain ⟨p, hp0, hgap, m, hES⟩ := exists_restart_energySep hκ hnL hnR hp hxp hsL hsR hL
    (fun t => hRω t (by rw [hζ]; exact ENNReal.coe_lt_top)) hη htr'
  exact hnullω p m hp0 ⟨by rw [hζ]; exact ENNReal.coe_lt_top, hgap,
    by rw [hζ, ENNReal.top_sub_coe]; exact hES⟩

/-! ### The crossing before every bad far collision -/

/-- **The stage crossing before every bad far collision** (GW2, p. 622, items 1–3; CS3, p. 594). For `0 < κ < 4` and
an ordered word with totals `(κ − 4, κ/2 − 2)`, outermost marks `x₋ ≤ −3` and `x₊ > 0`, whose left labels of index
`≥ m_L` (the designated far attracting groups, possibly inadmissible) start at most `−3`, whose left partial sums below
`m_L` and right partial sums before the total exceed `−2`: almost surely the driver crosses `−(2 + 1/8)` before the
lifetime. Input: Theorem 1.3 (the complete finite-force theorem). -/
theorem ae_exists_cross_far (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hnL : 0 < nL)
    (hnR : 0 < nR) (hF : IsOrderedForceWord xL xR) (hxp : 0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩)
    (hxm : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ ≤ -3) (hsL : ∑ i, ρL i = κ - 4) (hsR : ∑ j, ρR j = κ / 2 - 2)
    {mL : ℕ} (hpsL : ∀ i : Fin nL, (i : ℕ) < mL → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    (hfar : ∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≤ -3)
    (hpsR : ∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω ∧ W t ω < -(2 + 1 / 8) := by
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  set ℓ : Fin nL := ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ with hℓ
  filter_upwards [hE.2.2.2.2, hE.ae_tendsto_threshold hκ,
    ae_noContact_false_far h13 hκ hκ4 hnL hnR hF hxp hsL hsR hE] with ω hp hlim hnc
  by_contra hno
  push Not at hno
  have hpF := hp.isForcePath
  -- the far labels stay at most `−3`, hence strictly left of the driver
  have hfar' : ∀ i : Fin nL, mL ≤ (i : ℕ) → ∀ u : ℝ≥0, (u : ℝ≥0∞) < ζ ω → VL i u ω ≤ -3 := fun i hi u hu =>
    (hpF.vL_le_of_le zero_le hu i).trans (by rw [hpF.vL_zero i]; exact hfar i hi)
  have hℓm : ∀ u : ℝ≥0, (u : ℝ≥0∞) < ζ ω → VL ℓ u ω ≤ -3 := fun u hu =>
    (hpF.vL_le_of_le zero_le hu ℓ).trans (by rw [hpF.vL_zero ℓ]; exact hxm)
  by_cases hζ : ζ ω = ⊤
  · refine hnc hζ fun t => ?_
    have ht : (t : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
    have h1 := hno t ht
    have h2 := hℓm t ht
    linarith
  -- a finite lifetime is a threshold, which the far labels exclude
  have hfar0 : ∀ i : Fin nL, mL ≤ (i : ℕ) → xL i < 0 := fun i hi => by linarith [hfar i hi]
  have hnothr0 : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR :=
    not_threshold_far hκ hF.1 hF.2.1 hF.2.2.1 hF.2.2.2 hfar0 hsR hpsL hpsR
  have hζ0 : ζ ω ≠ 0 := fun h0 => hnothr0 (hpF.threshold_of_eq_zero h0)
  set T := (ζ ω).toNNReal with hT
  have hTe : (T : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal hζ
  have hT0 : 0 < T := by
    rw [pos_iff_ne_zero]; intro h; rw [h] at hTe; exact hζ0 (by rw [← hTe]; rfl)
  obtain ⟨w₀, vL₀, vR₀, hl, hthr⟩ := hlim T hT0 hTe
  have hbefore : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, ((t : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← hTe]; exact_mod_cast ht
  have hne : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT0⟩
  have hw : Tendsto (fun t => W t ω) (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hl
  have hvl : ∀ i, Tendsto (fun t => VL i t ω) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
    ((continuous_apply i).comp (continuous_fst.comp continuous_snd)).continuousAt.tendsto.comp hl
  have hvr : ∀ j, Tendsto (fun t => VR j t ω) (𝓝[<] T) (𝓝 (vR₀ j)) := fun j =>
    ((continuous_apply j).comp (continuous_snd.comp continuous_snd)).continuousAt.tendsto.comp hl
  have hw₀ : -(2 + 1 / 8) ≤ w₀ := ge_of_tendsto hw (hbefore.mono fun t ht => hno t ht)
  refine not_threshold_far hκ (vL₀ := vL₀) (vR₀ := vR₀) ?_ ?_ ?_ ?_ ?_ hsR hpsL hpsR hthr
  · intro i j hij
    exact le_of_tendsto_of_tendsto (hvl j) (hvl i) (hbefore.mono fun t ht => hpF.antitone_vL ht hij)
  · intro i
    exact le_of_tendsto_of_tendsto (hvl i) hw (hbefore.mono fun t ht => hpF.vL_le_w ht i)
  · intro i j hij
    exact le_of_tendsto_of_tendsto (hvr i) (hvr j) (hbefore.mono fun t ht => hpF.monotone_vR ht hij)
  · intro j
    exact le_of_tendsto_of_tendsto hw (hvr j) (hbefore.mono fun t ht => hpF.w_le_vR ht j)
  · intro i hi
    have : vL₀ i ≤ -3 := le_of_tendsto (hvl i) (hbefore.mono fun t ht => hfar' i hi t ht)
    linarith

/-- **The leftward stage reaches its target inside a buffer, almost surely** (GW2, p. 622, item 4; A.3: "This finite
compact prefix has bounded coordinates and positive designated far gaps"): `ae_exists_cross_far`, the protected right
tail, and PROVE-T14-TIP7's first passage `CS3Cross.exists_reach_left_of_path`. -/
theorem ae_exists_reachEvent_left_far (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hnL : 0 < nL) (hnR : 0 < nR) (hF : IsOrderedForceWord xL xR) (hxp : 0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩)
    (hxm : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ ≤ -3) (hsL : ∑ i, ρL i = κ - 4) (hsR : ∑ j, ρR j = κ / 2 - 2)
    {mL : ℕ} (hpsL : ∀ i : Fin nL, (i : ℕ) < mL → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    (hfar : ∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≤ -3)
    (hpsR : ∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∃ n : ℕ, ω ∈ reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) W VL VR ζ := by
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have htr : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ := by
    filter_upwards [h13 hκ hF hE] with ω h using ⟨h.2.choose, h.2.choose_spec.1⟩
  filter_upwards [ae_exists_cross_far h13 hκ hκ4 hnL hnR hF hxp hxm hsL hsR hpsL hfar hpsR hE,
    ae_lt_vR_last hκ hκ4 hnR hF hxp hsR hE htr, hE.2.2.2.2] with ω hcross hnoR hp
  obtain ⟨t, htζ, hwt⟩ := hcross
  have hfp := hp.isForcePath
  have hfar' : ∀ i : Fin nL, mL ≤ (i : ℕ) → ∀ u : ℝ≥0, (u : ℝ≥0∞) < ζ ω → VL i u ω ≤ -3 := fun i hi u hu =>
    (hfp.vL_le_of_le zero_le hu i).trans (by rw [hfp.vL_zero i]; exact hfar i hi)
  obtain ⟨n, t', ht'n, ht'ζ, hwt', hbuf⟩ := exists_reach_left_of_path (w := fun t => W t ω)
    (vL := fun i t => VL i t ω) (vR := fun j t => VR j t ω) hnR hfp.continuousOn_w hfp.continuousOn_vL
    hfp.continuousOn_vR hfp.w_zero hfar' htζ hwt
    (fun u hu => hnoR u (lt_of_le_of_lt (by exact_mod_cast hu) htζ))
  exact ⟨n, t', ht'n, ht'ζ, hwt', fun u hu => hbuf u hu⟩

/-- **The leftward stage crossing has probability tending to one** along the buffers. -/
theorem tendsto_measure_reachEvent_left_far (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hnL : 0 < nL) (hnR : 0 < nR) (hF : IsOrderedForceWord xL xR) (hxp : 0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩)
    (hxm : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ ≤ -3) (hsL : ∑ i, ρL i = κ - 4) (hsR : ∑ j, ρR j = κ / 2 - 2)
    {mL : ℕ} (hpsL : ∀ i : Fin nL, (i : ℕ) < mL → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    (hfar : ∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≤ -3)
    (hpsR : ∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    Tendsto (fun n : ℕ => P (reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) W VL VR ζ)) atTop (𝓝 1) := by
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hlim := tendsto_measure_iUnion_atTop (μ := P) (reachEvent_left_mono (nL := nL) (nR := nR) mL W VL VR ζ)
  have hae := ae_exists_reachEvent_left_far h13 hκ hκ4 hnL hnR hF hxp hxm hsL hsR hpsL hfar hpsR hE
  have hone : P (⋃ n : ℕ, reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) W VL VR ζ) = 1 := by
    refine le_antisymm prob_le_one ?_
    have hnull : P (⋃ n : ℕ, reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) W VL VR ζ)ᶜ = 0 := by
      rw [ae_iff] at hae
      refine measure_mono_null (fun ω hω => ?_) hae
      simp only [mem_compl_iff, mem_iUnion, not_exists] at hω
      simp only [mem_ofPred_eq, not_exists]
      exact hω
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ ≤ P (⋃ n : ℕ, reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) W VL VR ζ) +
          P (⋃ n : ℕ, reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) W VL VR ζ)ᶜ := by
            rw [← union_compl_self (⋃ n : ℕ, reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) W VL VR ζ)]
            exact measure_union_le _ _
      _ = _ := by rw [hnull, add_zero]
  rw [hone] at hlim
  exact hlim

/-- **A leftward buffer with crossing probability `> 1 − δ`** (A.3: "Choose a rational buffer for which this
probability exceeds `1 − ε/4`"), for stage words with bad far attracting groups. -/
theorem exists_lt_measure_reachEvent_left_far (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hnL : 0 < nL) (hnR : 0 < nR) (hF : IsOrderedForceWord xL xR) (hxp : 0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩)
    (hxm : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ ≤ -3) (hsL : ∑ i, ρL i = κ - 4) (hsR : ∑ j, ρR j = κ / 2 - 2)
    {mL : ℕ} (hpsL : ∀ i : Fin nL, (i : ℕ) < mL → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    (hfar : ∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≤ -3)
    (hpsR : ∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ n : ℕ, 1 - δ < P (reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) W VL VR ζ) := by
  have hlim := tendsto_measure_reachEvent_left_far h13 hκ hκ4 hnL hnR hF hxp hxm hsL hsR hpsL hfar hpsR hE
  have h1 : (1 : ℝ≥0∞) - δ < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hδ.ne'
  exact (hlim.eventually (lt_mem_nhds h1)).exists

/-- **A rightward buffer with crossing probability `> 1 − δ`** (the reflected stage: right total `κ − 4`, left total
`κ/2 − 2`, the far right labels of index `≥ m_R` at least `3`). -/
theorem exists_lt_measure_reachEvent_right_far (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hnL : 0 < nL) (hnR : 0 < nR) (hF : IsOrderedForceWord xL xR) (hxm : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ < 0)
    (hxp : 3 ≤ xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩) (hsR : ∑ j, ρR j = κ - 4) (hsL : ∑ i, ρL i = κ / 2 - 2)
    {mR : ℕ} (hpsR : ∀ j : Fin nR, (j : ℕ) < mR → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l)
    (hfar : ∀ j : Fin nR, mR ≤ (j : ℕ) → 3 ≤ xR j)
    (hpsL : ∀ i : Fin nL, (i : ℕ) < nL - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ n : ℕ, 1 - δ < P (reachEvent (n : ℝ≥0) rightTarget (rightBuf nL mR n) W VL VR ζ) := by
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hEr := IsIntegratedSLEEvolution.reflect hE
  have hxm' : (-xR) ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ ≤ -3 := by
    simp only [Pi.neg_apply]; linarith
  have hxp' : 0 < (-xL) ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ := by
    simp only [Pi.neg_apply]; linarith
  have hfar' : ∀ j : Fin nR, mR ≤ (j : ℕ) → (-xR) j ≤ -3 := fun j hj => by
    simp only [Pi.neg_apply]; linarith [hfar j hj]
  obtain ⟨n, hn⟩ := exists_lt_measure_reachEvent_left_far (P := P) h13 hκ hκ4 hnR hnL
    (isOrderedForceWord_reflect hF) hxp' hxm' hsR hsL hpsR hfar' hpsL hEr hδ
  refine ⟨n, lt_of_lt_of_le hn (measure_mono fun ω hω => ?_)⟩
  obtain ⟨t, htn, htζ, hO, hB⟩ := hω
  refine ⟨t, htn, htζ, ?_, fun u hu => ?_⟩
  · have : -W t ω < -(2 + 1 / 8) := hO
    show 2 + 1 / 8 < W t ω
    linarith
  · exact mem_leftBuf_reflect_iff.1 (hB u hu)

/-! ### The near-extreme stage (A.3: DS3 and Portmanteau) -/

section Near

variable {ρLs : ℕ → Fin nL → ℝ} {ρRs : ℕ → Fin nR → ℝ} {ρL₀ : Fin nL → ℝ} {ρR₀ : Fin nR → ℝ}
  {Ωs : ℕ → Type u} [mΩs : ∀ m, MeasurableSpace (Ωs m)] {Ps : ∀ m, Measure (Ωs m)}
  {𝓕s : ∀ m, Filtration ℝ≥0 (mΩs m)} {Ws : ∀ m, ℝ≥0 → Ωs m → ℝ} {VLs : ∀ m, Fin nL → ℝ≥0 → Ωs m → ℝ}
  {VRs : ∀ m, Fin nR → ℝ≥0 → Ωs m → ℝ} {Bs : ∀ m, ℝ≥0 → Ωs m → ℝ} {ζs : ∀ m, Ωs m → ℝ≥0∞}

/-- **The near-extreme leftward stage, with bad far attracting groups** (A.3; GW2, p. 622, item 4: "All uncut opposite
groups have the strict positive margin in (GW2.3); the finitely many old angle-side groups retain their strict
admissibility margin"). Positions fixed (seeds at the driver, the other labels at distance `≥ η`, the far left labels
of index `≥ m_L` at most `−3`); at the exact extreme the totals are `(κ − 4, κ/2 − 2)`; the words `θ_m → θ*` and the
limit satisfy DS1's uniform bounds with cutoffs `m_L` (left) and `n_R − 1` (right: only the junction is far). Then a
buffer `n` has crossing probability `> 1 − δ` under every word close enough to the extreme. Inputs: Theorem 1.3 and
the proved DS3 (`Supp12.DSReach.ds3ReachStatement`). The far attracting groups need not be admissible. -/
theorem exists_buffer_eventually_lt_left_far (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hnL : 0 < nL) (hnR : 0 < nR) {mL : ℕ} {Rw ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hxL0 : xL ⟨0, hnL⟩ = 0) (hxR0 : xR ⟨0, hnR⟩ = 0) (hxL : ∀ i, xL i ≠ 0 → xL i ≤ -η)
    (hxR : ∀ j, xR j ≠ 0 → η ≤ xR j) (hxp : 0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩)
    (hxm : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ ≤ -3) (hfar : ∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≤ -3)
    (hsL : ∑ i, ρL₀ i = κ - 4) (hsR : ∑ j, ρR₀ j = κ / 2 - 2)
    (hw : ∀ m, IsDS1Word mL (nR - 1) Rw ε xL xR (ρLs m) (ρRs m)) (hw₀ : IsDS1Word mL (nR - 1) Rw ε xL xR ρL₀ ρR₀)
    (hρL : Tendsto ρLs atTop (𝓝 ρL₀)) (hρR : Tendsto ρRs atTop (𝓝 ρR₀))
    (hE : ∀ m, IsIntegratedSLEEvolution κ xL xR (ρLs m) (ρRs m) (Ps m) (𝓕s m) (Ws m) (VLs m) (VRs m) (Bs m) (ζs m))
    (hE₀ : IsIntegratedSLEEvolution κ xL xR ρL₀ ρR₀ P 𝓕 W VL VR B ζ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ n : ℕ, ∀ᶠ m in atTop,
      1 - δ < Ps m (reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) (Ws m) (VLs m) (VRs m) (ζs m)) := by
  have hpL : ∀ i : Fin nL, (i : ℕ) < mL → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL₀ l := fun i hi => by
    have := hw₀.2.2.2.1 i hi; linarith
  have hpR : ∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR₀ l := fun j hj => by
    have := hw₀.2.2.2.2 j hj; linarith
  obtain ⟨n, hn⟩ := exists_lt_measure_reachEvent_left_far h13 hκ hκ4 hnL hnR hw₀.1 hxp hxm hsL hsR hpL hfar hpR
    hE₀ hδ
  have hg : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact ⟨n, eventually_lt_measure_reachEvent ds3ReachStatement hκ hnL hnR hε hg hη hxL0 hxR0 hxL hxR hw hw₀ hρL
    hρR hE hE₀ isOpen_leftTarget (isOpen_setOf_inBuffer mL (nR - 1) n (1 / ((n : ℝ) + 1))) (fun _ hp => hp) hn⟩

/-- **The near-extreme rightward stage, with bad far attracting groups** (the reflected statement: right total `κ − 4`,
left total `κ/2 − 2`, the far right labels of index `≥ m_R` at least `3`, DS1 cutoffs `n_L − 1` and `m_R`). -/
theorem exists_buffer_eventually_lt_right_far (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hnL : 0 < nL) (hnR : 0 < nR) {mR : ℕ} {Rw ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hxL0 : xL ⟨0, hnL⟩ = 0) (hxR0 : xR ⟨0, hnR⟩ = 0) (hxL : ∀ i, xL i ≠ 0 → xL i ≤ -η)
    (hxR : ∀ j, xR j ≠ 0 → η ≤ xR j) (hxm : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ < 0)
    (hxp : 3 ≤ xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩) (hfar : ∀ j : Fin nR, mR ≤ (j : ℕ) → 3 ≤ xR j)
    (hsR : ∑ j, ρR₀ j = κ - 4) (hsL : ∑ i, ρL₀ i = κ / 2 - 2)
    (hw : ∀ m, IsDS1Word (nL - 1) mR Rw ε xL xR (ρLs m) (ρRs m)) (hw₀ : IsDS1Word (nL - 1) mR Rw ε xL xR ρL₀ ρR₀)
    (hρL : Tendsto ρLs atTop (𝓝 ρL₀)) (hρR : Tendsto ρRs atTop (𝓝 ρR₀))
    (hE : ∀ m, IsIntegratedSLEEvolution κ xL xR (ρLs m) (ρRs m) (Ps m) (𝓕s m) (Ws m) (VLs m) (VRs m) (Bs m) (ζs m))
    (hE₀ : IsIntegratedSLEEvolution κ xL xR ρL₀ ρR₀ P 𝓕 W VL VR B ζ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ n : ℕ, ∀ᶠ m in atTop,
      1 - δ < Ps m (reachEvent (n : ℝ≥0) rightTarget (rightBuf nL mR n) (Ws m) (VLs m) (VRs m) (ζs m)) := by
  have hpR : ∀ j : Fin nR, (j : ℕ) < mR → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR₀ l := fun j hj => by
    have := hw₀.2.2.2.2 j hj; linarith
  have hpL : ∀ i : Fin nL, (i : ℕ) < nL - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL₀ l := fun i hi => by
    have := hw₀.2.2.2.1 i hi; linarith
  obtain ⟨n, hn⟩ := exists_lt_measure_reachEvent_right_far h13 hκ hκ4 hnL hnR hw₀.1 hxm hxp hsR hsL hpR hfar hpL
    hE₀ hδ
  have hg : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact ⟨n, eventually_lt_measure_reachEvent ds3ReachStatement hκ hnL hnR hε hg hη hxL0 hxR0 hxL hxR hw hw₀ hρL
    hρR hE hE₀ isOpen_rightTarget (isOpen_setOf_inBuffer (nL - 1) mR n (1 / ((n : ℝ) + 1))) (fun _ hp => hp) hn⟩

end Near

end GW2TipStage

end Theorem14

end InteractingSLE
