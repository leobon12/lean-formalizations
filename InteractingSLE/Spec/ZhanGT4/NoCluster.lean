/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.NoClusterHit
import InteractingSLE.Foundations.Loewner.YuanCorollary13Tip

/-!
# Lemma 3.4: separated two-force laws have no real terminal cluster point (κ > 4)

Packet PROVE-ZHAN-GT4-B2. Source: Astra, *Follow-up proofs*, §B.3 L1236–L1259 (ruling R38); additional note Lemma 3.4,
L1479–L1505 (ruling R39). Given Part A's two geometric outputs — (G5) at positive stopping times of ordinary `SLE_κ`
(`StoppingInverseBoundaryStatement κ`, the inverse-boundary half of (G1)) and the separated two-force confinement (G2)
(`SeparatedTwoForceStatement κ`) — the separated two-force law with weights `≥ κ/2 − 2` has no real terminal cluster
point: `SeparatedNoRealClusterStatement κ`, the named input of PROVE-ZHAN-GT4-B's two-force and two-seed transience.

## The argument (chordal form of the source's strip argument)

Marks `p_L < 0 < p_R`, `r = p_R/(−p_L)`. Real points outside `(p_L, p_R)` are excluded by (G2) (the trace stays in the
closure of the hull, which keeps a positive distance from `p_L`, `p_R` and every compact set beyond them). For the
points of `(p_L, p_R)`, fix `θ > 0`, restart at `T = ` the first time `≥ t₀` with `R = rL` (finite by the recurrence of
the gap ratio, `IsIntegratedSLEEvolution.ae_realRec_sep`). At `T` the word is `λ(p_L, p_R)` with `λ = L_T/(−p_L)`, so
the restarted law is the original one, dilated. A real terminal cluster point `x ∈ (p_L, p_R)` of the trace lifts
through the inverse map at `T` ((G5) at `T`, transferred to the two-force law by bounded-drift Girsanov) to a real
terminal cluster point of the restarted trace in `[V_L, V_L − p_L] ∪ [V_R − p_R, V_R]` (`exists_band_cluster`); since
`(V_R − V_L)² ≥ 8T ≥ 8t₀`, these bands lie in the `θ`-bands of the restarted word once `t₀` is large. Hence
`P(real cluster in (p_L, p_R)) ≤ P(θ-band event)`, and the band probabilities tend to `P(cluster at p_L or p_R) = 0`
as `θ ↓ 0` (`isTermCluster_of_forall_realBand`, (G2)). No annulus estimate is needed: the crowding of the exterior
coordinates at the marks is the contraction of real flows on one side of the driver (`re_sub_le_of_isForwardSol`).

## Main results

* `IsIntegratedSLEEvolution.measure_cluster_le_band`: the restart inequality.
* `IsIntegratedSLEEvolution.ae_not_isTermCluster_mark`: (G2) excludes the marks and the points beyond them.
* **`separatedNoRealClusterStatement`**: `StoppingInverseBoundaryStatement κ → SeparatedTwoForceStatement κ →
  SeparatedNoRealClusterStatement κ` for `κ > 4`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart QuantumZipper

/-! ### The force points are real Loewner flows -/

/-- **A force point strictly on one side of the driver is the centered real flow of its start** (Specification (1.11)),
for a path with infinite lifetime. -/
theorem isForwardSol_of_force {w v : ℝ≥0 → ℝ} {x : ℝ} (hw : Continuous w) (hv : Continuous v)
    (hne : ∀ t, v t ≠ w t)
    (heq : ∀ t : ℝ≥0, v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal)) (r : ℝ) :
    IsForwardSol (fun s : ℝ => w s.toNNReal) (x : ℂ) r
      (fun s : ℝ => ((v s.toNNReal - w s.toNNReal : ℝ) : ℂ)) := by
  refine ⟨?_, fun s hs => ⟨?_, ?_⟩⟩
  · exact (Complex.continuous_ofReal.comp ((hv.sub hw).comp continuous_real_toNNReal)).continuousOn
  · simp only [ne_eq, Complex.ofReal_eq_zero, sub_eq_zero]
    exact hne _
  · have hs0 : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs.1
    have hveq := heq s.toNNReal
    rw [hs0] at hveq
    have hint : (∫ q in (0 : ℝ)..s, (2 : ℂ) / ((v q.toNNReal - w q.toNNReal : ℝ) : ℂ)) =
        ((∫ q in (0 : ℝ)..s, 2 / (v q.toNNReal - w q.toNNReal) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun q _ => ?_
      push_cast
      rfl
    rw [hint]
    show ((v s.toNNReal - w s.toNNReal : ℝ) : ℂ) = (x : ℂ) - ((w s.toNNReal : ℝ) : ℂ) + _
    rw [hveq]
    push_cast
    ring

/-! ### The real-time band condition from a cluster point in a band -/

/-- A terminal cluster point in one of the two bands gives the real-time band condition. -/
theorem realBand_of_isTermCluster {θ : ℝ} {s : (Fin 1 → ℝ) × (Fin 1 → ℝ)} {η : ℝ≥0 → ℂ} {y : ℝ}
    (hy : y ∈ Icc (s.1 0) ((1 - θ) * s.1 0) ∨ y ∈ Icc ((1 - θ) * s.2 0) (s.2 0))
    (hcl : IsTermCluster η y) : RealBand θ s η := by
  intro ε hε N
  have hfr := (mapClusterPt_iff_frequently.1 hcl) _ (ball_mem_nhds (y : ℂ) hε)
  obtain ⟨t, ht1, ht2⟩ := (hfr.and_eventually (eventually_ge_atTop N)).exists
  rw [mem_ball, dist_eq_norm] at ht1
  refine ⟨t, ht2, ?_⟩
  unfold bandDist
  rcases hy with hy | hy
  · exact lt_of_le_of_lt (min_le_left _ _) (lt_of_le_of_lt (dIcc_le _ hy) ht1)
  · exact lt_of_le_of_lt (min_le_right _ _) (lt_of_le_of_lt (dIcc_le _ hy) ht1)

/-! ### The restarted driver has a trace -/

/-- Infinite horizon and a continuous generating trace on `[0, ∞)` (through the rational coding `topSet`). -/
def TopEvent (w : ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop := τ = ⊤ ∧ (fun q : ℚ≥0 => w q) ∈ topSet

/-- The Borel set of solution codes with `TopEvent`. -/
def topCodeSet : Set (XCode 1 1) :=
  (fun x => (cw x, cζ x)) ⁻¹' {p : (ℝ≥0 → ℝ) × ℝ≥0∞ | p.2 = ⊤ ∧ (fun q : ℚ≥0 => p.1 q) ∈ topSet}

theorem measurableSet_topCodeSet : MeasurableSet topCodeSet := by
  have hm : Measurable fun p : (ℝ≥0 → ℝ) × ℝ≥0∞ => fun q : ℚ≥0 => p.1 q :=
    measurable_pi_iff.2 fun q => (measurable_pi_apply _).comp measurable_fst
  exact measurable_cw_cζ ((measurable_snd (measurableSet_singleton ⊤)).inter (hm measurableSet_topSet))

theorem not_topEvent_congr (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞) (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t)
    (hn : ¬ TopEvent w τ) : ¬ TopEvent w' τ := by
  rintro ⟨hτ, h2⟩
  subst hτ
  have : w = w' := funext fun t => h t ENNReal.coe_lt_top
  subst this
  exact hn ⟨rfl, h2⟩

/-- At a separated one-mark-per-side word with weights `≥ κ/2 − 2`, the canonical probability of no trace on
`[0, ∞)` is zero. -/
theorem codeLaw_compl_topCodeSet_eq_zero {κ : ℝ} (hκ : 0 < κ) {ρL ρR : Fin 1 → ℝ} (hwL : κ / 2 - 2 ≤ ρL 0)
    (hwR : κ / 2 - 2 ≤ ρR 0) {s : (Fin 1 → ℝ) × (Fin 1 → ℝ)} (hs1 : s.1 0 < 0) (hs2 : 0 < s.2 0)
    (hsolv : ∀ᵐ f ∂wienerPath, enc f ∈ Prod.fst '' CRel κ s.1 s.2 ρL ρR) :
    codeLaw κ ρL ρR topCodeSetᶜ s = 0 := by
  have hs1' : ∀ i, s.1 i < 0 := fun i => by rw [Fin.fin_one_eq_zero i]; exact hs1
  have hs2' : ∀ j, 0 < s.2 j := fun j => by rw [Fin.fin_one_eq_zero j]; exact hs2
  have hsep : ∀ i j, s.1 i < s.2 j := fun i j => (hs1' i).trans (hs2' j)
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_of_ae_wienerPath.{0} hsep hsolv
  have hev : ∀ᵐ ω ∂P, TopEvent (fun t => W t ω) (ζ ω) := by
    filter_upwards [hE.ae_exists_isGeneratingTrace_top_of_hasAdmissiblePartialSums
      hκ (isOrderedForceWord_one hs1 hs2) (hasAdmissiblePartialSums_one hwL hwR) hs1' hs2',
      hE.2.2.2.2] with ω ⟨hζ, η, hη⟩ hp
    have hwc : Continuous fun t => W t ω := by
      have h := hp.2.2.2.1
      rw [hζ] at h
      exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
    rw [hζ]
    exact ⟨rfl, (ratVals_mem_topSet_iff hwc hp.1).2 ⟨η, hη⟩⟩
  have e := measure_eventOf_eq_codeLaw hκ hsep hE (Φ := fun w τ => ¬ TopEvent w τ)
    measurableSet_topCodeSet.compl (fun _ _ _ => Iff.rfl) not_topEvent_congr
  rw [← e]
  exact ae_iff.1 hev

/-! ### The pathwise step of the restart -/

/-- **The pathwise step** (B.3 L1247–L1256; additional note L1491–L1500). Let a continuous driver `w` (`w 0 = 0`) with a
generating trace `η` on `[0, ∞)` carry two force points `v_L < w < v_R` started at `p_L < 0 < p_R` (the integrated
equations (1.11)). At a time `m` where the gap ratio is back at `p_R/(−p_L)` and the marks have separated by at least
`(p_R − p_L)/θ`, if (G5) holds at `m` and the restarted driver has a generating trace `η₂` on `[0, ∞)`, then every
terminal cluster point `x ∈ (p_L, p_R)` of `η` puts the restarted driver in the `θ`-band event of its word. -/
theorem bandEvent_of_cluster {w vL vR : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) (hl : Continuous vL)
    (hr : Continuous vR) (hsL : ∀ t, vL t < w t) (hsR : ∀ t, w t < vR t) {pL pR : ℝ} (hpL : pL < 0)
    (hpR : 0 < pR) (hLeq : ∀ t : ℝ≥0, vL t = pL + ∫ s in (0 : ℝ)..t, 2 / (vL s.toNNReal - w s.toNNReal))
    (hReq : ∀ t : ℝ≥0, vR t = pR + ∫ s in (0 : ℝ)..t, 2 / (vR s.toNNReal - w s.toNNReal))
    {θ : ℝ} (hθ : 0 < θ) {m : ℝ≥0} (hsep : ((pR - pL) / θ) ^ 2 ≤ (vR m - vL m) ^ 2)
    (hratio : vR m - w m = pR / (-pL) * (w m - vL m)) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η)
    {η₂ : ℝ≥0 → ℂ} (hη₂ : IsGeneratingTrace (Sec7.shiftNN w m) ⊤ η₂)
    (hG5 : HasInteriorInverseBoundary (fun s : ℝ => w s.toNNReal) m) {x : ℝ} (hxL : pL < x) (hxR : x < pR)
    (hcl : IsTermCluster η x) :
    BandEvent θ ((fun _ => vL m - w m), fun _ => vR m - w m) (Sec7.shiftNN w m) ⊤ := by
  have hWrc : Continuous fun s : ℝ => w s.toNNReal := hw.comp continuous_real_toNNReal
  have huL := isForwardSol_of_force hw hl (fun t => (hsL t).ne) hLeq m
  have huR := isForwardSol_of_force hw hr (fun t => (hsR t).ne') hReq m
  have hfL : (fwdMap (fun s : ℝ => w s.toNNReal) m pL).re = vL m - w m := by
    rw [fwdMap_eq_of_isForwardSol hWrc huL ⟨m.coe_nonneg, le_rfl⟩]
    simp
  have hfR : (fwdMap (fun s : ℝ => w s.toNNReal) m pR).re = vR m - w m := by
    rw [fwdMap_eq_of_isForwardSol hWrc huR ⟨m.coe_nonneg, le_rfl⟩]
    simp
  obtain ⟨y, hy, hband⟩ := exists_band_cluster hw hw0 hη hη₂ hG5 huL huR hxL hxR hcl
  rw [hfL, hfR] at hband
  have hw₂ : Continuous (Sec7.shiftNN w m) := (hw.comp (continuous_const.add continuous_id)).sub continuous_const
  rw [bandEvent_top_iff hw₂ (Sec7.shiftNN_zero w m) hη₂]
  refine realBand_of_isTermCluster ?_ hy
  -- the bands of widths `−p_L`, `p_R` lie in the `θ`-bands
  set L := w m - vL m with hL
  set R := vR m - w m with hR
  have hL0 : 0 < L := sub_pos.2 (hsL m)
  have hR0 : 0 < R := sub_pos.2 (hsR m)
  have ha : 0 < -pL := neg_pos.2 hpL
  have hsep' : (pR - pL) / θ ≤ R + L := by
    have h1 : vR m - vL m = R + L := by rw [hR, hL]; ring
    rw [h1] at hsep
    exact (pow_le_pow_iff_left₀ (by have := sub_pos.2 (hpL.trans hpR); positivity) (by positivity)
      two_ne_zero).1 hsep
  have hRL : R = pR / (-pL) * L := hratio
  have hkey : -pL ≤ θ * L := by
    have hpL0 : pL ≠ 0 := hpL.ne
    have hD : 0 < pR - pL := by linarith
    have e : (-pL) * (R + L) = L * (pR - pL) := by rw [hRL]; field_simp; ring
    have h := (div_le_iff₀ hθ).1 hsep'
    have h5 : (-pL) * (pR - pL) ≤ (-pL) * ((R + L) * θ) := mul_le_mul_of_nonneg_left h ha.le
    have h6 : (-pL) * ((R + L) * θ) = θ * L * (pR - pL) := by rw [← mul_assoc, e]; ring
    rw [h6] at h5
    exact le_of_mul_le_mul_right (by linarith : (-pL) * (pR - pL) ≤ (θ * L) * (pR - pL)) hD
  rcases hband with h | h
  · left
    simp only
    refine ⟨h.1, h.2.trans ?_⟩
    show vL m - w m - pL ≤ (1 - θ) * (vL m - w m)
    have : vL m - w m = -L := by rw [hL]; ring
    rw [this]; linarith
  · right
    simp only
    refine ⟨le_trans ?_ h.1, h.2⟩
    show (1 - θ) * (vR m - w m) ≤ vR m - w m - pR
    rw [← hR]
    have h4 : pR ≤ θ * R := by
      rw [hRL]
      have := mul_le_mul_of_nonneg_left hkey (div_nonneg hpR.le ha.le)
      rw [div_mul_cancel₀ _ ha.ne'] at this
      have e : θ * (pR / -pL * L) = pR / -pL * (θ * L) := by ring
      linarith
    linarith

/-! ### The restart inequality -/

section Main

variable {κ : ℝ} {xL xR ρL ρR : Fin 1 → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- The pathwise facts of a separated two-force evolution used at the restart. -/
def GoodSep (r : ℝ) (xL xR : Fin 1 → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (ω : Ω) : Prop :=
  ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ Continuous (fun t => VL 0 t ω) ∧
    Continuous (fun t => VR 0 t ω) ∧ (∀ t, VL 0 t ω < W t ω) ∧ (∀ t, W t ω < VR 0 t ω) ∧
    (∀ t : ℝ≥0, VL 0 t ω = xL 0 + ∫ s in (0 : ℝ)..t, 2 / (VL 0 s.toNNReal ω - W s.toNNReal ω)) ∧
    (∀ t : ℝ≥0, VR 0 t ω = xR 0 + ∫ s in (0 : ℝ)..t, 2 / (VR 0 s.toNNReal ω - W s.toNNReal ω)) ∧
    RealRec r (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) ∧
    (∀ t : ℝ≥0, 8 * (t : ℝ) ≤ (VR 0 t ω - VL 0 t ω) ^ 2)

/-- The good event holds almost surely for a separated two-force evolution. -/
theorem IsIntegratedSLEEvolution.ae_goodSep [IsProbabilityMeasure P] (hκ : 0 < κ) (hxL : xL 0 < 0)
    (hxR : 0 < xR 0) (hwL : κ / 2 - 2 ≤ ρL 0) (hwR : κ / 2 - 2 ≤ ρR 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, GoodSep (xR 0 / (-xL 0)) xL xR W VL VR ζ ω := by
  have hadm := hasAdmissiblePartialSums_one (xL := xL) (xR := xR) hwL hwR
  filter_upwards [Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ (isOrderedForceWord_one hxL hxR) hadm hE,
    IsIntegratedSLEEvolution.ae_realRec_sep hκ hxL hxR hadm hE, hE.2.2.2.2] with ω ⟨hζ, hsep⟩ hrec hp
  obtain ⟨hw, hl, hr⟩ := continuous_state_of_top hζ hp
  have hsL : ∀ t, VL 0 t ω < W t ω := fun t => by
    rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ t) with h0 | h0
    · have e1 : W 0 ω = 0 := hp.1
      have e2 : VL 0 0 ω = xL 0 := hp.2.1 0
      rw [← h0, show (⊥ : ℝ≥0) = 0 from rfl, e1, e2]; exact hxL
    · exact (hsep t h0).1 0
  have hsR : ∀ t, W t ω < VR 0 t ω := fun t => by
    rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ t) with h0 | h0
    · have e1 : W 0 ω = 0 := hp.1
      have e2 : VR 0 0 ω = xR 0 := hp.2.2.1 0
      rw [← h0, show (⊥ : ℝ≥0) = 0 from rfl, e1, e2]; exact hxR
    · exact (hsep t h0).2 0
  rw [hζ] at hp
  refine ⟨hζ, hw, hp.1, hl, hr, hsL, hsR, fun t => hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t ENNReal.coe_lt_top 0,
    fun t => hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t ENNReal.coe_lt_top 0, hrec,
    eight_mul_le_sep_sq hp hsL hsR⟩

/-- **The restart inequality** (B.3 L1236–L1259; additional note Lemma 3.4). For a separated two-force evolution with
weights `≥ κ/2 − 2` and every `θ > 0`, given (G5) for ordinary `SLE_κ` at positive stopping times, the probability that
the trace has a terminal cluster point in `(p_L, p_R)` is at most the canonical probability of the `θ`-band event. -/
theorem IsIntegratedSLEEvolution.measure_cluster_le_band [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{u} κ) (hxL : xL 0 < 0) (hxR : 0 < xR 0)
    (hwL : κ / 2 - 2 ≤ ρL 0) (hwR : κ / 2 - 2 ≤ ρR 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {θ : ℝ} (hθ : 0 < θ) :
    P {ω | ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧
        ∃ x : ℝ, xL 0 < x ∧ x < xR 0 ∧ IsTermCluster η x} ≤ codeLaw κ ρL ρR (bandCodeSet θ) (xL, xR) := by
  set r : ℝ := xR 0 / (-xL 0) with hr
  have hr0 : 0 < r := div_pos hxR (neg_pos.2 hxL)
  have hxL' : ∀ i, xL i < 0 := fun i => by rw [Fin.fin_one_eq_zero i]; exact hxL
  have hxR' : ∀ j, 0 < xR j := fun j => by rw [Fin.fin_one_eq_zero j]; exact hxR
  have hsep : ∀ i j, xL i < xR j := fun i j => (hxL' i).trans (hxR' j)
  have hadm := hasAdmissiblePartialSums_one (xL := xL) (xR := xR) hwL hwR
  obtain ⟨𝓖', hEa, hnull⟩ : ∃ 𝓖' : Filtration ℝ≥0 mΩ, IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓖' W VL VR B ζ ∧
      ∀ N : Set Ω, MeasurableSet N → P N = 0 → ∀ t, MeasurableSet[𝓖' t] N :=
    ⟨_, Ito.isIntegratedSLEEvolution_usualAugmentation hE,
      fun N hN hN0 t => Ito.measurableSet_usualAugmentation_of_null hN hN0 t⟩
  obtain ⟨N, hNsub, hNm0, hN0⟩ := exists_measurable_superset_of_null
    (ae_iff.1 (IsIntegratedSLEEvolution.ae_goodSep hκ hxL hxR hwL hwR hE))
  have hNm : ∀ t, MeasurableSet[𝓖' t] N := hnull N hNm0 hN0
  have hgood : ∀ ω ∉ N, GoodSep r xL xR W VL VR ζ ω := fun ω hω => by
    by_contra h; exact hω (hNsub h)
  -- the threshold time `t₀`
  set t₀ : ℝ≥0 := ⟨((xR 0 - xL 0) / θ) ^ 2 / 8 + 1, by positivity⟩ with ht₀def
  have ht₀ : (0 : ℝ≥0) < t₀ := by
    rw [← NNReal.coe_pos]; show (0 : ℝ) < ((xR 0 - xL 0) / θ) ^ 2 / 8 + 1; positivity
  have h8 : ((xR 0 - xL 0) / θ) ^ 2 ≤ 8 * (t₀ : ℝ) := by
    show _ ≤ 8 * (((xR 0 - xL 0) / θ) ^ 2 / 8 + 1); linarith
  -- the ratio hitting time after `t₀`
  set Y := ratioGap r W VL VR with hY
  have hYa : AdaptedBefore 𝓖' ζ (posAfterT t₀ Y) :=
    adaptedBefore_of_eq (fun t p => max ((p.2.2 - p.1) - r * (p.1 - p.2.1)) ((t₀ : ℝ) - (t : ℝ)))
      (fun t => by fun_prop) hEa.2.1 (hEa.2.2.1 0) (hEa.2.2.2.1 0) fun t ω => rfl
  have hYa' : AdaptedBefore 𝓖' ζ (posAfterT t₀ (-Y)) :=
    adaptedBefore_of_eq (fun t p => max (-((p.2.2 - p.1) - r * (p.1 - p.2.1))) ((t₀ : ℝ) - (t : ℝ)))
      (fun t => by fun_prop) hEa.2.1 (hEa.2.2.1 0) (hEa.2.2.2.1 0) fun t ω => rfl
  have hZa : AdaptedBefore 𝓖' ζ (zeroProc (Ω := Ω)) :=
    adaptedBefore_of_eq (fun _ _ => 0) (fun _ => measurable_const) hEa.2.1 (hEa.2.2.1 0) (hEa.2.2.2.1 0)
      fun _ _ => rfl
  have hYc : ∀ ω ∉ N, Continuous fun t => Y t ω := fun ω hω => by
    obtain ⟨-, hw, -, hl, hr', -⟩ := hgood ω hω
    exact (hr'.sub hw).sub (continuous_const.mul (hw.sub hl))
  have hT₁ := Sec7.isStoppingTime_firstMeet_off hZa hYa hNm fun ω hω =>
    continuousOn_posAfterT_sub (hYc ω hω) _
  have hT₂ := Sec7.isStoppingTime_firstMeet_off hZa hYa' hNm fun ω hω =>
    continuousOn_posAfterT_sub (Y := -Y) (hYc ω hω).neg _
  set Th : Ω → ℝ≥0∞ := fun ω => max (Sec7.zeroOn N (Sec7.firstMeet zeroProc (posAfterT t₀ Y) ζ) ω)
    (Sec7.zeroOn N (Sec7.firstMeet zeroProc (posAfterT t₀ (-Y)) ζ) ω) with hTh
  have hThs : IsStoppingTime 𝓖' fun ω => (Th ω : WithTop ℝ≥0) := hT₁.max hT₂
  have hhit : ∀ ω ∉ N, ∃ m : ℝ≥0, Th ω = m ∧ t₀ ≤ m ∧ Y m ω = 0 := fun ω hω => by
    obtain ⟨hζ, hw, -, hl, hr', -, -, -, -, hrec, -⟩ := hgood ω hω
    obtain ⟨t₁, ht₁, hz⟩ := exists_rgap_eq_zero (continuous_rgap hw hl hr') hrec t₀
    have : Th ω = hitAfterT t₀ Y ζ ω := by
      simp only [hTh, hitAfterT, Sec7.zeroOn_of_notMem hω]
    rw [this]
    exact exists_hitAfterT (hYc ω hω) hζ ht₁ hz
  -- the capped stopping times and the restart events
  set Tn : ℕ → Ω → ℝ≥0 := fun n ω => (min (Th ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal with hTn
  have hTn_coe : ∀ n ω, ((Tn n ω : ℝ≥0) : ℝ≥0∞) = min (Th ω) ((n : ℝ≥0) : ℝ≥0∞) := fun n ω =>
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
  have hTns : ∀ n, IsStoppingTime 𝓖' fun ω => ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) := fun n => by
    have h := hThs.min_const (n : ℝ≥0)
    have he : (fun ω => ((Tn n ω : ℝ≥0) : WithTop ℝ≥0)) = fun ω => min (Th ω : WithTop ℝ≥0) (n : ℝ≥0) :=
      funext fun ω => hTn_coe n ω
    rw [he]; exact h
  set A : ℕ → Set Ω := fun n => Nᶜ ∩ {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} with hA
  have hTnA : ∀ n, ∀ ω ∈ A n, ((Tn n ω : ℝ≥0) : ℝ≥0∞) = Th ω := fun n ω hω => by
    rw [hTn_coe]; exact min_eq_left hω.2.le
  have hAm : ∀ n, MeasurableSet[(hTns n).measurableSpace] (A n) := by
    intro n
    have key : ∀ i : ℝ≥0, MeasurableSet[𝓖' i] (A n ∩ {ω | ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) ≤ i}) := by
      intro i
      have heq : A n ∩ {ω | ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) ≤ i} =
          Nᶜ ∩ ({ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} ∩ {ω | Th ω ≤ (i : ℝ≥0∞)}) := by
        ext ω
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, h2, ?_⟩
          have h3' : ((Tn n ω : ℝ≥0) : ℝ≥0∞) ≤ i := h3
          rwa [hTnA n ω ⟨h1, h2⟩] at h3'
        · rintro ⟨h1, h2, h3⟩
          refine ⟨⟨h1, h2⟩, ?_⟩
          show ((Tn n ω : ℝ≥0) : ℝ≥0∞) ≤ i
          rw [hTnA n ω ⟨h1, h2⟩]; exact h3
      rw [heq]
      refine (hNm i).compl.inter ?_
      rcases lt_or_ge i (n : ℝ≥0) with hin | hni
      · have he : {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} ∩ {ω | Th ω ≤ (i : ℝ≥0∞)} = {ω | Th ω ≤ (i : ℝ≥0∞)} := by
          refine inter_eq_right.2 fun ω (hω : Th ω ≤ i) => ?_
          exact lt_of_le_of_lt hω (by exact_mod_cast hin)
        rw [he]; exact hThs i
      · have he : {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} ∩ {ω | Th ω ≤ (i : ℝ≥0∞)} = {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} := by
          refine inter_eq_left.2 fun ω (hω : Th ω < (n : ℝ≥0)) => ?_
          exact le_trans hω.le (by exact_mod_cast hni)
        rw [he]; exact 𝓖'.mono hni _ (hThs.measurableSet_lt (n : ℝ≥0))
    refine ((hTns n).measurableSet _).2 ⟨?_, key⟩
    have h := key (n : ℝ≥0)
    have hsub : A n ∩ {ω | ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} = A n :=
      inter_eq_left.2 fun ω _ => by
        show ((Tn n ω : ℝ≥0) : ℝ≥0∞) ≤ ((n : ℝ≥0) : ℝ≥0∞)
        rw [hTn_coe]; exact min_le_right _ _
    rw [hsub] at h
    exact le_iSup (fun t => 𝓖' t) (n : ℝ≥0) _ h
  have hAT : ∀ n, ∀ ω ∈ A n, ((Tn n ω : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      (0 < Tn n ω ∨ ∀ i j, xL i < xR j) := fun n ω hω => by
    obtain ⟨hζ, -⟩ := hgood ω hω.1
    obtain ⟨m, hm, hm1, -⟩ := hhit ω hω.1
    refine ⟨by rw [hζ]; exact ENNReal.coe_lt_top, Or.inl ?_⟩
    have hTm : Tn n ω = m := by exact_mod_cast (hTnA n ω hω).trans hm
    rw [hTm]; exact lt_of_lt_of_le ht₀ hm1
  -- the restart formulas
  have hlawB := fun n => measure_restart_codeEventS hκ hEa (hTns n) (hAm n) (hAT n)
    (measurableSet_bandCodeSet θ) (fun _ _ _ => Iff.rfl) (bandEvent_congr θ)
  have hlawT := fun n => measure_restart_codeEvent hκ hEa (hTns n) (hAm n) (hAT n)
    (Φ := fun w τ => ¬ TopEvent w τ) measurableSet_topCodeSet.compl (fun _ _ _ => Iff.rfl) not_topEvent_congr
  have hAmeas : ∀ n, MeasurableSet (A n) := fun n => (hTns n).measurableSpace_le _ (hAm n)
  -- the canonical band probability is constant along the ray of words `(−L, rL)`
  set K := codeLaw κ ρL ρR (bandCodeSet θ) (xL, xR) with hK
  have htr := hE.ae_exists_isGeneratingTrace_top_of_hasAdmissiblePartialSums hκ (isOrderedForceWord_one hxL hxR)
    hadm hxL' hxR'
  have hdil : ∀ L : ℝ, 0 < L → codeLaw κ ρL ρR (bandCodeSet θ) ((fun _ => -L), fun _ => r * L) = K := by
    intro L hL
    have hxL0 : 0 < -xL 0 := neg_pos.2 hxL
    have hxne : xL 0 ≠ 0 := hxL.ne
    set c : ℝ≥0 := ⟨((-xL 0) / L) ^ 2, by positivity⟩ with hcdef
    have hc : c ≠ 0 := by
      intro h
      have : ((-xL 0) / L) ^ 2 = 0 := congrArg NNReal.toReal h
      exact (pow_pos (div_pos hxL0 hL) 2).ne' this
    have hsc : (√(c : ℝ))⁻¹ = L / (-xL 0) := by
      rw [show (c : ℝ) = ((-xL 0) / L) ^ 2 from rfl, Real.sqrt_sq (div_pos hxL0 hL).le, inv_div]
    rw [hK, ← codeLaw_band_dilate hκ hsep hE htr hc θ]
    congr 1
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · rw [Fin.fin_one_eq_zero i]
      show -L = (√(c : ℝ))⁻¹ * xL 0
      rw [hsc]
      field_simp
    · rw [Fin.fin_one_eq_zero j]
      show r * L = (√(c : ℝ))⁻¹ * xR 0
      rw [hsc, hr]
      field_simp
  have hRHS : ∀ n, ∫⁻ ω in A n, codeLaw κ ρL ρR (bandCodeSet θ) (wordAt W VL VR (Tn n) ω) ∂P =
      K * P (A n) := by
    intro n
    rw [← setLIntegral_const]
    refine setLIntegral_congr_fun (hAmeas n) fun ω hω => ?_
    obtain ⟨-, -, -, -, -, hsL, -⟩ := hgood ω hω.1
    obtain ⟨m, hm, hm1, hYm⟩ := hhit ω hω.1
    have hTm : Tn n ω = m := by exact_mod_cast (hTnA n ω hω).trans hm
    have hL : 0 < W m ω - VL 0 m ω := sub_pos.2 (hsL m)
    have hYm' : VR 0 m ω - W m ω = r * (W m ω - VL 0 m ω) := by
      simp only [hY, ratioGap] at hYm; linarith
    have hword : wordAt W VL VR (Tn n) ω =
        ((fun _ => -(W m ω - VL 0 m ω)), fun _ => r * (W m ω - VL 0 m ω)) := by
      simp only [wordAt, hTm]
      refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
      · rw [Fin.fin_one_eq_zero i]; simp only; ring
      · rw [Fin.fin_one_eq_zero j]; exact hYm'
    rw [hword, hdil _ hL]
  -- the restarted driver has a trace
  have hTop0 : ∀ n, ∫⁻ ω in A n, codeLaw κ ρL ρR topCodeSetᶜ (wordAt W VL VR (Tn n) ω) ∂P = 0 := by
    intro n
    refine (setLIntegral_congr_fun_ae (hAmeas n) ?_).trans ((setLIntegral_const _ 0).trans (zero_mul _))
    filter_upwards [ae_solvable_restart hκ hEa (hTns n) (hAm n) (hAT n)] with ω h hω
    obtain ⟨-, hsolv⟩ := h hω
    obtain ⟨-, -, -, -, -, hsL, hsR, -⟩ := hgood ω hω.1
    exact codeLaw_compl_topCodeSet_eq_zero hκ hwL hwR
      (show VL 0 (Tn n ω) ω - W (Tn n ω) ω < 0 by linarith [hsL (Tn n ω)])
      (show 0 < VR 0 (Tn n ω) ω - W (Tn n ω) ω by linarith [hsR (Tn n ω)]) hsolv
  -- (G5) at the restart times
  set T' : ℕ → Ω → ℝ≥0 := fun n ω => max (Tn n ω) t₀ with hT'
  have hT's : ∀ n, IsStoppingTime 𝓖' fun ω => ((T' n ω : ℝ≥0) : WithTop ℝ≥0) := fun n => by
    have h := (hTns n).max_const t₀
    have he : (fun ω => ((T' n ω : ℝ≥0) : WithTop ℝ≥0)) =
        fun ω => max ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) (t₀ : WithTop ℝ≥0) :=
      funext fun ω => by rw [hT']; push_cast; rfl
    rw [he]; exact h
  have hG5n := fun n => IsIntegratedSLEEvolution.ae_hasInteriorInverseBoundary hκ hG5 hEa (hT's n)
    (fun ω => lt_of_lt_of_le ht₀ (le_max_right _ _))
  -- the pathwise inclusion
  set Cl : Set Ω := {ω | ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧
      ∃ x : ℝ, xL 0 < x ∧ x < xR 0 ∧ IsTermCluster η x} with hCl
  have hincl : ∀ n, Cl ∩ A n ≤ᵐ[P] (A n ∩ {ω | BandEvent θ (wordAt W VL VR (Tn n) ω)
      (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω) (ζ ω - Tn n ω)}) ∪
      (A n ∩ {ω | ¬ TopEvent (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω) (ζ ω - Tn n ω)}) := by
    intro n
    filter_upwards [hG5n n] with ω hG ⟨⟨η, hη, x, hx1, hx2, hcl⟩, hωA⟩
    by_cases htop : TopEvent (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω) (ζ ω - Tn n ω)
    swap
    · exact Or.inr ⟨hωA, htop⟩
    refine Or.inl ⟨hωA, ?_⟩
    obtain ⟨hζ, hw, hw0, hl, hr', hsL, hsR, hLeq, hReq, -, h8m⟩ := hgood ω hωA.1
    obtain ⟨m, hm, hm1, hYm⟩ := hhit ω hωA.1
    have hTm : Tn n ω = m := by exact_mod_cast (hTnA n ω hωA).trans hm
    have hT'm : T' n ω = m := by simp only [hT', hTm]; exact max_eq_left hm1
    rw [hT'm] at hG
    have hζm : ζ ω - m = ⊤ := by rw [hζ]; exact ENNReal.top_sub_coe
    show BandEvent θ ((fun i => VL i (Tn n ω) ω - W (Tn n ω) ω), fun j => VR j (Tn n ω) ω - W (Tn n ω) ω)
      (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω) (ζ ω - Tn n ω)
    rw [hTm, hζm]
    rw [hTm, hζm] at htop
    have hw₂ : Continuous (Sec7.shiftNN (fun t => W t ω) m) :=
      (hw.comp (continuous_const.add continuous_id)).sub continuous_const
    obtain ⟨η₂, hη₂⟩ := (ratVals_mem_topSet_iff hw₂ (Sec7.shiftNN_zero _ m)).1 htop.2
    have hG' := hG (by rw [hζ]; exact ENNReal.coe_lt_top) (fun s _ => ⟨fun i => by
        rw [Fin.fin_one_eq_zero i]; exact hsL s, fun j => by rw [Fin.fin_one_eq_zero j]; exact hsR s⟩)
      (fun s : ℝ => W s.toNNReal ω) (hw.comp continuous_real_toNNReal) fun _ _ => rfl
    have hsep8 : ((xR 0 - xL 0) / θ) ^ 2 ≤ (VR 0 m ω - VL 0 m ω) ^ 2 :=
      h8.trans ((mul_le_mul_of_nonneg_left (show (t₀ : ℝ) ≤ m by exact_mod_cast hm1) (by norm_num)).trans
        (h8m m))
    have hratio : VR 0 m ω - W m ω = xR 0 / (-xL 0) * (W m ω - VL 0 m ω) := by
      rw [← hr]; simp only [hY, ratioGap] at hYm; linarith
    exact bandEvent_of_cluster hw hw0 hl hr' hsL hsR hxL hxR hLeq hReq hθ hsep8 hratio hη hη₂ hG' hx1 hx2 hcl
  -- the bound for each `n`
  have hbound : ∀ n, P Cl ≤ K + P (A n)ᶜ := by
    intro n
    have h1 : P (Cl ∩ A n) ≤ K := by
      calc P (Cl ∩ A n) ≤ P ((A n ∩ {ω | BandEvent θ (wordAt W VL VR (Tn n) ω)
            (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω) (ζ ω - Tn n ω)}) ∪
            (A n ∩ {ω | ¬ TopEvent (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω) (ζ ω - Tn n ω)})) :=
            measure_mono_ae (hincl n)
        _ ≤ P (A n ∩ {ω | BandEvent θ (wordAt W VL VR (Tn n) ω)
            (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω) (ζ ω - Tn n ω)}) +
            P (A n ∩ {ω | ¬ TopEvent (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω) (ζ ω - Tn n ω)}) :=
            measure_union_le _ _
        _ = K * P (A n) := by rw [hlawB n, hRHS n, hlawT n, hTop0 n, add_zero]
        _ ≤ K := mul_le_of_le_one_right' prob_le_one
    calc P Cl ≤ P (Cl ∩ A n) + P (A n)ᶜ := by
          refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
          by_cases h : ω ∈ A n
          · exact Or.inl ⟨hω, h⟩
          · exact Or.inr h
      _ ≤ K + P (A n)ᶜ := by gcongr
  -- the restart events exhaust the good event
  have hmonoA : Monotone A := fun n n' hnn' ω hω =>
    ⟨hω.1, show Th ω < ((n' : ℝ≥0) : ℝ≥0∞) from lt_of_lt_of_le hω.2 (by exact_mod_cast hnn')⟩
  have hcover : Nᶜ ⊆ ⋃ n, A n := fun ω hω => by
    obtain ⟨m, hm, -, -⟩ := hhit ω hω
    obtain ⟨n, hn⟩ := exists_nat_gt (m : ℝ)
    refine mem_iUnion.2 ⟨n, hω, ?_⟩
    show Th ω < ((n : ℝ≥0) : ℝ≥0∞)
    rw [hm]
    exact_mod_cast (show m < (n : ℝ≥0) by rw [← NNReal.coe_lt_coe]; exact_mod_cast hn)
  have hU : P (⋃ n, A n) = 1 := by
    refine le_antisymm prob_le_one ?_
    calc (1 : ℝ≥0∞) = P Nᶜ := by rw [prob_compl_eq_one_sub hNm0, hN0, tsub_zero]
      _ ≤ P (⋃ n, A n) := measure_mono hcover
  have hlim : Tendsto (fun n => P (A n)ᶜ) atTop (𝓝 0) := by
    have h1 := tendsto_measure_iUnion_atTop (μ := P) hmonoA
    rw [hU] at h1
    have e : (fun n => P (A n)ᶜ) = fun n => 1 - P (A n) := funext fun n => prob_compl_eq_one_sub (hAmeas n)
    rw [e]
    have h2 := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) h1 (Or.inl ENNReal.one_ne_top)
    simpa using h2
  have h := ge_of_tendsto (tendsto_const_nhds.add hlim) (Eventually.of_forall hbound)
  simpa using h

/-! ### (G2): no terminal cluster point at or beyond the marks -/

/-- **(G2) excludes the marks and the real points beyond them** (B.3 L1218–L1222; additional note (G2), L1359–L1366):
the trace stays in the closure of the hull, which keeps a positive distance from every compact subset of
`(−∞, p_L] ∪ [p_R, ∞)`. -/
theorem IsIntegratedSLEEvolution.ae_not_isTermCluster_mark [IsProbabilityMeasure P] (hκ4 : 4 < κ)
    (hG2 : SeparatedTwoForceStatement.{u} κ) (hxL : xL 0 < 0) (hxR : 0 < xR 0)
    (hwL : κ / 2 - 2 ≤ ρL 0) (hwR : κ / 2 - 2 ≤ ρR 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → ∀ x : ℝ, (x ≤ xL 0 ∨ xR 0 ≤ x) →
      ¬ IsTermCluster η x := by
  have e1 : (![xL 0] : Fin 1 → ℝ) = xL := by funext i; fin_cases i; rfl
  have e2 : (![xR 0] : Fin 1 → ℝ) = xR := by funext i; fin_cases i; rfl
  have e3 : (![ρL 0] : Fin 1 → ℝ) = ρL := by funext i; fin_cases i; rfl
  have e4 : (![ρR 0] : Fin 1 → ℝ) = ρR := by funext i; fin_cases i; rfl
  have hE' : IsIntegratedSLEEvolution κ ![xL 0] ![xR 0] ![ρL 0] ![ρR 0] P 𝓕 W VL VR B ζ := by
    rw [e1, e2, e3, e4]; exact hE
  filter_upwards [hG2 hκ4 (xL 0) (xR 0) (ρL 0) (ρR 0) hxL hxR hwL hwR P 𝓕 W VL VR B ζ hE', hE.2.2.2.2]
    with ω ⟨hζ, _, hdist⟩ hp η hη x hx
  obtain ⟨hw, -, -⟩ := continuous_state_of_top hζ hp
  have hWc : Continuous fun s : ℝ => W s.toNNReal ω := hw.comp continuous_real_toNNReal
  have hW0 : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by simpa using hp.1
  obtain ⟨δ, hδ, hfar⟩ := hdist {x} isCompact_singleton (by
    rintro y rfl
    rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr h)
  rw [isTermCluster_iff_not, not_not]
  refine ⟨δ, hδ, (eventually_gt_atTop 0).mono fun t ht => ?_⟩
  have htip := hη.tendsto_fwdMapInv_tip hw.continuousOn hp.1 (t := t) ENNReal.coe_lt_top
  have hcl := YuanCorollary13.mem_closure_fwdHull_of_tendsto hWc hW0 (NNReal.coe_pos.2 ht) htip
  have hsub : fwdHull (fun s : ℝ => W s.toNNReal ω) t ⊆ {z : ℂ | δ ≤ ‖z - x‖} := fun z hz =>
    hfar z (mem_iUnion₂.2 ⟨t, by rw [hζ]; exact ENNReal.coe_lt_top, hz⟩) x rfl
  have hclosed : IsClosed {z : ℂ | δ ≤ ‖z - x‖} :=
    isClosed_le continuous_const (continuous_id.sub continuous_const).norm
  exact hclosed.closure_subset_iff.2 hsub hcl

/-! ### Shrinking bands -/

/-- The band event is monotone in the fraction (for a word with marks on the two sides). -/
theorem bandEvent_mono {s : (Fin 1 → ℝ) × (Fin 1 → ℝ)} (hs1 : s.1 0 < 0) (hs2 : 0 < s.2 0) {θ θ' : ℝ}
    (hθ : 0 ≤ θ) (hθθ' : θ ≤ θ') {w : ℝ≥0 → ℝ} {τ : ℝ≥0∞} (h : BandEvent θ s w τ) : BandEvent θ' s w τ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun k N => ?_⟩
  obtain ⟨q, hq, hd⟩ := h3 k N
  refine ⟨q, hq, lt_of_le_of_lt ?_ hd⟩
  unfold bandDist
  have hab : s.1 0 ≤ (1 - θ) * s.1 0 := by nlinarith
  have hab' : (1 - θ) * s.2 0 ≤ s.2 0 := by nlinarith
  refine min_le_min ?_ ?_
  · refine dIcc_le _ ⟨(clamp_mem_Icc hab _).1, (clamp_mem_Icc hab _).2.trans (by nlinarith)⟩
  · refine dIcc_le _ ⟨le_trans (by nlinarith) (clamp_mem_Icc hab' _).1, (clamp_mem_Icc hab' _).2⟩

/-- The codes with the band event for every fraction `1/(k+1)`, `k ≤ m`. -/
def bandCodeSetLE (m : ℕ) : Set (XCode 1 1) := ⋂ k : ℕ, ⋂ (_ : k ≤ m), bandCodeSet (1 / ((k : ℝ) + 1))

theorem measurableSet_bandCodeSetLE (m : ℕ) : MeasurableSet (bandCodeSetLE m) :=
  MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => measurableSet_bandCodeSet _

/-- **The band probabilities tend to zero** (given (G2)). -/
theorem IsIntegratedSLEEvolution.tendsto_codeLaw_band [IsProbabilityMeasure P] (hκ4 : 4 < κ)
    (hG2 : SeparatedTwoForceStatement.{u} κ) (hxL : xL 0 < 0) (hxR : 0 < xR 0)
    (hwL : κ / 2 - 2 ≤ ρL 0) (hwR : κ / 2 - 2 ≤ ρR 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    Tendsto (fun m : ℕ => codeLaw κ ρL ρR (bandCodeSet (1 / ((m : ℝ) + 1))) (xL, xR)) atTop (𝓝 0) := by
  have hκ : 0 < κ := by linarith
  have hxL' : ∀ i, xL i < 0 := fun i => by rw [Fin.fin_one_eq_zero i]; exact hxL
  have hxR' : ∀ j, 0 < xR j := fun j => by rw [Fin.fin_one_eq_zero j]; exact hxR
  have hsep : ∀ i j, xL i < xR j := fun i j => (hxL' i).trans (hxR' j)
  have hcong : ∀ (Φ : ℕ → (Fin 1 → ℝ) × (Fin 1 → ℝ) → (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop),
      (∀ k, ∀ (s : (Fin 1 → ℝ) × (Fin 1 → ℝ)) (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞),
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) → Φ k s w τ → Φ k s w' τ) →
      ∀ (p : ℕ → Prop) (s : (Fin 1 → ℝ) × (Fin 1 → ℝ)) (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞),
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) → (∀ k, p k → Φ k s w τ) → ∀ k, p k → Φ k s w' τ :=
    fun Φ hΦ p s w w' τ h hk k hpk => hΦ k s w w' τ h (hk k hpk)
  -- the band probability is that of the bands for all fractions `1/(k+1)`, `k ≤ m`
  have heq : ∀ m : ℕ, codeLaw κ ρL ρR (bandCodeSet (1 / ((m : ℝ) + 1))) (xL, xR) =
      codeLaw κ ρL ρR (bandCodeSetLE m) (xL, xR) := by
    intro m
    rw [← measure_band_eq_codeLaw hκ hsep hE, ← measure_eventOf_eq_codeLawS hκ hsep hE
      (measurableSet_bandCodeSetLE m)
      (Φ := fun s w τ => ∀ k : ℕ, k ≤ m → BandEvent (1 / ((k : ℝ) + 1)) s w τ)
      (fun x _ _ => by simp only [bandCodeSetLE, mem_iInter]; rfl)
      (hcong (fun k s w τ => BandEvent (1 / ((k : ℝ) + 1)) s w τ) (fun k => bandEvent_congr _) _)]
    congr 1
    ext ω
    simp only [mem_ofPred_eq]
    constructor
    · intro h k hk
      refine bandEvent_mono hxL hxR (by positivity) ?_ h
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
    · intro h; exact h m le_rfl
  simp_rw [heq]
  have hanti : Antitone bandCodeSetLE := fun m m' hmm' x hx => by
    simp only [bandCodeSetLE, mem_iInter] at hx ⊢
    exact fun k hk => hx k (hk.trans hmm')
  have hlim := tendsto_codeLaw_iInter (a := κ) (ρL := ρL) (ρR := ρR) measurableSet_bandCodeSetLE hanti (xL, xR)
  convert hlim using 2
  -- the intersection has canonical probability zero
  rw [← measure_eventOf_eq_codeLawS hκ hsep hE (MeasurableSet.iInter measurableSet_bandCodeSetLE)
    (Φ := fun s w τ => ∀ m k : ℕ, k ≤ m → BandEvent (1 / ((k : ℝ) + 1)) s w τ)
    (fun x _ _ => by simp only [bandCodeSetLE, mem_iInter]; rfl)
    (fun s w w' τ h hb m k hk => bandEvent_congr _ s w w' τ h (hb m k hk))]
  symm
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [IsIntegratedSLEEvolution.ae_not_isTermCluster_mark hκ4 hG2 hxL hxR hwL hwR hE,
    hE.ae_exists_isGeneratingTrace_top_of_hasAdmissiblePartialSums hκ (isOrderedForceWord_one hxL hxR)
      (hasAdmissiblePartialSums_one hwL hwR) hxL' hxR', hE.2.2.2.2] with ω hmark ⟨hζ, η, hη⟩ hp hall
  obtain ⟨hw, -, -⟩ := continuous_state_of_top hζ hp
  have hb : ∀ m : ℕ, RealBand (1 / ((m : ℝ) + 1)) (xL, xR) η := fun m => by
    have h := hall m m le_rfl
    rw [hζ] at h
    exact (bandEvent_top_iff hw hp.1 hη _ _).1 h
  rcases isTermCluster_of_forall_realBand (s := (xL, xR)) hxL hxR hb with h | h
  · exact hmark η hη (xL 0) (Or.inl le_rfl) h
  · exact hmark η hη (xR 0) (Or.inr le_rfl) h

end Main

/-! ### Lemma 3.4 -/

/-- **Lemma 3.4 of the additional note (B.3 of the follow-up note), for `κ > 4`**: given Part A's (G5) at positive
stopping times of ordinary `SLE_κ` and the separated two-force confinement (G2), separated two-force laws with weights
`≥ κ/2 − 2` have no real terminal cluster point. -/
theorem separatedNoRealClusterStatement {κ : ℝ} (hκ4 : 4 < κ) (hG5 : StoppingInverseBoundaryStatement.{u} κ)
    (hG2 : SeparatedTwoForceStatement.{u} κ) : SeparatedNoRealClusterStatement.{u} κ := by
  intro xL xR ρL ρR hxL hxR hwL hwR Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hκ : 0 < κ := by linarith
  set Cl : Set Ω := {ω | ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧
      ∃ x : ℝ, xL 0 < x ∧ x < xR 0 ∧ IsTermCluster η x} with hCl
  have hCl0 : P Cl = 0 := by
    have hle : ∀ m : ℕ, P Cl ≤ codeLaw κ ρL ρR (bandCodeSet (1 / ((m : ℝ) + 1))) (xL, xR) := fun m =>
      IsIntegratedSLEEvolution.measure_cluster_le_band hκ hG5 hxL hxR hwL hwR hE (by positivity)
    exact le_antisymm (ge_of_tendsto (IsIntegratedSLEEvolution.tendsto_codeLaw_band hκ4 hG2 hxL hxR hwL hwR hE)
      (Eventually.of_forall hle)) bot_le
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hCl0,
    IsIntegratedSLEEvolution.ae_not_isTermCluster_mark hκ4 hG2 hxL hxR hwL hwR hE] with ω hω hmark η hη x
  by_contra hcon
  have hcl : IsTermCluster η x := isTermCluster_iff_not.2 hcon
  rcases le_or_gt x (xL 0) with h1 | h1
  · exact hmark η hη x (Or.inl h1) hcl
  rcases le_or_gt (xR 0) x with h2 | h2
  · exact hmark η hη x (Or.inr h2) hcl
  exact hω ⟨η, hη, x, h1, h2, hcl⟩

/-- Lemma 3.4 from the full stopping-time collar (G7) (`StoppingCollarStatement`), which contains (G5). -/
theorem separatedNoRealClusterStatement_of_collar {κ : ℝ} (hκ4 : 4 < κ) (hG7 : StoppingCollarStatement.{u} κ)
    (hG2 : SeparatedTwoForceStatement.{u} κ) : SeparatedNoRealClusterStatement.{u} κ :=
  separatedNoRealClusterStatement hκ4
    (fun P _ 𝓕 B hB T hT hT0 => (hG7 P 𝓕 B hB T hT hT0).mono fun _ h => h.1) hG2

/-! ### Consequences: the two-force bases for `κ > 4` -/

/-- **Two-seed transience for `κ > 4`** (B.3 L1260–L1264), given Part A's (G5) and (G2). -/
theorem twoSeedTransienceStatement_of_gt_four {κ : ℝ} (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) (hG2 : SeparatedTwoForceStatement.{0} κ) :
    TwoSeedTransienceStatement.{u} κ :=
  twoSeedTransienceStatement_of_separatedNoCluster (by linarith)
    (separatedNoRealClusterStatement hκ4 hG5 hG2)

/-- **Separated two-force transience for `κ > 4`** (B.3 L1265–L1276: "This proves all two-force bases, including
equality at the nonhitting threshold"), given Part A's (G5) and (G2): marks `x_L < 0 < x_R`, weights `≥ κ/2 − 2`; almost
surely every continuous generating trace on `[0, ∞)` tends to `∞`. -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoForce_gt_four {κ : ℝ} (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) (hG2 : SeparatedTwoForceStatement.{0} κ)
    {xL xR ρL ρR : Fin 1 → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hxL : xL 0 < 0) (hxR : 0 < xR 0) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop :=
  IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoForce_of_noCluster (by linarith)
    (separatedNoRealClusterStatement hκ4 hG5 hG2) hxL hxR hadm hE

end InteractingSLE.ZhanGT4
