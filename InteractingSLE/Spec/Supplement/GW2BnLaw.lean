/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BmAt
import InteractingSLE.Spec.Supplement.GW2BlCol
import InteractingSLE.Spec.Supplement.GW2BlLink
import InteractingSLE.Spec.Supplement.GB6LifeEndMain
import InteractingSLE.Spec.Supplement.GB6Glue
import InteractingSLE.Spec.Supplement.S9DCuts

/-!
# The contact clause in GB6's setting, from the canonical driver (decision D17 (B))

Packet PROVE-GW2-BUF (round 11). GB6's setting is the following.
* A counterflow `(wα, α)`: a continuous driver from `0` with a complete generating trace, read up to its time `s`
  with `α s ∈ ℍ`.
* An explored curve `(w, γ)`: a continuous driver from `0` with a complete transient generating trace.
* The first contact `T_c` of `−1/γ` with `α([0, s])`, and the relative clock `a(t) = relClock (wα, s) w t`.

D17 (B) identifies the relative driver before contact with a canonical flow-line driver `Wc`, whose generating
trace `ηc` has a lifetime `ζc`. In hull form: `K^{Wc}_{a(t)} = Ψ(K^w_t)` for `t < T_c`. If the clock is bounded
before contact, its supremum is the relative life `L = contactLife`, and `L ≤ ζc` (Theorem 1.3's continuity up to
`ζc`). Then:

* **`canonical_eq_relBdry`**: before contact `γ t` is safe and `ηc(a t) = relBdry (γ t)`. Proof: GB6's glued
  chain gives the clock; round 9's `relTrace` is a Loewner trace of `Wc`; the two traces of `Wc` agree
  (`eqOn_trace_of_eqOn`).
* **`contact_side_H`**: GB6's endpoint argument along interior points (the base statement `gb6BaseStatement`).
* **`gapVanishes_contact_gb6`**: the contact clause, stated without auxiliary choices.
  * Either `V̂^{0,L}_s < 0`, `junctionR ≤ Re ηc(L)`, and every mark `x ≤ Re ηc(L)` has `GapVanishes Wc x L`;
  * or the mirror statement holds on the left.

  The contact may be at a finite time or at the start of the counterflow (`T_c = ∞` with a bounded clock, using
  transience).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Bh

open MartChar.RealFlow Supp8 Supp8.GB6 Supp8.GB6.CoordB Supp8.Q3Rel Restart

/-- The first contact of `−1/γ` with the counterflow prefix `α([0, s])` (GB6's `T_c`). -/
def contactTc (α γ : ℝ≥0 → ℂ) (s : ℝ≥0) : ℝ≥0∞ :=
  firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)

/-- The relative clock `a(t)` of the explored driver `w` in the counterflow chart `(wα, s)`. -/
def relClk (wα w : ℝ≥0 → ℝ) (s : ℝ≥0) (t : ℝ≥0) : ℝ := relClock (rp wα) s (rp w) t

/-- **The relative life at the first contact**: the supremum of the relative clock before contact. -/
def contactLife (wα w : ℝ≥0 → ℝ) (α γ : ℝ≥0 → ℂ) (s : ℝ≥0) : ℝ :=
  sSup (relClk wα w s '' {t : ℝ≥0 | (t : ℝ≥0∞) < contactTc α γ s})

/-- A generating trace with lifetime `≥ L`, read on `ℝ`, is a continuous Loewner trace on `[0, L]`. -/
theorem isLoewnerTraceLT_canonical {Wc : ℝ≥0 → ℝ} {ζc : ℝ≥0∞} {ηc : ℝ≥0 → ℂ} (hη : IsGeneratingTrace Wc ζc ηc)
    {L : ℝ} (hL0 : 0 < L) (hLζ : ENNReal.ofReal L ≤ ζc) :
    IsLoewnerTraceLT (rp Wc) L (fun u : ℝ => ηc u.toNNReal) ∧ ContinuousOn (fun u : ℝ => ηc u.toNNReal) (Icc 0 L) := by
  have hle : ∀ u : ℝ, u ≤ L → ((u.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζc := fun u hu =>
    (ENNReal.ofReal_le_ofReal hu).trans hLζ
  have hlt : ∀ u : ℝ, u < L → ((u.toNNReal : ℝ≥0) : ℝ≥0∞) < ζc := fun u hu =>
    ((ENNReal.ofReal_lt_ofReal_iff hL0).2 hu).trans_le hLζ
  have hc : ContinuousOn (fun u : ℝ => ηc u.toNNReal) (Icc 0 L) :=
    hη.2.1.comp continuous_real_toNNReal.continuousOn fun u hu => hle u hu.2
  refine ⟨⟨by simpa using hη.1, hc.mono Ico_subset_Icc_self, fun t ht htL => ?_⟩, hc⟩
  have htT := hlt t htL
  have hfill := hη.2.2 t.toNNReal htT
  rw [Real.coe_toNNReal _ ht] at hfill
  have hA : IsCompact (ηc '' Icc 0 t.toNNReal) := isCompact_Icc.image_of_continuousOn
    (hη.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans htT.le)
  rw [image_toNNReal_Icc ηc ht]
  exact (fillH_eq_iff_isFilling_of_isClosed hA.isBounded hA.isClosed ((QuantumZipper.fwdHull_mono).2 _)).1 hfill

section Setting

variable {wα w : ℝ≥0 → ℝ} {α γ : ℝ≥0 → ℂ} {s : ℝ≥0}

/-- `s > 0` when the counterflow tip at `s` is interior. -/
theorem s_pos_of_tip (hα : IsGeneratingTrace wα ⊤ α) (hsH : α s ∈ H) : (0 : ℝ) < s := by
  rcases eq_or_lt_of_le (NNReal.coe_nonneg s) with h0 | h0
  · exfalso
    have hs' : s = 0 := by exact_mod_cast h0.symm
    exact ne_zero_of_mem_H hsH (by rw [hs']; exact hα.1)
  · exact h0

/-- The physical prefix before contact is disjoint from the counterflow hull (closures, inverted chart). -/
theorem disjoint_before_contact (hwα : Continuous wα) (hwα0 : wα 0 = 0) (hα : IsGeneratingTrace wα ⊤ α)
    (hw : Continuous w) (hw0 : w 0 = 0) (hγ : IsGeneratingTrace w ⊤ γ) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) < contactTc α γ s) :
    Disjoint (closure (fwdHull (rp wα) s)) (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w) T)) :=
  disjoint_closure_fwdHull_of_lt_firstContactTime hα hwα.continuousOn hwα0 hγ hw.continuousOn hw0
    ENNReal.coe_lt_top ENNReal.coe_lt_top hT

/-- The tip of the counterflow at `s` is the boundary value of its inverse chart at `0`. -/
theorem tip_tendsto (hwα : Continuous wα) (hwα0 : wα 0 = 0) (hα : IsGeneratingTrace wα ⊤ α) :
    Tendsto (fwdMapInv (rp wα) s) (𝓝[H] 0) (𝓝 (α s)) :=
  IsGeneratingTrace.tendsto_fwdMapInv_tip hα hwα.continuousOn hwα0 ENNReal.coe_lt_top

/-- The first contact is strictly positive. -/
theorem contactTc_pos (hα : IsGeneratingTrace wα ⊤ α) (hγ : IsGeneratingTrace w ⊤ γ) : 0 < contactTc α γ s := by
  have hγc : Continuous γ := by
    have := hγ.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  have hαc : ContinuousOn α (Icc 0 s) := hα.2.1.mono fun t _ => show ((t : ℝ≥0) : ℝ≥0∞) ≤ ⊤ from le_top
  have hk : IsCompact (α '' Icc 0 s) := isCompact_Icc.image_of_continuousOn hαc
  have := firstContactTime_pos hγc.continuousAt hγ.1 hk.isBounded
  rwa [image_image] at this

/-- **GB6's glued chain: the relative clock is `0` at `0`, strictly increasing and continuous before contact.** -/
theorem relClk_props (hwα : Continuous wα) (hwα0 : wα 0 = 0) (hα : IsGeneratingTrace wα ⊤ α) (hsH : α s ∈ H)
    (hw : Continuous w) (hw0 : w 0 = 0) (hγ : IsGeneratingTrace w ⊤ γ) :
    relClk wα w s 0 = 0 ∧ StrictMonoOn (relClk wα w s) {t | (t : ℝ≥0∞) < contactTc α γ s} ∧
      ContinuousOn (relClk wα w s) {t | (t : ℝ≥0∞) < contactTc α γ s} := by
  have hγK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactTc α γ s →
      IsFilling (fwdHull (fun r : ℝ => w r.toNNReal) t) (γ '' Icc 0 t) := fun t _ => hγ.2.2 t ENNReal.coe_lt_top
  obtain ⟨_, -, ha0, hsm, hac, -, -⟩ := exists_glued_relChain hw hw0 (continuous_rp hwα) (by simp [rp, hwα0])
    (s_pos_of_tip hα hsH) (tip_tendsto hwα hwα0 hα) (contactTc_pos hα hγ)
    (fun T hT => disjoint_before_contact hwα hwα0 hα hw hw0 hγ hT) hγK
  exact ⟨ha0, hsm, hac⟩

/-- The relative clock is a clock on `[0, τ]` for every `τ` before contact. -/
theorem isClockOn_relClk (hwα : Continuous wα) (hwα0 : wα 0 = 0) (hα : IsGeneratingTrace wα ⊤ α) (hsH : α s ∈ H)
    (hw : Continuous w) (hw0 : w 0 = 0) (hγ : IsGeneratingTrace w ⊤ γ) {τ : ℝ≥0}
    (hτ : (τ : ℝ≥0∞) < contactTc α γ s) : IsClockOn (relClk wα w s) (τ : ℝ≥0∞) := by
  obtain ⟨ha0, hsm, hac⟩ := relClk_props hwα hwα0 hα hsH hw hw0 hγ
  have hsub : {r : ℝ≥0 | (r : ℝ≥0∞) ≤ (τ : ℝ≥0∞)} ⊆ {t | (t : ℝ≥0∞) < contactTc α γ s} := fun r hr =>
    lt_of_le_of_lt hr hτ
  exact ⟨ha0, hsm.mono hsub, hac.mono hsub, fun h => absurd h ENNReal.coe_ne_top⟩

/-- **Before contact the canonical trace is `relBdry` of the physical trace at the relative clock.** -/
theorem canonical_eq_relBdry (hwα : Continuous wα) (hwα0 : wα 0 = 0) (hα : IsGeneratingTrace wα ⊤ α)
    (hsH : α s ∈ H) (hw : Continuous w) (hw0 : w 0 = 0) (hγ : IsGeneratingTrace w ⊤ γ) {Wc : ℝ≥0 → ℝ}
    (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) {ηc' : ℝ → ℂ} {L : ℝ} (hηL : IsLoewnerTraceLT (rp Wc) L ηc')
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactTc α γ s →
      fwdHull (rp Wc) (relClk wα w s t) = relMap (rp wα) s '' fwdHull (rp w) t)
    (hle : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactTc α γ s → relClk wα w s t ≤ L) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < contactTc α γ s) :
    γ t ∈ relSafe (rp wα) s ∧ ηc' (relClk wα w s t) = relBdry (rp wα) s (γ t) := by
  obtain ⟨τ, htτ, hτ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htτ' : t < τ := ENNReal.coe_lt_coe.1 htτ
  have hs := s_pos_of_tip hα hsH
  have hU := continuous_rp hwα
  have hU0 : rp wα 0 = 0 := by simp [rp, hwα0]
  have hd := disjoint_before_contact hwα hwα0 hα hw hw0 hγ hτ
  have htip := tip_tendsto (s := s) hwα hwα0 hα
  have ha := isClockOn_relClk hwα hwα0 hα hsH hw hw0 hγ hτ
  have hγc : Continuous γ := by
    have := hγ.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  have hsafe : MapsTo γ (Iic τ) (relSafe (rp wα) s) := mapsTo_relSafe hU hs hw hw0 hγ hd
  have hKτ : ∀ t' : ℝ≥0, t' ≤ τ → fwdHull (rp Wc) (relClk wα w s t') =
      fillH (relBdry (rp wα) s '' (γ '' Icc 0 t')) :=
    relBdry_hull_of_relMap hU hU0 hs htip hw hw0 hγ hd fun t' ht' =>
      hK t' (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht') hτ)
  have hrel := isLoewnerTraceLT_relTrace hU hU0 hs.le ha hγc.continuousOn hγ.1 hsafe hKτ
  have heq := eqOn_trace_of_eqOn (continuous_rp hWc) (by simp [rp, hWc0]) (continuous_rp hWc)
    (by simp [rp, hWc0]) (fun _ _ => rfl) hηL hrel (hle τ hτ)
  refine ⟨hsafe htτ'.le, ?_⟩
  have hmem : relClk wα w s t ∈ Ico 0 (relClk wα w s τ) := by
    refine ⟨?_, ha.strictMonoOn (show ((t : ℝ≥0) : ℝ≥0∞) ≤ τ from htτ.le)
      (show ((τ : ℝ≥0) : ℝ≥0∞) ≤ τ from le_rfl) htτ'⟩
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
    · rw [← h, ha.zero]
    · have := ha.strictMonoOn (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ τ by simp) (show ((t : ℝ≥0) : ℝ≥0∞) ≤ τ from htτ.le) h
      rw [ha.zero] at this
      exact this.le
  rw [heq hmem]
  show relBdry (rp wα) s (γ (invClock (relClk wα w s) τ (relClk wα w s t).toNNReal)) = _
  rw [ha.invClock_apply (show ((t : ℝ≥0) : ℝ≥0∞) ≤ τ from htτ.le)]

/-- **GB6's endpoint argument along interior points.** Interior safe points `P n` (`−1/P n` off the counterflow
hull) with `−1/P n → zs ∈ α([0, s])` and chart values `relMap (P n) → L`: then `L` is real and beyond a junction. -/
theorem contact_side_H (hwα : Continuous wα) (hwα0 : wα 0 = 0) (hα : IsGeneratingTrace wα ⊤ α) {P : ℕ → ℂ}
    (hPH : ∀ n, P n ∈ H) (hPA : ∀ n, -(P n)⁻¹ ∉ fwdHull (rp wα) s) {zs : ℂ}
    (hzs : Tendsto (fun n => -(P n)⁻¹) atTop (𝓝 zs)) (hzsA : zs ∈ α '' Icc 0 s) {L : ℂ}
    (hL : Tendsto (fun n => relMap (rp wα) s (P n)) atTop (𝓝 L)) :
    L.im = 0 ∧ ((baseL (rp wα) s < 0 ∧ junctionR (rp wα) s ≤ L.re) ∨
      (0 < baseR (rp wα) s ∧ L.re ≤ junctionL (rp wα) s)) := by
  have hs0 : (0 : ℝ) ≤ s := NNReal.coe_nonneg s
  have hU := continuous_rp hwα
  have hU0 : rp wα 0 = 0 := by simp [rp, hwα0]
  set z : ℕ → ℂ := fun n => -(P n)⁻¹ with hzdef
  have hzK : ∀ n, z n ∈ H \ fwdHull (rp wα) s := fun n => ⟨GB6.neg_inv_mem_H (hPH n), hPA n⟩
  have hfz : ∀ n, fwdMap (rp wα) s (z n) = -(relMap (rp wα) s (P n))⁻¹ := fun n => by
    simp only [hzdef, relMap, GB6.neg_inv_neg_inv]
  have hrH : ∀ n, relMap (rp wα) s (P n) ∈ H := fun n => by
    have h := GB6.neg_inv_mem_H (QuantumZipper.FwdHolo.mapsTo_fwdMap hU hs0 (hzK n))
    rw [hfz n, GB6.neg_inv_neg_inv] at h
    exact h
  -- `L` is real
  have hLnotH : L ∉ H := by
    intro hLH
    have hzeq : ∀ n, z n = fwdMapInv (rp wα) s (-(relMap (rp wα) s (P n))⁻¹) := fun n => by
      rw [← hfz n, QuantumZipper.RS.fwdMapInv_fwdMap hU hU0 hs0 (hzK n)]
    have h1 : Tendsto (fun n => -(relMap (rp wα) s (P n))⁻¹) atTop (𝓝[H] (-L⁻¹)) :=
      tendsto_nhdsWithin_iff.2 ⟨(hL.inv₀ (ne_zero_of_mem_H hLH)).neg,
        Eventually.of_forall fun n => GB6.neg_inv_mem_H (hrH n)⟩
    have h2 := (continuousOn_fwdMapInv hU hU0 hs0 _ (GB6.neg_inv_mem_H hLH)).tendsto
    have hlim : Tendsto z atTop (𝓝 (fwdMapInv (rp wα) s (-L⁻¹))) := by
      have e : z = fun n => fwdMapInv (rp wα) s (-(relMap (rp wα) s (P n))⁻¹) := funext hzeq
      rw [e]; exact h2.comp h1
    have hq := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hU hU0 hs0 (GB6.neg_inv_mem_H hLH)
    rw [← tendsto_nhds_unique hzs hlim] at hq
    have hfill := Sec5.CrossRestart.inter_H_subset_of_isFilling (hα.2.2 s ENNReal.coe_lt_top) ⟨hzsA, hq.1⟩
    exact hq.2 hfill
  have hLHbar : L ∈ Hbar := by
    rw [← closure_H]
    exact mem_closure_of_tendsto hL (Eventually.of_forall hrH)
  have hLim : L.im = 0 := le_antisymm (not_lt.1 hLnotH) hLHbar
  -- `L ≠ 0` (uniform displacement)
  have hL0 : L ≠ 0 := by
    intro hL0
    obtain ⟨M', hM'⟩ : ∃ M', ∀ r ∈ Icc (0 : ℝ) s, |rp wα r| ≤ M' := by
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hU.continuousOn
      exact ⟨C, fun r hr => by simpa [Real.norm_eq_abs] using hC r hr⟩
    have hdisp : ∀ n, ‖fwdMap (rp wα) s (z n) - z n‖ ≤ 24 * M' + 8 * Real.sqrt s := fun n =>
      norm_fwdMap_sub_self_le hU hU0 hs0 hM' (hzK n) ⟨hs0, le_rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, ∀ n, ‖z n‖ ≤ B := by
      obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto z hzs).exists_norm_le
      exact ⟨B, fun n => hB _ ⟨n, rfl⟩⟩
    have hinf : Tendsto (fun n => ‖fwdMap (rp wα) s (z n)‖) atTop atTop := by
      have e : (fun n => ‖fwdMap (rp wα) s (z n)‖) = fun n => (‖relMap (rp wα) s (P n)‖)⁻¹ := by
        funext n; rw [hfz, norm_neg, norm_inv]
      rw [e]
      have h0 : Tendsto (fun n => ‖relMap (rp wα) s (P n)‖) atTop (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => norm_pos_iff.2 (ne_zero_of_mem_H (hrH n))⟩
        have := (continuous_norm.tendsto L).comp hL
        rw [hL0, norm_zero] at this
        exact this
      exact tendsto_inv_nhdsGT_zero.comp h0
    obtain ⟨n, hn⟩ := (hinf.eventually_gt_atTop (B + (24 * M' + 8 * Real.sqrt s))).exists
    have h1 : ‖fwdMap (rp wα) s (z n)‖ ≤ ‖fwdMap (rp wα) s (z n) - z n‖ + ‖z n‖ := by
      have := norm_add_le (fwdMap (rp wα) s (z n) - z n) (z n)
      rwa [sub_add_cancel] at this
    linarith [hdisp n, hB n]
  -- the base statement at `y = −1/L`
  have hLre : L = (L.re : ℂ) := Complex.ext rfl (by simp [hLim])
  have hLre0 : L.re ≠ 0 := fun h => hL0 (by rw [hLre, h, Complex.ofReal_zero])
  set y : ℝ := -(L.re)⁻¹ with hydef
  have hy0 : y ≠ 0 := neg_ne_zero.2 (inv_ne_zero hLre0)
  have hyconv : Tendsto (fun n => fwdMap (fun r : ℝ => wα r.toNNReal) s (z n)) atTop (𝓝 (y : ℂ)) := by
    show Tendsto (fun n => fwdMap (rp wα) s (z n)) atTop (𝓝 (y : ℂ))
    simp_rw [hfz]
    have hy : (y : ℂ) = -L⁻¹ := by
      rw [hLre, hydef]; push_cast; ring
    rw [hy]
    exact (hL.inv₀ hL0).neg
  obtain ⟨hyL, hyR⟩ := gb6BaseStatement wα ⊤ α s hα hwα.continuousOn hwα0 ENNReal.coe_lt_top z zs y hzK hzs hzsA
    hyconv
  change baseL (rp wα) s ≤ y at hyL
  change y ≤ baseR (rp wα) s at hyR
  refine ⟨hLim, ?_⟩
  have hLy : L.re = -y⁻¹ := by rw [hydef, inv_neg, inv_inv, neg_neg]
  rw [hLy]
  rcases lt_or_gt_of_ne hy0 with hyn | hyp
  · left
    have hbL0 : baseL (rp wα) s < 0 := lt_of_le_of_lt hyL hyn
    refine ⟨hbL0, ?_⟩
    unfold junctionR
    have := (inv_le_inv_of_neg hyn hbL0).2 hyL
    linarith
  · right
    have hbR0 : 0 < baseR (rp wα) s := lt_of_lt_of_le hyp hyR
    refine ⟨hbR0, ?_⟩
    unfold junctionL
    have := (inv_le_inv₀ hbR0 hyp).2 hyR
    linarith

end Setting

end InteractingSLE.Theorem14.GW2Bh
