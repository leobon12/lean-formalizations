/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BmSide
import InteractingSLE.Spec.Supplement.GB6LifeBase
import InteractingSLE.Spec.Supplement.GB6Disjoint
import InteractingSLE.Foundations.Loewner.Capacity

/-!
# The contact clause at the first contact (decision D17 (B), provisional): the deterministic theorem

Packet PROVE-GW2-BUF (round 10). D17 (B): on `[0, L)`, `L` the relative life at the first contact, the relative
driver `D` equals a canonical stage flow-line driver `Wc` (the stage law, an input owned by STAGEMEAN/RELDET).
Theorem 1.3 makes `Wc`'s trace `ηc` continuous on `[0, L]`. Before `L`, `ηc` is the relative trace: `relBdry` of safe
physical points `P u`. These converge to a contact point `p` with `−1/p` on the counterflow trace `α([0, s])`.

* **`contact_side`**: the limit of `relBdry (P n)` is a real point beyond a junction. Precisely,
  `V̂^{0,L}_s < 0` and `L ≥ junctionR`, or `V̂^{0,R}_s > 0` and `L ≤ junctionL`. This is GB6's endpoint argument
  (`GB6.gb6Endpoint_core`) in the relative trace's coordinates:
  * the safe points are approximated by interior points of the chart domain;
  * GB6's proved base statement `GB6.gb6BaseStatement` places `−1/L` in the filled base;
  * the uniform displacement bound gives `L ≠ 0`.
* **`gapVanishes_at_contact`**: the contact clause.
  * On a right contact, every mark `x ≤ Re ηc L` (in particular the right junction) has a vanishing gap along `D`
    at `L`.
  * On a left contact, the mirror statement holds for the negated driver.
  * The proof takes `x₀` = the junction and combines `GW2BmSide` (earlier real visits lie strictly between the
    junctions) with `GW2BmTip.gapVanishes_of_canonical_off` / `gapVanishes_neg_of_canonical_off`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Bh

open MartChar.RealFlow Supp8 Supp8.GB6 Supp8.GB6.CoordB Supp8.Q3Rel

/-- A safe point is approximated by interior safe points with close chart values. -/
theorem exists_interior_near {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : z ∈ relSafe U s) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℂ, q ∈ H ∧ q ∉ closure (invHull U s) ∧ dist q z < ε ∧ dist (relMap U s q) (relBdry U s z) < ε := by
  set O : Set ℂ := (closure (invHull U s))ᶜ with hO
  have hOo : IsOpen O := isClosed_closure.isOpen_compl
  have hzcl : z ∈ closure (O ∩ H) := by
    have h1 : z ∈ O ∩ closure H := ⟨hz.2, by rw [closure_H]; exact hz.1⟩
    exact hOo.inter_closure h1
  have : (𝓝[O ∩ H] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hzcl
  have hsub : O ∩ H ⊆ relSafe U s := fun q hq => ⟨QuantumZipper.H_subset_Hbar hq.2, hq.1⟩
  have hcont : Tendsto (relBdry U s) (𝓝[O ∩ H] z) (𝓝 (relBdry U s z)) :=
    ((continuousOn_relBdry hU hU0 hs) z hz).mono hsub
  have hid : Tendsto id (𝓝[O ∩ H] z) (𝓝 z) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hev : ∀ᶠ x in 𝓝[O ∩ H] z, x ∈ O ∩ H := self_mem_nhdsWithin
  obtain ⟨q, ⟨hqO, hqH⟩, hq1, hq2⟩ :=
    (hev.and ((hid.eventually (ball_mem_nhds z hε)).and (hcont.eventually (ball_mem_nhds _ hε)))).exists
  refine ⟨q, hqH, hqO, hq1, ?_⟩
  rw [← relBdry_eq hU hs hqH hqO]
  exact hq2

/-- **The side of the contact.** Safe points `P n → p`, with `−1/p` on the counterflow trace, whose chart values
converge to `L`: then `L` is real and lies beyond a junction (with the corresponding base end nonzero). -/
theorem contact_side {wα : ℝ≥0 → ℝ} {Tα : ℝ≥0∞} {α : ℝ≥0 → ℂ} {s : ℝ≥0} (hα : IsGeneratingTrace wα Tα α)
    (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα}) (hwα0 : wα 0 = 0) (hs : (s : ℝ≥0∞) < Tα) {U : ℝ → ℝ}
    (hU : Continuous U) (hU0 : U 0 = 0) (hagree_s : ∀ r ∈ Icc (0 : ℝ) s, wα r.toNNReal = U r)
    (hhull : fwdHull (fun r : ℝ => wα r.toNNReal) s = fwdHull U s) {P : ℕ → ℂ}
    (hP : ∀ n, P n ∈ relSafe U s) {p : ℂ} (hPp : Tendsto P atTop (𝓝 p)) (hp0 : p ≠ 0)
    (hpα : -p⁻¹ ∈ α '' Icc 0 s) {L : ℂ} (hL : Tendsto (fun n => relBdry U s (P n)) atTop (𝓝 L)) :
    L.im = 0 ∧ ((baseL U s < 0 ∧ junctionR U s ≤ L.re) ∨ (0 < baseR U s ∧ L.re ≤ junctionL U s)) := by
  have hs0 : (0 : ℝ) ≤ s := NNReal.coe_nonneg s
  -- interior approximations
  have happ : ∀ n : ℕ, ∃ q : ℂ, q ∈ H ∧ q ∉ closure (invHull U s) ∧ dist q (P n) < 1 / ((n : ℝ) + 1) ∧
      dist (relMap U s q) (relBdry U s (P n)) < 1 / ((n : ℝ) + 1) := fun n =>
    exists_interior_near hU hU0 hs0 (hP n) (by positivity)
  choose q hqH hqA hq1 hq2 using happ
  have hεt : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hqp : Tendsto q atTop (𝓝 p) := by
    refine tendsto_iff_dist_tendsto_zero.2 ?_
    have h1 : Tendsto (fun n => dist (P n) p) atTop (𝓝 0) := tendsto_iff_dist_tendsto_zero.1 hPp
    refine squeeze_zero (g := fun n : ℕ => 1 / ((n : ℝ) + 1) + dist (P n) p) (fun n => dist_nonneg)
      (fun n => (dist_triangle (q n) (P n) p).trans (add_le_add_left (hq1 n).le _)) ?_
    simpa using (hεt.add h1)
  have hqL : Tendsto (fun n => relMap U s (q n)) atTop (𝓝 L) := by
    refine tendsto_iff_dist_tendsto_zero.2 ?_
    have h1 : Tendsto (fun n => dist (relBdry U s (P n)) L) atTop (𝓝 0) := tendsto_iff_dist_tendsto_zero.1 hL
    refine squeeze_zero (g := fun n : ℕ => 1 / ((n : ℝ) + 1) + dist (relBdry U s (P n)) L)
      (fun n => dist_nonneg)
      (fun n => (dist_triangle _ (relBdry U s (P n)) L).trans (add_le_add_left (hq2 n).le _)) ?_
    simpa using (hεt.add h1)
  -- the points in the counterflow chart
  set z : ℕ → ℂ := fun n => -(q n)⁻¹ with hzdef
  have hzK : ∀ n, z n ∈ H \ fwdHull U s := fun n => by
    refine ⟨GB6.neg_inv_mem_H (hqH n), fun hK => hqA n (subset_closure ⟨z n, hK, ?_⟩)⟩
    simp only [hzdef, GB6.neg_inv_neg_inv]
  have hzs : Tendsto z atTop (𝓝 (-p⁻¹)) := ((continuousAt_inv₀ hp0).neg.tendsto).comp hqp
  have hfz : ∀ n, fwdMap U s (z n) = -(relMap U s (q n))⁻¹ := fun n => by
    simp only [hzdef, relMap, GB6.neg_inv_neg_inv]
  have hrH : ∀ n, relMap U s (q n) ∈ H := fun n => by
    have h := GB6.neg_inv_mem_H (QuantumZipper.FwdHolo.mapsTo_fwdMap hU hs0 (hzK n))
    rw [hfz n, GB6.neg_inv_neg_inv] at h
    exact h
  -- `L` is real
  have hLnotH : L ∉ H := by
    intro hLH
    have hzeq : ∀ n, z n = fwdMapInv U s (-(relMap U s (q n))⁻¹) := fun n => by
      rw [← hfz n, QuantumZipper.RS.fwdMapInv_fwdMap hU hU0 hs0 (hzK n)]
    have h1 : Tendsto (fun n => -(relMap U s (q n))⁻¹) atTop (𝓝[H] (-L⁻¹)) :=
      tendsto_nhdsWithin_iff.2 ⟨(hqL.inv₀ (ne_zero_of_mem_H hLH)).neg,
        Eventually.of_forall fun n => GB6.neg_inv_mem_H (hrH n)⟩
    have h2 := (continuousOn_fwdMapInv hU hU0 hs0 _ (GB6.neg_inv_mem_H hLH)).tendsto
    have hlim : Tendsto z atTop (𝓝 (fwdMapInv U s (-L⁻¹))) := by
      have e : z = fun n => fwdMapInv U s (-(relMap U s (q n))⁻¹) := funext hzeq
      rw [e]; exact h2.comp h1
    have hq := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hU hU0 hs0 (GB6.neg_inv_mem_H hLH)
    rw [← tendsto_nhds_unique hzs hlim] at hq
    have hfill := Sec5.CrossRestart.inter_H_subset_of_isFilling (hα.2.2 s hs) ⟨hpα, hq.1⟩
    rw [hhull] at hfill
    exact hq.2 hfill
  have hLHbar : L ∈ Hbar := by
    rw [← closure_H]
    exact mem_closure_of_tendsto hqL (Eventually.of_forall hrH)
  have hLim : L.im = 0 := le_antisymm (not_lt.1 hLnotH) hLHbar
  -- `L ≠ 0` (uniform displacement)
  have hL0 : L ≠ 0 := by
    intro hL0
    obtain ⟨M', hM'⟩ : ∃ M', ∀ r ∈ Icc (0 : ℝ) s, |U r| ≤ M' := by
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hU.continuousOn
      exact ⟨C, fun r hr => by simpa [Real.norm_eq_abs] using hC r hr⟩
    have hdisp : ∀ n, ‖fwdMap U s (z n) - z n‖ ≤ 24 * M' + 8 * Real.sqrt s := fun n =>
      norm_fwdMap_sub_self_le hU hU0 hs0 hM' (hzK n) ⟨hs0, le_rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, ∀ n, ‖z n‖ ≤ B := by
      obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto z hzs).exists_norm_le
      exact ⟨B, fun n => hB _ ⟨n, rfl⟩⟩
    have hinf : Tendsto (fun n => ‖fwdMap U s (z n)‖) atTop atTop := by
      have e : (fun n => ‖fwdMap U s (z n)‖) = fun n => (‖relMap U s (q n)‖)⁻¹ := by
        funext n; rw [hfz, norm_neg, norm_inv]
      rw [e]
      have h0 : Tendsto (fun n => ‖relMap U s (q n)‖) atTop (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => norm_pos_iff.2 (ne_zero_of_mem_H (hrH n))⟩
        have := (continuous_norm.tendsto L).comp hqL
        rw [hL0, norm_zero] at this
        exact this
      exact tendsto_inv_nhdsGT_zero.comp h0
    obtain ⟨n, hn⟩ := (hinf.eventually_gt_atTop (B + (24 * M' + 8 * Real.sqrt s))).exists
    have h1 : ‖fwdMap U s (z n)‖ ≤ ‖fwdMap U s (z n) - z n‖ + ‖z n‖ := by
      have := norm_add_le (fwdMap U s (z n) - z n) (z n)
      rwa [sub_add_cancel] at this
    linarith [hdisp n, hB n]
  -- the base statement at `y = −1/L`
  have hLre : L = (L.re : ℂ) := Complex.ext rfl (by simp [hLim])
  have hLre0 : L.re ≠ 0 := fun h => hL0 (by rw [hLre, h, Complex.ofReal_zero])
  set y : ℝ := -(L.re)⁻¹ with hydef
  have hy0 : y ≠ 0 := neg_ne_zero.2 (inv_ne_zero hLre0)
  have hyconv : Tendsto (fun n => fwdMap (fun r : ℝ => wα r.toNNReal) s (z n)) atTop (𝓝 (y : ℂ)) := by
    have e : ∀ n, fwdMap (fun r : ℝ => wα r.toNNReal) s (z n) = fwdMap U s (z n) :=
      fun n => fwdMap_eq_of_eqOn hs0 hagree_s
    simp_rw [e, hfz]
    have hy : (y : ℂ) = -L⁻¹ := by
      rw [hLre, hydef]; push_cast; ring
    rw [hy]
    exact (hqL.inv₀ hL0).neg
  have hzK' : ∀ n, z n ∈ H \ fwdHull (fun r : ℝ => wα r.toNNReal) s := fun n => by
    rw [hhull]; exact hzK n
  obtain ⟨hyL, hyR⟩ := gb6BaseStatement wα Tα α s hα hwα hwα0 hs z (-p⁻¹) y hzK' hzs hpα hyconv
  -- the base ends of the agreeing continuous driver
  have hbR : baseR (fun r : ℝ => wα r.toNNReal) s = baseR U s := by
    unfold baseR
    rw [rightImg_congr hU hs0 hagree_s]
    exact congrArg (fun t => rightImg U 0 s - t) (hagree_s s ⟨hs0, le_rfl⟩)
  have hbL : baseL (fun r : ℝ => wα r.toNNReal) s = baseL U s := by
    unfold baseL
    rw [rightImg_congr hU.neg hs0 (fun r hr => by simp only [hagree_s r hr, Pi.neg_apply])]
    exact congrArg (fun t => -rightImg (-U) 0 s - t) (hagree_s s ⟨hs0, le_rfl⟩)
  rw [hbR] at hyR
  rw [hbL] at hyL
  refine ⟨hLim, ?_⟩
  have hLy : L.re = -y⁻¹ := by rw [hydef, inv_neg, inv_inv, neg_neg]
  rw [hLy]
  rcases lt_or_gt_of_ne hy0 with hyn | hyp
  · left
    have hbL0 : baseL U s < 0 := lt_of_le_of_lt hyL hyn
    refine ⟨hbL0, ?_⟩
    unfold junctionR
    have := (inv_le_inv_of_neg hyn hbL0).2 hyL
    linarith
  · right
    have hbR0 : 0 < baseR U s := lt_of_lt_of_le hyp hyR
    refine ⟨hbR0, ?_⟩
    unfold junctionL
    have := (inv_le_inv₀ hbR0 hyp).2 hyR
    linarith

/-- **The contact clause at the first contact.** On `[0, L)` the driver `D` equals the continuous canonical driver
`Wc`, whose Loewner trace `ηc` is continuous on `[0, L]`; before `L`, `ηc u = relBdry (P u)` for safe physical points
`P u`, which tend (as `u ↑ L`) to a contact point `p` with `−1/p` on the counterflow trace. Then either the contact
is on the right (`V̂^{0,L}_s < 0`, `junctionR ≤ Re ηc L`) and every mark `x ≤ Re ηc L` has a vanishing gap along `D`
at `L`, or it is on the left and the mirror statement holds for the negated driver. -/
theorem gapVanishes_at_contact {wα : ℝ≥0 → ℝ} {Tα : ℝ≥0∞} {α : ℝ≥0 → ℂ} {s : ℝ≥0}
    (hα : IsGeneratingTrace wα Tα α) (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα}) (hwα0 : wα 0 = 0)
    (hs : (s : ℝ≥0∞) < Tα) {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    (hagree_s : ∀ r ∈ Icc (0 : ℝ) s, wα r.toNNReal = U r)
    (hhull : fwdHull (fun r : ℝ => wα r.toNNReal) s = fwdHull U s)
    {D Wc : ℝ → ℝ} (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) {L : ℝ} (hL : 0 < L)
    (hagree : ∀ r ∈ Ico 0 L, D r = Wc r) {ηc : ℝ → ℂ} (hη : IsLoewnerTraceLT Wc L ηc)
    (hc : ContinuousOn ηc (Icc 0 L)) {P : ℝ → ℂ}
    (hP : ∀ u ∈ Ico 0 L, P u ∈ relSafe U s ∧ ηc u = relBdry U s (P u)) {p : ℂ}
    (hPp : Tendsto P (𝓝[<] L) (𝓝 p)) (hp0 : p ≠ 0) (hpα : -p⁻¹ ∈ α '' Icc 0 s) :
    (baseL U s < 0 ∧ junctionR U s ≤ (ηc L).re ∧ ∀ x : ℝ, x ≤ (ηc L).re → GapVanishes D x L) ∨
      (0 < baseR U s ∧ (ηc L).re ≤ junctionL U s ∧
        ∀ x : ℝ, (ηc L).re ≤ x → GapVanishes (fun r => -D r) (-x) L) := by
  have hs0 : (0 : ℝ) ≤ s := NNReal.coe_nonneg s
  -- relative times increasing to `L`
  set v : ℕ → ℝ := fun n => L - L / ((n : ℝ) + 2) with hvdef
  have hvmem : ∀ n, v n ∈ Ico 0 L := fun n => by
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h3 : L / ((n : ℝ) + 2) ≤ L / 2 := div_le_div_of_nonneg_left hL.le (by norm_num) (by linarith)
    have h4 : 0 < L / ((n : ℝ) + 2) := div_pos hL h2
    exact ⟨by simp only [hvdef]; linarith, by simp only [hvdef]; linarith⟩
  have hvL : Tendsto v atTop (𝓝[<] L) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => (hvmem n).2⟩
    have h1 : Tendsto (fun n : ℕ => L / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
      exact tendsto_const_nhds.div_atTop this
    simpa [hvdef] using (tendsto_const_nhds (x := L)).sub h1
  have hPv : Tendsto (fun n => P (v n)) atTop (𝓝 p) := hPp.comp hvL
  have hηv : Tendsto (fun n => relBdry U s (P (v n))) atTop (𝓝 (ηc L)) := by
    have hcw : ContinuousWithinAt ηc (Icc 0 L) L := hc L ⟨hL.le, le_rfl⟩
    have hvI : Tendsto v atTop (𝓝[Icc 0 L] L) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_nhdsWithin_iff.1 hvL |>.1,
        Eventually.of_forall fun n => Ico_subset_Icc_self (hvmem n)⟩
    exact (hcw.tendsto.comp hvI).congr fun n => (hP (v n) (hvmem n)).2
  obtain ⟨hLim, hside⟩ := contact_side hα hwα hwα0 hs hU hU0 hagree_s hhull (fun n => (hP (v n) (hvmem n)).1)
    hPv hp0 hpα hηv
  rcases hside with ⟨hbL, hjR⟩ | ⟨hbR, hjL⟩
  · left
    refine ⟨hbL, hjR, fun x hx => ?_⟩
    have hjR0 : 0 < junctionR U s := by unfold junctionR; exact neg_pos.2 (inv_lt_zero.2 hbL)
    refine gapVanishes_of_canonical_off hWc hWc0 hL hagree hη hc hLim hjR0 hjR (fun u hu r hr h => ?_) hx
    have hlt := lt_junctionR_of_relBdry_eq hU hU0 hs0 (hP u hu).1 ((hP u hu).2.symm.trans h) hbL
    linarith
  · right
    refine ⟨hbR, hjL, fun x hx => ?_⟩
    have hjL0 : junctionL U s < 0 := by unfold junctionL; exact neg_lt_zero.2 (inv_pos.2 hbR)
    refine gapVanishes_neg_of_canonical_off hWc hWc0 hL hagree hη hc hLim hjL0 hjL (fun u hu r hr h => ?_) hx
    have hlt := junctionL_lt_of_relBdry_eq hU hU0 hs0 (hP u hu).1 ((hP u hu).2.symm.trans h) hbR
    linarith

end InteractingSLE.Theorem14.GW2Bh
