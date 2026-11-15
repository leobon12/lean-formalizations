/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CwIdent

/-!
# The identification at one sample, over any right-dense set of B-times

Packet PROVE-SB2-CANON, round 5 (`Mz.CanonIdentOn` at `relOff`). **`ident_canon_gen`** is `ident_canon_at` with the
rational B-times replaced by any set `Q` of B-times that is right-dense in every open set (`hQ`); the versions' hull,
alive and coverage clauses are asked at the times of `Q`, the reach clause at rational clock levels, as before. At the
root, B's time is read from the entrance time `τ` of `R`, and the versions' clauses hold at the rational B-times after
`τ`, i.e. at `Q = {q − τ}` in the shifted time (`ident_canon_shift`, `SB2CqRoot`). The proof is `ident_canon_at`'s.

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.SB.Cz

open Sec7.PocketTraversal Sec7.Lemma71C Exist.Staged Sec2.Assembly

variable {ρ : ℝ → ℂ} {L : ℝ≥0∞}

/-- **The identification at one sample over a right-dense set of B-times.** See the module docstring. -/
theorem ident_canon_gen (hdr : IsDrivenCurve ρ) (hL : L ≠ 0) {Wm : ℕ → ℝ≥0 → ℝ} {am : ℕ → ℝ≥0 → ℝ≥0∞}
    {V : ℕ → ℝ≥0∞} {relLife : ℝ≥0∞} (hWc : ∀ m, Continuous (Wm m)) (hW0 : ∀ m, Wm m 0 = 0)
    (hac : ∀ m, Continuous (am m)) (ha0 : ∀ m, am m 0 = 0)
    (hsup : ⨆ m, V m = relLife)
    {Q : Set ℝ≥0} (hQ : ∀ O : Set ℝ≥0, IsOpen O → ∀ t ∈ O, ∃ q ∈ Q, q ∈ O ∧ t < q)
    (hhull : ∀ m, ∀ q ∈ Q, am m q < V m →
      fwdHull (fun s : ℝ => Wm m s.toNNReal) ((am m q).toNNReal : ℝ) = fillH (ρ '' Icc 0 (Nc.uOf L (q : ℝ))))
    (halive : ∀ m, ∀ q ∈ Q, am m q < V m → (q : ℝ≥0∞) < L)
    (hreach : ∀ m, ∀ q : ℚ, (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < V m →
      ∃ t, (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ am m t)
    (hcl : ∀ q ∈ Q, (q : ℝ≥0∞) < L → ∃ m, am m q < V m)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver e)
    (hmatch : ∀ m, V m ≤ e.2 ∧ ∀ n k, (dyad n k : ℝ≥0∞) < V m → Wm m (dyad n k) = e.1 (dyad n k))
    (hlife : e.2 = relLife) :
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < capLife ρ → e.1 t = segDriver ρ t) ∧ e.2 = capLife ρ := by
  set cl : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (capClock ρ (Nc.uOf L t)) with hcldef
  -- step 1: capacities at the times of `Q`
  have hcap : ∀ m, ∀ q ∈ Q, am m q < V m → am m q = cl q := by
    intro m q hqQ ht
    have hne : am m q ≠ ⊤ := ne_top_of_lt ht
    have hWc' : Continuous fun s : ℝ => Wm m s.toNNReal := (hWc m).comp continuous_real_toNNReal
    have h1 := ZhanGT4.A1Ref.hcapSet_fwdHull hWc' (NNReal.coe_nonneg (am m q).toNNReal)
    rw [hhull m q hqQ ht] at h1
    have hcc : capClock ρ (Nc.uOf L (q : ℝ)) = ((am m q).toNNReal : ℝ) := by
      show ConformalImage.hcapSet _ / 2 = _
      rw [h1]; ring
    show am m q = ENNReal.ofReal (capClock ρ (Nc.uOf L (q : ℝ)))
    rw [hcc, ENNReal.ofReal_coe_nnreal, ENNReal.coe_toNNReal hne]
  -- step 2: on the open set `{a m < V m}` B's time is before `L` and the clock is the canonical clock
  have hopen : ∀ m, IsOpen {t : ℝ≥0 | am m t < V m} := fun m => isOpen_lt (hac m) continuous_const
  have halive' : ∀ m, ∀ t : ℝ≥0, am m t < V m → (t : ℝ≥0∞) < L := by
    intro m t ht
    obtain ⟨q, hqQ, hqO, hqt⟩ := hQ _ (hopen m) t ht
    exact lt_trans (ENNReal.coe_lt_coe.2 hqt) (halive m q hqQ hqO)
  have hclock : ∀ m, ∀ t : ℝ≥0, am m t < V m → am m t = cl t := by
    intro m
    have hsub : {t : ℝ≥0 | am m t < V m} ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < L} := fun t ht => halive' m t ht
    refine EqOn.of_subset_closure
      (s := {t : ℝ≥0 | am m t < V m} ∩ Q) ?_
      (hac m).continuousOn ((continuousOn_clockB hdr).mono hsub) inter_subset_left fun t ht => ?_
    · rintro q ⟨ht, hqQ⟩
      exact hcap m q hqQ ht
    · rw [mem_closure_iff]
      intro O hO htO
      obtain ⟨q, hqQ, hqO, -⟩ := hQ _ (hO.inter (hopen m)) t ⟨htO, ht⟩
      exact ⟨q, hqO.1, hqO.2, hqQ⟩
  have hclt : ∀ m, ∀ t : ℝ≥0, am m t < V m → am m t < capLife ρ := fun m t ht => by
    rw [hclock m t ht]
    exact hdr.ofReal_capClock_lt (Nc.uOf_nonneg (Nc.beforeL_of_lt (halive' m t ht)))
  -- step 3: every stop is at most `capLife ρ`
  have hVle : ∀ m, V m ≤ capLife ρ := by
    intro m
    refine le_of_forall_lt fun c hc => ?_
    obtain ⟨q, -, hcq, hqV⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hc
    obtain ⟨t, ht⟩ := hreach m q hqV
    obtain ⟨t₁, -, ht₁⟩ := intermediate_value_Icc (bot_le : (0 : ℝ≥0) ≤ t) (hac m).continuousOn
      (show (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ∈ Icc (am m 0) (am m t) from ⟨by rw [ha0 m]; simp, ht⟩)
    have h1 : am m t₁ < V m := by rw [ht₁]; exact hqV
    calc c < (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) := hcq
      _ = am m t₁ := ht₁.symm
      _ < capLife ρ := hclt m t₁ h1
  have hrel : relLife ≤ capLife ρ := hsup ▸ iSup_le hVle
  -- step 4: `capLife ρ ≤ relLife`
  have hcapl : capLife ρ ≤ relLife := by
    refine iSup_le fun n => ?_
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    set s : ℝ := Nc.rTime L n with hsdef
    have hs0 : 0 ≤ s := Nc.rTime_nonneg hL hn
    have hsL : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < L := by
      by_cases hLt : L = ⊤
      · rw [hLt]; exact ENNReal.coe_lt_top
      · rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hs0]
        exact (ENNReal.ofReal_lt_iff_lt_toReal hs0 hLt).2 (rTime_lt hL hLt hn)
    obtain ⟨q, hqQ, hqL, hsq⟩ := hQ {t : ℝ≥0 | (t : ℝ≥0∞) < L}
      (isOpen_lt ENNReal.continuous_coe continuous_const) _ hsL
    obtain ⟨m, hm⟩ := hcl q hqQ hqL
    have hBs : Nc.BeforeL L s := by
      have := Nc.beforeL_of_lt hsL; rwa [Real.coe_toNNReal _ hs0] at this
    have hBq : Nc.BeforeL L (q : ℝ) := Nc.beforeL_of_lt hqL
    have hsq' : s ≤ (q : ℝ) := by
      have := hsq.le
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0] at this; exact this
    have hmono : capClock ρ n ≤ capClock ρ (Nc.uOf L (q : ℝ)) := by
      rw [show (n : ℝ) = Nc.uOf L s from (Nd.uOf_rTime hL hn).symm]
      rcases (Nc.monotoneOn_uOf hBs hBq hsq').lt_or_eq with h | h
      · exact (hdr.strictMonoOn_capClock (Nc.uOf_nonneg hBs) (Nc.uOf_nonneg hBq) h).le
      · rw [h]
    calc ENNReal.ofReal (capClock ρ n) ≤ cl q := ENNReal.ofReal_le_ofReal hmono
      _ = am m q := (hclock m _ hm).symm
      _ ≤ V m := hm.le
      _ ≤ relLife := hsup ▸ le_iSup V m
  have he2 : e.2 = capLife ρ := hlife.trans (le_antisymm hrel hcapl)
  refine ⟨fun t ht => ?_, he2⟩
  -- step 5: the drivers agree below the lifetime
  have hrel' : relLife = capLife ρ := le_antisymm hrel hcapl
  rw [← hrel', ← hsup] at ht
  obtain ⟨m, hm⟩ := lt_iSup_iff.1 ht
  obtain ⟨T, htT, hTV⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hm
  obtain ⟨v, hTv, hvV⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hTV
  have hvC : (v : ℝ≥0∞) < capLife ρ := lt_of_lt_of_le hvV (hVle m)
  obtain ⟨hsd0, hsdc, -⟩ := hdr.segDriver_spec
  set W₁ : ℝ → ℝ := fun s => Wm m s.toNNReal with hW₁
  set W₂ : ℝ → ℝ := fun s => segDriver ρ (min s.toNNReal v) with hW₂
  have hW₁c : Continuous W₁ := (hWc m).comp continuous_real_toNNReal
  have hW₂c : Continuous W₂ := by
    have hmn : Continuous fun s : ℝ => min s.toNNReal v := continuous_real_toNNReal.min continuous_const
    exact hsdc.comp_continuous hmn fun s => lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) hvC
  have hW₂eq : ∀ r ∈ Icc (0 : ℝ) v, W₂ r = segDriver ρ r.toNNReal := fun r hr => by
    have : r.toNNReal ≤ v := by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]; exact hr.2
    simp only [hW₂, min_eq_left this]
  set D : Set ℝ := {d | ∃ q ∈ Q, am m q < V m ∧ d = ((am m q).toNNReal : ℝ) ∧ d < v} with hDdef
  have hDhull : ∀ d ∈ D, fwdHull W₁ d = fwdHull W₂ d := by
    rintro d ⟨q, hqQ, hq, rfl, hdv⟩
    have hd0 : (0 : ℝ) ≤ ((am m q).toNNReal : ℝ) := NNReal.coe_nonneg _
    have hne : am m q ≠ ⊤ := ne_top_of_lt hq
    have hcl' := hclock m _ hq
    have hBq : Nc.BeforeL L (q : ℝ) := Nc.beforeL_of_lt (halive' m _ hq)
    have hc0 := hdr.capClock_nonneg (Nc.uOf_nonneg hBq)
    have hdc : ((am m q).toNNReal : ℝ) = capClock ρ (Nc.uOf L (q : ℝ)) := by
      rw [hcl']
      show ((ENNReal.ofReal _).toNNReal : ℝ) = _
      rw [ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal hc0]
    rw [hhull m q hqQ hq, Cf.fwdHull_congr hd0 hdv hW₂eq]
    rw [hdr.fwdHull_segDriver hd0 (by
      rw [← ENNReal.ofReal_coe_nnreal] at hvC
      exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hdv.le) hvC), hdc, hdr.capInv_eq (Nc.uOf_nonneg hBq)]
  have hTpos : (0 : ℝ) < T := lt_of_le_of_lt t.2 (by exact_mod_cast (ENNReal.coe_lt_coe.1 htT))
  have hDdense : ∀ t₀ ∈ Icc (0 : ℝ) T, ∀ ε > 0, ∃ s ∈ D, t₀ < s ∧ s < t₀ + ε := by
    intro t₀ ht₀ ε hε
    have hTv' : (T : ℝ) < v := by exact_mod_cast hTv
    set δ : ℝ := min ε (v - t₀) / 2 with hδ
    have hδ0 : 0 < δ := by
      have : 0 < min ε (v - t₀) := lt_min hε (by linarith [ht₀.2])
      linarith
    have hδ1 : t₀ + 2 * δ ≤ t₀ + ε := by have := min_le_left ε (v - t₀); linarith
    have hδ2 : t₀ + 2 * δ ≤ v := by have := min_le_right ε (v - t₀); linarith
    -- a B-time where the clock is `t₀ + δ`
    have hcV : ENNReal.ofReal (t₀ + δ) < V m := by
      refine lt_of_le_of_lt ?_ hvV
      rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal (by linarith)
    obtain ⟨q₀, -, hcq₀, hq₀V⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hcV
    obtain ⟨t₂, ht₂⟩ := hreach m q₀ hq₀V
    obtain ⟨t₁, -, ht₁⟩ := intermediate_value_Icc (bot_le : (0 : ℝ≥0) ≤ t₂) (hac m).continuousOn
      (show ENNReal.ofReal (t₀ + δ) ∈ Icc (am m 0) (am m t₂) from ⟨by rw [ha0 m]; simp,
        hcq₀.le.trans ht₂⟩)
    -- rational times near `t₁` have clock values in `(t₀, t₀ + 2δ)`
    set O : Set ℝ≥0 := am m ⁻¹' Ioo (ENNReal.ofReal t₀) (ENNReal.ofReal (t₀ + 2 * δ)) with hO
    have hOo : IsOpen O := isOpen_Ioo.preimage (hac m)
    have ht₀0 : 0 ≤ t₀ := ht₀.1
    have ht₁O : t₁ ∈ O := by
      show am m t₁ ∈ Ioo _ _
      rw [ht₁]
      exact ⟨(ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith),
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)⟩
    obtain ⟨q, hqQ, hqO, -⟩ := hQ _ hOo _ ht₁O
    have hq1 := hqO.1
    have hq2 := hqO.2
    have hqV : am m q < V m := by
      refine lt_trans hq2 (lt_of_le_of_lt ?_ hvV)
      rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hδ2
    have hne : am m q ≠ ⊤ := ne_top_of_lt hqV
    have hlo : t₀ < ((am m q).toNNReal : ℝ) := by
      have := (ENNReal.ofReal_lt_iff_lt_toReal (by linarith [ht₀.1]) hne).1 hq1
      rwa [ENNReal.toReal] at this
    have hhi : ((am m q).toNNReal : ℝ) < t₀ + 2 * δ := by
      have h' := (ENNReal.toReal_lt_toReal hne ENNReal.ofReal_ne_top).2 hq2
      rwa [ENNReal.toReal_ofReal (by linarith [ht₀.1]), ENNReal.toReal] at h'
    exact ⟨_, ⟨q, hqQ, hqV, rfl, by linarith⟩, hlo, by linarith⟩
  have heqW := eqOn_of_fwdHull_dense hW₁c hW₂c (by simp only [hW₁, Real.toNNReal_zero]; exact hW0 m) (by
    simp only [hW₂, Real.toNNReal_zero, zero_min]; exact hsd0) hTpos hDdense hDhull
  have htT' : t < T := ENNReal.coe_lt_coe.1 htT
  have hT' : (t : ℝ) ∈ Icc (0 : ℝ) T := ⟨t.2, by exact_mod_cast htT'.le⟩
  have h5a : Wm m t = segDriver ρ t := by
    have := heqW hT'
    simp only [hW₁, hW₂, Real.toNNReal_coe] at this
    rwa [min_eq_left (htT'.trans (ENNReal.coe_lt_coe.1 hTv)).le] at this
  have h5b : e.1 t = Wm m t := by
    refine eq_of_dyad_flr_eq ?_ (hWc m).continuousWithinAt fun n => ?_
    · have hlt : (t : ℝ≥0∞) < e.2 := lt_of_lt_of_le hm (hmatch m).1
      exact (hreg.1.continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hlt)).continuousWithinAt
    · exact ((hmatch m).2 n _ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (dyad_flr_le n t)) hm)).symm
  rw [h5b, h5a]


/-- **The rational B-times after `τ`, read from `τ`, are right-dense.** -/
theorem exists_shift_rat_mem_gt (τ : ℝ≥0) {O : Set ℝ≥0} (hO : IsOpen O) {t : ℝ≥0} (ht : t ∈ O) :
    ∃ q : ℚ, τ < (q : ℝ).toNNReal ∧ (q : ℝ).toNNReal - τ ∈ O ∧ t < (q : ℝ).toNNReal - τ := by
  have hO' : IsOpen ((fun u : ℝ≥0 => u - τ) ⁻¹' O) := hO.preimage (continuous_id.sub continuous_const)
  have hτt : τ + t ∈ (fun u : ℝ≥0 => u - τ) ⁻¹' O := by
    show τ + t - τ ∈ O; rwa [add_tsub_cancel_left]
  obtain ⟨q, hqO, hqt⟩ := exists_rat_mem_gt hO' hτt
  have hτq : τ < (q : ℝ).toNNReal := lt_of_le_of_lt le_self_add hqt
  refine ⟨q, hτq, hqO, ?_⟩
  exact lt_tsub_iff_left.2 hqt

/-- **The identification at one sample from a tail start `τ`** (the root): the versions' clock is `0` up to `τ`, and
their hull, alive and coverage clauses are asked at the rational B-times after `τ`; the canonical curve `ρ` is that of
B's piece after `τ` (lifetime `L`). -/
theorem ident_canon_shift (hdr : IsDrivenCurve ρ) (hL : L ≠ 0) {τ : ℝ≥0} {Wm : ℕ → ℝ≥0 → ℝ}
    {am : ℕ → ℝ≥0 → ℝ≥0∞} {V : ℕ → ℝ≥0∞} {relLife : ℝ≥0∞} (hWc : ∀ m, Continuous (Wm m))
    (hW0 : ∀ m, Wm m 0 = 0) (hac : ∀ m, Continuous (am m)) (ham : ∀ m, Monotone (am m)) (haτ : ∀ m, am m τ = 0)
    (hsup : ⨆ m, V m = relLife)
    (hhull : ∀ m, ∀ q : ℚ, τ < (q : ℝ).toNNReal → am m (q : ℝ).toNNReal < V m →
      fwdHull (fun s : ℝ => Wm m s.toNNReal) ((am m (q : ℝ).toNNReal).toNNReal : ℝ) =
        fillH (ρ '' Icc 0 (Nc.uOf L (((q : ℝ).toNNReal - τ : ℝ≥0) : ℝ))))
    (halive : ∀ m, ∀ q : ℚ, τ < (q : ℝ).toNNReal → am m (q : ℝ).toNNReal < V m →
      (((q : ℝ).toNNReal - τ : ℝ≥0) : ℝ≥0∞) < L)
    (hreach : ∀ m, ∀ q : ℚ, (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < V m →
      ∃ t, (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ am m t)
    (hcl : ∀ q : ℚ, τ < (q : ℝ).toNNReal → (((q : ℝ).toNNReal - τ : ℝ≥0) : ℝ≥0∞) < L →
      ∃ m, am m (q : ℝ).toNNReal < V m)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver e)
    (hmatch : ∀ m, V m ≤ e.2 ∧ ∀ n k, (dyad n k : ℝ≥0∞) < V m → Wm m (dyad n k) = e.1 (dyad n k))
    (hlife : e.2 = relLife) :
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < capLife ρ → e.1 t = segDriver ρ t) ∧ e.2 = capLife ρ := by
  set Q : Set ℝ≥0 := {s | ∃ q : ℚ, τ < (q : ℝ).toNNReal ∧ s = (q : ℝ).toNNReal - τ} with hQdef
  have hτs : ∀ q : ℚ, τ < (q : ℝ).toNNReal → τ + ((q : ℝ).toNNReal - τ) = (q : ℝ).toNNReal := fun q hq =>
    add_tsub_cancel_of_le hq.le
  refine ident_canon_gen hdr hL (am := fun m s => am m (τ + s)) hWc hW0
    (fun m => (hac m).comp (continuous_const.add continuous_id)) (fun m => by simp [haτ m]) hsup
    (Q := Q) (fun O hO t ht => ?_) (fun m q hqQ hq => ?_) (fun m q hqQ hq => ?_) (fun m q hq => ?_)
    (fun q hqQ hq => ?_) hreg hmatch hlife
  · obtain ⟨q, hτq, hqO, htq⟩ := exists_shift_rat_mem_gt τ hO ht
    exact ⟨_, ⟨q, hτq, rfl⟩, hqO, htq⟩
  · obtain ⟨q', hτq, rfl⟩ := hqQ
    simp only [hτs q' hτq] at hq ⊢
    exact hhull m q' hτq hq
  · obtain ⟨q', hτq, rfl⟩ := hqQ
    simp only [hτs q' hτq] at hq
    exact halive m q' hτq hq
  · obtain ⟨t, ht⟩ := hreach m q hq
    refine ⟨t - τ, ht.trans (ham m ?_)⟩
    exact le_add_tsub
  · obtain ⟨q', hτq, rfl⟩ := hqQ
    obtain ⟨m, hm⟩ := hcl q' hτq hq
    exact ⟨m, by simp only [hτs q' hτq]; exact hm⟩

end InteractingSLE.Theorem14.SB.Cz
