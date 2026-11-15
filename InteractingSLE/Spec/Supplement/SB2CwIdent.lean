/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CwDrv
import InteractingSLE.Spec.Supplement.SB2CwChain
import InteractingSLE.Spec.ZhanGT4.A1RefBridge

/-!
# The canonical driver is the canonical curve's driver (deterministic, one sample)

Packet PROVE-SB2-CANON, round 4 ((P4)). **`ident_canon_at`**: at one sample, let `ρ` be a driven curve, `L ≠ 0` B's
lifetime, and `(W m, a m, V m)` relative versions (continuous drivers from `0`, continuous monotone clocks from `0`,
stops `V m` increasing to `relLife`) such that, at every rational B-time `t` with `a m t < V m`, the version's hull at
its clock is the filled prefix `ρ[0, uOf t]` and `t < L` (the versions' hull and alive clauses read through NOJUMP's
identity), the versions reach every rational level below their stop, and every rational B-time before `L` is below
some stop (clause (i)). Then a regular driver `e` that is matched by the versions before their stops (K2) with lifetime
`relLife` is `ρ`'s driver below `ρ`'s capacity lifetime, and `e.2 = capLife ρ` — the inputs `he1`, `he2` of
`chainFor_canon`.

Steps: capacities give `a m t = capClock ρ (uOf t)` at rational times, hence on the open set `{a m < V m}` by
continuity; the stops are at most `capLife ρ` (intermediate values), and `capLife ρ ≤ relLife` (clause (i)); the
hulls of
`W m` and `ρ`'s driver agree on the right-dense set of rational clock values, so the drivers agree
(`eqOn_of_fwdHull_dense`), and `e = W m` at dyadic times gives `e = ρ`'s driver.

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

/-- Two functions continuous from the left at `t` that agree on the dyadic floors of `t` agree at `t`. -/
theorem eq_of_dyad_flr_eq {f g : ℝ≥0 → ℝ} {t : ℝ≥0} (hf : ContinuousWithinAt f (Iic t) t)
    (hg : ContinuousWithinAt g (Iic t) t) (h : ∀ n, f (dyad n (flr n t)) = g (dyad n (flr n t))) : f t = g t := by
  have hd : Tendsto (fun n => dyad n (flr n t)) atTop (𝓝[Iic t] t) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_dyad_flr t, Eventually.of_forall fun n => dyad_flr_le n t⟩
  have h1 := hf.tendsto.comp hd
  have h2 := hg.tendsto.comp hd
  simp only [Function.comp_def, h] at h1
  exact tendsto_nhds_unique h1 h2

variable {ρ : ℝ → ℂ} {L : ℝ≥0∞}

/-- The canonical clock in B's time, `t ↦ capClock ρ (uOf t)`, is continuous on B's times before `L`. -/
theorem continuousOn_clockB (hdr : IsDrivenCurve ρ) :
    ContinuousOn (fun t : ℝ≥0 => ENNReal.ofReal (capClock ρ (Nc.uOf L t))) {t : ℝ≥0 | (t : ℝ≥0∞) < L} := by
  have h1 : ContinuousOn (fun s : ℝ => capClock ρ (Nc.uOf L s)) {s | Nc.BeforeL L s} :=
    hdr.continuousOn_capClock.comp Nc.continuousOn_uOf fun s hs => Nc.uOf_nonneg hs
  have h2 : ContinuousOn (fun t : ℝ≥0 => capClock ρ (Nc.uOf L t)) {t : ℝ≥0 | (t : ℝ≥0∞) < L} :=
    h1.comp continuous_subtype_val.continuousOn fun t ht => Nc.beforeL_of_lt ht
  exact ENNReal.continuous_ofReal.comp_continuousOn h2

/-- A rational time `(q : ℝ).toNNReal` just above `t` inside an open set containing `t`. -/
theorem exists_rat_mem_gt {O : Set ℝ≥0} (hO : IsOpen O) {t : ℝ≥0} (ht : t ∈ O) :
    ∃ q : ℚ, (q : ℝ).toNNReal ∈ O ∧ t < (q : ℝ).toNNReal := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO t ht
  set δ : ℝ≥0 := ⟨ε / 2, by linarith⟩ with hδ
  have hlt : t < t + δ := lt_add_of_pos_right t (by rw [← NNReal.coe_pos, hδ]; show (0 : ℝ) < ε / 2; linarith)
  obtain ⟨q, -, hq1, hq2⟩ := (NNReal.lt_iff_exists_rat_btwn t (t + δ)).1 hlt
  refine ⟨q, hball ?_, hq1⟩
  rw [Metric.mem_ball, NNReal.dist_eq, abs_lt]
  have h1 := (NNReal.coe_lt_coe.2 hq1)
  have h2 := (NNReal.coe_lt_coe.2 hq2)
  rw [NNReal.coe_add] at h2
  have : ((δ : ℝ≥0) : ℝ) = ε / 2 := rfl
  constructor <;> linarith

/-- **The identification at one sample.** See the module docstring. -/
theorem ident_canon_at (hdr : IsDrivenCurve ρ) (hL : L ≠ 0) {Wm : ℕ → ℝ≥0 → ℝ} {am : ℕ → ℝ≥0 → ℝ≥0∞}
    {V : ℕ → ℝ≥0∞} {relLife : ℝ≥0∞} (hWc : ∀ m, Continuous (Wm m)) (hW0 : ∀ m, Wm m 0 = 0)
    (hac : ∀ m, Continuous (am m)) (ha0 : ∀ m, am m 0 = 0)
    (hsup : ⨆ m, V m = relLife)
    (hhull : ∀ m, ∀ q : ℚ, am m (q : ℝ).toNNReal < V m →
      fwdHull (fun s : ℝ => Wm m s.toNNReal) ((am m (q : ℝ).toNNReal).toNNReal : ℝ) =
        fillH (ρ '' Icc 0 (Nc.uOf L (((q : ℝ).toNNReal : ℝ≥0) : ℝ))))
    (halive : ∀ m, ∀ q : ℚ, am m (q : ℝ).toNNReal < V m → (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < L)
    (hreach : ∀ m, ∀ q : ℚ, (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < V m →
      ∃ t, (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ am m t)
    (hcl : ∀ q : ℚ, (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < L → ∃ m, am m (q : ℝ).toNNReal < V m)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver e)
    (hmatch : ∀ m, V m ≤ e.2 ∧ ∀ n k, (dyad n k : ℝ≥0∞) < V m → Wm m (dyad n k) = e.1 (dyad n k))
    (hlife : e.2 = relLife) :
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < capLife ρ → e.1 t = segDriver ρ t) ∧ e.2 = capLife ρ := by
  set cl : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (capClock ρ (Nc.uOf L t)) with hcldef
  -- step 1: capacities at rational times
  have hcap : ∀ m, ∀ q : ℚ, am m (q : ℝ).toNNReal < V m → am m (q : ℝ).toNNReal = cl (q : ℝ).toNNReal := by
    intro m q ht
    have hne : am m (q : ℝ).toNNReal ≠ ⊤ := ne_top_of_lt ht
    have hWc' : Continuous fun s : ℝ => Wm m s.toNNReal := (hWc m).comp continuous_real_toNNReal
    have h1 := ZhanGT4.A1Ref.hcapSet_fwdHull hWc' (NNReal.coe_nonneg (am m (q : ℝ).toNNReal).toNNReal)
    rw [hhull m q ht] at h1
    have hcc : capClock ρ (Nc.uOf L (((q : ℝ).toNNReal : ℝ≥0) : ℝ)) =
        ((am m (q : ℝ).toNNReal).toNNReal : ℝ) := by
      show ConformalImage.hcapSet _ / 2 = _
      rw [h1]; ring
    show am m (q : ℝ).toNNReal = ENNReal.ofReal (capClock ρ (Nc.uOf L (((q : ℝ).toNNReal : ℝ≥0) : ℝ)))
    rw [hcc, ENNReal.ofReal_coe_nnreal, ENNReal.coe_toNNReal hne]
  -- step 2: on the open set `{a m < V m}` B's time is before `L` and the clock is the canonical clock
  have hopen : ∀ m, IsOpen {t : ℝ≥0 | am m t < V m} := fun m => isOpen_lt (hac m) continuous_const
  have halive' : ∀ m, ∀ t : ℝ≥0, am m t < V m → (t : ℝ≥0∞) < L := by
    intro m t ht
    obtain ⟨q, hqO, hqt⟩ := exists_rat_mem_gt (hopen m) ht
    exact lt_trans (ENNReal.coe_lt_coe.2 hqt) (halive m q hqO)
  have hclock : ∀ m, ∀ t : ℝ≥0, am m t < V m → am m t = cl t := by
    intro m
    have hsub : {t : ℝ≥0 | am m t < V m} ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < L} := fun t ht => halive' m t ht
    refine EqOn.of_subset_closure
      (s := {t : ℝ≥0 | am m t < V m} ∩ range (fun q : ℚ => (q : ℝ).toNNReal)) ?_
      (hac m).continuousOn ((continuousOn_clockB hdr).mono hsub) inter_subset_left fun t ht => ?_
    · rintro _ ⟨ht, q, rfl⟩
      exact hcap m q ht
    · rw [mem_closure_iff]
      intro O hO htO
      obtain ⟨q, hqO, -⟩ := exists_rat_mem_gt (hO.inter (hopen m)) ⟨htO, ht⟩
      exact ⟨_, hqO.1, hqO.2, q, rfl⟩
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
    obtain ⟨q, -, hsq, hqL⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hsL
    obtain ⟨m, hm⟩ := hcl q hqL
    have hBs : Nc.BeforeL L s := by
      have := Nc.beforeL_of_lt hsL; rwa [Real.coe_toNNReal _ hs0] at this
    have hBq : Nc.BeforeL L (((q : ℝ).toNNReal : ℝ≥0) : ℝ) := Nc.beforeL_of_lt hqL
    have hsq' : s ≤ (((q : ℝ).toNNReal : ℝ≥0) : ℝ) := by
      have := ENNReal.coe_le_coe.1 hsq.le
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0] at this; exact this
    have hmono : capClock ρ n ≤ capClock ρ (Nc.uOf L (((q : ℝ).toNNReal : ℝ≥0) : ℝ)) := by
      rw [show (n : ℝ) = Nc.uOf L s from (Nd.uOf_rTime hL hn).symm]
      rcases (Nc.monotoneOn_uOf hBs hBq hsq').lt_or_eq with h | h
      · exact (hdr.strictMonoOn_capClock (Nc.uOf_nonneg hBs) (Nc.uOf_nonneg hBq) h).le
      · rw [h]
    calc ENNReal.ofReal (capClock ρ n) ≤ cl (q : ℝ).toNNReal := ENNReal.ofReal_le_ofReal hmono
      _ = am m (q : ℝ).toNNReal := (hclock m _ hm).symm
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
  set D : Set ℝ := {d | ∃ q : ℚ, am m (q : ℝ).toNNReal < V m ∧ d = ((am m (q : ℝ).toNNReal).toNNReal : ℝ) ∧
    d < v} with hDdef
  have hDhull : ∀ d ∈ D, fwdHull W₁ d = fwdHull W₂ d := by
    rintro d ⟨q, hq, rfl, hdv⟩
    have hd0 : (0 : ℝ) ≤ ((am m (q : ℝ).toNNReal).toNNReal : ℝ) := NNReal.coe_nonneg _
    have hne : am m (q : ℝ).toNNReal ≠ ⊤ := ne_top_of_lt hq
    have hcl' := hclock m _ hq
    have hBq : Nc.BeforeL L (((q : ℝ).toNNReal : ℝ≥0) : ℝ) := Nc.beforeL_of_lt (halive' m _ hq)
    have hc0 := hdr.capClock_nonneg (Nc.uOf_nonneg hBq)
    have hdc : ((am m (q : ℝ).toNNReal).toNNReal : ℝ) = capClock ρ (Nc.uOf L (((q : ℝ).toNNReal : ℝ≥0) : ℝ)) := by
      rw [hcl']
      show ((ENNReal.ofReal _).toNNReal : ℝ) = _
      rw [ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal hc0]
    rw [hhull m q hq, Cf.fwdHull_congr hd0 hdv hW₂eq]
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
    obtain ⟨q, hqO, -⟩ := exists_rat_mem_gt hOo ht₁O
    have hq1 := hqO.1
    have hq2 := hqO.2
    have hqV : am m (q : ℝ).toNNReal < V m := by
      refine lt_trans hq2 (lt_of_le_of_lt ?_ hvV)
      rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hδ2
    have hne : am m (q : ℝ).toNNReal ≠ ⊤ := ne_top_of_lt hqV
    have hlo : t₀ < ((am m (q : ℝ).toNNReal).toNNReal : ℝ) := by
      have := (ENNReal.ofReal_lt_iff_lt_toReal (by linarith [ht₀.1]) hne).1 hq1
      rwa [ENNReal.toReal] at this
    have hhi : ((am m (q : ℝ).toNNReal).toNNReal : ℝ) < t₀ + 2 * δ := by
      have h' := (ENNReal.toReal_lt_toReal hne ENNReal.ofReal_ne_top).2 hq2
      rwa [ENNReal.toReal_ofReal (by linarith [ht₀.1]), ENNReal.toReal] at h'
    exact ⟨_, ⟨q, hqV, rfl, by linarith⟩, hlo, by linarith⟩
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

end InteractingSLE.Theorem14.SB.Cz
