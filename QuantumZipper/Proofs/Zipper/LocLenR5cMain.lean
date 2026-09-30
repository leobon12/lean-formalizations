import QuantumZipper.Proofs.Zipper.LocLenR5cRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5c (D75): `LocHitScaleArcStmt` from almost-sure good behaviour (open arcs)

Open-arc copy (`handoff/FOLLOW-PAPER-13.md`, task R5c) of `LocHitScaleMain.lean`, with
`unzipLengths ↦ unzipLengthsArc`, `tHit ↦ lenTimeArc`, the readers `lenLoc/tauLoc/aLoc ↦
lenLocArc/tauLocArc/aLocArc` (`LocLenR5cRead.lean`), and the global boundary limits at rational
times replaced by goodness off `offSet W q` (`HitScaleGoodArc.lim`). The radii `E6.Rp` and
`E6.window_locRich` are reused.

Main result: `locHitScaleArcStmt_of_good`. Own elementary argument, as for the original
(Sheffield arXiv:1012.4797 §5.4, pp. 70–72, asserts the locality without proof).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper.LocLen.R5c

open E6 D3Plus MeasUnzip CharFun

/-- **Good behaviour of a configuration** for the local reading of the open-arc hitting time
and the scale (copy of `E6.HitScaleGood`). -/
structure HitScaleGoodArc (γ ℓ : ℝ) (y : Cfg) : Prop where
  cont : Continuous y.2
  zero : y.2 0 = 0
  alive : ∀ z : ℝ, z ≠ 0 → ∀ s : ℝ, 0 ≤ s → ∃ u, IsForwardSol y.2 (z : ℂ) s u
  lim : ∀ q : ℚ, 0 < (q : ℝ) → IsLQGGoodOff γ (unzippedField γ y q) (offSet y.2 q)
  mono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → (unzipLengthsArc γ y s).1 ≤ (unzipLengthsArc γ y t).1
  reach : ∃ s : ℝ, 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengthsArc γ y s).1
  pos : 0 < lenTimeArc γ ℓ y
  area : ∃ μ, IsVagueLimitOn H (areaApprox γ (unzippedField γ y (lenTimeArc γ ℓ y))) μ
  scale : 0 < scaleParam γ (unzippedField γ y (lenTimeArc γ ℓ y))

/-- The good set of local data. -/
def goodSetHitArc (γ κ ℓ : ℝ) (R T M : ℕ) : Set FullData :=
  {d | (∀ r : ℚ, 0 ≤ (r : ℝ) → (r : ℝ) ≤ T → |d.2 (r : ℝ).toNNReal| ≤ M) ∧
    ENNReal.ofReal ℓ ≤ lenLocArc γ κ T (Rp R T M) T ⟨natCast_nonneg' T, le_rfl⟩ d ∧
    0 < tauLocArc γ κ ℓ T (Rp R T M) d ∧ 0 < aLocArc γ κ ℓ T (Rp R T M) M d ∧
    aLocArc γ κ ℓ T (Rp R T M) M d < M ∧
    tauLocArc γ κ ℓ T (Rp R T M) d + aLocArc γ κ ℓ T (Rp R T M) M d ^ 2 * R ≤ T}

theorem measurableSet_goodSetHitArc (γ κ ℓ : ℝ) (R T M : ℕ) : MeasurableSet (goodSetHitArc γ κ ℓ R T M) := by
  have hτ := measurable_tauLocArc γ κ ℓ T (Rp R T M)
  have ha := measurable_aLocArc γ κ ℓ T (Rp R T M) M
  have h1 : MeasurableSet {d : FullData |
      ∀ r : ℚ, 0 ≤ (r : ℝ) → (r : ℝ) ≤ T → |d.2 (r : ℝ).toNNReal| ≤ M} := by
    have e : {d : FullData | ∀ r : ℚ, 0 ≤ (r : ℝ) → (r : ℝ) ≤ T → |d.2 (r : ℝ).toNNReal| ≤ M} =
        ⋂ r : ℚ, {d : FullData | 0 ≤ (r : ℝ) → (r : ℝ) ≤ T → |d.2 (r : ℝ).toNNReal| ≤ M} := by
      ext d; simp only [Set.mem_ofPred_eq, mem_iInter]
    rw [e]
    refine MeasurableSet.iInter fun r => ?_
    by_cases hr : 0 ≤ (r : ℝ) ∧ (r : ℝ) ≤ T
    · simp only [hr.1, hr.2, true_implies]
      exact measurableSet_le (continuous_abs.measurable.comp
        ((measurable_pi_apply _).comp measurable_snd)) measurable_const
    · have e2 : {d : FullData | 0 ≤ (r : ℝ) → (r : ℝ) ≤ T → |d.2 (r : ℝ).toNNReal| ≤ M} =
          univ := by
        ext d
        simp only [Set.mem_ofPred_eq, mem_univ, iff_true]
        intro h0 hT
        exact absurd ⟨h0, hT⟩ hr
      rw [e2]
      exact MeasurableSet.univ
  exact h1.inter ((measurableSet_le measurable_const (measurable_lenLocArc _ _ _ _ _ _)).inter
    ((measurableSet_lt measurable_const hτ).inter ((measurableSet_lt measurable_const ha).inter
    ((measurableSet_lt ha measurable_const).inter
      (measurableSet_le (hτ.add ((ha.pow_const 2).mul_const _)) measurable_const)))))

theorem limArc_natCast {γ ℓ : ℝ} {y : Cfg} (hg : HitScaleGoodArc γ ℓ y) {T : ℕ} (hT : 0 < T) :
    IsLQGGoodOff γ (unzippedField γ y T) (offSet y.2 T) := by
  have := hg.lim (T : ℚ) (by exact_mod_cast hT)
  simpa using this

/-- **Membership of the local data in the good set gives the conclusions of
`LocHitScaleArcStmt`.** -/
theorem conclusionsArc_of_mem {γ κ ℓ : ℝ} (hκ : 0 < κ) {R T M : ℕ} (hT : 0 < T) {y : Cfg}
    (hg : HitScaleGoodArc γ ℓ y) (hmem : locRich (Rp R T M) y ∈ goodSetHitArc γ κ ℓ R T M) :
    (∀ r ∈ Icc (0 : ℝ) T, |y.2 r| ≤ M) ∧
      (∃ s ∈ Icc (0 : ℝ) T, ENNReal.ofReal ℓ ≤ (unzipLengthsArc γ y s).1) ∧
      0 < lenTimeArc γ ℓ y ∧ tauLocArc γ κ ℓ T (Rp R T M) (locRich (Rp R T M) y) = lenTimeArc γ ℓ y ∧
      0 < scaleParam γ (unzippedField γ y (lenTimeArc γ ℓ y)) ∧
      aLocArc γ κ ℓ T (Rp R T M) M (locRich (Rp R T M) y) =
        scaleParam γ (unzippedField γ y (lenTimeArc γ ℓ y)) ∧
      lenTimeArc γ ℓ y + scaleParam γ (unzippedField γ y (lenTimeArc γ ℓ y)) ^ 2 * R ≤ T ∧
      scaleParam γ (unzippedField γ y (lenTimeArc γ ℓ y)) * R + 6 * (M : ℝ) +
          6 * Real.sqrt T + 6 ≤ Rp R T M := by
  obtain ⟨x, W⟩ := y
  obtain ⟨hb, hl, hτ0, ha0, haM, hsum⟩ := hmem
  have hTR := le_Rp R T M
  have hR9 := bound9_le_Rp R T M
  have hRb := bound_le_Rp R T M
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hM : ∀ r ∈ Icc (0 : ℝ) T, |W r| ≤ M := B5.abs_le_of_forall_rat hg.cont hT'
    fun q h0 hq => by
      have := hb q h0 hq
      rwa [window_locRich hTR (x, W) h0 hq] at this
  have hlenT := lenLocArc_locRich (γ := γ) hκ hTR x hg.cont hg.zero hM hR9
    ⟨natCast_nonneg' T, le_rfl⟩ hT' (fun z hz => hg.alive z hz T (natCast_nonneg' T))
    (limArc_natCast hg hT)
  have hreach : ENNReal.ofReal ℓ ≤ (unzipLengthsArc γ (x, W) T).1 := hlenT ▸ hl
  have hτ := tauLocArc_locRich (γ := γ) (ℓ := ℓ) hκ hTR x hg.cont hg.zero hM hR9 hg.alive hg.lim
    (fun s t hs hst _ => hg.mono s t hs hst) hreach
  have htT : lenTimeArc γ ℓ (x, W) ≤ T := csInf_le ⟨0, fun _ h => h.1⟩ ⟨natCast_nonneg' T, hreach⟩
  have ht0 : 0 < lenTimeArc γ ℓ (x, W) := hτ ▸ hτ0
  have haL : aLocArc γ κ ℓ T (Rp R T M) M (locRich (Rp R T M) (x, W)) =
      aLocAt γ κ T (Rp R T M) M (lenTimeArc γ ℓ (x, W)) (locRich (Rp R T M) (x, W)) := by
    unfold aLocArc; rw [hτ]
  have ha := aLocAt_eq_scale (γ := γ) hκ hTR (le_refl (M : ℝ)) x hg.cont hg.zero hM hR9
    ⟨ht0.le, htT⟩ ht0 hg.area (Or.inr (haL ▸ haM))
  rw [haL, ha] at ha0 haM hsum
  rw [hτ] at hsum
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hsq := Real.sqrt_nonneg (T : ℝ)
  refine ⟨hM, ⟨T, ⟨natCast_nonneg' T, le_rfl⟩, hreach⟩, ht0, hτ, ha0, haL.trans ha, hsum, ?_⟩
  have : scaleParam γ (unzippedField γ (x, W) (lenTimeArc γ ℓ (x, W))) * R ≤ (M : ℝ) * R :=
    mul_le_mul_of_nonneg_right haM.le hR0
  linarith

/-- **A good configuration belongs to the good sets eventually** (all large `T`, then all large
`M`). -/
theorem eventually_mem_goodSetHitArc {γ κ ℓ : ℝ} (hκ : 0 < κ) (R : ℕ) {y : Cfg}
    (hg : HitScaleGoodArc γ ℓ y) :
    ∃ k : ℕ, ∀ n ≥ k, ∃ M0 : ℕ, ∀ m ≥ M0,
      locRich (Rp R (n + 1) m) y ∈ goodSetHitArc γ κ ℓ R (n + 1) m := by
  obtain ⟨x, W⟩ := y
  obtain ⟨s0, hs0, hl0⟩ := hg.reach
  set t := lenTimeArc γ ℓ (x, W) with htdef
  set a := scaleParam γ (unzippedField γ (x, W) t) with hadef
  refine ⟨⌈max s0 (t + a ^ 2 * R)⌉₊, fun n hn => ?_⟩
  have hTr : max s0 (t + a ^ 2 * R) ≤ ((n + 1 : ℕ) : ℝ) := by
    have h1 := Nat.le_ceil (max s0 (t + a ^ 2 * R))
    have h2 : (⌈max s0 (t + a ^ 2 * R)⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    linarith
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hg.cont.continuousOn (s := Icc (0 : ℝ) ((n + 1 : ℕ) : ℝ)))
  refine ⟨⌈max B a⌉₊ + 1, fun m hm => ?_⟩
  have hmB : max B a < m := by
    have h1 := Nat.le_ceil (max B a)
    have h2 : ((⌈max B a⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
    push_cast at h2
    linarith
  have hT : 0 < n + 1 := Nat.succ_pos n
  have hT' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hT
  have hTR := le_Rp R (n + 1) m
  have hR9 := bound9_le_Rp R (n + 1) m
  have hM : ∀ r ∈ Icc (0 : ℝ) ((n + 1 : ℕ) : ℝ), |W r| ≤ m := fun r hr => by
    have := hB r hr
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans hmB.le)
  have hlenT := lenLocArc_locRich (γ := γ) hκ hTR x hg.cont hg.zero hM hR9
    ⟨natCast_nonneg' (n + 1), le_rfl⟩ hT' (fun z hz => hg.alive z hz _ (natCast_nonneg' _))
    (limArc_natCast hg hT)
  have hreach : ENNReal.ofReal ℓ ≤ (unzipLengthsArc γ (x, W) ((n + 1 : ℕ) : ℝ)).1 :=
    hl0.trans (hg.mono s0 _ hs0 ((le_max_left _ _).trans hTr))
  have hτ := tauLocArc_locRich (γ := γ) (ℓ := ℓ) hκ hTR x hg.cont hg.zero hM hR9 hg.alive hg.lim
    (fun s t hs hst _ => hg.mono s t hs hst) hreach
  have htT : t ≤ ((n + 1 : ℕ) : ℝ) :=
    csInf_le ⟨0, fun _ h => h.1⟩ ⟨natCast_nonneg' _, hreach⟩
  have haL : aLocArc γ κ ℓ (n + 1) (Rp R (n + 1) m) m (locRich (Rp R (n + 1) m) (x, W)) =
      aLocAt γ κ (n + 1) (Rp R (n + 1) m) m t (locRich (Rp R (n + 1) m) (x, W)) := by
    unfold aLocArc; rw [hτ]
  have ha := aLocAt_eq_scale (γ := γ) hκ hTR (le_refl (m : ℝ)) x hg.cont hg.zero hM hR9
    ⟨hg.pos.le, htT⟩ hg.pos hg.area (Or.inl ⟨hg.scale, (le_max_right _ _).trans hmB.le⟩)
  refine ⟨fun r h0 hr => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [window_locRich hTR (x, W) h0 hr]; exact hM r ⟨h0, hr⟩
  · rw [hlenT]; exact hreach
  · rw [hτ]; exact hg.pos
  · rw [haL, ha]; exact hg.scale
  · rw [haL, ha]; exact (le_max_right _ _).trans_lt hmB
  · rw [hτ, haL, ha]; exact (le_max_right _ _).trans hTr

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- **`LocHitScaleArcStmt` from almost-sure good behaviour** (and a.e.-measurable local data). -/
theorem locHitScaleArcStmt_of_good {γ κ ℓ : ℝ} (hκ : 0 < κ) {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {c' : Ω' → Cfg}
    (hc : ∀ R' : ℕ, AEMeasurable (fun ω' => locRich R' (c' ω')) P')
    (hg : ∀ᵐ ω' ∂P', HitScaleGoodArc γ ℓ (c' ω')) : LocHitScaleArcStmt γ ℓ P' c' := by
  intro R ε hε
  set G : ℕ → ℕ → Set Ω' := fun n m =>
    {ω' | locRich (Rp R (n + 1) m) (c' ω') ∈ goodSetHitArc γ κ ℓ R (n + 1) m} with hGdef
  have hGn : ∀ n m, NullMeasurableSet (G n m) P' := fun n m =>
    (hc _).nullMeasurable (measurableSet_goodSetHitArc γ κ ℓ R (n + 1) m)
  set F : ℕ → Set Ω' := fun n => ⋃ M0 : ℕ, ⋂ m ≥ M0, G n m with hFdef
  set Hs : ℕ → Set Ω' := fun k => ⋂ n ≥ k, F n with hHsdef
  have hHmono : Monotone Hs := fun k k' hkk' ω hω =>
    mem_iInter₂.2 fun n hn => mem_iInter₂.1 hω n (hkk'.trans hn)
  have hae : ∀ᵐ ω' ∂P', ω' ∈ ⋃ k, Hs k := by
    filter_upwards [hg] with ω' hω'
    obtain ⟨k, hk⟩ := eventually_mem_goodSetHitArc (κ := κ) hκ R hω'
    refine mem_iUnion.2 ⟨k, mem_iInter₂.2 fun n hn => ?_⟩
    obtain ⟨M0, hM0⟩ := hk n hn
    exact mem_iUnion.2 ⟨M0, mem_iInter₂.2 fun m hm => hM0 m hm⟩
  have hfull : P' (⋃ k, Hs k) = 1 := by
    refine le_antisymm prob_le_one ?_
    have h1 : P' (⋃ k, Hs k)ᶜ = 0 := ae_iff.1 hae
    calc (1 : ℝ≥0∞) = P' univ := measure_univ.symm
      _ ≤ P' (⋃ k, Hs k) + P' (⋃ k, Hs k)ᶜ := by
        rw [← union_compl_self (⋃ k, Hs k)]; exact measure_union_le _ _
      _ = P' (⋃ k, Hs k) := by rw [h1, add_zero]
  have hε1 : 1 - ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε.ne'
  obtain ⟨k, hk⟩ := ((tendsto_measure_iUnion_atTop (μ := P') hHmono).eventually
    (lt_mem_nhds (hfull.symm ▸ hε1 : 1 - ε < P' (⋃ k, Hs k)))).exists
  have hFk : 1 - ε < P' (F k) :=
    hk.trans_le (measure_mono (iInter₂_subset (s := fun n (_ : n ≥ k) => F n) k le_rfl))
  set Gs : ℕ → Set Ω' := fun M0 => ⋂ m ≥ M0, G k m with hGsdef
  have hGmono : Monotone Gs := fun a b hab ω hω =>
    mem_iInter₂.2 fun m hm => mem_iInter₂.1 hω m (hab.trans hm)
  obtain ⟨M0, hM0⟩ := ((tendsto_measure_iUnion_atTop (μ := P') hGmono).eventually
    (lt_mem_nhds (show 1 - ε < P' (⋃ M0, Gs M0) from hFk))).exists
  have hGk : 1 - ε < P' (G k M0) :=
    hM0.trans_le (measure_mono (iInter₂_subset (s := fun m (_ : m ≥ M0) => G k m) M0 le_rfl))
  refine ⟨k + 1, Rp R (k + 1) M0, M0, goodSetHitArc γ κ ℓ R (k + 1) M0,
    tauLocArc γ κ ℓ (k + 1) (Rp R (k + 1) M0), aLocArc γ κ ℓ (k + 1) (Rp R (k + 1) M0) M0,
    le_Rp _ _ _, measurableSet_goodSetHitArc _ _ _ _ _ _, measurable_tauLocArc _ _ _ _ _,
    measurable_aLocArc _ _ _ _ _ _, ?_, ?_⟩
  · have e : {ω' | locRich (Rp R (k + 1) M0) (c' ω') ∉ goodSetHitArc γ κ ℓ R (k + 1) M0} =
        (G k M0)ᶜ := rfl
    rw [e, prob_compl_eq_one_sub₀ (hGn k M0)]
    refine tsub_le_iff_right.2 ?_
    calc (1 : ℝ≥0∞) ≤ 1 - ε + ε := le_tsub_add
      _ ≤ P' (G k M0) + ε := add_le_add hGk.le le_rfl
      _ = ε + P' (G k M0) := add_comm _ _
  · filter_upwards [hg] with ω' hω' hmem
    exact conclusionsArc_of_mem hκ (Nat.succ_pos k) hω' hmem

end QuantumZipper.LocLen.R5c
