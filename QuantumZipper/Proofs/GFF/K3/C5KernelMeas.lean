import QuantumZipper.Proofs.GFF.K3.C5Kernel
import QuantumZipper.Proofs.GFF.K3.C5Interface
import QuantumZipper.Proofs.GFF.K3.KernelForm4

/-!
# GFF-K3, node C5 (via C5′): measurability of `V_T`

`VTe W T` (the monotone limit of AD-4, `C5Kernel.lean`) is Borel on `ℍ × ℍ`: by continuity of
`t ↦ G_ℍ(f_t a, f_t b)` from the right, the infimum over admissible times equals the infimum
over admissible times in the countable set `ℚ ∪ {T}` (`VTe_eq_iInf_countable`), and for each
fixed time `q` the kernel `(a,b) ↦ G_ℍ(f_q a, f_q b)` is Borel on the open set
`(ℍ \ K_q)²` (C2's `measurable_confKer`).  Own elementary argument.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate
open Classical

namespace QuantumZipper.K3

variable {W : ℝ → ℝ} {T : ℝ} {a b : ℂ}

/-- `s ↦ G_ℍ(f_s a, f_s b)` is continuous on `[0,t']` before both swallowing times. -/
theorem continuousOn_greenH_fwdMap (hW : Continuous W) (ha : a ∈ H) (hb : b ∈ H) {t' : ℝ}
    (ht' : 0 ≤ t') (hsa : ENNReal.ofReal t' < swallowTime W a)
    (hsb : ENNReal.ofReal t' < swallowTime W b) :
    ContinuousOn (fun s => greenH (fwdMap W s a) (fwdMap W s b)) (Icc 0 t') := by
  have haK : a ∈ H \ fwdHull W t' := ⟨ha, fun h => (not_le.2 hsa) h.2⟩
  have hbK : b ∈ H \ fwdHull W t' := ⟨hb, fun h => (not_le.2 hsb) h.2⟩
  have ca := FwdHolo.continuousOn_fwdMap_time hW ht' haK
  have cb := FwdHolo.continuousOn_fwdMap_time hW ht' hbK
  have pa := (im_fwdMap_antitoneOn hW ha (exists_sol_of_lt_swallowTime ha ht' hsa)).2
  have pb := (im_fwdMap_antitoneOn hW hb (exists_sol_of_lt_swallowTime hb ht' hsb)).2
  have h1 : ContinuousOn (fun s => Real.log ‖fwdMap W s a - conj (fwdMap W s b)‖) (Icc 0 t') := by
    refine ((ca.sub (Complex.continuous_conj.comp_continuousOn cb)).norm).log fun s hs => ?_
    refine norm_ne_zero_iff.2 fun h => ?_
    have := congrArg Complex.im h
    simp only [Pi.sub_apply, Function.comp_apply, Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith [pa s hs, pb s hs]
  have h2 : ContinuousOn (fun s => Real.log ‖fwdMap W s a - fwdMap W s b‖) (Icc 0 t') := by
    by_cases hab : a = b
    · subst hab; simp only [sub_self, norm_zero, Real.log_zero]; exact continuousOn_const
    refine ((ca.sub cb).norm).log fun s hs => ?_
    refine norm_ne_zero_iff.2 (sub_ne_zero.2 fun h => hab ?_)
    have hs0 : 0 ≤ s := hs.1
    have hsa' : a ∈ H \ fwdHull W s := ⟨ha, fun hK => haK.2 (fwdHull_mono.1 hs.2 hK)⟩
    have hsb' : b ∈ H \ fwdHull W s := ⟨hb, fun hK => hbK.2 (fwdHull_mono.1 hs.2 hK)⟩
    exact FwdHolo.injOn_fwdMap hW hs0 hsa' hsb' h
  exact h1.sub h2

/-- The countable time set `ℚ ∪ {T}`. -/
def vtQ (T : ℝ) : Set ℝ := insert T (range ((↑) : ℚ → ℝ))

theorem countable_vtQ (T : ℝ) : (vtQ T).Countable :=
  (countable_range _).insert T

/-- `V_T` as an infimum over admissible times in `ℚ ∪ {T}`. -/
theorem VTe_eq_iInf_countable (hW : Continuous W) (ha : a ∈ H) (hb : b ∈ H) :
    VTe W T a b = ⨅ q ∈ vtQ T ∩ vtIdx W T a b, vtKer W q a b := by
  refine le_antisymm (le_iInf₂ fun q hq => iInf₂_le q hq.2) (le_iInf₂ fun t ht => ?_)
  rcases eq_or_lt_of_le ht.2.1 with htT | htT
  · exact iInf₂_le t ⟨by rw [htT]; exact mem_insert T _, ht⟩
  -- a later admissible time `t'`
  obtain ⟨r, hr0, htr, hrs⟩ := ENNReal.lt_iff_exists_real_btwn.1
    (lt_min ht.2.2.1 ht.2.2.2)
  have htr' : t < r := (ENNReal.ofReal_lt_ofReal_iff'.1 htr).1
  set t' := min T r with ht'def
  have htt' : t < t' := lt_min htT htr'
  have hs' : ∀ s, s ≤ t' → ENNReal.ofReal s < swallowTime W a ∧
      ENNReal.ofReal s < swallowTime W b := fun s hs => by
    have := (ENNReal.ofReal_le_ofReal (hs.trans (min_le_right T r))).trans_lt hrs
    exact ⟨this.trans_le (min_le_left _ _), this.trans_le (min_le_right _ _)⟩
  have ht'0 : 0 ≤ t' := ht.1.trans htt'.le
  have hcont := (continuousOn_greenH_fwdMap hW ha hb ht'0 (hs' t' le_rfl).1
    (hs' t' le_rfl).2) t ⟨ht.1, htt'.le⟩
  -- rationals decreasing to `t`
  have hq : ∀ n : ℕ, ∃ q : ℚ, t < q ∧ (q : ℝ) < min t' (t + 1 / ((n : ℝ) + 1)) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact exists_rat_btwn (lt_min htt' (by linarith))
  choose q hq1 hq2 using hq
  have hqlim : Tendsto (fun n => (q n : ℝ)) atTop (𝓝[Icc 0 t'] t) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
      ⟨ht.1.trans (hq1 n).le, (hq2 n).le.trans (min_le_left _ _)⟩⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by have := (tendsto_const_nhds (x := t)).add tendsto_one_div_add_atTop_nhds_zero_nat
          rwa [add_zero] at this)
      (fun n => (hq1 n).le) (fun n => (hq2 n).le.trans (min_le_right _ _))
  have hlim : Tendsto (fun n => vtKer W (q n) a b) atTop (𝓝 (vtKer W t a b)) :=
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hcont.tendsto.comp hqlim))
  refine ge_of_tendsto' hlim fun n => iInf₂_le (q n : ℝ) ⟨mem_insert_of_mem _ ⟨q n, rfl⟩,
    ?_, ?_, (hs' _ ((hq2 n).le.trans (min_le_left _ _))).1,
      (hs' _ ((hq2 n).le.trans (min_le_left _ _))).2⟩
  · exact ht.1.trans (hq1 n).le
  · exact ((hq2 n).le.trans (min_le_left _ _)).trans (min_le_left _ _)

/-- The fixed-time kernel on its admissible set, `⊤` elsewhere. -/
def vtKerQ (W : ℝ → ℝ) (T q : ℝ) (p : ℂ × ℂ) : ℝ≥0∞ :=
  if (0 ≤ q ∧ q ≤ T) ∧ p ∈ (H \ fwdHull W q) ×ˢ (H \ fwdHull W q) then
    confKer (fwdMap W q) (H \ fwdHull W q) p else ⊤

theorem measurable_vtKerQ (hW : Continuous W) (hW0 : W 0 = 0) (T q : ℝ) :
    Measurable (vtKerQ W T q) := by
  unfold vtKerQ
  by_cases hq : 0 ≤ q ∧ q ≤ T
  · simp only [hq, true_and]
    have hm : MeasurableSet ((H \ fwdHull W q) ×ˢ (H \ fwdHull W q)) :=
      ((FwdHolo.isOpen_compl_fwdHull hW hq.1).prod
        (FwdHolo.isOpen_compl_fwdHull hW hq.1)).measurableSet
    exact Measurable.ite hm (measurable_confKer (isConformalOnto_fwdMap hW hW0 hq.1))
      measurable_const
  · simp only [hq, false_and, ite_false]; exact measurable_const

/-- **`V_T` is Borel on `ℍ × ℍ`.** -/
theorem measurable_indicator_VTe (hW : Continuous W) (hW0 : W 0 = 0) (T : ℝ) :
    Measurable ((H ×ˢ H).indicator fun p : ℂ × ℂ => VTe W T p.1 p.2) := by
  have heq : (H ×ˢ H).indicator (fun p : ℂ × ℂ => VTe W T p.1 p.2) =
      (H ×ˢ H).indicator (fun p => ⨅ q ∈ vtQ T, vtKerQ W T q p) := by
    refine indicator_congr fun p hp => ?_
    rw [VTe_eq_iInf_countable hW hp.1 hp.2]
    refine le_antisymm (le_iInf₂ fun q hq => ?_) (le_iInf₂ fun q hq => ?_)
    · unfold vtKerQ
      split_ifs with h
      · have hmem : q ∈ vtQ T ∩ vtIdx W T p.1 p.2 := ⟨hq, h.1.1, h.1.2,
          not_le.1 fun hle => h.2.1.2 ⟨hp.1, hle⟩, not_le.1 fun hle => h.2.2.2 ⟨hp.2, hle⟩⟩
        refine (iInf₂_le q hmem).trans (le_of_eq ?_)
        unfold confKer vtKer
        rw [confMod_eqOn h.2.1, confMod_eqOn h.2.2]
      · exact le_top
    · have h1 : p.1 ∈ H \ fwdHull W q := ⟨hp.1, fun h => (not_le.2 hq.2.2.2.1) h.2⟩
      have h2 : p.2 ∈ H \ fwdHull W q := ⟨hp.2, fun h => (not_le.2 hq.2.2.2.2) h.2⟩
      refine iInf₂_le q hq.1 |>.trans (le_of_eq ?_)
      unfold vtKerQ confKer vtKer
      rw [if_pos (show (0 ≤ q ∧ q ≤ T) ∧ p ∈ (H \ fwdHull W q) ×ˢ (H \ fwdHull W q) from
        ⟨⟨hq.2.1, hq.2.2.1⟩, h1, h2⟩), confMod_eqOn h1, confMod_eqOn h2]
  rw [heq]
  exact (Measurable.biInf _ (countable_vtQ T) fun q _ => measurable_vtKerQ hW hW0 T q).indicator
    (isOpen_H.prod isOpen_H).measurableSet

end QuantumZipper.K3
