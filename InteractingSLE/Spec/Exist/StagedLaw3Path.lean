/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw3Lim

/-!
# Along one path: the record at the stop and the marks

Packet PROVE-STAGEDLAW3. Pathwise facts linking the record `R = recOf t e` of a regular driver `e` with the
integrated evolution it drives:

* `histTime_recHist`, **`recChart_eq`**: for **every** record the record chart is the Loewner chart of the record
  driver `rdrv R` at the record time `rtime R`;
* `rdrv_recOf_eq`: on a good record the record driver is the driver on `[0, stop]` (at a lifetime stop, the left limit);
* `tendsto_stopSeq`: the stops `min t σₙ` of an announcing sequence increase to the stop `min t ζ`;
* `isMark_of_lt`: a solution of the integrated equation before `T` with a limit at `T` is a mark on `[0, T]`;
* **`tendsto_gap_markPos`**: along stops `sₙ → T` (`sₙ ≤ T`, `sₙ < ζ`), the centred position `v − w` of a right mark
  converges to `markPos D T x` for the record driver `D`, both when `T < ζ` and at the lifetime `T = ζ` (then with the
  terminal limit of Aux. lemma 3).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open QuantumZipper Staged

/-! ### The record chart -/

theorem histTime_recHist (r : RecData) : (LocalExt.histTime (recHist r) : ℝ) = rtime r := by
  obtain ⟨f, T, b⟩ := r
  unfold LocalExt.histTime rtime recHist
  induction T using ENNReal.recTopCoe with
  | top => rfl
  | coe x => rfl

/-- **The record chart is the Loewner chart of the record driver at the record time** (every record). -/
theorem recChart_eq (r : RecData) : recChart r = Chart.id.loewner (rdrv r) (rtime r) := by
  unfold recChart LocalExt.histChart
  rw [histTime_recHist]
  rfl

theorem isConformal_loewner_rdrv (r : RecData) : (Chart.id.loewner (rdrv r) (rtime r)).IsConformal :=
  Chart.isConformal_id.loewner (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r)

/-! ### The record driver on a good record -/

/-- On a good record of a finite stop, the record driver is the driver on `[0, stop]`. -/
theorem rdrv_recOf_eq {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (hg : LocalExt.IsDrvGood (recHist (recOf t e))) (hfin : min t e.2 ≠ ⊤) {s : ℝ}
    (hsT : s ≤ rtime (recOf t e)) : rdrv (recOf t e) s = e.1 s.toNNReal := by
  change LocalExt.histDrv (recHist (recOf t e)) s.toNNReal = _
  rw [histDrv_recHist he hg]
  change e.1 (min ((s.toNNReal : ℝ≥0) : ℝ≥0∞) (min t e.2)).toNNReal = _
  have hle : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ min t e.2 := by
    rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_le_coe]
    exact Real.toNNReal_le_iff_le_coe.2 hsT
  rw [min_eq_left hle, ENNReal.toNNReal_coe]

theorem rtime_recOf_coe {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} :
    rtime (recOf t e) = (((min t e.2).toNNReal : ℝ≥0) : ℝ) := rfl

/-! ### Stops of an announcing sequence -/

/-- **The stops `min t σₙ` increase to the stop `min t ζ`.** -/
theorem tendsto_stopSeq {σ : ℕ → ℝ≥0} {ζ t : ℝ≥0∞} (hmono : Monotone σ) (hlt : ∀ n, (σ n : ℝ≥0∞) < ζ)
    (hann : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → ∃ n, s ≤ σ n) (hfin : min t ζ ≠ ⊤) :
    (∀ n, (min t (σ n : ℝ≥0∞)).toNNReal ≤ (min t ζ).toNNReal) ∧
      Tendsto (fun n => (min t (σ n : ℝ≥0∞)).toNNReal) atTop (𝓝 (min t ζ).toNNReal) := by
  refine ⟨fun n => ENNReal.toNNReal_mono hfin (min_le_min le_rfl (hlt n).le), ?_⟩
  have hmono' : Monotone fun n => (σ n : ℝ≥0∞) := fun m n hmn => ENNReal.coe_le_coe.2 (hmono hmn)
  have hsup : (⨆ n, (σ n : ℝ≥0∞)) = ζ := by
    refine le_antisymm (iSup_le fun n => (hlt n).le) (ENNReal.le_of_forall_nnreal_lt fun r hr => ?_)
    obtain ⟨n, hn⟩ := hann r hr
    exact (ENNReal.coe_le_coe.2 hn).trans (le_iSup (fun n => (σ n : ℝ≥0∞)) n)
  have h1 := tendsto_atTop_iSup hmono'
  rw [hsup] at h1
  have h2 : Tendsto (fun n => min t (σ n : ℝ≥0∞)) atTop (𝓝 (min t ζ)) :=
    ((continuous_const.min continuous_id).tendsto ζ).comp h1
  exact (ENNReal.tendsto_toNNReal hfin).comp h2

/-! ### Marks with a limit at the end -/

section MarkLim

variable {w d : ℝ → ℝ} {T x : ℝ}

/-- **A solution of the integrated equation before `T` with a limit at `T` is a mark on `[0, T]`.** -/
theorem isMark_of_lt (hT : 0 < T) (hw : ContinuousOn w (Icc 0 T))
    (hd : ∀ r ∈ Ico 0 T, 0 ≤ d r ∧ d r = x - w r + (∫ s in (0 : ℝ)..r, 2 / d s) ∧
      IntervalIntegrable (fun s => 2 / d s) volume 0 r)
    (hnull : volume {r | r ∈ Ico 0 T ∧ d r = 0} = 0) (hlim : Tendsto d (𝓝[<] T) (𝓝 (d T))) :
    IsMark w T x d := by
  have hev : ∀ᶠ r in 𝓝[<] T, r ∈ Ico 0 T := by
    filter_upwards [Ioo_mem_nhdsLT hT] with r hr using ⟨hr.1.le, hr.2⟩
  -- the primitive converges at `T`
  have hprim : Tendsto (fun r => ∫ s in (0 : ℝ)..r, 2 / d s) (𝓝[<] T) (𝓝 (d T - x + w T)) := by
    have hIcc : Icc 0 T ∈ 𝓝[<] T := mem_of_superset (Ioo_mem_nhdsLT hT) Ioo_subset_Icc_self
    have hwT : Tendsto w (𝓝[<] T) (𝓝 (w T)) :=
      ((hw T ⟨hT.le, le_rfl⟩).mono_of_mem_nhdsWithin hIcc).tendsto
    refine ((hlim.sub_const x).add hwT).congr' ?_
    filter_upwards [hev] with r hr
    rw [(hd r hr).2.1]
    ring
  -- integrability on `[0, T]` (nonnegative integrand, bounded primitive)
  have hpos : ∀ r ∈ Ico 0 T, 0 ≤ 2 / d r := fun r hr => div_nonneg (by norm_num) (hd r hr).1
  set s : ℕ → ℝ := fun n => T - T / (n + 2) with hsdef
  have hs : ∀ n, s n ∈ Ico 0 T := fun n => by
    have h2 : (0 : ℝ) < n + 2 := by positivity
    refine ⟨?_, ?_⟩
    · rw [hsdef]
      have : T / (n + 2) ≤ T := div_le_self hT.le (by linarith)
      linarith
    · rw [hsdef]
      have : 0 < T / (n + 2) := div_pos hT h2
      linarith
  have hsT : Tendsto s atTop (𝓝 T) := by
    have h : Tendsto (fun n : ℕ => T / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have := tendsto_const_div_atTop_nhds_zero_nat T
      refine (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
    simpa using (tendsto_const_nhds (x := T)).sub h
  have hsT' : Tendsto s atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.2 ⟨hsT, Eventually.of_forall fun n => (hs n).2⟩
  obtain ⟨I, hI⟩ : ∃ I, ∀ n, (∫ r in (0 : ℝ)..s n, 2 / d r) ≤ I := by
    have hc := (hprim.comp hsT').bddAbove_range
    obtain ⟨I, hI⟩ := hc
    exact ⟨I, fun n => hI ⟨n, rfl⟩⟩
  have hIoc : IntegrableOn (fun r => 2 / d r) (Ioc 0 T) := by
    refine integrableOn_Ioc_of_intervalIntegral_norm_bounded (I := I) (l := atTop) (a := fun _ => (0 : ℝ))
      (fun n => ?_) tendsto_const_nhds hsT (Eventually.of_forall fun n => ?_)
    · exact ((hd (s n) (hs n)).2.2.def'.mono_set (by rw [uIoc_of_le (hs n).1]))
    · have hint := (hd (s n) (hs n)).2.2
      rw [← intervalIntegral.integral_of_le (hs n).1]
      refine le_of_eq_of_le ?_ (hI n)
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le (hs n).1] at hr
      have hrT : r ∈ Ico 0 T := ⟨hr.1, hr.2.trans_lt (hs n).2⟩
      simp only [Real.norm_eq_abs]
      exact abs_of_nonneg (hpos r hrT)
  have hII : IntervalIntegrable (fun r => 2 / d r) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).2 hIoc
  -- the equation at `T`
  have hcont : Tendsto (fun r => ∫ s in (0 : ℝ)..r, 2 / d s) (𝓝[<] T) (𝓝 (∫ s in (0 : ℝ)..T, 2 / d s)) := by
    have hp : ContinuousOn (fun r => ∫ s in (0 : ℝ)..r, 2 / d s) (uIcc 0 T) := by
      refine intervalIntegral.continuousOn_primitive_interval ?_
      rw [uIcc_of_le hT.le]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).1 hII
    rw [uIcc_of_le hT.le] at hp
    have hIcc : Icc 0 T ∈ 𝓝[<] T := mem_of_superset (Ioo_mem_nhdsLT hT) Ioo_subset_Icc_self
    exact ((hp T ⟨hT.le, le_rfl⟩).mono_of_mem_nhdsWithin hIcc).tendsto
  have hTeq : d T = x - w T + ∫ s in (0 : ℝ)..T, 2 / d s := by
    have := tendsto_nhds_unique hprim hcont
    linarith
  refine ⟨fun r hr => ?_, fun r hr => ?_, hII, ?_⟩
  · rcases hr.2.lt_or_eq with hlt | heq
    · exact (hd r ⟨hr.1, hlt⟩).1
    · rw [heq]
      exact ge_of_tendsto hlim (by filter_upwards [hev] with r hr using (hd r hr).1)
  · rcases hr.2.lt_or_eq with hlt | heq
    · exact (hd r ⟨hr.1, hlt⟩).2.1
    · rw [heq]; exact hTeq
  · refine measure_mono_null (t := {r | r ∈ Ico 0 T ∧ d r = 0} ∪ {T}) (fun r hr => ?_)
      (measure_union_null hnull (measure_singleton T))
    rcases hr.1.2.lt_or_eq with hlt | heq
    · exact Or.inl ⟨⟨hr.1.1, hlt⟩, hr.2⟩
    · exact Or.inr heq

end MarkLim

/-! ### The marks of an integrated path at the stop -/

theorem toNNReal_lt_of_lt {T : ℝ≥0} (hT : 0 < T) {r : ℝ} (hr : r < T) : r.toNNReal < T := by
  by_cases h0 : 0 ≤ r
  · exact (Real.toNNReal_lt_iff_lt_coe h0).2 hr
  · rw [Real.toNNReal_of_nonpos (le_of_not_ge h0)]
    exact hT

theorem tendsto_toNNReal_nhdsLT {T : ℝ≥0} (hT : 0 < T) :
    Tendsto Real.toNNReal (𝓝[<] (T : ℝ)) (𝓝[<] T) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h := (continuous_real_toNNReal.tendsto (T : ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio (T : ℝ)))
    rwa [Real.toNNReal_coe] at h
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact toNNReal_lt_of_lt hT hr

section Gap

variable {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {x : ℝ} {D : ℝ → ℝ}

/-- **The centred position of a right mark converges to the position read from the driver at the stop.** -/
theorem tendsto_gap_markPos (hD : Continuous D) (hD0 : D 0 = 0) {T : ℝ≥0} (hTζ : (T : ℝ≥0∞) ≤ ζ)
    (hDw : ∀ s : ℝ≥0, s ≤ T → (s : ℝ≥0∞) < ζ → D s = w s)
    (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hvc : ContinuousOn v {t | (t : ℝ≥0∞) < ζ})
    (hge : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t ≤ v t)
    (heq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    (hint : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun s : ℝ => (w s.toNNReal - v s.toNNReal)⁻¹) volume 0 t)
    (hnull : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = v s.toNNReal} = 0)
    (hT : (T : ℝ≥0∞) = ζ → 0 < T ∧ ∃ L, Tendsto (fun s => v s - w s) (𝓝[<] T) (𝓝 L))
    {s : ℕ → ℝ≥0} (hsζ : ∀ n, (s n : ℝ≥0∞) < ζ) (hsT : Tendsto s atTop (𝓝 T)) :
    Tendsto (fun n => v (s n) - w (s n)) atTop (𝓝 (markPos D T x)) := by
  have hint2 : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun r : ℝ => 2 / (v r.toNNReal - w r.toNNReal)) volume 0 t := by
    intro t ht
    have h := (hint t ht).const_mul (-2)
    refine h.congr fun r _ => ?_
    change -2 * (w r.toNNReal - v r.toNNReal)⁻¹ = 2 / (v r.toNNReal - w r.toNNReal)
    rw [show w r.toNNReal - v r.toNNReal = -(v r.toNNReal - w r.toNNReal) by ring, inv_neg]
    ring
  -- the equation in the real time variable
  have heqr : ∀ r : ℝ, 0 ≤ r → r ≤ T → (r.toNNReal : ℝ≥0∞) < ζ →
      v r.toNNReal - w r.toNNReal = x - D r + ∫ s in (0 : ℝ)..r, 2 / (v s.toNNReal - w s.toNNReal) := by
    intro r hr hrT hrζ
    have h := heq r.toNNReal hrζ
    rw [Real.coe_toNNReal r hr] at h
    have hD' := hDw r.toNNReal (Real.toNNReal_le_iff_le_coe.2 hrT) hrζ
    rw [Real.coe_toNNReal r hr] at hD'
    rw [h, hD']
    ring
  have hle : ∀ r : ℝ, r ≤ T → (r.toNNReal : ℝ≥0∞) ≤ T := fun r hr => by
    exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hr
  rcases hTζ.lt_or_eq with hlt | heqT
  · -- a stop before the lifetime
    set d : ℝ → ℝ := fun r => v r.toNNReal - w r.toNNReal with hddef
    have hmark : IsMark D T x d := by
      refine ⟨fun r hr => sub_nonneg.2 (hge _ ((hle r hr.2).trans_lt hlt)), fun r hr =>
        heqr r hr.1 hr.2 ((hle r hr.2).trans_lt hlt), hint2 T hlt, ?_⟩
      refine measure_mono_null (fun r hr => ?_) hnull
      exact ⟨hr.1.1, (hle r hr.1.2).trans_lt hlt, (sub_eq_zero.1 hr.2).symm⟩
    rw [markPos_eq hD hD0 T.coe_nonneg hmark]
    have hc : ContinuousAt (fun t => v t - w t) T :=
      (hvc.sub hwc).continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hlt)
    have h := hc.tendsto.comp hsT
    have e : d T = v T - w T := by simp only [hddef, Real.toNNReal_coe]
    rw [e]
    exact h
  · -- a stop at the lifetime
    obtain ⟨hT0, L, hL⟩ := hT heqT
    set d : ℝ → ℝ := fun r => if (r.toNNReal : ℝ≥0∞) < ζ then v r.toNNReal - w r.toNNReal else L with hddef
    have hltT : ∀ r : ℝ, r < T → (r.toNNReal : ℝ≥0∞) < ζ := fun r hr => by
      rw [← heqT]
      exact_mod_cast toNNReal_lt_of_lt hT0 hr
    have hdlt : ∀ r : ℝ, r < T → d r = v r.toNNReal - w r.toNNReal := fun r hr => by
      simp only [hddef, hltT r hr, ↓reduceIte]
    have hdT : d T = L := by
      have : ¬ (((T : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := by rw [Real.toNNReal_coe, heqT]; exact lt_irrefl _
      simp only [hddef, this, ↓reduceIte]
    have hmark : IsMark D T x d := by
      refine isMark_of_lt (by exact_mod_cast hT0) hD.continuousOn (fun r hr => ?_) ?_ ?_
      · have hcongr : (∫ s in (0 : ℝ)..r, 2 / d s) = ∫ s in (0 : ℝ)..r, 2 / (v s.toNNReal - w s.toNNReal) := by
          refine intervalIntegral.integral_congr fun s hs => ?_
          rw [uIcc_of_le hr.1] at hs
          simp only [hdlt s (hs.2.trans_lt hr.2)]
        have hint' := hint2 r.toNNReal (hltT r hr.2)
        rw [Real.coe_toNNReal r hr.1] at hint'
        refine ⟨by rw [hdlt r hr.2]; exact sub_nonneg.2 (hge _ (hltT r hr.2)), ?_, ?_⟩
        · rw [hdlt r hr.2, hcongr]
          exact heqr r hr.1 hr.2.le (hltT r hr.2)
        · refine hint'.congr fun s hs => ?_
          rw [uIoc_of_le hr.1] at hs
          simp only [hdlt s (hs.2.trans_lt hr.2)]
      · refine measure_mono_null (fun r hr => ?_) hnull
        have hr' := hr.2
        rw [hdlt r hr.1.2] at hr'
        exact ⟨hr.1.1, hltT r hr.1.2, (sub_eq_zero.1 hr').symm⟩
      · rw [hdT]
        refine (hL.comp (tendsto_toNNReal_nhdsLT hT0)).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact (hdlt r hr).symm
    rw [markPos_eq hD hD0 T.coe_nonneg hmark, hdT]
    have hsT' : Tendsto s atTop (𝓝[<] T) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hsT, Eventually.of_forall fun n => ?_⟩
      have := hsζ n
      rw [← heqT] at this
      exact_mod_cast this
    exact hL.comp hsT'

end Gap

end StagedLaw

end Exist

end InteractingSLE
