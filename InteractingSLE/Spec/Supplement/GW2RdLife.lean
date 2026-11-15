/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdCap
import InteractingSLE.Spec.Supplement.GW2RdGauge
import InteractingSLE.Spec.Supplement.GW2RdExt
import InteractingSLE.Spec.Restart.StoppedExtendProofDet

/-!
# GW2's relative determination, part 6: the cap at the flow's lifetime (deterministic)

Packet PROVE-GW2-RELDET (`GW2RdVersionStatement`). Deterministic ingredients of the capped versions:

* **`tendsto_norm_trace_of_frozen`**: a generating trace on `[0, ∞)` of a continuous driver that is frozen after a
  positive time `S` is transient (after `S` it is the image of the vertical slit under the inverse Loewner map at
  `S`, `BW1Prop.isLoewnerTrace_ext_close`, and generating traces of one driver agree,
  `StoppedExtend.trace_eq_of_driver_eq`); hence the extended flow trace `extTr` is transient on `{0 < ζα < ∞}`;
* `capGauge s B` (the distance of the physical trace read back from (record, relative path) to a closed set `B`,
  capped at `1`) and `capLife a Tc ζ′` (the relative clock of the flow's lifetime `ζ′` when it precedes the contact
  `Tc`, else `∞`);
* **`capLife_facts`**: if the physical trace is outside `B` before `ζ′` and in `B` at a finite positive `ζ′`, the read
  back trace is outside `B` before `capLife` and in `B` at `capLife` (one sample, from the read-back of
  `GW2Rd.ae_physicalReadback_nr`);
* `exists_lt_clock_of_lt_capLife`, `lt_min_capLife`: every relative time below the cap is the relative clock of a time
  before `ζ′`, and the clock of every time before `min(ζ′, Tc)` is below the cap.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdMapInv)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version Supp8.GB6.ReadD Exist.StagedLaw

/-! ### Transience of a frozen trace -/

/-- **A generating trace of a driver frozen after a positive time is transient.** -/
theorem tendsto_norm_trace_of_frozen {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {S : ℝ≥0} (hS : 0 < S)
    (hfrz : ∀ t : ℝ≥0, S ≤ t → w t = w S) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η) :
    Tendsto (fun t => ‖η t‖) atTop atTop := by
  set U : ℝ → ℝ := fun r => w r.toNNReal with hUdef
  have hUc : Continuous U := hw.comp continuous_real_toNNReal
  have hU0 : U 0 = 0 := by simp only [hUdef, Real.toNNReal_zero, hw0]
  have hfd : frozenDrive w (S : ℝ) = U := funext fun r => by
    simp only [frozenDrive, hUdef]
    rcases le_total r S with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, Real.toNNReal_coe, hfrz r.toNNReal (Real.le_toNNReal_iff_coe_le (S.2.trans h) |>.2 h)]
  have hLT := hη.isLoewnerTraceLT (t₂ := (S : ℝ)) (by simp)
  rw [hfd] at hLT
  have hησ : ContinuousOn (fun r : ℝ => η r.toNNReal) (Icc 0 (S : ℝ)) :=
    hη.2.1.comp continuous_real_toNNReal.continuousOn fun x _ =>
      (le_top : ((x.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ⊤)
  have hext := BW1Prop.isLoewnerTrace_ext_close hLT hUc hU0 (NNReal.coe_pos.2 hS) hησ
  have hUe : YuanCorollary13.extDrive U S = U := funext fun r => by
    simp only [YuanCorollary13.extDrive, hUdef]
    rcases le_total r S with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, Real.toNNReal_coe, hfrz r.toNNReal (Real.le_toNNReal_iff_coe_le (S.2.trans h) |>.2 h)]
  rw [hUe] at hext
  set ξ : ℝ → ℂ := YuanCorollary13.extTrace U (fun r : ℝ => η r.toNNReal) S with hξ
  have hgen := BW1In.isGeneratingTrace_of_isLoewnerTrace (U := U) (fun x => by simp only [hUdef, Real.toNNReal_coe])
    hext
  have hwe : (fun s : ℝ≥0 => U s) = w := funext fun t => by simp only [hUdef, Real.toNNReal_coe]
  rw [hwe] at hgen
  have huniq := Restart.StoppedExtend.trace_eq_of_driver_eq hη hw.continuousOn hw0 hgen hw.continuousOn hw0
    le_rfl le_rfl (fun _ _ => rfl)
  -- after `S` the trace is the image of the vertical slit
  have hslit : ∀ t : ℝ≥0, S < t → η t = fwdMapInv U S (((2 * Real.sqrt ((t : ℝ) - S) : ℝ) : ℂ) * Complex.I) := by
    intro t ht
    rw [huniq t le_top]
    have ht' : ¬ ((t : ℝ) ≤ S) := not_le.2 (NNReal.coe_lt_coe.2 ht)
    simp only [hξ, YuanCorollary13.extTrace, ht', ↓reduceIte]
    have hpos : 0 < 2 * Real.sqrt ((t : ℝ) - S) := by
      have : (0 : ℝ) < (t : ℝ) - S := sub_pos.2 (NNReal.coe_lt_coe.2 ht)
      positivity
    have hz : (((2 * Real.sqrt ((t : ℝ) - S) : ℝ) : ℂ) * Complex.I) ∈ H := by
      show 0 < ((((2 * Real.sqrt ((t : ℝ) - S) : ℝ) : ℂ) * Complex.I)).im
      simpa using hpos
    have hcont : ContinuousOn (fwdMapInv U S) H :=
      (QuantumZipper.RS.differentiableOn_fwdMapInv hUc hU0 S.2).continuousOn
    exact extendFrom_eq (subset_closure hz)
      ((hcont.continuousAt (QuantumZipper.isOpen_H.mem_nhds hz)).tendsto.mono_left nhdsWithin_le_nhds)
  -- the slit tends to `∞` in `ℍ`
  have hf : Tendsto (fun t : ℝ≥0 => (((2 * Real.sqrt ((t : ℝ) - S) : ℝ) : ℂ) * Complex.I)) atTop
      (Bornology.cobounded ℂ ⊓ 𝓟 H) := by
    refine tendsto_inf.2 ⟨?_, tendsto_principal.2 ?_⟩
    · rw [← tendsto_norm_atTop_iff_cobounded]
      have h0 : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.2 tendsto_id
      have h1 : Tendsto (fun t : ℝ≥0 => (t : ℝ) - S) atTop atTop := by
        simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(S : ℝ)) h0
      have h2 := (Real.tendsto_sqrt_atTop.comp h1).const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop S] with t ht
      have : (0 : ℝ) ≤ Real.sqrt ((t : ℝ) - S) := Real.sqrt_nonneg _
      simp [Function.comp, Complex.norm_I, abs_of_nonneg this]
    · filter_upwards [eventually_gt_atTop S] with t ht
      have : (0 : ℝ) < (t : ℝ) - S := sub_pos.2 (NNReal.coe_lt_coe.2 ht)
      show 0 < ((((2 * Real.sqrt ((t : ℝ) - S) : ℝ) : ℂ) * Complex.I)).im
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
        mul_zero, add_zero]
      positivity
  have hg := (tendsto_norm_cobounded_atTop.comp
    ((InteractingSLE.tendsto_fwdMapInv_cobounded hUc hU0 S.2).comp hf))
  refine hg.congr' ?_
  filter_upwards [eventually_gt_atTop S] with t ht
  rw [hslit t ht]
  rfl

/-! ### The cap gauge and the cap life -/

section CapGauge

open Classical

/-- **The cap gauge**: the distance of the read-back physical trace to `B`, capped at `1` (`1` if `B = ∅`). -/
def capGauge (s : ℝ≥0) (B : Set ℂ) : GaugeReadout := fun t p =>
  if B.Nonempty then min 1 (infDist (physicalTrace s t p) B) else 1

theorem measurable_capGauge (s : ℝ≥0) (B : Set ℂ) (t : ℝ≥0) : Measurable (capGauge s B t) := by
  unfold capGauge
  split_ifs
  · exact measurable_const.min ((continuous_infDist_pt B).measurable.comp (measurable_physicalTrace s t))
  · exact measurable_const

theorem isCausal_capGauge (s : ℝ≥0) (B : Set ℂ) : IsCausal (capGauge s B) := by
  intro t r w w' hw
  unfold capGauge
  rw [physicalTrace_congr s t r hw]

theorem capGauge_nonneg (s : ℝ≥0) (B : Set ℂ) (t : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) : 0 ≤ capGauge s B t p := by
  unfold capGauge
  split_ifs
  · exact le_min zero_le_one infDist_nonneg
  · exact zero_le_one

end CapGauge

/-- **The cap life**: the relative clock of `ζ′` when `ζ′` precedes the contact `Tc`, else `∞`. -/
def capLife (a : ℝ≥0 → ℝ) (Tc ζ' : ℝ≥0∞) : ℝ≥0∞ := if ζ' < Tc then ENNReal.ofReal (a ζ'.toNNReal) else ⊤

section Sample

variable {a : ℝ≥0 → ℝ} {Tc ζ' L : ℝ≥0∞}

theorem nonneg_of_strictMono (ha0 : a 0 = 0) (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < Tc) : 0 ≤ a t := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
  · rw [← h, ha0]
  · rw [← ha0]; exact (ham (lt_of_le_of_lt (by simp) ht) ht h).le

/-- **The read-back trace and the cap** (one sample). -/
theorem capLife_facts {X αb α : ℝ≥0 → ℂ} {B : Set ℂ} (ha0 : a 0 = 0)
    (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc})
    (hcap : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ a t = u ∧ X u = αb t)
    (hpos : 0 < ζ') (hagree : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ ζ' → αb u = α u)
    (hnot : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' → α t ∉ B) (hin : ∀ T : ℝ≥0, (T : ℝ≥0∞) = ζ' → 0 < T → α T ∈ B) :
    0 < capLife a Tc ζ' ∧ (∀ u : ℝ≥0, (u : ℝ≥0∞) < L → (u : ℝ≥0∞) < capLife a Tc ζ' → X u ∉ B) ∧
      ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → (u : ℝ≥0∞) = capLife a Tc ζ' → X u ∈ B := by
  refine ⟨?_, fun u hu hlt => ?_, fun u hu heq => ?_⟩
  · unfold capLife
    split_ifs with h
    · have hfin : ζ' ≠ ⊤ := ne_top_of_lt h
      have hζ : ((ζ'.toNNReal : ℝ≥0) : ℝ≥0∞) = ζ' := ENNReal.coe_toNNReal hfin
      have hz : (0 : ℝ≥0) < ζ'.toNNReal := by rw [← ENNReal.coe_lt_coe, hζ]; simpa using hpos
      have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < Tc := lt_of_le_of_lt (by simp) h
      have := ham h0 (show ((ζ'.toNNReal : ℝ≥0) : ℝ≥0∞) < Tc by rw [hζ]; exact h) hz
      rw [ha0] at this
      exact ENNReal.ofReal_pos.2 this
    · exact ENNReal.zero_lt_top
  · obtain ⟨t, htc, hat, hX⟩ := hcap u hu
    have htζ : (t : ℝ≥0∞) < ζ' := by
      unfold capLife at hlt
      split_ifs at hlt with h
      · have hfin : ζ' ≠ ⊤ := ne_top_of_lt h
        have hζ : ((ζ'.toNNReal : ℝ≥0) : ℝ≥0∞) = ζ' := ENNReal.coe_toNNReal hfin
        have hlt' : (u : ℝ) < a ζ'.toNNReal := by
          rw [← ENNReal.ofReal_coe_nnreal] at hlt
          exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg u.2).1 hlt
        rw [← hat] at hlt'
        have := (ham.lt_iff_lt htc (show ((ζ'.toNNReal : ℝ≥0) : ℝ≥0∞) < Tc by rw [hζ]; exact h)).1 hlt'
        rw [← hζ]; exact_mod_cast this
      · exact lt_of_lt_of_le htc (not_lt.1 h)
    rw [hX, hagree t htζ.le]
    exact hnot t htζ
  · have hne : capLife a Tc ζ' ≠ ⊤ := by rw [← heq]; exact ENNReal.coe_ne_top
    unfold capLife at heq hne
    split_ifs at heq hne with h
    · have hfin : ζ' ≠ ⊤ := ne_top_of_lt h
      have hζ : ((ζ'.toNNReal : ℝ≥0) : ℝ≥0∞) = ζ' := ENNReal.coe_toNNReal hfin
      obtain ⟨t, htc, hat, hX⟩ := hcap u hu
      have hn := nonneg_of_strictMono ha0 ham (show ((ζ'.toNNReal : ℝ≥0) : ℝ≥0∞) < Tc by rw [hζ]; exact h)
      have hu' : (u : ℝ) = a ζ'.toNNReal := by
        rw [← ENNReal.ofReal_coe_nnreal] at heq
        exact (ENNReal.ofReal_eq_ofReal_iff u.2 hn).1 heq
      have hζT : ((ζ'.toNNReal : ℝ≥0) : ℝ≥0∞) < Tc := by rw [hζ]; exact h
      have htz : t = ζ'.toNNReal := ham.injOn htc hζT (hat.trans hu')
      have hz : (0 : ℝ≥0) < ζ'.toNNReal := by rw [← ENNReal.coe_lt_coe, hζ]; simpa using hpos
      rw [hX, htz, hagree _ hζ.le]
      exact hin _ hζ hz
    · exact absurd rfl hne

/-- **Below the cap, a relative time is the clock of a time before `ζ′`.** -/
theorem exists_lt_clock_of_lt_capLife (hac : ContinuousOn a {t | (t : ℝ≥0∞) < Tc}) (hpos : 0 < ζ')
    (hcov : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ (u : ℝ) < a t)
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) < L) (hlt : (u : ℝ≥0∞) < capLife a Tc ζ') :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ' ∧ (u : ℝ) < a t := by
  unfold capLife at hlt
  split_ifs at hlt with h
  · have hfin : ζ' ≠ ⊤ := ne_top_of_lt h
    have hζ : ((ζ'.toNNReal : ℝ≥0) : ℝ≥0∞) = ζ' := ENNReal.coe_toNNReal hfin
    have hlt' : (u : ℝ) < a ζ'.toNNReal := by
      rw [← ENNReal.ofReal_coe_nnreal] at hlt
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg u.2).1 hlt
    have hz : (0 : ℝ≥0) < ζ'.toNNReal := by rw [← ENNReal.coe_lt_coe, hζ]; simpa using hpos
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < Tc} := isOpen_lt ENNReal.continuous_coe continuous_const
    have hζT : ((ζ'.toNNReal : ℝ≥0) : ℝ≥0∞) < Tc := by rw [hζ]; exact h
    have hca : ContinuousAt a ζ'.toNNReal := hac.continuousAt (hopen.mem_nhds hζT)
    have hev : ∀ᶠ t in 𝓝[<] ζ'.toNNReal, (u : ℝ) < a t :=
      (hca.eventually (lt_mem_nhds hlt')).filter_mono nhdsWithin_le_nhds
    have : NeBot (𝓝[<] ζ'.toNNReal) := nhdsLT_neBot_of_exists_lt ⟨0, hz⟩
    obtain ⟨t, ht1, ht2⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨t, by rw [← hζ]; exact_mod_cast ht2, ht1⟩
  · obtain ⟨t, htc, hat⟩ := hcov u hu
    exact ⟨t, lt_of_lt_of_le htc (not_lt.1 h), hat⟩

/-- **Before `min(ζ′, Tc)`, the clock is below the cap.** -/
theorem lt_capLife (ha0 : a 0 = 0) (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc}) {t : ℝ≥0}
    (htζ : (t : ℝ≥0∞) < ζ') (htc : (t : ℝ≥0∞) < Tc) : ENNReal.ofReal (a t) < capLife a Tc ζ' := by
  unfold capLife
  split_ifs with h
  · have hfin : ζ' ≠ ⊤ := ne_top_of_lt h
    have hζ : ((ζ'.toNNReal : ℝ≥0) : ℝ≥0∞) = ζ' := ENNReal.coe_toNNReal hfin
    have hζT : ((ζ'.toNNReal : ℝ≥0) : ℝ≥0∞) < Tc := by rw [hζ]; exact h
    have hlt : a t < a ζ'.toNNReal := ham htc hζT (by rw [← ENNReal.coe_lt_coe, hζ]; exact htζ)
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (nonneg_of_strictMono ha0 ham htc) hlt)).2 hlt
  · exact ENNReal.ofReal_lt_top

end Sample

end InteractingSLE.Theorem14.GW2Rd
