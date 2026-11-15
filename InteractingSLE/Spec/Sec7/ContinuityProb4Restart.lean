/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb3Cont
import InteractingSLE.Spec.Sec7.ContinuityProb4Band

/-!
# §7.3: band traces after every rational restart time

Packet PROVE-SEC7-C4. The band argument of Aux. lemma 103 (`source/spec/p337-384.md` L292–L300: "Every new phase is
pulled back through the continuously extended inverse map of the preceding finite continuous prefix") runs the band
transfer (`ContinuityProb4Band`) from the state of the evolution at later times. This file restarts the evolution at
every deterministic rational time and applies the band transfer to the restarted solution through its conditional
law:

* `restart_core_marks`: PROVE-RANDRESTART2's `restart_core`, with the decoding of the restarted force points;
* `ae_restart_mem_of_codeLaw`: if `codeLaw Sᶜ` vanishes at almost every realized word, the restarted code lies in
  `S` almost surely;
* **`ae_band_rational`**: almost surely, for every rational `q < ζ`, rational `δ > 0` and `n`, the driver restarted
  at `q` has the trace event up to both band horizons (first rational time at which a mark of the deleted side is
  within `2δ`, capped by `n` and `ζ − q`), provided the two reduced words (all right, resp. all left, weights `0`)
  have the full trace event Wiener-almost surely at every separated ordered start.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Band

open Sec2 Sec2.Assembly Sec2.Restart QuantumZipper.StrongMarkov RandRestart

variable {nL nR : ℕ}

section Restart

variable {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The restart at a stopping time, in code form, with the restarted marks** (PROVE-RANDRESTART2's
`restart_core`, whose proof is repeated here, with the decoding of the restarted force points added). -/
theorem restart_core_marks (ha : 0 < a) (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A)
    (hAT : ∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω ∧ (0 < T ω ∨ ∀ i j, xL i < xR j)) :
    ∃ (st : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)) (g : Ω → ℝ≥0 → ℝ) (c : Ω → XCode nL nR),
      Measurable st ∧ Measurable g ∧
      (∀ E : Set (((Fin nL → ℝ) × (Fin nR → ℝ)) × (ℝ≥0 → ℝ)), MeasurableSet E →
        P (A ∩ (fun ω => (st ω, g ω)) ⁻¹' E) = ∫⁻ ω in A, wienerPath (Prod.mk (st ω) ⁻¹' E) ∂P) ∧
      ∀ᵐ ω ∂P, ω ∈ A → st ω = wordAt W VL VR T ω ∧ SepStart (st ω) ∧
        c ω ∈ CRel a (st ω).1 (st ω).2 ρL ρR ∧ (c ω).1 = enc (g ω) ∧ cζ (c ω) = ζ ω - T ω ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω - T ω → cw (c ω) t = W (T ω + t) ω - W (T ω) ω ∧
          (∀ i, cvL (c ω) i t = VL i (T ω + t) ω - W (T ω) ω) ∧
          ∀ j, cvR (c ω) j t = VR j (T ω + t) ω - W (T ω) ω) ∧
        HasLimW (c ω) := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hlimE := hE.ae_tendsto_threshold ha
  obtain ⟨hBF, hWad, hVLad, hVRad, hpath⟩ := hE
  obtain ⟨Bv, hBvm, hBvc, hBvF, hBvae⟩ := exists_continuous_version hBF
  have h𝓕𝓖 : 𝓕 ≤ usualAugmentation 𝓕 P := Ito.le_usualAugmentation 𝓕 P
  have hT𝓖 : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T ω : WithTop ℝ≥0) :=
    fun u => h𝓕𝓖 u _ (hT u)
  have hle𝓖 : hT.measurableSpace ≤ hT𝓖.measurableSpace :=
    Ito.measurableSpace_le_of_filtration_le h𝓕𝓖 hT hT𝓖
  -- the state at `T`, through the progressive versions
  set st : Ω → (Fin nL → ℝ) × (Fin nR → ℝ) := fun ω =>
    ((fun i => progVersion ζ (VL i) (T ω) ω - progVersion ζ W (T ω) ω),
      fun j => progVersion ζ (VR j) (T ω) ω - progVersion ζ W (T ω) ω) with hst
  have hstT : Measurable[hT.measurableSpace] st :=
    @measurable_start_aux nL nR Ω hT.measurableSpace _ _ _
      (measurable_eval_stop (isStronglyProgressive_progVersion hWad) hT)
      (fun i => measurable_eval_stop (isStronglyProgressive_progVersion (hVLad i)) hT)
      (fun j => measurable_eval_stop (isStronglyProgressive_progVersion (hVRad j)) hT)
  have hstm : Measurable st := hstT.mono (hT.measurableSpace_le) le_rfl
  -- the restarted Brownian path: Wiener law, independent of `𝓖_T`
  set g : Ω → ℝ≥0 → ℝ := smPath Bv T with hg
  have hgm : Measurable g := measurable_smPath hBvc hBvm (measurable_of_isStoppingTime hT)
  have hind := indep_future hBvF
  have hlaw : P.map g = wienerPath :=
    map_path_eq_wienerPath
      (isBrownianReal_smShift hBvF.1.toIsPreBrownianReal hBvc hBvm hind hT𝓖).toIsPreBrownianReal
      hgm
  have hindT := indep_smPath hBvF.1.toIsPreBrownianReal hBvc hBvm hind hT𝓖
  have hpair : Measurable fun ω => (st ω, g ω) := hstm.prodMk hgm
  have hjoint : (P.restrict A).map (fun ω => (st ω, g ω)) =
      ((P.restrict A).map st).prod wienerPath := by
    refine (Measure.prod_eq fun D F hD hF => ?_).symm
    rw [Measure.map_apply hpair (hD.prod hF), Measure.map_apply hstm hD, ← hlaw,
      Measure.map_apply hgm hF, Measure.restrict_apply (hpair (hD.prod hF)),
      Measure.restrict_apply (hstm hD)]
    have hDA : MeasurableSet[hT𝓖.measurableSpace] (st ⁻¹' D ∩ A) :=
      hle𝓖 _ ((hstT hD).inter hA)
    have e : (fun ω => (st ω, g ω)) ⁻¹' (D ×ˢ F) ∩ A = (st ⁻¹' D ∩ A) ∩ g ⁻¹' F := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_prod]
      tauto
    rw [e]
    exact (Indep_iff _ _ _).1 hindT _ _ hDA ⟨F, hF, rfl⟩
  refine ⟨st, g, fun ω => codeOf (wordAt W VL VR T ω).1 (wordAt W VL VR T ω).2 (smShift Bv T)
      (fun t ω' => W (T ω' + t) ω' - W (T ω') ω') (fun i t ω' => VL i (T ω' + t) ω' - W (T ω') ω')
      (fun j t ω' => VR j (T ω' + t) ω' - W (T ω') ω') (fun ω' => ζ ω' - T ω') ω,
    hstm, hgm, fun E hEm => ?_, ?_⟩
  · rw [inter_comm, ← Measure.restrict_apply (hpair hEm), ← Measure.map_apply hpair hEm, hjoint,
      Measure.prod_apply hEm]
    rw [lintegral_map (measurable_measure_prodMk_left hEm) hstm]
  · filter_upwards [hpath, hBvae, hlimE] with ω hp hb hl hωA
    obtain ⟨hTζ, hT0⟩ := hAT ω hωA
    have h0 := restart_values hp hTζ
    have hst_eq : st ω = wordAt W VL VR T ω := by
      simp only [hst, wordAt, h0.1, h0.2.1, h0.2.2]
    have hr := hp.restart hTζ
    have hb' : (fun t => B (T ω + t) ω - B (T ω) ω) = fun t => smShift Bv T t ω := by
      funext t; simp only [smShift, hb]
    rw [hb'] at hr
    have hsep : SepStart (wordAt W VL VR T ω) := by
      rcases hT0 with hT0 | hsx
      · exact sepStart_restart hp hT0 hTζ
      · exact sepStart_restart_of_sep hp hsx hTζ
    have hrl := restart_tendsto hTζ hl
    have hcode := codeOf_mem_cRel_of_path (Ω := Ω) (ω := ω)
      (xL := fun i => VL i (T ω) ω - W (T ω) ω) (xR := fun j => VR j (T ω) ω - W (T ω) ω)
      (W := fun t ω' => W (T ω' + t) ω' - W (T ω') ω')
      (VL := fun i t ω' => VL i (T ω' + t) ω' - W (T ω') ω')
      (VR := fun j t ω' => VR j (T ω' + t) ω' - W (T ω') ω')
      (B := smShift Bv T) (B' := smShift Bv T) (ζ := fun ω' => ζ ω' - T ω') hr
      (((hBvc ω).comp (continuous_const.add continuous_id)).sub continuous_const) (fun t => rfl) hrl
    rw [hst_eq]
    exact ⟨rfl, hsep, hcode.1, rfl, rfl,
      fun t ht => ⟨(hcode.2 t ht).1, (hcode.2 t ht).2.1, (hcode.2 t ht).2.2.1⟩,
      hasLimW_of_tendsto (fun t ht => (hcode.2 t ht).1) hrl⟩


/-- **The conditional law of a code event of the restarted solution.** Under the hypotheses of
`restart_core_marks`, for a Borel set `S` of codes, almost surely on `A` the restarted code lies in `S` as soon as
`codeLaw Sᶜ` vanishes at almost every realized word on `A`. -/
theorem ae_restart_mem_of_codeLaw (ha : 0 < a)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A)
    (hAT : ∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω ∧ (0 < T ω ∨ ∀ i j, xL i < xR j))
    {S : Set (XCode nL nR)} (hS : MeasurableSet S)
    (h0 : ∀ᵐ ω ∂P, ω ∈ A → codeLaw a ρL ρR Sᶜ (wordAt W VL VR T ω) = 0) :
    ∃ c : Ω → XCode nL nR, ∀ᵐ ω ∂P, ω ∈ A →
      c ω ∈ CRel a (wordAt W VL VR T ω).1 (wordAt W VL VR T ω).2 ρL ρR ∧ cζ (c ω) = ζ ω - T ω ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω - T ω → cw (c ω) t = W (T ω + t) ω - W (T ω) ω ∧
        (∀ i, cvL (c ω) i t = VL i (T ω + t) ω - W (T ω) ω) ∧
        ∀ j, cvR (c ω) j t = VR j (T ω + t) ω - W (T ω) ω) ∧
      HasLimW (c ω) ∧ c ω ∈ S := by
  obtain ⟨st, g, c, -, -, hlaw, hid⟩ := restart_core_marks ha hE hT hA hAT
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  have hnull : P (A ∩ (fun ω => (st ω, g ω)) ⁻¹' restartSetS a ρL ρR Sᶜ) = 0 := by
    rw [hlaw _ (measurableSet_restartSetS hS.compl)]
    refine (setLIntegral_congr_fun_ae hAm ?_).trans (setLIntegral_const _ 0 |>.trans (zero_mul _))
    filter_upwards [hid, h0] with ω h h0' hωA
    rw [(h hωA).1]
    exact h0' hωA
  have hS' : ∀ᵐ ω ∂P, ω ∈ A → c ω ∈ S := by
    have := measure_eq_zero_iff_ae_notMem.1 hnull
    filter_upwards [this, hid] with ω hn h hωA
    obtain ⟨-, hsep, hc, hc1, -⟩ := h hωA
    by_contra hcS
    have e1 : (st ω, g ω) ∈ restartSetS a ρL ρR Sᶜ ↔
        (((st ω).1, (st ω).2), (c ω).1) ∈ lawSetS a ρL ρR Sᶜ := by
      rw [hc1]; exact Iff.rfl
    exact hn ⟨hωA, e1.2 ((mem_lawSetS_iff hsep hc).2 hcS)⟩
  refine ⟨c, ?_⟩
  filter_upwards [hid, hS'] with ω h hS'' hωA
  obtain ⟨hst, -, hc, -, hcζ, hdec, hcl⟩ := h hωA
  rw [← hst]
  exact ⟨hc, hcζ, hdec, hcl, hS'' hωA⟩

/-! ### Band traces from every rational time -/

/-- The force points restarted at `σ`, seen from the driver at `σ`. -/
def shiftMarks {n : ℕ} (v : Fin n → ℝ≥0 → ℝ) (w : ℝ≥0 → ℝ) (σ : ℝ≥0) : Fin n → ℝ≥0 → ℝ :=
  fun j t => v j (σ + t) - w σ

theorem measurableSet_lt_lifetime_const (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (q : ℝ≥0) :
    MeasurableSet[(isStoppingTime_const (usualAugmentation 𝓕 P) q).measurableSpace] {ω | (q : ℝ≥0∞) < ζ ω} := by
  rw [IsStoppingTime.measurableSpace_const]
  have h := (Ito.isStoppingTime_lifetime (Ito.isIntegratedSLEEvolution_usualAugmentation hE).2.1 q).compl
  convert h using 1
  ext ω
  simp only [mem_ofPred_eq, mem_compl_iff]
  exact not_le.symm

/-- **Band traces after a deterministic restart time** (one band, one time). -/
theorem ae_band_at [IsProbabilityMeasure P] (hκ : 0 < a)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hredR : ∀ s : (Fin nL → ℝ) × (Fin nR → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS a ρL (0 : Fin nR → ℝ) (fullTraceSet (nL := nL) (nR := nR)))
    (hredL : ∀ s : (Fin nL → ℝ) × (Fin nR → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS a (0 : Fin nL → ℝ) ρR (fullTraceSet (nL := nL) (nR := nR)))
    (q : ℝ≥0) (hq : 0 < q ∨ ∀ i j, xL i < xR j) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ ω →
      TraceEvent (shiftNN (fun t => W t ω) q)
        (horizonR δ n (shiftNN (fun t => W t ω) q) (shiftMarks (fun j t => VR j t ω) (fun t => W t ω) q)
          (ζ ω - q)) ∧
      TraceEvent (shiftNN (fun t => W t ω) q)
        (horizonL δ n (shiftNN (fun t => W t ω) q) (shiftMarks (fun i t => VL i t ω) (fun t => W t ω) q)
          (ζ ω - q)) := by
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hT := isStoppingTime_const (usualAugmentation 𝓕 P) q
  have hA := measurableSet_lt_lifetime_const hE q
  have hAT : ∀ ω ∈ {ω | (q : ℝ≥0∞) < ζ ω}, ((fun _ : Ω => q) ω : ℝ≥0∞) < ζ ω ∧
      (0 < (fun _ : Ω => q) ω ∨ ∀ i j, xL i < xR j) := fun ω hω => ⟨hω, hq⟩
  have hsolv := ae_solvable_restart hκ hE𝓖 hT hA hAT
  have hord : ∀ᵐ ω ∂P, ω ∈ {ω | (q : ℝ≥0∞) < ζ ω} →
      IsOrderedForceWord (wordAt W VL VR (fun _ => q) ω).1 (wordAt W VL VR (fun _ => q) ω).2 := by
    filter_upwards [hE.2.2.2.2] with ω hp hω
    exact isOrderedForceWord_at hp hω
  obtain ⟨cR, hcR⟩ := ae_restart_mem_of_codeLaw hκ hE𝓖 hT hA hAT (measurableSet_bandSetR δ n) (by
    filter_upwards [hsolv, hord] with ω h1 h2 hω
    exact codeLaw_compl_bandSetR_eq_zero hκ (h1 hω).1 (h1 hω).2 (hredR _ (h1 hω).1 (h2 hω)) hδ n)
  obtain ⟨cL, hcL⟩ := ae_restart_mem_of_codeLaw hκ hE𝓖 hT hA hAT (measurableSet_bandSetL δ n) (by
    filter_upwards [hsolv, hord] with ω h1 h2 hω
    exact codeLaw_compl_bandSetL_eq_zero hκ (h1 hω).1 (h1 hω).2 (hredL _ (h1 hω).1 (h2 hω)) hδ n)
  filter_upwards [hcR, hcL] with ω hR hL hω
  obtain ⟨hc, hcζ, hdec, hcl, hcS⟩ := hR hω
  obtain ⟨hc', hcζ', hdec', hcl', hcS'⟩ := hL hω
  refine ⟨?_, ?_⟩
  · have hev := (mem_bandSetR_iff δ n (mem_cRelF_iff.2 hc).1 hcl).1 hcS
    rw [hcζ, horizonR_congr δ n (w' := shiftNN (fun t => W t ω) q)
      (vR' := shiftMarks (fun j t => VR j t ω) (fun t => W t ω) q) (fun t ht => (hdec t ht).1)
      (fun t ht => (hdec t ht).2.2)] at hev
    exact hev.congr fun t ht => (hdec t (ht.trans_le (horizonR_le_lifetime _ _ _ _ _))).1
  · have hev := (mem_bandSetL_iff δ n (mem_cRelF_iff.2 hc').1 hcl').1 hcS'
    rw [hcζ', horizonL_congr δ n (w' := shiftNN (fun t => W t ω) q)
      (vL' := shiftMarks (fun i t => VL i t ω) (fun t => W t ω) q) (fun t ht => (hdec' t ht).1)
      (fun t ht => (hdec' t ht).2.1)] at hev
    exact hev.congr fun t ht => (hdec' t (ht.trans_le (horizonL_le_lifetime _ _ _ _ _))).1

/-- **Band traces after every rational restart time**, for every rational `δ > 0` and every horizon `n`. -/
theorem ae_band_rational [IsProbabilityMeasure P] (hκ : 0 < a)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hredR : ∀ s : (Fin nL → ℝ) × (Fin nR → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS a ρL (0 : Fin nR → ℝ) (fullTraceSet (nL := nL) (nR := nR)))
    (hredL : ∀ s : (Fin nL → ℝ) × (Fin nR → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS a (0 : Fin nL → ℝ) ρR (fullTraceSet (nL := nL) (nR := nR))) :
    ∀ᵐ ω ∂P, ∀ q : ℚ, ∀ δ : ℚ, 0 < δ → ∀ n : ℕ, (0 < Real.toNNReal q ∨ ∀ i j, xL i < xR j) →
      ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < ζ ω →
      TraceEvent (shiftNN (fun t => W t ω) (Real.toNNReal q))
        (horizonR δ n (shiftNN (fun t => W t ω) (Real.toNNReal q))
          (shiftMarks (fun j t => VR j t ω) (fun t => W t ω) (Real.toNNReal q)) (ζ ω - Real.toNNReal q)) ∧
      TraceEvent (shiftNN (fun t => W t ω) (Real.toNNReal q))
        (horizonL δ n (shiftNN (fun t => W t ω) (Real.toNNReal q))
          (shiftMarks (fun i t => VL i t ω) (fun t => W t ω) (Real.toNNReal q)) (ζ ω - Real.toNNReal q)) := by
  rw [ae_all_iff]
  intro q
  rw [ae_all_iff]
  intro δ
  by_cases hq : 0 < Real.toNNReal q ∨ ∀ i j, xL i < xR j
  · by_cases hδ : (0 : ℚ) < δ
    · have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
      have h := fun n : ℕ => ae_band_at hκ hE hredR hredL (Real.toNNReal q) hq hδ' n
      filter_upwards [ae_all_iff.2 h] with ω hω _ n _ hqζ
      exact hω n hqζ
    · exact ae_of_all _ fun ω h => absurd h hδ
  · exact ae_of_all _ fun ω _ _ h _ => absurd h hq

end Restart

end Band

end Sec7

end InteractingSLE
