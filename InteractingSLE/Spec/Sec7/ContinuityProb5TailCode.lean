/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb5Tail

/-!
# §7.3: infinite-band events on solution codes and after rational restarts

Packet PROVE-SEC7-C5. The infinite bands of `ContinuityProb5Tail.lean` restarted at every rational time, through the
canonical code law of PROVE-RANDRESTART2 and PROVE-SEC7-C4 (`codeLaw`, `ae_restart_mem_of_codeLaw`), exactly as C4's
finite bands (`ae_band_rational`): the band events are Borel on codes (`bandTailSetR/L`), have canonical law one at
every separated start where the reduced word has the full trace event (`codeLaw_compl_bandTailSetR_eq_zero`), and hence
hold for the restarted evolution at every rational time (`ae_bandTail_rational`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Band

open Sec2 Sec2.Assembly Sec2.Restart RandRestart Girsanov

variable {nL nR : ℕ} {i₀ : Fin nL} {j₀ : Fin nR}

/-! ### Codes -/

theorem measurableSet_exitR (m : ℕ) (s : ℝ≥0) :
    MeasurableSet {x : XCode nL nR | ExitR m (cw x) (cvL x) (cvR x) i₀ j₀ s} := by
  have hR : ∀ t, Measurable fun x : XCode nL nR => cvR x j₀ t := fun t =>
    measurable_dec_at (measurable_code_vR j₀) t
  have hL : ∀ t, Measurable fun x : XCode nL nR => cvL x i₀ t := fun t =>
    measurable_dec_at (measurable_code_vL i₀) t
  have hw : ∀ t, Measurable fun x : XCode nL nR => cw x t := fun t => measurable_dec_at measurable_code_w t
  have h1 := measurableSet_le (((hR s).sub (hw s)).const_mul 4) ((hR s).sub (hL s))
  have h2 : Measurable fun x : XCode nL nR => discClock (cvL x) (cvR x) i₀ j₀ s :=
    Finset.measurable_sum _ fun k _ => (((hR _).sub (hL _)).inv).pow_const 2
  exact h1.union (measurableSet_le measurable_const h2)

theorem measurableSet_exitL (m : ℕ) (s : ℝ≥0) :
    MeasurableSet {x : XCode nL nR | ExitL m (cw x) (cvL x) (cvR x) i₀ j₀ s} := by
  have hR : ∀ t, Measurable fun x : XCode nL nR => cvR x j₀ t := fun t =>
    measurable_dec_at (measurable_code_vR j₀) t
  have hL : ∀ t, Measurable fun x : XCode nL nR => cvL x i₀ t := fun t =>
    measurable_dec_at (measurable_code_vL i₀) t
  have hw : ∀ t, Measurable fun x : XCode nL nR => cw x t := fun t => measurable_dec_at measurable_code_w t
  have h1 := measurableSet_le (((hw s).sub (hL s)).const_mul 4) ((hR s).sub (hL s))
  have h2 : Measurable fun x : XCode nL nR => discClock (cvL x) (cvR x) i₀ j₀ s :=
    Finset.measurable_sum _ fun k _ => (((hR _).sub (hL _)).inv).pow_const 2
  exact h1.union (measurableSet_le measurable_const h2)

theorem measurable_tailHorizonR (m : ℕ) :
    Measurable fun x : XCode nL nR => tailHorizonR m (cw x) (cvL x) (cvR x) i₀ j₀ (cζ x) :=
  (measurable_hitTime measurable_cζ fun s => measurableSet_exitR m s).min measurable_cζ

theorem measurable_tailHorizonL (m : ℕ) :
    Measurable fun x : XCode nL nR => tailHorizonL m (cw x) (cvL x) (cvR x) i₀ j₀ (cζ x) :=
  (measurable_hitTime measurable_cζ fun s => measurableSet_exitL m s).min measurable_cζ

/-- Codes whose driver has the trace event up to the tail horizon of the right band. -/
def bandTailSetR (i₀ : Fin nL) (j₀ : Fin nR) (m : ℕ) : Set (XCode nL nR) :=
  {x | (cw x, tailHorizonR m (cw x) (cvL x) (cvR x) i₀ j₀ (cζ x)) ∈ traceSet}

/-- Codes whose driver has the trace event up to the tail horizon of the left band. -/
def bandTailSetL (i₀ : Fin nL) (j₀ : Fin nR) (m : ℕ) : Set (XCode nL nR) :=
  {x | (cw x, tailHorizonL m (cw x) (cvL x) (cvR x) i₀ j₀ (cζ x)) ∈ traceSet}

theorem measurableSet_bandTailSetR (m : ℕ) : MeasurableSet (bandTailSetR i₀ j₀ m : Set (XCode nL nR)) :=
  (measurable_cw.prodMk (measurable_tailHorizonR m)) measurableSet_traceSet

theorem measurableSet_bandTailSetL (m : ℕ) : MeasurableSet (bandTailSetL i₀ j₀ m : Set (XCode nL nR)) :=
  (measurable_cw.prodMk (measurable_tailHorizonL m)) measurableSet_traceSet

theorem mem_bandTailSetR_iff {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (m : ℕ) {x : XCode nL nR}
    (hx : x ∈ CRelF a ρL ρR) (hl : HasLimW x) :
    x ∈ bandTailSetR i₀ j₀ m ↔ TraceEvent (cw x) (tailHorizonR m (cw x) (cvL x) (cvR x) i₀ j₀ (cζ x)) := by
  have hp : IsIntegratedSLEPath a (startOf x).1 (startOf x).2 ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) :=
    hx.1.2.2
  exact mem_traceSet_iff_of_le hp.isForcePath.continuousOn_w hp.1 tailHorizonR_le_lifetime hl

theorem mem_bandTailSetL_iff {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (m : ℕ) {x : XCode nL nR}
    (hx : x ∈ CRelF a ρL ρR) (hl : HasLimW x) :
    x ∈ bandTailSetL i₀ j₀ m ↔ TraceEvent (cw x) (tailHorizonL m (cw x) (cvL x) (cvR x) i₀ j₀ (cζ x)) := by
  have hp : IsIntegratedSLEPath a (startOf x).1 (startOf x).2 ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) :=
    hx.1.2.2
  exact mem_traceSet_iff_of_le hp.isForcePath.continuousOn_w hp.1 tailHorizonL_le_lifetime hl

/-! ### The horizons only see the paths before the lifetime -/

theorem discClock_congr {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < ζ) (hvL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ i, vL i t = vL' i t)
    (hvR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ j, vR j t = vR' j t) :
    discClock vL vR i₀ j₀ s = discClock vL' vR' i₀ j₀ s := by
  refine Finset.sum_congr rfl fun k hk => ?_
  have hks : ((k : ℝ≥0)) ≤ s := by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
    exact (Nat.cast_le.2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).trans (Nat.floor_le s.coe_nonneg)
  have hkζ : ((k : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hks) hs
  simp only [crossGap, hvL _ hkζ, hvR _ hkζ]

theorem tailHorizonR_congr (m : ℕ) {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ}
    {vR vR' : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t = w' t)
    (hvL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ i, vL i t = vL' i t)
    (hvR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ j, vR j t = vR' j t) :
    tailHorizonR m w vL vR i₀ j₀ ζ = tailHorizonR m w' vL' vR' i₀ j₀ ζ := by
  unfold tailHorizonR
  rw [hitTime_congr fun s hs => ?_]
  simp only [ExitR, crossGap, hw s hs, hvL s hs, hvR s hs, discClock_congr hs hvL hvR]

theorem tailHorizonL_congr (m : ℕ) {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ}
    {vR vR' : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t = w' t)
    (hvL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ i, vL i t = vL' i t)
    (hvR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ j, vR j t = vR' j t) :
    tailHorizonL m w vL vR i₀ j₀ ζ = tailHorizonL m w' vL' vR' i₀ j₀ ζ := by
  unfold tailHorizonL
  rw [hitTime_congr fun s hs => ?_]
  simp only [ExitL, crossGap, hw s hs, hvL s hs, hvR s hs, discClock_congr hs hvL hvR]

/-! ### Canonical law of the infinite-band events -/

section CodeLaw

variable {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The infinite right-band event has canonical law one** at every separated start at which the word has an
evolution and the word with all right weights `0` has the full trace event Wiener-almost surely. -/
theorem codeLaw_compl_bandTailSetR_eq_zero (hκ : 0 < κ) {s : (Fin nL → ℝ) × (Fin nR → ℝ)} (hsep : SepStart s)
    (hsolv : ∀ᵐ f ∂wienerPath, enc f ∈ Prod.fst '' CRel κ s.1 s.2 ρL ρR)
    (hred : ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS κ ρL (0 : Fin nR → ℝ) (fullTraceSet (nL := nL) (nR := nR)))
    (hj₀ : ∀ j, j₀ ≤ j) (m : ℕ) :
    codeLaw κ ρL ρR (bandTailSetR i₀ j₀ m)ᶜ s = 0 := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_of_ae_wienerPath.{0} hsep hsolv
  have hband := ae_traceEvent_tailHorizonR (i₀ := i₀) hκ hE hsep hj₀ m hred
  refine codeLaw_compl_eq_zero_of_ae hκ hsep hE (measurableSet_bandTailSetR m) fun B' hc hae => ?_
  filter_upwards [ae_codeOf_mem hκ hE hc hae, hband, hE.ae_tendsto_threshold hκ] with ω ⟨hmemC, hdec⟩ hb hl
  set x := codeOf s.1 s.2 B' W VL VR ζ ω with hx
  have hxF : x ∈ CRelF κ ρL ρR := (mem_cRelF_iff.2 hmemC).1
  have hxl : HasLimW x := hasLimW_of_tendsto (fun t ht => (hdec t ht).1) hl
  have hxζ : cζ x = ζ ω := rfl
  rw [mem_bandTailSetR_iff m hxF hxl, hxζ,
    tailHorizonR_congr m (w' := fun t => W t ω) (vL' := fun i t => VL i t ω) (vR' := fun j t => VR j t ω)
      (fun t ht => (hdec t ht).1) (fun t ht => (hdec t ht).2.1) (fun t ht => (hdec t ht).2.2.1)]
  exact hb.congr fun t ht => ((hdec t (ht.trans_le tailHorizonR_le_lifetime)).1).symm

/-- **The infinite left-band event has canonical law one** (the reflected statement). -/
theorem codeLaw_compl_bandTailSetL_eq_zero (hκ : 0 < κ) {s : (Fin nL → ℝ) × (Fin nR → ℝ)} (hsep : SepStart s)
    (hsolv : ∀ᵐ f ∂wienerPath, enc f ∈ Prod.fst '' CRel κ s.1 s.2 ρL ρR)
    (hred : ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS κ (0 : Fin nL → ℝ) ρR (fullTraceSet (nL := nL) (nR := nR)))
    (hi₀ : ∀ i, i₀ ≤ i) (m : ℕ) :
    codeLaw κ ρL ρR (bandTailSetL i₀ j₀ m)ᶜ s = 0 := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_of_ae_wienerPath.{0} hsep hsolv
  have hband := ae_traceEvent_tailHorizonL (j₀ := j₀) hκ hE hsep hi₀ m hred
  refine codeLaw_compl_eq_zero_of_ae hκ hsep hE (measurableSet_bandTailSetL m) fun B' hc hae => ?_
  filter_upwards [ae_codeOf_mem hκ hE hc hae, hband, hE.ae_tendsto_threshold hκ] with ω ⟨hmemC, hdec⟩ hb hl
  set x := codeOf s.1 s.2 B' W VL VR ζ ω with hx
  have hxF : x ∈ CRelF κ ρL ρR := (mem_cRelF_iff.2 hmemC).1
  have hxl : HasLimW x := hasLimW_of_tendsto (fun t ht => (hdec t ht).1) hl
  have hxζ : cζ x = ζ ω := rfl
  rw [mem_bandTailSetL_iff m hxF hxl, hxζ,
    tailHorizonL_congr m (w' := fun t => W t ω) (vL' := fun i t => VL i t ω) (vR' := fun j t => VR j t ω)
      (fun t ht => (hdec t ht).1) (fun t ht => (hdec t ht).2.1) (fun t ht => (hdec t ht).2.2.1)]
  exact hb.congr fun t ht => ((hdec t (ht.trans_le tailHorizonL_le_lifetime)).1).symm

end CodeLaw

/-! ### Infinite bands after every rational restart time -/

section Restart

variable {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Infinite-band traces after a deterministic restart time.** -/
theorem ae_bandTail_at [IsProbabilityMeasure P] (hκ : 0 < a)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hredR : ∀ s : (Fin nL → ℝ) × (Fin nR → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS a ρL (0 : Fin nR → ℝ) (fullTraceSet (nL := nL) (nR := nR)))
    (hredL : ∀ s : (Fin nL → ℝ) × (Fin nR → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS a (0 : Fin nL → ℝ) ρR (fullTraceSet (nL := nL) (nR := nR)))
    (hi₀ : ∀ i, i₀ ≤ i) (hj₀ : ∀ j, j₀ ≤ j)
    (q : ℝ≥0) (hq : 0 < q ∨ ∀ i j, xL i < xR j) (m : ℕ) :
    ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ ω →
      TraceEvent (shiftNN (fun t => W t ω) q)
        (tailHorizonR m (shiftNN (fun t => W t ω) q) (shiftMarks (fun i t => VL i t ω) (fun t => W t ω) q)
          (shiftMarks (fun j t => VR j t ω) (fun t => W t ω) q) i₀ j₀ (ζ ω - q)) ∧
      TraceEvent (shiftNN (fun t => W t ω) q)
        (tailHorizonL m (shiftNN (fun t => W t ω) q) (shiftMarks (fun i t => VL i t ω) (fun t => W t ω) q)
          (shiftMarks (fun j t => VR j t ω) (fun t => W t ω) q) i₀ j₀ (ζ ω - q)) := by
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
  obtain ⟨cR, hcR⟩ := ae_restart_mem_of_codeLaw hκ hE𝓖 hT hA hAT (measurableSet_bandTailSetR (i₀ := i₀)
    (j₀ := j₀) m) (by
      filter_upwards [hsolv, hord] with ω h1 h2 hω
      exact codeLaw_compl_bandTailSetR_eq_zero hκ (h1 hω).1 (h1 hω).2 (hredR _ (h1 hω).1 (h2 hω)) hj₀ m)
  obtain ⟨cL, hcL⟩ := ae_restart_mem_of_codeLaw hκ hE𝓖 hT hA hAT (measurableSet_bandTailSetL (i₀ := i₀)
    (j₀ := j₀) m) (by
      filter_upwards [hsolv, hord] with ω h1 h2 hω
      exact codeLaw_compl_bandTailSetL_eq_zero hκ (h1 hω).1 (h1 hω).2 (hredL _ (h1 hω).1 (h2 hω)) hi₀ m)
  filter_upwards [hcR, hcL] with ω hR hL hω
  obtain ⟨hc, hcζ, hdec, hcl, hcS⟩ := hR hω
  obtain ⟨hc', hcζ', hdec', hcl', hcS'⟩ := hL hω
  refine ⟨?_, ?_⟩
  · have hev := (mem_bandTailSetR_iff m (mem_cRelF_iff.2 hc).1 hcl).1 hcS
    rw [hcζ, tailHorizonR_congr m (w' := shiftNN (fun t => W t ω) q)
      (vL' := shiftMarks (fun i t => VL i t ω) (fun t => W t ω) q)
      (vR' := shiftMarks (fun j t => VR j t ω) (fun t => W t ω) q) (fun t ht => (hdec t ht).1)
      (fun t ht => (hdec t ht).2.1) (fun t ht => (hdec t ht).2.2)] at hev
    exact hev.congr fun t ht => (hdec t (ht.trans_le tailHorizonR_le_lifetime)).1
  · have hev := (mem_bandTailSetL_iff m (mem_cRelF_iff.2 hc').1 hcl').1 hcS'
    rw [hcζ', tailHorizonL_congr m (w' := shiftNN (fun t => W t ω) q)
      (vL' := shiftMarks (fun i t => VL i t ω) (fun t => W t ω) q)
      (vR' := shiftMarks (fun j t => VR j t ω) (fun t => W t ω) q) (fun t ht => (hdec' t ht).1)
      (fun t ht => (hdec' t ht).2.1) (fun t ht => (hdec' t ht).2.2)] at hev
    exact hev.congr fun t ht => (hdec' t (ht.trans_le tailHorizonL_le_lifetime)).1

/-- **Infinite-band traces after every rational restart time**, for every clock cutoff `m`. -/
theorem ae_bandTail_rational [IsProbabilityMeasure P] (hκ : 0 < a)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hredR : ∀ s : (Fin nL → ℝ) × (Fin nR → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS a ρL (0 : Fin nR → ℝ) (fullTraceSet (nL := nL) (nR := nR)))
    (hredL : ∀ s : (Fin nL → ℝ) × (Fin nR → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS a (0 : Fin nL → ℝ) ρR (fullTraceSet (nL := nL) (nR := nR)))
    (hi₀ : ∀ i, i₀ ≤ i) (hj₀ : ∀ j, j₀ ≤ j) :
    ∀ᵐ ω ∂P, ∀ q : ℚ, ∀ m : ℕ, (0 < Real.toNNReal q ∨ ∀ i j, xL i < xR j) →
      ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < ζ ω →
      TraceEvent (shiftNN (fun t => W t ω) (Real.toNNReal q))
        (tailHorizonR m (shiftNN (fun t => W t ω) (Real.toNNReal q))
          (shiftMarks (fun i t => VL i t ω) (fun t => W t ω) (Real.toNNReal q))
          (shiftMarks (fun j t => VR j t ω) (fun t => W t ω) (Real.toNNReal q)) i₀ j₀ (ζ ω - Real.toNNReal q)) ∧
      TraceEvent (shiftNN (fun t => W t ω) (Real.toNNReal q))
        (tailHorizonL m (shiftNN (fun t => W t ω) (Real.toNNReal q))
          (shiftMarks (fun i t => VL i t ω) (fun t => W t ω) (Real.toNNReal q))
          (shiftMarks (fun j t => VR j t ω) (fun t => W t ω) (Real.toNNReal q)) i₀ j₀ (ζ ω - Real.toNNReal q)) := by
  rw [ae_all_iff]
  intro q
  rw [ae_all_iff]
  intro m
  by_cases hq : 0 < Real.toNNReal q ∨ ∀ i j, xL i < xR j
  · filter_upwards [ae_bandTail_at hκ hE hredR hredL hi₀ hj₀ (Real.toNNReal q) hq m] with ω hω _ hqζ
    exact hω hqζ
  · exact ae_of_all _ fun ω h => absurd h hq

end Restart

end Band

end Sec7

end InteractingSLE
