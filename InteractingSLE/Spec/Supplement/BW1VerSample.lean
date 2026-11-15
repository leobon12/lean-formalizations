/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1VerRead

/-!
# One sample of a relative exploration with the retained time read from the record

Packet PROVE-BW1-INPUTS2. GB6's preterminal and terminal read-back analysis (`Supp8.GB6.GaugeE`) is a sample-by-sample
argument behind its almost-sure statements. Here it is stated for ONE sample, with the own time of the retained
prefix read from the record (`recS r`): a good sample (`IsGoodSample`: positive own time, retained chart, a global
continuous trace of the record driver, a continuous counterflow from `0` with a complete transient trace) and
relative coordinates `(D, L)` of it (`IsSampleCoord`) give the regular clock, the physical read-back, continuity and
positivity of the separation gauge before `L` and its zero limit at a finite `L` (`sample_readout`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BW1Ver

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.ReadD Supp8.GB6.GaugeE Sec7.PocketTraversal

/-- The first contact of the physical counterflow (from `∞`, inverted trace `γ`) with the retained prefix
`A([0, s])`. -/
def contactT (γ A : ℝ≥0 → ℂ) (s : ℝ≥0) : ℝ≥0∞ :=
  firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun v => (A v : OnePoint ℂ)) '' Icc 0 s)

/-- The relative clock of a sample: `a(t) = hcap(Ψ(K'_t))/2` for the retained chart of the record at its own time. -/
abbrev rclk (r : RecData) (w : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ := relClock (rdrv r) (recS r) (Ito.rpath w) t

/-- **A good sample**: the record's own time is positive, its retained chart is an `IsRetainedChartOff`, the record
driver has a global continuous trace `A`, and the counterflow driver `w` is continuous from `0` with a complete
transient generating trace `γ`. -/
structure IsGoodSample (r : RecData) (A : ℝ≥0 → ℂ) (w : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) : Prop where
  pos : 0 < recS r
  chart : Supp8.Q3Rel.IsRetainedChartOff (Supp8.Q3Rel.invHull (rdrv r) (recS r)) (relMap (rdrv r) (recS r))
    (relInv (rdrv r) (recS r)) (Supp8.Q3Rel.relLog (rdrv r) (recS r)) (Supp8.Q3Rel.relBad (rdrv r) (recS r))
  trace : IsGeneratingTrace (fun u : ℝ≥0 => rdrv r u) ⊤ A
  cont : Continuous w
  zero : w 0 = 0
  ctrace : IsGeneratingTrace w ⊤ γ
  trans : Tendsto (fun t => ‖γ t‖) atTop atTop

/-- **Relative coordinates of one sample**: a driver `D`, continuous and `0` at `0` before a positive life `L`, whose
times before `L` are relative clock values before the contact, and which generates the images of the counterflow
hulls at the clock values. -/
structure IsSampleCoord (r : RecData) (A : ℝ≥0 → ℂ) (w : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (D : ℝ≥0 → ℝ) (L : ℝ≥0∞) :
    Prop where
  cont : ContinuousOn D {u | (u : ℝ≥0∞) < L}
  zero : D 0 = 0
  pos : 0 < L
  range : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → ∃ t : ℝ≥0, (t : ℝ≥0∞) < contactT γ A (recS r) ∧ (u : ℝ) < rclk r w t
  hulls : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactT γ A (recS r) → 0 ≤ rclk r w t ∧ ENNReal.ofReal (rclk r w t) < L ∧
    fwdHull (Ito.rpath D) (rclk r w t) = relMap (rdrv r) (recS r) '' fwdHull (Ito.rpath w) t

section Good

variable {r : RecData} {A : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}

theorem continuous_rdrv_nn (r : RecData) : Continuous fun u : ℝ≥0 => rdrv r u :=
  (continuous_rdrv r).comp NNReal.continuous_coe

theorem IsGoodSample.continuous_A (hg : IsGoodSample r A w γ) : Continuous A := by
  have hc := hg.trace.2.1
  simp only [le_top, ofPred_true] at hc
  exact continuousOn_univ.1 hc

theorem IsGoodSample.continuous_γ (hg : IsGoodSample r A w γ) : Continuous γ := by
  have hc := hg.ctrace.2.1
  simp only [le_top, ofPred_true] at hc
  exact continuousOn_univ.1 hc

theorem IsGoodSample.recordTrace_eq (hg : IsGoodSample r A w γ) (v : ℝ≥0) : recordTrace v r = A v :=
  LP.traceAt_eq_of_isGeneratingTrace hg.trace (continuous_rdrv_nn r).continuousOn (rdrv_zero r)
    ENNReal.coe_lt_top

theorem IsGoodSample.tip (hg : IsGoodSample r A w γ) :
    Tendsto (QuantumZipper.fwdMapInv (rdrv r) (recS r)) (𝓝[H] 0) (𝓝 (A (recS r))) := by
  have h := IsGeneratingTrace.tendsto_fwdMapInv_tip hg.trace (continuous_rdrv_nn r).continuousOn (rdrv_zero r)
    (ENNReal.coe_lt_top (r := recS r))
  rwa [rdrv_toNNReal] at h

theorem IsGoodSample.disjoint (hg : IsGoodSample r A w γ) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) < contactT γ A (recS r)) :
    Disjoint (closure (fwdHull (rdrv r) (recS r)))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w) T)) := by
  have h := disjoint_closure_fwdHull_of_lt_firstContactTime hg.trace (continuous_rdrv_nn r).continuousOn
    (rdrv_zero r) hg.ctrace hg.cont.continuousOn hg.zero ENNReal.coe_lt_top ENNReal.coe_lt_top hT
  rwa [rdrv_toNNReal] at h

theorem IsGoodSample.contactT_pos (hg : IsGoodSample r A w γ) : 0 < contactT γ A (recS r) := by
  have h := firstContactTime_pos hg.continuous_γ.continuousAt hg.ctrace.1
    ((isCompact_Icc (a := (0 : ℝ≥0)) (b := recS r)).image hg.continuous_A).isBounded
  simpa only [contactT, image_image, Function.comp_def] using h

end Good

/-- **One sample's read-back analysis.** On a good sample with relative coordinates: the clock is `0` at `0`,
strictly increasing and continuous before the contact; the record and relative driver reconstruct the physical trace
at every clock value and every live relative time; GB6's separation gauge at the record's own time is continuous and
positive before `L`; at a finite `L` it tends to `0`. -/
theorem sample_readout {r : RecData} {A : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {D : ℝ≥0 → ℝ} {L : ℝ≥0∞}
    (hg : IsGoodSample r A w γ) (hC : IsSampleCoord r A w γ D L) :
    rclk r w 0 = 0 ∧ StrictMonoOn (rclk r w) {t | (t : ℝ≥0∞) < contactT γ A (recS r)} ∧
      ContinuousOn (rclk r w) {t | (t : ℝ≥0∞) < contactT γ A (recS r)} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < contactT γ A (recS r) → physicalTrace (recS r) (rclk r w t).toNNReal (r, D) = γ t) ∧
      (∀ u : ℝ≥0, (u : ℝ≥0∞) < L → ∃ t : ℝ≥0, (t : ℝ≥0∞) < contactT γ A (recS r) ∧ rclk r w t = u ∧
        physicalTrace (recS r) u (r, D) = γ t) ∧
      ContinuousOn (fun t => separationRead (recS r) t (r, D)) {t | (t : ℝ≥0∞) < L} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L → 0 < separationRead (recS r) t (r, D)) ∧
      ∀ T : ℝ≥0, (T : ℝ≥0∞) = L → Tendsto (fun t => separationRead (recS r) t (r, D)) (𝓝[<] T) (𝓝 0) := by
  classical
  have hU := continuous_rdrv r
  have hU0 := rdrv_zero r
  have hs0 := hg.pos
  have hsR : (0 : ℝ) < (recS r : ℝ) := by exact_mod_cast hs0
  have htip := hg.tip
  have hd : ∀ T : ℝ≥0, (T : ℝ≥0∞) < (contactT γ A (recS r)) → Disjoint (closure (fwdHull (rdrv r) (recS r)))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w) T)) := fun T hT => hg.disjoint hT
  obtain ⟨ha0, ham, hac⟩ := relative_clock_regular hU hU0 hsR htip hg.cont hg.zero hg.ctrace hg.contactT_pos hd
  change rclk r w 0 = 0 at ha0
  change StrictMonoOn (rclk r w) {t | (t : ℝ≥0∞) < contactT γ A (recS r)} at ham
  change ContinuousOn (rclk r w) {t | (t : ℝ≥0∞) < contactT γ A (recS r)} at hac
  have hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (contactT γ A (recS r)) →
      physicalTrace (recS r) (rclk r w t).toNNReal (r, D) = γ t := by
    intro t ht
    obtain ⟨S, htS, hS⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    obtain ⟨T, hST, hT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hS
    have hST' : S < T := ENNReal.coe_lt_coe.1 hST
    have htS' : t < S := ENNReal.coe_lt_coe.1 htS
    have hS0 : 0 < S := lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ t) htS'
    have hT0 : 0 < T := hS0.trans hST'
    have hlife : ENNReal.ofReal (rclk r w S) < L := (hC.hulls S hS).2.1
    have hD : ∀ q ∈ Icc (0 : ℝ) S, fwdHull (Ito.rpath D) (relClock (rdrv r) (recS r) (Ito.rpath w) q) =
        relMap (rdrv r) (recS r) '' fwdHull (Ito.rpath w) q := by
      intro q hq
      have hqS : q.toNNReal ≤ S := Real.toNNReal_le_iff_le_coe.2 hq.2
      have hqTc : (q.toNNReal : ℝ≥0∞) < (contactT γ A (recS r)) := (ENNReal.coe_le_coe.2 hqS).trans_lt hS
      have he := (hC.hulls q.toNNReal hqTc).2.2
      rw [← Real.coe_toNNReal q hq.1]
      exact he
    exact physicalTrace_of_relHulls (recS r) hs0 hg.chart htip hg.cont hg.zero hg.ctrace hT0 hS0 hST' (hd T hT)
      hC.cont hC.zero hlife hD htS'.le
  have hcap : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → ∃ t : ℝ≥0, (t : ℝ≥0∞) < (contactT γ A (recS r)) ∧ rclk r w t = u ∧
      physicalTrace (recS r) u (r, D) = γ t := by
    intro u hu
    obtain ⟨T, hT, huT⟩ := hC.range u hu
    obtain ⟨t, ht, hat⟩ := exists_clock_eq (hac.mono fun q hq =>
      (ENNReal.coe_le_coe.2 hq.2).trans_lt hT) ha0 huT.le
    have htTc : (t : ℝ≥0∞) < (contactT γ A (recS r)) := (ENNReal.coe_le_coe.2 ht.2).trans_lt hT
    refine ⟨t, htTc, hat, ?_⟩
    have hr := hread t htTc
    have hat' : rclk r w t = u := hat
    rw [hat', Real.toNNReal_coe] at hr
    exact hr
  have hγc := hg.continuous_γ
  have hX : ContinuousOn (fun u => physicalTrace (recS r) u (r, D)) {u | (u : ℝ≥0∞) < L} :=
    continuousOn_liveReadback (X := fun u => physicalTrace (recS r) u (r, D)) ha0 ham hac hC.range hγc hread
  have hA : ContinuousOn (fun v => recordTrace v r) (Iic (recS r)) :=
    (hg.continuous_A.continuousOn).congr fun v _ => hg.recordTrace_eq v
  have hA0 : recordTrace 0 r = 0 := by rw [hg.recordTrace_eq]; exact hg.trace.1
  refine ⟨ha0, ham, hac, hread, hcap, continuousOn_separationRead (recS r) _ _ hX hA, ?_, ?_⟩
  · intro t ht
    apply separationRead_pos (recS r) t _ _ (hX.mono (fun u hu => (ENNReal.coe_le_coe.2 hu).trans_lt ht)) hA
    intro u hu v hv
    obtain ⟨q, hq, _, hXu⟩ := hcap u ((ENNReal.coe_le_coe.2 hu).trans_lt ht)
    rw [hXu, hg.recordTrace_eq v]
    intro hzero
    exact notMem_of_lt_firstContactTime hq ⟨v, ⟨zero_le, hv⟩,
      ((SourceC.sphereInv_eq_iff _ _).2 hzero).symm⟩
  · intro T hTL
    have hXI : ContinuousOn (fun u => physicalTrace (recS r) u (r, D)) (Iio T) :=
      hX.mono (fun u hu => by rw [← hTL]; exact ENNReal.coe_lt_coe.2 hu)
    have hbound : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (contactT γ A (recS r)) → 0 ≤ rclk r w t ∧ rclk r w t < T := by
      intro t ht
      obtain ⟨hn, hl, _⟩ := hC.hulls t ht
      refine ⟨hn, ?_⟩
      rw [← hTL] at hl
      simpa only [ENNReal.coe_toReal] using (ENNReal.ofReal_lt_iff_lt_toReal hn ENNReal.coe_ne_top).1 hl
    have hex : ∀ u : ℝ≥0, u < T → ∃ t : ℝ≥0, (t : ℝ≥0∞) < (contactT γ A (recS r)) ∧ rclk r w t = u ∧
        physicalTrace (recS r) u (r, D) = γ t := fun u hu => hcap u (by rw [← hTL]; exact ENNReal.coe_lt_coe.2 hu)
    let c : ℝ≥0 → ℝ≥0 := fun u => if hu : u < T then (hex u hu).choose else 0
    have hcspec : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < (contactT γ A (recS r)) ∧ rclk r w (c u) = u ∧
        physicalTrace (recS r) u (r, D) = γ (c u) := by
      intro u hu
      simpa only [c, hu, ↓reduceDIte] using (hex u hu).choose_spec
    have hc : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < (contactT γ A (recS r)) ∧ rclk r w (c u) = u :=
      fun u hu => ⟨(hcspec u hu).1, (hcspec u hu).2.1⟩
    have hu : ∀ᶠ u : ℝ≥0 in 𝓝[<] T, u < T := self_mem_nhdsWithin
    have he : (fun u => γ (c u)) =ᶠ[𝓝[<] T] (fun u => physicalTrace (recS r) u (r, D)) :=
      hu.mono (fun u hu => (hcspec u hu).2.2.symm)
    rcases eq_top_or_lt_top (contactT γ A (recS r)) with htop | hfin
    · have hm : StrictMonoOn (rclk r w) {t | (t : ℝ≥0∞) < ⊤} := by simpa only [htop] using ham
      have hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ⊤ → 0 ≤ rclk r w t ∧ rclk r w t < T := by
        simpa only [htop] using hbound
      have hc' : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < ⊤ ∧ rclk r w (c u) = u := by simpa only [htop] using hc
      have hinf := hg.trans.comp (tendsto_clockInverse_top hm hb hc')
      exact tendsto_separationRead_escape (recS r) _ _ hs0 hXI hA hA0
        (hinf.congr' (he.mono (fun _ h => congrArg norm h)))
    · let C := (contactT γ A (recS r)).toNNReal
      have hTc : (contactT γ A (recS r)) = (C : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin.ne).symm
      have hm : StrictMonoOn (rclk r w) {t | (t : ℝ≥0∞) < (C : ℝ≥0∞)} := by simpa only [hTc] using ham
      have hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (C : ℝ≥0∞) → 0 ≤ rclk r w t ∧ rclk r w t < T := by
        simpa only [hTc] using hbound
      have hc' : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < (C : ℝ≥0∞) ∧ rclk r w (c u) = u := by
        simpa only [hTc] using hc
      have hlim := ((hγc.tendsto C).comp (tendsto_clockInverse_finite hm hb hc')).congr' he
      have hAc : IsCompact ((fun v => (A v : OnePoint ℂ)) '' Icc 0 (recS r)) := by
        have hcompact : IsCompact (A '' Icc 0 (recS r)) := isCompact_Icc.image hg.continuous_A
        simpa only [image_image] using hcompact.image OnePoint.continuous_coe
      obtain ⟨v, hv, hcontact⟩ := firstContactTime_mem
        (continuous_sphereInv.comp (OnePoint.continuous_coe.comp hγc)) hAc.isClosed hTc
      refine tendsto_separationRead_contact (recS r) _ _ hs0 hXI hA hv.2 hlim ?_
      rw [hg.recordTrace_eq v]
      exact (SourceC.sphereInv_eq_iff _ _).1 hcontact.symm

end InteractingSLE.Theorem14.BW1Ver
