/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.CondDet
import InteractingSLE.Spec.Restart.FCDetDriver
import InteractingSLE.Spec.Restart.FCDetTransfer
import InteractingSLE.Spec.Restart.Integrate
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Spec.Coupling.LawUniqueTransfer

/-!
# First-contact determination: the driver-to-path bridge

The path code and driver code are related under the conditional field law by the two canonical-code properties.
The relation records only strict pre-lifetime trace evaluations, where `traceAt` is determined by the driver prefix.
The actual path match is then recovered from dyadic evaluations and continuity on the closed available interval.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

open Sec2.Assembly

/-- The Borel relation between a path code and a driver code: their lifetimes agree, the decoded path starts at the
seed `0`, and at each dyadic time strictly before the common lifetime its value is the trace evaluation of the
decoded driver. -/
def PathDriverCodeLink (p : (PCode × PCode) × ℝ≥0∞) (q : PCode × ℝ≥0∞) : Prop :=
  p.2 = q.2 ∧ decPath p 0 = 0 ∧
    ∀ n k : ℕ, (dyad n k : ℝ≥0∞) < q.2 →
      decPath p (dyad n k) = LP.traceAt (dyad n k) (fun t => dec q.1 t)

theorem measurableSet_pathDriverCodeLink {C S : Type*} [MeasurableSpace C] [MeasurableSpace S]
    {F : C × S → (PCode × PCode) × ℝ≥0∞} (hF : Measurable F)
    {G : C × S → PCode × ℝ≥0∞} (hG : Measurable G) :
    MeasurableSet {p : C × S | PathDriverCodeLink (F p) (G p)} := by
  have hlife : MeasurableSet {p : C × S | (F p).2 = (G p).2} :=
    measurableSet_eq_fun (measurable_snd.comp hF) (measurable_snd.comp hG)
  have hstart : MeasurableSet {p : C × S | decPath (F p) 0 = 0} :=
    measurableSet_eq_fun ((measurable_decPath 0).comp hF) measurable_const
  have hdecoded : Measurable fun p : C × S => fun t : ℝ≥0 => dec (G p).1 t :=
    measurable_pi_iff.2 fun t =>
      (measurable_dec.comp ((measurable_fst.comp hG).prodMk measurable_const))
  have htrace (n k : ℕ) : Measurable fun p : C × S =>
      LP.traceAt (dyad n k) (fun t => dec (G p).1 t) :=
    (LP.measurable_traceAt _).comp hdecoded
  have hd : ∀ n k : ℕ, MeasurableSet {p : C × S |
      (dyad n k : ℝ≥0∞) < (G p).2 →
        decPath (F p) (dyad n k) = LP.traceAt (dyad n k) (fun t => dec (G p).1 t)} := fun n k => by
    have h1 : MeasurableSet {p : C × S | (dyad n k : ℝ≥0∞) < (G p).2} :=
      measurableSet_lt measurable_const (measurable_snd.comp hG)
    have h2 : MeasurableSet {p : C × S |
        decPath (F p) (dyad n k) = LP.traceAt (dyad n k) (fun t => dec (G p).1 t)} :=
      measurableSet_eq_fun ((measurable_decPath _).comp hF) (htrace n k)
    have heq : {p : C × S | (dyad n k : ℝ≥0∞) < (G p).2 →
        decPath (F p) (dyad n k) = LP.traceAt (dyad n k) (fun t => dec (G p).1 t)} =
        {p | (dyad n k : ℝ≥0∞) < (G p).2}ᶜ ∪
          {p | decPath (F p) (dyad n k) = LP.traceAt (dyad n k) (fun t => dec (G p).1 t)} := by
      ext p
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
    rw [heq]
    exact h1.compl.union h2
  have heq : {p : C × S | PathDriverCodeLink (F p) (G p)} =
      {p | (F p).2 = (G p).2} ∩ {p | decPath (F p) 0 = 0} ∩
        ⋂ n : ℕ, ⋂ k : ℕ, {p | (dyad n k : ℝ≥0∞) < (G p).2 →
          decPath (F p) (dyad n k) = LP.traceAt (dyad n k) (fun t => dec (G p).1 t)} := by
    ext p
    simp only [PathDriverCodeLink, mem_ofPred_eq, mem_inter_iff, mem_iInter, and_assoc]
  rw [heq]
  exact (hlife.inter hstart).inter (MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => hd n k)

private theorem uc_of_driverCodeMatch {p : PCode} {W : ℝ≥0 → ℝ} {L Lcode : ℝ≥0∞}
    (hm : IsDriverCodeMatch (p, Lcode) W L) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < L)
    (hW : ContinuousOn W (Iic T)) : UC p T := by
  have he := uc_enc hW
  intro m
  obtain ⟨N, hN⟩ := he m
  refine ⟨N, fun n k n' k' hnk hnk' hclose => ?_⟩
  have hlt : ∀ {n k : ℕ}, dyad n k ≤ T → (dyad n k : ℝ≥0∞) < L := fun hle =>
    (ENNReal.coe_le_coe.mpr hle).trans_lt hT
  have h1 := hm.2.2 n k (hlt hnk)
  have h2 := hm.2.2 n' k' (hlt hnk')
  calc
    |p n k - p n' k'| = |W (dyad n k) - W (dyad n' k')| := by rw [h1, h2]
    _ ≤ 1 / (m + 1) := by simpa only [enc] using hN n k n' k' hnk hnk' hclose

/-- A driver code that matches a continuous driver decodes to that driver at every strict pre-lifetime time. The
uniform-continuity argument is restricted to a dyadic compact prefix containing the queried time. -/
theorem dec_eq_of_driverCodeMatch {p : PCode} {W : ℝ≥0 → ℝ} {L Lcode : ℝ≥0∞}
    (hm : IsDriverCodeMatch (p, Lcode) W L)
    (hWc : ContinuousOn W {t | (t : ℝ≥0∞) < L}) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < L) :
    dec p t = W t := by
  obtain ⟨n, k, htk, hTL⟩ := exists_dyad_btwn ht
  have hWIic : ContinuousOn W (Iic (dyad n k)) := by
    intro s hs
    have hs' : s ≤ dyad n k := by exact_mod_cast hs
    have hst : (s : ℝ≥0∞) < L := (ENNReal.coe_le_coe.mpr hs').trans_lt hTL
    have hopen : IsOpen {u : ℝ≥0 | (u : ℝ≥0∞) < L} :=
      isOpen_lt ENNReal.continuous_coe continuous_const
    exact (hWc s hst).continuousAt (hopen.mem_nhds hst) |>.continuousWithinAt
  have hUC := uc_of_driverCodeMatch hm hTL hWIic
  have hseqIn : Tendsto (fun i => dyad i (flr i t)) atTop
      (𝓝[{s : ℝ≥0 | (s : ℝ≥0∞) < L}] t) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨tendsto_dyad_flr t, Eventually.of_forall fun i => ?_⟩
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.mpr (dyad_flr_le i t)) ht
  have hWseq := (hWc t ht).tendsto.comp hseqIn
  have hPseq := hUC.tendsto_flr htk.le
  have hseqeq : ∀ i : ℕ, p i (flr i t) = W (dyad i (flr i t)) := fun i => by
    have hti : (t : ℝ≥0∞) < L := ht
    exact (hm.2.2 i (flr i t)
      (lt_of_le_of_lt (ENNReal.coe_le_coe.mpr (dyad_flr_le i t)) hti)).symm
  have hWseq' : Tendsto (fun i => p i (flr i t)) atTop (𝓝 (W t)) :=
    hWseq.congr' (Eventually.of_forall fun i => (hseqeq i).symm)
  exact tendsto_nhds_unique hPseq hWseq'

/-- Strict dyadic path-code agreement and equality at time zero determine a path on the entire closed available
interval. At a positive finite endpoint, use the dyadic sequence approaching from below. -/
theorem codeMatch_of_eq_dyad_lt {p : (PCode × PCode) × ℝ≥0∞} {Γ : ℝ≥0 → ℂ} {U : ℝ≥0∞}
    (hU : U = p.2) (hΓc : ContinuousOn Γ {t | (t : ℝ≥0∞) ≤ U})
    (hzero : Γ 0 = decPath p 0)
    (hdyad : ∀ n k : ℕ, (dyad n k : ℝ≥0∞) < U → Γ (dyad n k) = decPath p (dyad n k)) :
    IsCodeMatch p Γ U := by
  refine ⟨hU, fun t ht => ?_⟩
  by_cases htlt : (t : ℝ≥0∞) < U
  · have hseqIn : Tendsto (fun n => dyad n (flr n t)) atTop
        (𝓝[{s : ℝ≥0 | (s : ℝ≥0∞) ≤ U}] t) := by
      apply tendsto_nhdsWithin_iff.2
      refine ⟨tendsto_dyad_flr t, Eventually.of_forall fun n => ?_⟩
      exact (ENNReal.coe_le_coe.mpr (dyad_flr_le n t)).trans ht
    have hΓlim := (hΓc t ht).tendsto.comp hseqIn
    have hPcont := continuousOn_decPath p
    have hseqInP : Tendsto (fun n => dyad n (flr n t)) atTop
        (𝓝[{s : ℝ≥0 | (s : ℝ≥0∞) ≤ p.2}] t) := by
      convert hseqIn using 1
      congr 1
      ext s
      simp [hU]
    have hPlim := (hPcont t (hU ▸ ht)).tendsto.comp hseqInP
    have hseqeq : ∀ n : ℕ, Γ (dyad n (flr n t)) = decPath p (dyad n (flr n t)) := fun n =>
      hdyad n (flr n t) (lt_of_le_of_lt (ENNReal.coe_le_coe.mpr (dyad_flr_le n t)) htlt)
    have hPlim' : Tendsto (fun n => Γ (dyad n (flr n t))) atTop (𝓝 (decPath p t)) :=
      hPlim.congr' (Eventually.of_forall fun n => (hseqeq n).symm)
    exact tendsto_nhds_unique hΓlim hPlim'
  · have hEq : U = (t : ℝ≥0∞) := le_antisymm (le_of_not_gt htlt) ht
    by_cases hzeroT : t = 0
    · simpa [hzeroT] using hzero
    · have hpos : 0 < t := pos_iff_ne_zero.mpr hzeroT
      let q : ℕ → ℝ≥0 := fun n => LP.dyadicBelow n t
      have hqIn : Tendsto q atTop (𝓝[{s : ℝ≥0 | (s : ℝ≥0∞) ≤ U}] t) := by
        apply tendsto_nhdsWithin_iff.2
        refine ⟨LP.tendsto_dyadicBelow t, Eventually.of_forall fun n => ?_⟩
        exact (ENNReal.coe_le_coe.mpr (LP.dyadicBelow_lt hpos n).le).trans_eq hEq.symm
      have hΓlim := (hΓc t ht).tendsto.comp hqIn
      have hqInP : Tendsto q atTop (𝓝[{s : ℝ≥0 | (s : ℝ≥0∞) ≤ p.2}] t) := by
        convert hqIn using 1
        congr 1
        ext s
        simp [hU]
      have hPlim := (continuousOn_decPath p t (hU ▸ ht)).tendsto.comp hqInP
      have hqeq : ∀ n : ℕ, Γ (q n) = decPath p (q n) := by
        intro n
        change Γ (dyad n (LP.dyadicIdx n t)) = decPath p (dyad n (LP.dyadicIdx n t))
        apply hdyad
        rw [hEq]
        exact ENNReal.coe_lt_coe.mpr (LP.dyadicBelow_lt hpos n)
      have hPlim' : Tendsto (fun n => Γ (q n)) atTop (𝓝 (decPath p t)) :=
        hPlim.congr' (Eventually.of_forall fun n => (hqeq n).symm)
      exact tendsto_nhds_unique hΓlim hPlim'

private theorem ae_pathDriverCodeLink_of_flowLine
    {S : Type} [MeasurableSpace S] {Q : Measure S} [IsProbabilityMeasure Q] {κ θ : ℝ}
    {c : BoundaryWord} (hc : c.IsSorted) {H : S → DistOn upperHalfPlaneOpens}
    {F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hF : IsCanonicalFlowCode κ θ F)
    {G : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hG : IsCanonicalDriverCode κ θ G)
    (hh : IsGFFWithBoundaryData Q H c.fn c.jumps) :
    ∀ᵐ s ∂Q, PathDriverCodeLink (F ((c, 0), H s)) (G (c, H s)) := by
  let pcode (s : S) := F ((c, 0), H s)
  let dcode (s : S) := G (c, H s)
  have hlife : Measurable fun s : S => (pcode s).2 :=
    measurable_snd.comp (hF.1.comp (measurable_const.prodMk hh.1))
  have htrivial : ∀ᵐ s ∂Q, IsCodeMatch (F ((c, 0), H s))
      (decPath (F ((c, 0), H s))) (F ((c, 0), H s)).2 :=
    ae_of_all _ fun _ => ⟨rfl, fun _ _ => rfl⟩
  have hflow := hF.2.1 c 0 hc Q H (fun s => decPath (F ((c, 0), H s)))
    (fun s => (F ((c, 0), H s)).2) hh hlife htrivial
  obtain ⟨h', 𝓕, W, VL, VR, B, htrans, hopt, hgen⟩ := hflow
  have htype : FCDet.IsFlowType κ θ c (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hdriver : IsFlowLineDriver κ c.fn c.jumps θ Q H W (fun s => (pcode s).2) :=
    FCDet.isFlowLineDriver_of_isOptionalHullCoupling htype htrans hopt
  have hmatch := hG.2.2 c Q H W (fun s => (pcode s).2) hdriver
  have hzeroW : ∀ᵐ s ∂Q, W 0 s = 0 := by
    have hpath := hopt.1.2.2.2.2
    filter_upwards [hpath] with s hs
    exact hs.1
  have hcontW : ∀ᵐ s ∂Q, ContinuousOn (fun t => W t s)
      {t | (t : ℝ≥0∞) < (pcode s).2} := by
    exact (LawUnique.IsIntegratedSLEEvolution.ae_continuousOn_driving hopt.1).mono fun s hs => hs.1
  have hgen' : ∀ᵐ s ∂Q, IsGeneratingTrace (fun t => W t s) ((pcode s).2)
      (fun t => decPath (pcode s) t) := by
    filter_upwards [hgen] with s hs
    simpa [pcode, sub_zero] using hs
  have hcontW' : ∀ᵐ s ∂Q, ContinuousOn (fun t => W t s) {t | (t : ℝ≥0∞) < (pcode s).2} := hcontW
  filter_upwards [hmatch, hgen', hzeroW, hcontW'] with s hm hg h0 hcW
  have hlifeEq : (pcode s).2 = (dcode s).2 := hm.1
  have hstart : decPath (pcode s) 0 = 0 := hg.1
  refine ⟨hlifeEq, hstart, fun n k hnk => ?_⟩
  have hnk' : (dyad n k : ℝ≥0∞) < (pcode s).2 := by rw [hlifeEq]; exact hnk
  have hdecode : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (pcode s).2 → dec (dcode s).1 t = W t s :=
    fun t ht => dec_eq_of_driverCodeMatch hm hcW ht
  have htr := LP.traceAt_eq_of_isGeneratingTrace hg hcW h0 hnk'
  calc
    decPath (pcode s) (dyad n k) = LP.traceAt (dyad n k) (fun t => W t s) := htr.symm
    _ = LP.traceAt (dyad n k) (fun t => dec (dcode s).1 t) := by
      apply LP.traceAt_congr
      intro t ht
      exact (hdecode t (lt_of_le_of_lt (ENNReal.coe_le_coe.mpr ht) hnk')).symm

/-! ### Transfer to an arbitrary continuation carrier -/

/-- **Generic driver-to-path determination bridge.** Suppose the conditional field is a GFF with the current word,
the chart path is the generating trace of a continuous driver, that driver matches a canonical driver code, and its
lifetime is the chart path's available lifetime. Then the chart path matches any canonical flow code at seed `0`.
Only the strict pre-lifetime trace relation is transferred through the conditional kernel; endpoint equality follows
from continuity. -/
theorem ae_codeMatch_of_driverCodeMatch_of_generatingTrace
    {Ω : Type*} {C S : Type} [MeasurableSpace Ω] [MeasurableSpace C] [MeasurableSpace S]
    {P : Measure Ω} [IsFiniteMeasure P] {M : Set Ω} (hM : MeasurableSet M)
    {β : Ω → C} {X : Ω → S} (hβ : Measurable β) (hX : Measurable X)
    {K : Kernel C S} [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K)
    {w : C → BoundaryWord} (hw : Measurable w) {H : S → DistOn upperHalfPlaneOpens} (hH : Measurable H)
    {Γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞}
    (hΓc : ∀ s, ContinuousOn (Γ s) {t | (t : ℝ≥0∞) ≤ U s})
    {W : ℝ≥0 → S → ℝ} {L : S → ℝ≥0∞}
    (hWc : ∀ s, ContinuousOn (fun t => W t s) {t | (t : ℝ≥0∞) < L s})
    {κ θ : ℝ}
    {F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hF : IsCanonicalFlowCode κ θ F)
    {G : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hG : IsCanonicalDriverCode κ θ G)
    (hgff : ∀ᵐ c ∂(P.restrict M).map β,
      (w c).IsSorted ∧ IsGFFWithBoundaryData (K c) H (w c).fn (w c).jumps)
    (hdriver : ∀ᵐ ω ∂P, ω ∈ M →
      IsDriverCodeMatch (G (w (β ω), H (X ω))) (fun t => W t (X ω)) (L (X ω)))
    (hWzero : ∀ᵐ ω ∂P, ω ∈ M → W 0 (X ω) = 0)
    (htrace : ∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (fun t => W t (X ω)) (L (X ω)) (Γ (X ω)))
    (hUL : ∀ᵐ ω ∂P, ω ∈ M → U (X ω) = L (X ω)) :
    ∀ᵐ ω ∂P, ω ∈ M →
      IsCodeMatch (F ((w (β ω), 0), H (X ω))) (Γ (X ω)) (U (X ω)) := by
  let PF : C × S → (PCode × PCode) × ℝ≥0∞ := fun p => F ((w p.1, 0), H p.2)
  let DG : C × S → PCode × ℝ≥0∞ := fun p => G (w p.1, H p.2)
  have hPF : Measurable PF := hF.1.comp (((hw.comp measurable_fst).prodMk measurable_const).prodMk
    (hH.comp measurable_snd))
  have hDG : Measurable DG := hG.1.comp ((hw.comp measurable_fst).prodMk (hH.comp measurable_snd))
  have hE := measurableSet_pathDriverCodeLink hPF hDG
  have hkernelLink : ∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ s ∂(K c),
      (c, s) ∈ {p : C × S | PathDriverCodeLink (PF p) (DG p)} := by
    filter_upwards [hgff] with c hc
    obtain ⟨hcs, hh⟩ := hc
    have hlocal := ae_pathDriverCodeLink_of_flowLine hcs hF hG hh
    filter_upwards [hlocal] with s hs
    exact hs
  have hlink := ae_mem_of_ae_ae_compProd hM hβ hX hlaw hE hkernelLink
  filter_upwards [hlink, hdriver, hWzero, htrace, hUL] with ω hrel hdrv hW0 hgen hlife hωM
  obtain ⟨hpL, hp0, hrelDyad⟩ := hrel hωM
  obtain ⟨hWL, _, _⟩ := hdrv hωM
  have hlifeCode : U (X ω) = (PF (β ω, X ω)).2 := (hlife hωM).trans (hWL.trans hpL.symm)
  have hdyad : ∀ n k : ℕ, (dyad n k : ℝ≥0∞) < U (X ω) →
      Γ (X ω) (dyad n k) = decPath (PF (β ω, X ω)) (dyad n k) := by
    intro n k hlt
    have hltL : (dyad n k : ℝ≥0∞) < L (X ω) := by rw [← hlife hωM]; exact hlt
    have htraceEq := LP.traceAt_eq_of_isGeneratingTrace (hgen hωM) (fun t ht => hWc (X ω) t ht) (hW0 hωM)
      hltL
    have hrelEq := hrelDyad n k (by rw [← hWL]; exact hltL)
    calc
      Γ (X ω) (dyad n k) = LP.traceAt (dyad n k) (fun t => W t (X ω)) := htraceEq.symm
      _ = LP.traceAt (dyad n k) (fun t => dec (DG (β ω, X ω)).1 t) := by
        apply LP.traceAt_congr
        intro t ht
        exact (dec_eq_of_driverCodeMatch (hdrv hωM) (hWc (X ω))
          (lt_of_le_of_lt (ENNReal.coe_le_coe.mpr ht) hltL)).symm
      _ = decPath (PF (β ω, X ω)) (dyad n k) := hrelEq.symm
  have hzero : Γ (X ω) 0 = decPath (PF (β ω, X ω)) 0 := by
    rw [(hgen hωM).1, hp0]
  exact codeMatch_of_eq_dyad_lt hlifeCode (hΓc (X ω)) hzero hdyad

end Restart

end InteractingSLE
