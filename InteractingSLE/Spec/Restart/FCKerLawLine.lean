/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCKerLawC
import InteractingSLE.Spec.Restart.FCK2CapRead

/-!
# The corrected forward inputs from the laws on deterministic physical lines

Packet PROVE-T15-FCKER2. Both fields of `FCK2CapForwardInputsC` follow from the standard deterministic-line forms
(Aux. 77/79 at physical later lines, the inputs of `DomainMarkov.Aux79.hasSafeLaw_of_lineLaw` and
`hasSafeMembers_of_lineMembers`) together with the observation of the capacity-time driver on the clock cuts:

* `measurable_hitT`: the first passage of a continuous nondecreasing measurable clock is measurable;
* **`hasFCK2CapForwardKernel_of_lineLaw`**: the Gaussian field (the inverse clock is `hitT`, the protected sets are
  the line safe events, the kernels are `cfAt` at the clock value, truncated to modulus `1`);
* **`hasFCK2CapForwardMembers_of_lineMembers`**: the corrected member field.

Thus the corrected statement reduces to the physical-line conditional law, the physical-line member identities, the
clock-cut observations, reach and force regularity, for each canonical chart path. None of these is asserted here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb

open LQGMetric WangWu.ChartConst DomainMarkov DomainMarkov.K2 DomainMarkov.Aux79 Coupling LocalSets

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The first passage time of a continuous nondecreasing measurable clock is measurable (it is `0` on the event where
the level is never reached). -/
theorem measurable_hitT {Qc : ℝ≥0 → Ω → ℝ≥0} (hQm : ∀ t, Measurable (Qc t))
    (hc : ∀ ω, Continuous fun t => Qc t ω) (hmono : ∀ ω, Monotone fun t => Qc t ω) (q : ℝ≥0) :
    Measurable (hitT Qc q) := by
  have hreach : {ω | ∃ t, q ≤ Qc t ω} = ⋃ n : ℕ, {ω | q ≤ Qc n ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨t, ht⟩
      obtain ⟨n, hn⟩ := exists_nat_ge t
      exact ⟨n, ht.trans (hmono ω hn)⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, hn⟩
  have hR : MeasurableSet {ω | ∃ t, q ≤ Qc t ω} := by
    rw [hreach]
    exact MeasurableSet.iUnion fun n => measurableSet_le measurable_const (hQm n)
  refine measurable_of_Iic fun t => ?_
  have he : hitT Qc q ⁻¹' Iic t =
      ({ω | ∃ s, q ≤ Qc s ω} ∩ {ω | q ≤ Qc t ω}) ∪ {ω | ∃ s, q ≤ Qc s ω}ᶜ := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff]
    by_cases hr : ∃ s, q ≤ Qc s ω
    · rw [← le_Qc_iff (hc ω) (hmono ω) hr]
      simp only [hr, true_and, not_true_eq_false, or_false]
    · have h0 : hitT Qc q ω = 0 := by
        have hempty : {s | q ≤ Qc s ω} = ∅ := by
          ext s
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
          exact fun h => hr ⟨s, h⟩
        simp only [hitT, hempty, NNReal.sInf_empty]
      simp only [h0, zero_le, hr, false_and, not_false_eq_true, or_true]
  rw [he]
  exact (hR.inter (measurableSet_le measurable_const (hQm t))).union hR.compl

omit mΩ in
/-- The clock at the strict upper dyadic times after the first passage tends to the level. -/
theorem tendsto_Qc_dyF_hitT {Qc : ℝ≥0 → Ω → ℝ≥0} {q : ℝ≥0} {ω : Ω} (hc : Continuous fun t => Qc t ω)
    (hm : Monotone fun t => Qc t ω) (h0 : Qc 0 ω = 0) (hr : ∃ t, q ≤ Qc t ω) :
    Tendsto (fun n => Qc (dyF n (hitT Qc q ω)) ω) atTop (𝓝 q) := by
  have h := (hc.tendsto (hitT Qc q ω)).comp (tendsto_dyF (hitT Qc q ω))
  rwa [Qc_hitT hc hm h0 hr] at h

section Gaussian

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ≥0∞} {F : Set Ω} {Qc : ℝ≥0 → Ω → ℝ≥0} {𝓖 : Filtration ℝ≥0 mΩ}

/-- **The Gaussian forward kernel from the conditional law on deterministic physical lines.** Let `Qc` be a continuous
nondecreasing clock from `0` adapted to a physical filtration `𝓖` which observes the retained history and the driver
on the clock cuts. Suppose that on the live event `F` the clock reaches every level below the lifetime, the
continuation is regular, and at every physical time `t`, given forward marks `𝓜 t ⊇ 𝓖 t`, the field pairing has
the coupling characteristic function at the clock value on the line safe event. Then the pairing has the forward
kernel of `FCK2CapForwardInputsC.gaussian` in the completed retained-driver filtration. -/
theorem hasFCK2CapForwardKernel_of_lineLaw {d : PairData Ω} (hd : d.IsMeasGood)
    (hm : ∀ r, Measurable (W r)) (hc : ∀ ω, Continuous fun t => Qc t ω)
    (hmono : ∀ ω, Monotone fun t => Qc t ω) (h0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t)) (hret : Measurable[𝓖 0] (retHist d))
    (hobs : ∀ r t, Measurable[𝓖 t] ({ω | r ≤ Qc t ω}.indicator (W r)))
    (hF : MeasurableSet[𝓖 0] F) (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0)
    (hS : ∀ t, MeasurableSet[𝓖 t] (lineSafe Qc W U (tsupport ψ) t))
    (hreach : ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < U ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR U ω)
    (𝓜 : ℝ≥0 → MeasurableSpace Ω) (h𝓖𝓜 : ∀ t, 𝓖 t ≤ 𝓜 t) (h𝓜 : ∀ t, 𝓜 t ≤ mΩ) {X : Ω → ℂ}
    (hline : ∀ t, 0 < t → ∀ᵐ ω ∂P, ω ∈ F → ω ∈ lineSafe Qc W U (tsupport ψ) t →
      P[X | 𝓜 t] ω = cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (Qc t) ω) :
    HasFCK2CapForwardKernel P (fcRetainedDriverFiltration P hd W hm q)
      {ω | ω ∈ F ∧ ω ∈ avoidSet W U ψ q} X (cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (fun _ => q)) := by
  classical
  set u := bheProc κ ρL ρR W VL VR with hu
  set Av : ℝ≥0 → Set Ω := fun t => {_ω | 0 < t} ∩ (F ∩ lineSafe Qc W U (tsupport ψ) t) with hAv_def
  set K : ℝ≥0 → Ω → ℂ := fun t ω =>
    if ‖cfAt κ W u ψ 1 (Qc t) ω‖ ≤ 1 then cfAt κ W u ψ 1 (Qc t) ω else 0 with hK_def
  have hQm : ∀ t, Measurable (Qc t) := fun t => (hQa t).mono (𝓖.le t) le_rfl
  have hτ := measurable_hitT hQm hc hmono q
  have hAv : ∀ t, MeasurableSet[𝓜 t] (Av t) := fun t =>
    h𝓖𝓜 t _ ((MeasurableSet.const (0 < t)).inter ((𝓖.mono (zero_le (a := t)) _ hF).inter (hS t)))
  have hb : ∀ t ω, ω ∈ Av t → ‖K t ω‖ ≤ 1 := fun t ω _ => by
    simp only [hK_def]
    split_ifs with h
    · exact h
    · rw [norm_zero]; exact zero_le_one
  have hKeq : ∀ t ω, ω ∈ Av t → IsForceReg W VL VR U ω → K t ω = cfAt κ W u ψ 1 (Qc t) ω :=
    fun t ω hω hp => by
      have hle := norm_cfAt_le_one_of_isForceReg (κ := κ) u ψ hp hω.2.2.1 hω.2.2.2
      simp only [hK_def, hle, ↓reduceIte]
  have hdet : ∀ t, ∀ᵐ ω ∂P, ω ∈ Av t → P[X | 𝓜 t] ω = K t ω := fun t => by
    rcases eq_or_ne t 0 with rfl | ht
    · exact ae_of_all P fun ω hω => absurd (show (0 : ℝ≥0) < 0 from hω.1) (lt_irrefl 0)
    filter_upwards [hline t (pos_iff_ne_zero.2 ht), hreg] with ω hl hp hω
    rw [hKeq t ω hω (hp hω.2.1), hl hω.2.1 hω.2.2]
  refine fcCapForwardKernel_of_observed_cuts hd W hm hQa hret hobs hτ
    (fun ω hr t => (le_Qc_iff (hc ω) (hmono ω) hr).symm) h𝓖𝓜 h𝓜 hAv hb hdet ?_ ?_
  · filter_upwards [hreach] with ω hω hS'
    exact hω hS'.1 hS'.2.1
  · filter_upwards [hreach, hreg] with ω hr hp hS'
    obtain ⟨hωF, hav⟩ := hS'
    have hp' := hp hωF
    have hrω := hr hωF hav.1
    have hQt := tendsto_Qc_dyF_hitT (hc ω) (hmono ω) (h0 ω) hrω
    have hsafe := eventually_mem_lineSafe ψ.hasCompactSupport.isCompact (tsupport_subset_H ψ) hp' hav.1 hav.2
      (fun n => dyF n (hitT Qc q ω)) hQt
    have hev : ∀ᶠ n in atTop, ω ∈ Av (dyF n (hitT Qc q ω)) := hsafe.mono fun n hn =>
      ⟨(zero_le (a := hitT Qc q ω)).trans_lt (lt_dyF n _), hωF, hn⟩
    refine ⟨hev, ?_⟩
    have hlim := (tendsto_cfAt_of_isForceReg (κ := κ) (ρL := ρL) (ρR := ρR) (u := u)
      (isBoundedHarmonicExtension_bheProc) ψ hp' hav.1 hav.2 hQt).2
    refine hlim.congr' ?_
    filter_upwards [hev] with n hn
    exact (hKeq _ ω hn hp').symm

end Gaussian

section Members

variable {W : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ≥0∞} {F : Set Ω} {Qc : ℝ≥0 → Ω → ℝ≥0}
  {𝓖 : Filtration ℝ≥0 mΩ}

/-- **The corrected member field from the member identities on deterministic physical lines.** Same clock and
observations as `hasFCK2CapForwardKernel_of_lineLaw`; if at every physical time `t` the member identity holds on
every event of the forward marks inside the live line safe event of the balls, the pairing has the forward member
data of `FCK2CapForwardInputsC.members`. -/
theorem hasFCK2CapForwardMembers_of_lineMembers {nL nR : ℕ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {d : PairData Ω} (hd : d.IsMeasGood)
    (hm : ∀ r, Measurable (W r)) (hc : ∀ ω, Continuous fun t => Qc t ω)
    (hmono : ∀ ω, Monotone fun t => Qc t ω) (h0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t)) (hret : Measurable[𝓖 0] (retHist d))
    (hobs : ∀ r t, Measurable[𝓖 t] ({ω | r ≤ Qc t ω}.indicator (W r)))
    (hF : MeasurableSet[𝓖 0] F) (Fb : Finset (ℚ × ℚ × ℚ)) (hFb : ballsK Fb ⊆ QuantumZipper.H)
    (q : ℝ≥0) (hS : ∀ t, MeasurableSet[𝓖 t] (lineSafe Qc W U (ballsK Fb) t))
    (hreach : ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < U ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR U ω)
    (𝓜 : ℝ≥0 → MeasurableSpace Ω) (h𝓖𝓜 : ∀ t, 𝓖 t ≤ 𝓜 t) (h𝓜 : ∀ t, 𝓜 t ≤ mΩ) {X Y : Ω → ℂ} {c : ℂ}
    (hline : ∀ t, 0 < t → ∀ E, MeasurableSet[𝓜 t] E →
      (∀ᵐ ω ∂P, ω ∈ E → ω ∈ F ∧ ω ∈ lineSafe Qc W U (ballsK Fb) t) →
      ∫ ω in E, X ω ∂P = c * ∫ ω in E, Y ω ∂P) :
    HasFCK2CapForwardMembers P (fcRetainedDriverFiltration P hd W hm q)
      {ω | ω ∈ F ∧ (q : ℝ≥0∞) < U ω ∧
        Disjoint (ballsK Fb) (QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) q)} X Y c := by
  set Av : ℝ≥0 → Set Ω := fun t => {_ω | 0 < t} ∩ (F ∩ lineSafe Qc W U (ballsK Fb) t) with hAv_def
  have hQm : ∀ t, Measurable (Qc t) := fun t => (hQa t).mono (𝓖.le t) le_rfl
  have hτ := measurable_hitT hQm hc hmono q
  have hAv : ∀ t, MeasurableSet[𝓜 t] (Av t) := fun t =>
    h𝓖𝓜 t _ ((MeasurableSet.const (0 < t)).inter ((𝓖.mono (zero_le (a := t)) _ hF).inter (hS t)))
  have hline' : ∀ t E, MeasurableSet[𝓜 t] E → (∀ᵐ ω ∂P, ω ∈ E → ω ∈ Av t) →
      ∫ ω in E, X ω ∂P = c * ∫ ω in E, Y ω ∂P := by
    intro t E hE hEA
    rcases eq_or_ne t 0 with rfl | ht
    · have hE0 : P E = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [hEA] with ω hω hωE
        exact lt_irrefl 0 (show (0 : ℝ≥0) < 0 from (hω hωE).1)
      rw [setIntegral_measure_zero _ hE0, setIntegral_measure_zero _ hE0, mul_zero]
    · exact hline t (pos_iff_ne_zero.2 ht) E hE (hEA.mono fun ω hω hωE => (hω hωE).2)
  refine ⟨𝓜, Av, hitT Qc q, h𝓜, hτ, hline', ?_, ?_⟩
  · intro D hD hs n k
    refine fcCap_censored_versions_of_observed_cuts hd W hm hQa hret hobs
      (fun ω hr t => (le_Qc_iff (hc ω) (hmono ω) hr).symm) h𝓖𝓜 hAv hD ?_ n k
    filter_upwards [hs, hreach] with ω hsω hr hωD
    exact hr (hsω hωD).1 (hsω hωD).2.1
  · filter_upwards [hreach, hreg] with ω hr hp hS'
    obtain ⟨hωF, hqU, hdis⟩ := hS'
    have hQt := tendsto_Qc_dyF_hitT (hc ω) (hmono ω) (h0 ω) (hr hωF hqU)
    have hsafe := eventually_mem_lineSafe (isCompact_ballsK Fb) hFb (hp hωF) hqU hdis
      (fun n => dyF n (hitT Qc q ω)) hQt
    exact hsafe.mono fun n hn => ⟨(zero_le (a := hitT Qc q ω)).trans_lt (lt_dyF n _), hωF, hn⟩

end Members

end InteractingSLE.Restart.FCPlumb
