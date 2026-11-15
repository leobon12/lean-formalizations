/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2ImgEndTrace
import InteractingSLE.Spec.ZhanGT4.A2ImgEndRestart

/-!
# The image endpoint, part 4: the pathwise assembly from the restarts

Packet PROVE-A2-IMGEND. Source: Astra, *Follow-up 5* §1.1–§1.2 (L66–L196, `source/external/AstraIG1/ig1_followup5.txt`,
R73), in the reflected chart of A.2 part 1 (`A2P1.ae_exit_trace`: left marks strictly ordered, the last one carrying
the only non-admissible weight, one right mark). Deterministic: given a local path of the word before `τ > 0` whose
restarts at every positive rational time `q < τ` are canonical solution codes in `goodSet` (the output of
`ae_restart_codes`), the path extends to a solution of Definition 2.1 whose trace is a simple crosscut ending on `ℝ`
left of the last left mark (`exists_exit_trace_of_restarts`).

* `vL_last_lt_upTo`: the last left mark stays strictly left of the driver before `τ` (total left weight `≤ −2`);
* `noncoll_of_restarts`: the marks are strictly separated from the driver at every positive time before `τ`;
* `restartData_of_restarts`: the restarts give `RestartData`, hence (`isGeneratingTraceIcc_of_restarts`) a simple
  generating trace on `[0, q₀]` for every `q₀ < τ`;
* the extension: the local path up to a positive rational `q₀` followed by the canonical code at `q₀`
  (`Sec2.Assembly2.isIntegratedSLEPath_concat`); its trace is the join (`Sec7.IsGeneratingTraceIcc.join`) of the trace
  on `[0, q₀]` and the code's trace, and the code's left strip end (`exitCode`) gives the exit
  (`A2P1.exit_of_restart`, `A2P1.exists_extendFrom_eq_lt_last`), exactly as in `A2P1.ae_exit_trace`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A2ImgEnd

open QuantumZipper (H Hbar fwdHull fwdMapInv)
open Sec2 Sec2.Assembly Sec7.RandRestart Sec5.Prop49Exit
open Sec7 (IsGeneratingTraceIcc shiftNN joinTrace)

/-- Congruence of a closed-interval generating trace in the trace. -/
theorem isGeneratingTraceIcc_congr {w : ℝ≥0 → ℝ} {σ : ℝ≥0} {η η' : ℝ≥0 → ℂ} (h : IsGeneratingTraceIcc w σ η)
    (he : ∀ t : ℝ≥0, t ≤ σ → η' t = η t) : IsGeneratingTraceIcc w σ η' := by
  refine ⟨A2P1.isGeneratingTrace_congr h.1 fun t ht => he t (ENNReal.coe_le_coe.1 ht), ?_, ?_⟩
  · have e : η' '' Icc 0 σ = η '' Icc 0 σ := image_congr fun t ht => he t ht.2
    rw [e]; exact h.2.1
  · rw [he σ le_rfl]; exact h.2.2

section Path

variable {k : ℝ} {j : ℕ} {xL : Fin (j + 1) → ℝ} {xR : Fin 1 → ℝ} {ρL : Fin (j + 1) → ℝ} {ρR : Fin 1 → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin (j + 1) → ℝ≥0 → ℝ} {vR : Fin 1 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞}

/-- **The last left mark stays left of the driver before `τ`** (A2P1's `vL_last_lt` for local paths). -/
theorem vL_last_lt_upTo (hp : IsSLEPathUpTo k xL xR ρL ρR w vL vR b τ) (hsum : ∑ i, ρL i ≤ -2)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) : vL (Fin.last j) t < w t := by
  refine lt_of_le_of_ne (hp.vL_le_w ht _) fun heq => hp.not_threshold ht (Or.inl ?_)
  have hall : ∀ i, vL i t = w t := fun i =>
    le_antisymm (hp.vL_le_w ht i) (heq ▸ hp.antitone_vL ht (Fin.le_last i))
  have e : Finset.univ.filter (fun i => vL i t = w t) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => hall i
  show (∑ i ∈ Finset.univ.filter (fun i => vL i t = w t), ρL i) ≤ -2
  rw [e]
  exact hsum

/-- **The restart hypothesis** (the output of `ae_restart_codes` at one sample): at every positive rational time
`q < τ` the restarted word has a canonical solution code in `goodSet`, driven by the increments of `b` after `q`, of
lifetime at least `τ − q`, agreeing with the restarted local path before `τ − q`. -/
def RestartHyp (k : ℝ) (ρL : Fin (j + 1) → ℝ) (ρR : Fin 1 → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin (j + 1) → ℝ≥0 → ℝ)
    (vR : Fin 1 → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop :=
  ∀ q : ℚ≥0, 0 < q → ((q : ℝ≥0) : ℝ≥0∞) < τ →
    ∃ x ∈ CRel k (fun i => vL i q - w q) (fun j => vR j q - w q) ρL ρR, x ∈ goodSet k ρL ρR ∧
      (∀ t, cb x t = b (q + t) - b q) ∧ τ - (q : ℝ≥0) ≤ cζ x ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ - (q : ℝ≥0) →
        cw x t = w (q + t) - w q ∧ (∀ i, cvL x i t = vL i (q + t) - w q) ∧ ∀ j, cvR x j t = vR j (q + t) - w q

/-- A restart code is in `simpSet` (its start has the last left mark off the source). -/
theorem RestartHyp.mem_simpSet (hp : IsSLEPathUpTo k xL xR ρL ρR w vL vR b τ) (hsum : ∑ i, ρL i ≤ -2)
    {q : ℚ≥0} (hqτ : ((q : ℝ≥0) : ℝ≥0∞) < τ) {x : XCode (j + 1) 1}
    (hxC : x ∈ CRel k (fun i => vL i q - w q) (fun j => vR j q - w q) ρL ρR) (hxG : x ∈ goodSet k ρL ρR) :
    x ∈ simpSet := by
  rcases hxG.1 with h | h
  · refine absurd ?_ h
    have hst := (mem_cRelF_iff.2 hxC).2
    show (startOf x).1 (Fin.last j) < 0
    rw [hst]
    exact sub_neg.2 (vL_last_lt_upTo hp hsum hqτ)
  · exact h

/-- **Noncollision at every positive time before `τ`** from the restarts. -/
theorem noncoll_of_restarts (hp : IsSLEPathUpTo k xL xR ρL ρR w vL vR b τ) (hsum : ∑ i, ρL i ≤ -2)
    (hR : RestartHyp k ρL ρR w vL vR b τ) {t : ℝ≥0} (ht0 : 0 < t) (ht : (t : ℝ≥0∞) < τ) :
    (∀ i, vL i t < w t) ∧ ∀ j, w t < vR j t := by
  obtain ⟨q, hq0, hqt⟩ := exists_nnrat_btwn ht0
  have hq0' : (0 : ℚ≥0) < q := by exact_mod_cast hq0
  have hqτ : ((q : ℝ≥0) : ℝ≥0∞) < τ := lt_trans (ENNReal.coe_lt_coe.2 hqt) ht
  obtain ⟨x, hxC, hxG, -, hle, hag⟩ := hR q hq0' hqτ
  have hxS := RestartHyp.mem_simpSet hp hsum hqτ hxC hxG
  have hfp := hxC.1.2.2.isForcePath
  set u : ℝ≥0 := t - q with hu
  have htu : (q : ℝ≥0) + u = t := add_tsub_cancel_of_le hqt.le
  have huτ : (u : ℝ≥0∞) < τ - (q : ℝ≥0) := (Restart.coe_lt_sub_iff _ _).2 (by rw [htu]; exact ht)
  have hu0 : 0 < u := tsub_pos_of_lt hqt
  obtain ⟨-, hL, hR'⟩ := (mem_simpSet_iff.1 hxS).mem_H hfp.continuousOn_w hfp.w_zero hfp.continuousOn_vL
    hfp.continuousOn_vR hu0 (lt_of_lt_of_le huτ hle)
  obtain ⟨e1, e2, e3⟩ := hag u huτ
  rw [htu] at e1 e2 e3
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have := hL i; rw [e1, e2 i] at this; linarith
  · have := hR' j; rw [e1, e3 j] at this; linarith

/-- **The restarts give the restart data on `[0, q₀]`** (the traces of the shifted drivers, read by `LP.traceAt`). -/
theorem restartData_of_restarts (hp : IsSLEPathUpTo k xL xR ρL ρR w vL vR b τ) (hsum : ∑ i, ρL i ≤ -2)
    (hR : RestartHyp k ρL ρR w vL vR b τ) {q₀ : ℝ≥0} (hq₀τ : (q₀ : ℝ≥0∞) < τ) :
    RestartData w q₀ (range ((↑) : ℚ≥0 → ℝ≥0)) (fun q u => LP.traceAt u (shiftNN w q)) := by
  rintro _ ⟨r, rfl⟩ hq0 hqq₀
  have hr0 : (0 : ℚ≥0) < r := by exact_mod_cast hq0
  have hrτ : ((r : ℝ≥0) : ℝ≥0∞) < τ := lt_trans (ENNReal.coe_lt_coe.2 hqq₀) hq₀τ
  obtain ⟨x, hxC, hxG, -, hle, hag⟩ := hR r hr0 hrτ
  have hxS := mem_simpSet_iff.1 (RestartHyp.mem_simpSet hp hsum hrτ hxC hxG)
  have hfp := hxC.1.2.2.isForcePath
  set q : ℝ≥0 := (r : ℝ≥0) with hq
  have hσ : (((q₀ - q : ℝ≥0)) : ℝ≥0∞) < τ - q :=
    (Restart.coe_lt_sub_iff _ _).2 (by rw [add_tsub_cancel_of_le hqq₀.le]; exact hq₀τ)
  have hσc : (((q₀ - q : ℝ≥0)) : ℝ≥0∞) < cζ x := lt_of_lt_of_le hσ hle
  obtain ⟨s', hs', hs'ζ⟩ := exists_nnrat_btwn_top hσc
  have hgen := hxS.isGeneratingTrace hfp.continuousOn_w hfp.w_zero hs'ζ
  have hIcc := Sec7.IsGeneratingTrace.isGeneratingTraceIcc hgen
    (hfp.continuousOn_w.mono fun t ht => lt_trans ht hs'ζ) hfp.w_zero (by exact_mod_cast hs')
  have hagw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ - q → cw x t = shiftNN w q t := fun t ht => (hag t ht).1
  have hIcc' := WangWu.ImgDrv.IsGeneratingTraceIcc.congr_of_lt hIcc hσ hagw
  have htr : ∀ u : ℝ≥0, (u : ℝ≥0∞) < τ - q → LP.traceAt u (shiftNN w q) = LP.traceAt u (cw x) :=
    fun u hu => LP.traceAt_congr fun r' hr' => (hagw r' (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr') hu)).symm
  have hle' : ∀ u : ℝ≥0, u ≤ q₀ - q → (u : ℝ≥0∞) < τ - q := fun u hu =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hu) hσ
  refine ⟨isGeneratingTraceIcc_congr hIcc' fun u hu => htr u (hle' u hu), ?_, fun u hu0 hu => ?_⟩
  · intro u₁ hu₁ u₂ hu₂ he
    simp only at he
    rw [htr u₁ (hle' u₁ hu₁.2), htr u₂ (hle' u₂ hu₂.2)] at he
    exact hxS.injOn hfp.continuousOn_w hfp.w_zero (lt_of_lt_of_le (hle' u₁ hu₁.2) hle)
      (lt_of_lt_of_le (hle' u₂ hu₂.2) hle) he
  · show LP.traceAt u (shiftNN w q) ∈ H
    rw [htr u (hle' u hu)]
    exact (hxS.mem_H hfp.continuousOn_w hfp.w_zero hfp.continuousOn_vL hfp.continuousOn_vR hu0
      (lt_of_lt_of_le (hle' u hu) hle)).1

/-- **The trace on `[0, q₀]` from the restarts.** -/
theorem trace_Icc_of_restarts (hp : IsSLEPathUpTo k xL xR ρL ρR w vL vR b τ) (hsum : ∑ i, ρL i ≤ -2)
    (hR : RestartHyp k ρL ρR w vL vR b τ) {q₀ : ℝ≥0} (hq₀ : 0 < q₀) (hq₀τ : (q₀ : ℝ≥0∞) < τ) :
    IsGeneratingTraceIcc w q₀ (fun t => LP.traceAt t w) ∧ InjOn (fun t => LP.traceAt t w) (Icc 0 q₀) ∧
      ∀ t : ℝ≥0, 0 < t → t ≤ q₀ → LP.traceAt t w ∈ H :=
  isGeneratingTraceIcc_of_restarts hp.continuousOn_w hp.w_zero hq₀ hq₀τ
    (fun a b hab => by obtain ⟨q, h1, h2⟩ := exists_nnrat_btwn hab; exact ⟨q, ⟨q, rfl⟩, h1, h2⟩)
    (restartData_of_restarts hp hsum hR hq₀τ)

/-- **The extension by the canonical code at a positive rational time** and its basic properties. -/
theorem exists_extension (hp : IsSLEPathUpTo k xL xR ρL ρR w vL vR b τ) {q : ℚ≥0} (hq0 : 0 < (q : ℝ≥0))
    (hqτ : ((q : ℝ≥0) : ℝ≥0∞) < τ) {x : XCode (j + 1) 1}
    (hxC : x ∈ CRel k (fun i => vL i q - w q) (fun j => vR j q - w q) ρL ρR)
    (hcb : ∀ t, cb x t = b (q + t) - b q) (hle : τ - (q : ℝ≥0) ≤ cζ x)
    (hag : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ - (q : ℝ≥0) →
      cw x t = w (q + t) - w q ∧ (∀ i, cvL x i t = vL i (q + t) - w q) ∧ ∀ j, cvR x j t = vR j (q + t) - w q) :
    IsIntegratedSLEPath k xL xR ρL ρR (concatAt q w (w q) (cw x)) (fun i => concatAt q (vL i) (w q) (cvL x i))
        (fun i => concatAt q (vR i) (w q) (cvR x i)) b ((q : ℝ≥0) + cζ x) ∧
      τ ≤ (q : ℝ≥0) + cζ x ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → concatAt q w (w q) (cw x) t = w t ∧
        (∀ i, concatAt q (vL i) (w q) (cvL x i) t = vL i t) ∧ ∀ i, concatAt q (vR i) (w q) (cvR x i) t = vR i t) ∧
      shiftNN (concatAt q w (w q) (cw x)) q = cw x := by
  have hxp := hxC.1.2.2
  have hcp := hxp.isForcePath
  refine ⟨Assembly2.isIntegratedSLEPath_concat hp hqτ hq0 hxp hcb, ?_, fun t ht => ?_, ?_⟩
  · have := tsub_le_iff_left.1 hle
    exact this
  · rcases lt_or_ge t (q : ℝ≥0) with htq | htq
    · exact ⟨concatAt_of_lt htq, fun i => concatAt_of_lt htq, fun i => concatAt_of_lt htq⟩
    · have hu : ((t - q : ℝ≥0) : ℝ≥0∞) < τ - (q : ℝ≥0) :=
        (Restart.coe_lt_sub_iff _ _).2 (by rw [add_tsub_cancel_of_le htq]; exact ht)
      obtain ⟨e1, e2, e3⟩ := hag _ hu
      rw [add_tsub_cancel_of_le htq] at e1 e2 e3
      refine ⟨by rw [concatAt_of_le htq, e1]; ring, fun i => ?_, fun i => ?_⟩
      · rw [concatAt_of_le htq, e2 i]; ring
      · rw [concatAt_of_le htq, e3 i]; ring
  · funext t
    simp only [shiftNN, concatAt_of_le (le_add_of_nonneg_right zero_le : (q : ℝ≥0) ≤ q + t),
      concatAt_of_le (le_refl (q : ℝ≥0)), add_tsub_cancel_left, tsub_self, hcp.w_zero]
    ring

/-- **The joined trace of the extension**: if the local path has the simple generating trace `γ` on `[0, σ]` and the
code driving the extension after `σ` is in `simpSet`, the joined trace `joinTrace` is a simple generating trace of the
extension before its lifetime, in `ℍ` at positive times. -/
theorem joined_trace {wG : ℝ≥0 → ℝ} {ζG : ℝ≥0∞} {σ : ℝ≥0} {x : XCode (j + 1) 1} {γ : ℝ≥0 → ℂ}
    (hwc : ContinuousOn wG {t | (t : ℝ≥0∞) < ζG}) (hw0 : wG 0 = 0) (hζG : ζG = (σ : ℝ≥0∞) + cζ x)
    (hσζ : (σ : ℝ≥0∞) < ζG) (hsh : shiftNN wG σ = cw x)
    (hxc : ContinuousOn (cw x) {t | (t : ℝ≥0∞) < cζ x}) (hx0 : cw x 0 = 0)
    (hxvL : ∀ i, ContinuousOn (cvL x i) {t | (t : ℝ≥0∞) < cζ x})
    (hxvR : ∀ i, ContinuousOn (cvR x i) {t | (t : ℝ≥0∞) < cζ x})
    (hxS : SimpPath (cw x) (cvL x) (cvR x) (cζ x)) (h₁ : IsGeneratingTraceIcc wG σ γ)
    (hinj : InjOn γ (Icc 0 σ)) (hH : ∀ t : ℝ≥0, 0 < t → t ≤ σ → γ t ∈ H) :
    (∀ s : ℝ≥0, (s : ℝ≥0∞) < ζG →
      IsGeneratingTrace wG s (joinTrace wG σ γ fun u => LP.traceAt u (cw x))) ∧
      InjOn (joinTrace wG σ γ fun u => LP.traceAt u (cw x)) {t | (t : ℝ≥0∞) < ζG} ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζG → joinTrace wG σ γ (fun u => LP.traceAt u (cw x)) t ∈ H := by
  set η₂ : ℝ≥0 → ℂ := fun u => LP.traceAt u (cw x) with hη₂
  set γG := joinTrace wG σ γ η₂ with hγG
  have hσne : (σ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hcζ0 : 0 < cζ x := by
    rw [hζG] at hσζ
    by_contra h0
    rw [not_lt, nonpos_iff_eq_zero] at h0
    rw [h0, add_zero] at hσζ
    exact lt_irrefl _ hσζ
  -- the generating traces
  have hgen : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζG → IsGeneratingTrace wG s γG := by
    intro s hs
    have hsσ : ((s - σ : ℝ≥0) : ℝ≥0∞) < cζ x := by
      rcases le_or_gt σ s with h | h
      · have : ((σ + (s - σ) : ℝ≥0) : ℝ≥0∞) < (σ : ℝ≥0∞) + cζ x := by
          rw [add_tsub_cancel_of_le h, ← hζG]; exact hs
        rw [ENNReal.coe_add] at this
        exact (ENNReal.add_lt_add_iff_left hσne).1 this
      · rw [tsub_eq_zero_of_le h.le, ENNReal.coe_zero]; exact hcζ0
    obtain ⟨s'', hs'', hs''ζ⟩ := exists_nnrat_btwn_top hsσ
    have h₂ : IsGeneratingTrace (shiftNN wG σ) ((s'' : ℝ≥0) : ℝ≥0∞) η₂ := by
      rw [hsh]; exact hxS.isGeneratingTrace hxc hx0 hs''ζ
    have hlt : (σ : ℝ≥0∞) + ((s'' : ℝ≥0) : ℝ≥0∞) ≤ ζG := by
      rw [hζG]; gcongr
    have hJ := (Sec7.IsGeneratingTraceIcc.join (hwc.mono fun t ht => lt_of_lt_of_le ht hlt) hw0 h₁ h₂).1
    refine hJ.mono_horizon ?_
    rw [← ENNReal.coe_add]
    exact ENNReal.coe_le_coe.2 (le_trans le_add_tsub (by gcongr))
  -- the extension data at `σ`
  obtain ⟨t₂, hσt₂, ht₂ζ⟩ := exists_real_btwn_of_lt hσζ
  have hfc : Continuous (frozenDrive wG t₂) := continuous_frozenDrive_of_lt hwc ht₂ζ
  have ht₂0 : 0 ≤ t₂ := σ.coe_nonneg.trans hσt₂.le
  have hW0 : frozenDrive wG t₂ 0 = 0 := by rw [frozenDrive_zero ht₂0, hw0]
  obtain ⟨hF₃, hK₃, hFeq₃, -, -, -, -⟩ := h₁.extend_props hσt₂ hfc hw0
  have hη₂H : ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < cζ x → η₂ u ∈ H := fun u hu0 hu =>
    (hxS.mem_H hxc hx0 hxvL hxvR hu0 hu).1
  have hafter : ∀ t : ℝ≥0, σ < t → (t : ℝ≥0∞) < ζG →
      γG t = fwdMapInv (frozenDrive wG t₂) σ (η₂ (t - σ)) ∧ η₂ (t - σ) ∈ H ∧ (t - σ : ℝ≥0∞) < cζ x := by
    intro t hσt ht
    have hu : ((t - σ : ℝ≥0) : ℝ≥0∞) < cζ x := by
      have : ((σ + (t - σ) : ℝ≥0) : ℝ≥0∞) < (σ : ℝ≥0∞) + cζ x := by
        rw [add_tsub_cancel_of_le hσt.le, ← hζG]; exact ht
      rw [ENNReal.coe_add] at this
      exact (ENNReal.add_lt_add_iff_left hσne).1 this
    have hzH := hη₂H _ (tsub_pos_of_lt hσt) hu
    refine ⟨?_, hzH, by exact_mod_cast hu⟩
    rw [hγG, Sec7.joinTrace_of_lt hσt, hF₃]
    exact hFeq₃ hzH
  have hFK : ∀ z ∈ H, fwdMapInv (frozenDrive wG t₂) σ z ∈ H \ fwdHull (frozenDrive wG t₂) σ := fun z hz =>
    QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hfc hW0 σ.coe_nonneg hz
  have hγK : ∀ t : ℝ≥0, 0 < t → t ≤ σ → γ t ∈ fwdHull (frozenDrive wG t₂) σ := fun t ht0 htσ => by
    rw [hK₃]
    refine ⟨hH t ht0 htσ, Or.inl (subset_closure ⟨(t : ℝ), ⟨t.coe_nonneg, by exact_mod_cast htσ⟩, ?_⟩)⟩
    simp
  have hγ0 : γ 0 = 0 := h₁.1.1
  have h0H : (0 : ℂ) ∉ H := by simp [QuantumZipper.H]
  have hFinj : InjOn (fwdMapInv (frozenDrive wG t₂) σ) H :=
    (isConformalBijection_fwdMapInv hfc hW0 σ.coe_nonneg).2.injOn
  refine ⟨hgen, ?_, fun t ht0 ht => ?_⟩
  · have key : ∀ t₁ t₃ : ℝ≥0, t₁ ≤ σ → σ < t₃ → (t₃ : ℝ≥0∞) < ζG → γG t₁ ≠ γG t₃ := by
      intro t₁ t₃ h1 h3 h3ζ he
      obtain ⟨e3, hz3, -⟩ := hafter t₃ h3 h3ζ
      rw [hγG, Sec7.joinTrace_of_le h1, ← hγG, e3] at he
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t₁) with h0 | h0
      · rw [← h0, hγ0] at he
        exact h0H (he ▸ (hFK _ hz3).1)
      · exact (hFK _ hz3).2 (he ▸ hγK t₁ h0 h1)
    intro t₁ ht₁ t₃ ht₃ he
    rcases le_or_gt t₁ σ with h1 | h1 <;> rcases le_or_gt t₃ σ with h3 | h3
    · have e1 : γG t₁ = γ t₁ := Sec7.joinTrace_of_le h1
      have e3 : γG t₃ = γ t₃ := Sec7.joinTrace_of_le h3
      exact hinj ⟨zero_le, h1⟩ ⟨zero_le, h3⟩ (by rw [← e1, ← e3]; exact he)
    · exact absurd he (key t₁ t₃ h1 h3 ht₃)
    · exact absurd he.symm (key t₃ t₁ h3 h1 ht₁)
    · obtain ⟨e1, hz1, hu1⟩ := hafter t₁ h1 ht₁
      obtain ⟨e3, hz3, hu3⟩ := hafter t₃ h3 ht₃
      have hz := hFinj hz1 hz3 (by rw [← e1, ← e3]; exact he)
      have hu := hxS.injOn hxc hx0 hu1 hu3 hz
      calc t₁ = σ + (t₁ - σ) := (add_tsub_cancel_of_le h1.le).symm
        _ = σ + (t₃ - σ) := by rw [hu]
        _ = t₃ := add_tsub_cancel_of_le h3.le
  · rcases le_or_gt t σ with h | h
    · have e : γG t = γ t := Sec7.joinTrace_of_le h
      rw [e]; exact hH t ht0 h
    · obtain ⟨e, hz, -⟩ := hafter t h ht
      rw [e]; exact (hFK _ hz).1

/-- **The exit trace from the restarts** (`A2P1.ae_exit_trace`'s conclusion, pathwise, for a local path whose
restarts are canonical codes in `goodSet`). The local path extends before `τ` to a driver `wG` with lifetime
`ζG ≥ τ`, `0 < ζG < ∞`, and a generating trace on `[0, ζG]`, injective on `[0, ζG]`, in `ℍ` on `(0, ζG)`, whose
endpoint is a real point left of the last left mark. -/
theorem exists_exit_trace_of_restarts (hp : IsSLEPathUpTo k xL xR ρL ρR w vL vR b τ)
    (hF : IsOrderedForceWord xL xR) (hxL : StrictAnti xL) (hsum : ∑ i, ρL i ≤ -2) (hτ0 : 0 < τ)
    (hR : RestartHyp k ρL ρR w vL vR b τ) :
    ∃ (wG : ℝ≥0 → ℝ) (ζG : ℝ≥0∞) (η : ℝ≥0 → ℂ), τ ≤ ζG ∧ (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → wG t = w t) ∧
      0 < ζG ∧ ζG ≠ ⊤ ∧ IsGeneratingTrace wG ζG η ∧ InjOn η {t | (t : ℝ≥0∞) ≤ ζG} ∧
      (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζG → η t ∈ H) ∧ ∃ x₀ : ℝ, x₀ < xL (Fin.last j) ∧ η ζG.toNNReal = x₀ := by
  obtain ⟨q, hq0, hqτ⟩ := exists_nnrat_btwn_top (s := 0) (by simpa using hτ0)
  have hq0' : (0 : ℚ≥0) < q := by exact_mod_cast hq0
  set σ : ℝ≥0 := (q : ℝ≥0) with hσdef
  obtain ⟨hγIcc0, hγinj, hγH⟩ := trace_Icc_of_restarts hp hsum hR hq0 hqτ
  set γ : ℝ≥0 → ℂ := fun t => LP.traceAt t w with hγdef
  obtain ⟨x, hxC, hxG, hcb, hle, hag⟩ := hR q hq0' hqτ
  have hxS := mem_simpSet_iff.1 (RestartHyp.mem_simpSet hp hsum hqτ hxC hxG)
  have hcp := hxC.1.2.2.isForcePath
  obtain ⟨hG, hτζ, hagG, hsh⟩ := exists_extension hp hq0 hqτ hxC hcb hle hag
  set wG := concatAt σ w (w σ) (cw x) with hwG
  set vLG : Fin (j + 1) → ℝ≥0 → ℝ := fun i => concatAt σ (vL i) (w σ) (cvL x i) with hvLG
  set ζG : ℝ≥0∞ := (σ : ℝ≥0∞) + cζ x with hζG
  have hGp := hG.isForcePath
  have hσζ : (σ : ℝ≥0∞) < ζG := lt_of_lt_of_le hqτ hτζ
  have h₁ : IsGeneratingTraceIcc wG σ γ :=
    WangWu.ImgDrv.IsGeneratingTraceIcc.congr_of_lt hγIcc0 hqτ fun t ht => (hagG t ht).1.symm
  obtain ⟨hgen, hinj, hH⟩ := joined_trace hGp.continuousOn_w hGp.w_zero rfl hσζ hsh hcp.continuousOn_w
    hcp.w_zero hcp.continuousOn_vL hcp.continuousOn_vR hxS h₁ hγinj hγH
  set γG := joinTrace wG σ γ fun u => LP.traceAt u (cw x) with hγG
  have hIccG : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζG → IsGeneratingTraceIcc wG s γG := by
    intro s hs
    obtain ⟨s', hss', hs'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
    exact Sec7.IsGeneratingTrace.isGeneratingTraceIcc (hgen s' hs'ζ)
      (hGp.continuousOn_w.mono fun t ht => lt_trans (show (t : ℝ≥0∞) < s' from ht) hs'ζ) hGp.w_zero hss'
  -- the strictly separated start at `σ`
  have hnc := fun t ht0 ht => noncoll_of_restarts hp hsum hR (t := t) ht0 ht
  have hstrict : StrictStart ((fun i => vL i σ - w σ), fun i => vR i σ - w σ) := by
    refine ⟨fun i i' hii' => ?_, fun i => sub_neg.2 ((hnc σ hq0 hqτ).1 i), fun a c hac => ?_,
      fun i => sub_pos.2 ((hnc σ hq0 hqτ).2 i)⟩
    · have h := hGp.vL_lt_vL_of_lt hσζ (hxL hii') fun r hr => by
        rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ r) with h0 | h0
        · rw [← h0, hGp.vL_zero, hGp.w_zero]
          exact (hxL hii').trans_le (hF.2.1 i)
        · have hrτ : (r : ℝ≥0∞) < τ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hqτ
          obtain ⟨e1, e2, -⟩ := hagG r hrτ
          have e2' : vLG i' r = vL i' r := e2 i'
          rw [e1, e2']
          exact (hnc r h0 hrτ).1 i'
      obtain ⟨-, e2, -⟩ := hagG σ hqτ
      have e2i : vLG i σ = vL i σ := e2 i
      have e2i' : vLG i' σ = vL i' σ := e2 i'
      rw [e2i, e2i'] at h
      exact sub_lt_sub_right h _
    · exact absurd hac (by rw [Subsingleton.elim a c]; exact lt_irrefl c)
  obtain ⟨Sx, y, hend⟩ := (mem_exitCode_iff hstrict hxC).1 hxG.2
  have hgap : ∀ r : ℝ≥0, r ≤ σ → vLG (Fin.last j) r < wG r := fun r hr =>
    A2P1.vL_last_lt hG hsum (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hσζ)
  have he : vL (Fin.last j) σ - w σ = vLG (Fin.last j) σ - wG σ := by
    obtain ⟨e1, e2, -⟩ := hagG σ hqτ
    have e2' : vLG (Fin.last j) σ = vL (Fin.last j) σ := e2 _
    rw [e1, e2']
  have hgeo : ∀ y' : ℝ, y' < vL (Fin.last j) σ - w σ →
      extendFrom H (fwdMapInv (fun s : ℝ => wG s.toNNReal) σ) y' ∉ H := by
    intro y' hy' hmem
    rw [he] at hy'
    obtain ⟨x₁, -, hx₁⟩ := A2P1.exists_extendFrom_eq_lt_last hG hσζ hgap (hIccG σ hσζ) (yt := y') hy'
    have hpos : (0 : ℝ) < (extendFrom H (fwdMapInv (fun s : ℝ => wG s.toNNReal) σ) y').im := hmem
    rw [hx₁, Complex.ofReal_im] at hpos
    exact lt_irrefl _ hpos
  have hagree : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζG - σ → cw x t = wG (σ + t) - wG σ := fun t _ => by
    rw [← hsh]; rfl
  have hζc : cζ x ≤ ζG - σ := by rw [hζG, ENNReal.add_sub_cancel_left ENNReal.coe_ne_top]
  obtain ⟨hζeq, hconv⟩ := A2P1.exit_of_restart hGp.continuousOn_w hGp.w_zero hIccG hH hq0 hσζ
    hcp.continuousOn_w hcp.w_zero hagree hζc hend hgeo
  obtain ⟨x₀, hx₀, hFx₀⟩ := A2P1.exists_extendFrom_eq_lt_last hG hσζ hgap (hIccG σ hσζ) (yt := y)
    (by rw [← he]; exact hend.2.2.2.1)
  rw [hFx₀] at hconv
  set Z : ℝ≥0 := σ + Sx with hZdef
  have hZ : ζG = (Z : ℝ≥0∞) := hζeq
  have hζ0 : 0 < ζG := lt_of_le_of_lt zero_le hσζ
  have hx₀0 : x₀ < 0 := hx₀.trans_le (hF.2.1 _)
  set η : ℝ≥0 → ℂ := fun t => if (t : ℝ≥0∞) < ζG then γG t else (x₀ : ℂ) with hη
  have hηγ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζG → η t = γG t := fun t ht => by simp only [hη, ht, ↓reduceIte]
  have hηZ : η Z = x₀ := by simp only [hη, hZ, lt_irrefl, ↓reduceIte]
  have hγne : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζG → γG t ≠ x₀ := by
    intro t ht h
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | h0
    · have h1 : γG 0 = 0 := (hgen 0 hζ0).1
      rw [← h0, h1] at h
      have : (x₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx₀0.ne
      exact this h.symm
    · have hpos : (0 : ℝ) < (γG t).im := hH t h0 ht
      rw [h, Complex.ofReal_im] at hpos
      exact lt_irrefl _ hpos
  refine ⟨wG, ζG, η, hτζ, fun t ht => (hagG t ht).1, hζ0, by rw [hZ]; exact ENNReal.coe_ne_top,
    ⟨?_, ?_, ?_⟩, ?_, ?_, x₀, hx₀, ?_⟩
  · rw [hηγ 0 hζ0]
    exact (hgen 0 hζ0).1
  · intro t ht
    rcases (show (t : ℝ≥0∞) ≤ ζG from ht).lt_or_eq with hlt | heq
    · obtain ⟨s', hts', hs'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
      have hts'' : t < s' := by exact_mod_cast hts'
      have hγc : ContinuousAt γG t :=
        ((hgen s' hs'ζ).2.1.mono fun r (hr : r ∈ Iic s') =>
          (by exact_mod_cast hr : (r : ℝ≥0∞) ≤ s')).continuousAt (Iic_mem_nhds hts'')
      have hev : η =ᶠ[𝓝 t] γG := by
        filter_upwards [Iio_mem_nhds hts''] with r hr
        exact hηγ r (lt_trans (by exact_mod_cast hr) hs'ζ)
      exact (hγc.congr hev.symm).continuousWithinAt
    · have htZ : t = Z := by rw [hZ] at heq; exact_mod_cast heq
      have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζG} = Iic Z := by
        ext r
        simp only [mem_ofPred_eq, mem_Iic, hZ, ENNReal.coe_le_coe]
      rw [hset, htZ]
      refine continuousWithinAt_Iio_iff_Iic.1 ?_
      show Tendsto η (𝓝[<] Z) (𝓝 (η Z))
      rw [hηZ]
      refine hconv.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (hηγ r (by rw [hZ]; exact_mod_cast hr)).symm
  · intro t ht
    obtain ⟨s', hts', hs'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    have e : η '' Icc 0 t = γG '' Icc 0 t :=
      image_congr fun r hr => hηγ r (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr.2) ht)
    rw [e]
    exact (hgen s' hs'ζ).2.2 t hts'
  · intro t₁ ht₁ t₂ ht₂ heq
    have ht₁' : (t₁ : ℝ≥0∞) ≤ ζG := ht₁
    have ht₂' : (t₂ : ℝ≥0∞) ≤ ζG := ht₂
    by_cases h1 : (t₁ : ℝ≥0∞) < ζG <;> by_cases h2 : (t₂ : ℝ≥0∞) < ζG
    · rw [hηγ t₁ h1, hηγ t₂ h2] at heq
      exact hinj h1 h2 heq
    · have e2 : η t₂ = x₀ := by simp only [hη, h2, ↓reduceIte]
      rw [hηγ t₁ h1, e2] at heq
      exact absurd heq (hγne t₁ h1)
    · have e1 : η t₁ = x₀ := by simp only [hη, h1, ↓reduceIte]
      rw [hηγ t₂ h2, e1] at heq
      exact absurd heq.symm (hγne t₂ h2)
    · have e1 : (t₁ : ℝ≥0∞) = ζG := le_antisymm ht₁' (not_lt.1 h1)
      have e2 : (t₂ : ℝ≥0∞) = ζG := le_antisymm ht₂' (not_lt.1 h2)
      exact_mod_cast e1.trans e2.symm
  · intro t ht0 ht
    rw [hηγ t ht]
    exact hH t ht0 ht
  · rw [hZ, ENNReal.toNNReal_coe]
    exact hηZ

end Path

end InteractingSLE.ZhanGT4.A2ImgEnd
