/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop49QExitKilled
import InteractingSLE.Spec.Sec7.SideHeightGeom
import InteractingSLE.Spec.Zhan.StripTailPullback

/-!
# A.2, part 1: the restart at a positive time and the exit through the upper span

Packet PROVE-ZHAN-A2P1. Source: Astra, *Follow-up proofs*, §A.2 L527–L536 ("Its endpoint is supplied by the already
proved `κ̂ ≤ 4` endpoint theorem … Thus the small curve `J` is a crosscut with its other endpoint strictly in
`(x₂, p₂)`"). In the reflected chart the span `(x₂, p₂)` is the left span `(−∞, x^{L,last})` beyond the last left
mark, and PROVE-GLUECOND9's left strip end (`Sec5.Prop49Exit`: the Borel code event `exitCode` of full canonical law
at every separated start, from Zhan's strip endpoint theorem) applies to the evolution restarted at any positive
time, where the word is separated (part 1's noncollision). This file supplies the three remaining steps:

* `ae_restart_mem`: at a positive stopping time `T < ζ`, the restarted canonical code lies in every Borel code set
  whose complement has canonical law zero at every separated ordered start (the code-membership form of
  `Sec7.RandRestart.measure_restart_codeEvent`);
* `exit_of_restart`: the pathwise exit (PROVE-GLUECOND9's `leftExit_of_restart` when the restarted lifetime is the
  remaining lifetime): the lifetime is `q + S` and the trace converges to `F̄_q(y)`;
* `exists_extendFrom_eq_lt`: for an alive left real point `x₀`, every real point left of its image is the image of an
  alive real point left of `x₀`, so `F̄_q` sends it to a real point left of `x₀` (intermediate value theorem for the
  `1`-Lipschitz real flow).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2P1

open QuantumZipper (H Hbar fwdMapInv)
open Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

/-! ### The restarted code lies in every code set of full canonical law -/

section Restart

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The restarted code lies in a code set of full canonical law.** Let `T` be a stopping time, `A ∈ 𝓕_T` with
`0 < T < ζ` on `A`, and `S` a Borel set of solution codes whose complement has canonical law `0` at every separated
ordered start. Then almost surely on `A` the restarted evolution has a canonical code in `S` from the word `V_T − W_T`,
with lifetime `ζ − T` and driver `W_{T+·} − W_T` before it. -/
theorem ae_restart_mem (ha : 0 < a) (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A) (hAT : ∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω ∧ 0 < T ω)
    {S : Set (XCode nL nR)} (hS : MeasurableSet S)
    (hS0 : ∀ s : (Fin nL → ℝ) × (Fin nR → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      codeLaw a ρL ρR Sᶜ s = 0) :
    ∀ᵐ ω ∂P, ω ∈ A → ∃ x : XCode nL nR, x ∈ CRel a (wordAt W VL VR T ω).1 (wordAt W VL VR T ω).2 ρL ρR ∧
      x ∈ S ∧ cζ x = ζ ω - T ω ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω - T ω → cw x t = W (T ω + t) ω - W (T ω) ω := by
  obtain ⟨st, g, c, -, -, hlaw, hid⟩ :=
    restart_core ha hE hT hA fun ω hω => ⟨(hAT ω hω).1, Or.inl (hAT ω hω).2⟩
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  have hord : ∀ᵐ ω ∂P, ω ∈ A → IsOrderedForceWord (st ω).1 (st ω).2 := by
    filter_upwards [hid, hE.ae_isIntegratedSLEPath] with ω h hp hωA
    obtain ⟨hst, -⟩ := h hωA
    have hfp := hp.isForcePath
    have hTζ := (hAT ω hωA).1
    rw [hst]
    exact ⟨fun i i' hii' => sub_le_sub_right (hfp.antitone_vL hTζ hii') _,
      fun i => sub_nonpos.2 (hfp.vL_le_w hTζ i), fun i i' hii' => sub_le_sub_right (hfp.monotone_vR hTζ hii') _,
      fun i => sub_nonneg.2 (hfp.w_le_vR hTζ i)⟩
  have h0 : P (A ∩ (fun ω => (st ω, g ω)) ⁻¹' restartSetS a ρL ρR Sᶜ) = 0 := by
    rw [hlaw _ (measurableSet_restartSetS hS.compl)]
    have e : (∫⁻ ω in A, wienerPath (Prod.mk (st ω) ⁻¹' restartSetS a ρL ρR Sᶜ) ∂P) = ∫⁻ _ in A, 0 ∂P := by
      refine setLIntegral_congr_fun_ae hAm ?_
      filter_upwards [hid, hord] with ω h ho hωA
      exact hS0 (st ω) (h hωA).2.1 (ho hωA)
    rw [e, lintegral_zero]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0, hid] with ω h1 h2 hωA
  obtain ⟨hst, hsep, hc, hc1, hcζ, hcw, -⟩ := h2 hωA
  refine ⟨c ω, hst ▸ hc, ?_, hcζ, hcw⟩
  by_contra hcS
  refine h1 ⟨hωA, ?_⟩
  have e1 : (st ω, g ω) ∈ restartSetS a ρL ρR Sᶜ ↔
      (((st ω).1, (st ω).2), (c ω).1) ∈ lawSetS a ρL ρR Sᶜ := by
    rw [hc1]; exact Iff.rfl
  show (st ω, g ω) ∈ restartSetS a ρL ρR Sᶜ
  rw [e1, mem_lawSetS_iff hsep hc]
  exact hcS

end Restart

/-! ### The exit when the restart lives through the remaining lifetime -/

section Exit

open Sec5.Prop49Exit

/-- **The exit through the left span** (PROVE-GLUECOND9's `Sec5.Prop49Exit.leftExit_of_restart`, in the case where
the restarted lifetime is at most the remaining lifetime `T − q`, so that the exit cannot happen in `ℍ`). Let `γ`
generate the chain of `w` on every `[0, s]`, `s < T`, in `ℍ` at positive times; let `c` be the driver restarted at
`q ∈ (0, T)`, with a left strip end `EndCond e c ζc S y` and `ζc ≤ T − q`, and suppose `F̄_q` sends every real point
left of `e` off `ℍ`. Then `T = q + S` and `γ` converges at `T` to `F̄_q(y)`. -/
theorem exit_of_restart {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < T})
    (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → Sec7.IsGeneratingTraceIcc w s γ)
    (hγH : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < T → γ t ∈ H) {q : ℝ≥0} (hq0 : 0 < q) (hqT : (q : ℝ≥0∞) < T)
    {c : ℝ≥0 → ℝ} {ζc : ℝ≥0∞} (hcc : ContinuousOn c {t | (t : ℝ≥0∞) < ζc}) (hc0 : c 0 = 0)
    (hagree : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T - q → c t = w (q + t) - w q) (hζc : ζc ≤ T - q)
    {e : ℝ} {S : ℝ≥0} {y : ℝ} (hend : EndCond e c ζc S y)
    (hgeo : ∀ y' : ℝ, y' < e → extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) q) y' ∉ H) :
    T = ((q + S : ℝ≥0) : ℝ≥0∞) ∧
      Tendsto γ (𝓝[<] (q + S)) (𝓝 (extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) q) y)) := by
  have hqSle : (((q + S : ℝ≥0)) : ℝ≥0∞) ≤ T := by
    have h1 : (S : ℝ≥0∞) ≤ T - q := hend.2.1.trans hζc
    rw [ENNReal.coe_add]
    calc (q : ℝ≥0∞) + S ≤ q + (T - q) := add_le_add le_rfl h1
      _ = T := add_tsub_cancel_of_le hqT.le
  obtain ⟨hS0, hSζ, hy0, hye, htr, hav, hlim⟩ := hend
  set F := extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) q) with hFdef
  -- the extension `F̄_q`
  obtain ⟨t₂, hqt₂, ht₂T⟩ := exists_real_btwn_of_lt hqT
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg q).trans hqt₂.le
  have hwfz := continuous_frozenDrive_of_lt hwc ht₂T
  have hW0' : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hw0]
  obtain ⟨hFeq, -, hEq, hFc, -, -, hF0⟩ := (hγ q hqT).extend_props hqt₂ hwfz hw0
  have hFc' : ContinuousOn F Hbar := by rw [hFdef, hFeq]; exact hFc
  have hF0' : F 0 = γ q := by rw [hFdef, hFeq]; exact hF0
  have hFH : ∀ v ∈ H, F v ∈ H := fun v hv => by
    rw [hFdef, hFeq, hEq hv]
    exact (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hwfz hW0' q.coe_nonneg hv).1
  -- the concatenation `X` of `w` before `q` and `c` after `q`
  set X : ℝ≥0 → ℝ := concatAt q w (w q) c with hXdef
  have hcq : w q + c 0 = w q := by rw [hc0, add_zero]
  have hXc : ContinuousOn X {s | (s : ℝ≥0∞) < (q : ℝ≥0∞) + ζc} := continuousOn_concatAt hqT hwc hcc hcq
  have hX0 : X 0 = 0 := by rw [hXdef, concatAt_of_lt hq0]; exact hw0
  have hXw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → X t = w t := by
    intro t ht
    rcases lt_or_ge t q with htq | htq
    · exact concatAt_of_lt htq
    · rw [hXdef, concatAt_of_le htq]
      have hlt : ((t - q : ℝ≥0) : ℝ≥0∞) < T - q := by
        rw [Assembly2.coe_lt_sub_iff, add_tsub_cancel_of_le htq]; exact ht
      rw [hagree _ hlt, add_tsub_cancel_of_le htq]
      ring
  have hshift : Sec7.shiftNN X q = c := by
    funext u
    simp only [Sec7.shiftNN, hXdef, concatAt_of_le (le_add_of_nonneg_right zero_le : q ≤ q + u),
      concatAt_of_le (le_refl q), add_tsub_cancel_left, tsub_self, hc0]
    ring
  have h₁ : Sec7.IsGeneratingTraceIcc X q γ :=
    WangWu.ImgDrv.IsGeneratingTraceIcc.congr_of_lt (hγ q hqT) hqT fun t ht => (hXw t ht).symm
  have hSζ' : ∀ r : ℝ≥0, r ≤ S → (r : ℝ≥0∞) ≤ ζc := fun r hr => (by exact_mod_cast hr : (r : ℝ≥0∞) ≤ S).trans hSζ
  -- traces of `c` on `[0, r]`, `r < S` rational, around each time `u < S`
  have hctr : ∀ u : ℝ≥0, u < S → ∃ r : ℚ≥0, u < (r : ℝ≥0) ∧ (r : ℝ≥0) < S ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace c ((r : ℝ≥0) : ℝ≥0∞) η := by
    intro u hu
    obtain ⟨r, hr1, hr2⟩ := exists_nnrat_btwn' u.coe_nonneg (show (u : ℝ) < S from hu)
    have hr2' : (r : ℝ≥0) < S := by exact_mod_cast hr2
    exact ⟨r, by exact_mod_cast hr1, hr2', exists_trace_of_trQ hcc hc0 hSζ htr hr2'⟩
  -- the key identity `γ(q + u) = F̄_q(η(u))`
  have hKI : ∀ u : ℝ≥0, 0 < u → u < S → ((q + u : ℝ≥0) : ℝ≥0∞) < T → γ (q + u) = F (LP.traceAt u c) := by
    intro u hu0 huS hquT
    obtain ⟨r, hur, hrS, η, hη⟩ := hctr u huS
    have hXr : ContinuousOn X {s | (s : ℝ≥0∞) < (q : ℝ≥0∞) + ((r : ℝ≥0) : ℝ≥0∞)} :=
      hXc.mono fun s (hs : (s : ℝ≥0∞) < (q : ℝ≥0∞) + ((r : ℝ≥0) : ℝ≥0∞)) =>
        show (s : ℝ≥0∞) < (q : ℝ≥0∞) + ζc from lt_of_lt_of_le hs (add_le_add_right (hSζ' _ hrS.le) _)
    have hJ := (Sec7.IsGeneratingTraceIcc.join hXr hX0 h₁ (by rw [hshift]; exact hη)).1
    have e1 : LP.traceAt (q + u) X = Sec7.joinTrace X q γ η (q + u) :=
      LP.traceAt_eq_of_isGeneratingTrace hJ hXr hX0 (by exact_mod_cast add_lt_add_right hur q)
    have e2 : LP.traceAt (q + u) X = LP.traceAt (q + u) w :=
      LP.traceAt_congr fun s hs => hXw s (lt_of_le_of_lt (by exact_mod_cast hs) hquT)
    obtain ⟨s', hs'1, hs'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hquT
    have e3 : LP.traceAt (q + u) w = γ (q + u) :=
      LP.traceAt_eq_of_isGeneratingTrace (hγ s' hs'2).1 (hwc.mono fun t ht => lt_trans ht hs'2) hw0 hs'1
    have e4 := Sec7.joinTrace_of_lt (w := X) (η₁ := γ) (η₂ := η) (lt_add_of_pos_right q hu0)
    have e5 : fwdMapInv (fun s : ℝ => X s.toNNReal) q = fwdMapInv (fun s : ℝ => w s.toNNReal) q := by
      refine fwdMapInv_eq_of_eqOn q.coe_nonneg hqt₂ fun r hr => hXw _ ?_
      exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hr.2) ht₂T
    have e6 : η u = LP.traceAt u c := (traceAt_eq_of_trace hη hcc hc0 (hSζ' _ hrS.le) hur).symm
    rw [← e3, ← e2, e1, e4, e5, add_tsub_cancel_left, e6]
  -- the evaluation of `c` is continuous before `S` and lies in `ℍ̄`
  have hcont : ∀ u : ℝ≥0, u < S → ContinuousAt (fun t => LP.traceAt t c) u := by
    intro u hu
    obtain ⟨r, hur, hrS, η, hη⟩ := hctr u hu
    have hηc : ContinuousAt η u :=
      (hη.2.1.mono fun t (ht : t ∈ Iic (r : ℝ≥0)) => by exact_mod_cast ht).continuousAt (Iic_mem_nhds hur)
    refine hηc.congr ?_
    filter_upwards [Iio_mem_nhds hur] with t ht
    exact (traceAt_eq_of_trace hη hcc hc0 (hSζ' _ hrS.le) ht).symm
  have hHbar : ∀ u : ℝ≥0, u < S → LP.traceAt u c ∈ Hbar := by
    intro u hu
    obtain ⟨r, hur, hrS, η, hη⟩ := hctr u hu
    rw [traceAt_eq_of_trace hη hcc hc0 (hSζ' _ hrS.le) hur]
    exact Sec7.IsGeneratingTrace.mem_Hbar hη (hcc.mono fun t ht => lt_of_lt_of_le ht (hSζ' _ hrS.le)) hc0
      (by exact_mod_cast hur.le)
  have hyH : ((y : ℝ) : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((y : ℝ) : ℂ).im by simp
  have hconvS : Tendsto (fun t => LP.traceAt t c) (𝓝[<] S) (𝓝 (y : ℂ)) := tendsto_of_limQ hlim hcont
  have hFy : Tendsto (fun t => F (LP.traceAt t c)) (𝓝[<] S) (𝓝 (F y)) :=
    (hFc' _ hyH).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hconvS, by
      filter_upwards [self_mem_nhdsWithin] with t ht using hHbar t ht⟩)
  have hevS : ∀ᶠ u in 𝓝[<] S, 0 < u := eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hS0)
  rcases lt_trichotomy (((q + S : ℝ≥0)) : ℝ≥0∞) T with hlt | heq | hgt
  · -- `q + S < T` is impossible
    exfalso
    obtain ⟨s', hs'1, hs'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
    have hγc : ContinuousAt γ (q + S) :=
      ((hγ s' hs'2).1.2.1.mono fun t (ht : t ∈ Iic s') => by exact_mod_cast ht).continuousAt
        (Iic_mem_nhds (by exact_mod_cast hs'1))
    have h1 : Tendsto (fun u => γ (q + u)) (𝓝[<] S) (𝓝 (γ (q + S))) :=
      (hγc.tendsto.comp ((continuous_const.add continuous_id).tendsto S)).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun u => γ (q + u)) (𝓝[<] S) (𝓝 (F y)) := by
      refine hFy.congr' ?_
      filter_upwards [hevS, self_mem_nhdsWithin] with u hu0 hu
      refine (hKI u hu0 hu (lt_of_le_of_lt ?_ hlt)).symm
      have : q + u ≤ q + S := add_le_add_right hu.le q
      exact_mod_cast this
    have : (𝓝[<] S).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hS0⟩
    have heq := tendsto_nhds_unique h1 h2
    have hmem := hγH (q + S) (by positivity) hlt
    rw [heq] at hmem
    exact hgeo y hye hmem
  · -- `T = q + S`: convergence to `F̄_q(y)`
    refine ⟨heq.symm, (tendsto_comp_tsub hS0 hFy).congr' ?_⟩
    have hq : ∀ᶠ t in 𝓝[<] (q + S), q < t :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (lt_add_of_pos_right q hS0))
    filter_upwards [hq, self_mem_nhdsWithin] with t hqt ht
    have hu0 : 0 < t - q := tsub_pos_of_lt hqt
    have huS : t - q < S := by rw [tsub_lt_iff_left hqt.le]; exact ht
    have htT : (((q + (t - q) : ℝ≥0)) : ℝ≥0∞) < T := by
      rw [add_tsub_cancel_of_le hqt.le, ← heq]; exact_mod_cast ht
    have := hKI (t - q) hu0 huS htT
    rw [add_tsub_cancel_of_le hqt.le] at this
    exact this.symm
  · exact absurd hgt (not_lt.2 hqSle)

end Exit

/-! ### Real points beyond an alive left point -/

section Location

open MartChar.RealFlow

variable {W : ℝ → ℝ}

/-- The flow of an alive point dominates its start: `X^y_t ≥ y − w_t`. -/
theorem le_cflow_of_alive {w : ℝ → ℝ} (hw : Continuous w) {y t : ℝ} (ht : 0 ≤ t) (h : Alive w y t) :
    y - w t ≤ cflow w y t := by
  obtain ⟨-, hX⟩ := h.isPosSol hw
  have hI : 0 ≤ ∫ r in (0 : ℝ)..t, 2 / cflow w y r :=
    intervalIntegral.integral_nonneg ht fun r hr => (div_pos two_pos (hX r hr).1).le
  have := (hX t ⟨ht, le_rfl⟩).2
  linarith

/-- **Real points beyond an alive left point.** Let `W` be continuous with `W 0 = 0`, `F` the continuous extension of
`F_t` to `ℍ̄`, and `x₀ = −y₀ < 0` a left real point alive at time `t` (for the reflected driver), with centred image
`−X^{y₀}_t`. Every real `ỹ` left of that image is sent by `F` to a real point left of `x₀`. -/
theorem exists_extendFrom_eq_lt (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {F : ℂ → ℂ}
    (hFeq : EqOn F (fwdMapInv W t) H) (hFc : ContinuousOn F Hbar) {y₀ : ℝ}
    (hy₀ : Alive (fun s => -W s) y₀ t) {yt : ℝ} (hyt : yt < -cflow (fun s => -W s) y₀ t) :
    ∃ x : ℝ, x < -y₀ ∧ F yt = x := by
  have hW' : Continuous fun s => -W s := hW.neg
  set f : ℝ → ℝ := fun y => cflow (fun s => -W s) y t with hf
  have halive : ∀ y, y₀ ≤ y → Alive (fun s => -W s) y t := fun y hy => hy₀.of_le hW' hy ht
  -- `f` is `1`-Lipschitz and increasing on `[y₀, ∞)`
  have hlip : ∀ y y', y₀ ≤ y → y ≤ y' → f y ≤ f y' ∧ f y' - f y ≤ y' - y := by
    intro y y' hy hyy'
    rcases hyy'.eq_or_lt with rfl | hlt
    · simp
    · obtain ⟨h1, h2⟩ := cflow_lt_and_sub_le hW' (halive y hy) hlt ht ⟨ht, le_rfl⟩
      exact ⟨h1.le, h2⟩
  have hcont : ∀ Y, ContinuousOn f (Icc y₀ Y) := by
    intro Y
    refine LipschitzOnWith.continuousOn (K := 1) (LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_)
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
    rcases le_total a b with hab | hab
    · obtain ⟨h1, h2⟩ := hlip a b ha.1 hab
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · obtain ⟨h1, h2⟩ := hlip b a hb.1 hab
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  -- a point `Y` whose image is beyond `−ỹ`
  set Y : ℝ := max y₀ (-yt - W t) + 1 with hY
  have hy₀Y : y₀ ≤ Y := by rw [hY]; linarith [le_max_left y₀ (-yt - W t)]
  have hfY : -yt ≤ f Y := by
    have := le_cflow_of_alive hW' ht (halive Y hy₀Y)
    have h2 : -yt - W t ≤ max y₀ (-yt - W t) := le_max_right _ _
    simp only [hf] at this ⊢
    linarith
  obtain ⟨y, hyI, hfy⟩ := intermediate_value_Icc hy₀Y (hcont Y) ⟨(by simp only [hf]; linarith), hfY⟩
  have hy₀y : y₀ < y := by
    rcases hyI.1.eq_or_lt with h | h
    · exfalso
      rw [← h] at hfy
      simp only [hf] at hfy
      linarith
    · exact h
  have hsol := WangWu.isForwardSol_neg_of_alive hW (halive y hyI.1)
  have hsol' : QuantumZipper.IsForwardSol W (((-y : ℝ)) : ℂ) t
      (fun s => -(cflow (fun s => -W s) y s : ℂ)) := by
    have e : (((-y : ℝ)) : ℂ) = -(y : ℂ) := by push_cast; ring
    rw [e]; exact hsol
  have hF := Zhan.extendFrom_eq_of_isForwardSol hW hW0 ht hFeq hFc hsol'
  refine ⟨-y, by linarith, ?_⟩
  have e2 : -(cflow (fun s => -W s) y t : ℂ) = (yt : ℂ) := by
    have : cflow (fun s => -W s) y t = -yt := hfy
    rw [this]; push_cast; ring
  rw [e2] at hF
  exact hF

/-- **The last left mark is an alive point of the frozen reflected flow.** If the last left mark stays strictly
left of the driver on `[0, q]`, `q < t₂`, then `−x^{L,last}` is alive at `q` for the reflected frozen driver, with
centred image `w_q − V^{L,last}_q`. -/
theorem alive_last {k : ℝ} {j nR : ℕ} {xL : Fin (j + 1) → ℝ} {xR : Fin nR → ℝ} {ρL : Fin (j + 1) → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (j + 1) → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ) {q : ℝ≥0} {t₂ : ℝ} (hqt₂ : (q : ℝ) < t₂)
    (ht₂ : ENNReal.ofReal t₂ < ζ) (hgap : ∀ r : ℝ≥0, r ≤ q → vL (Fin.last j) r < w r) :
    Alive (fun s => -frozenDrive w t₂ s) (-xL (Fin.last j)) q ∧
      cflow (fun s => -frozenDrive w t₂ s) (-xL (Fin.last j)) q = w q - vL (Fin.last j) q := by
  have hfp := hp.isForcePath
  have hwf : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hfp.continuousOn_w ht₂
  have hlt : ∀ s ∈ Icc (0 : ℝ) q, (s.toNNReal : ℝ≥0∞) < ζ := fun s hs =>
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (hs.2.trans hqt₂.le)) ht₂
  have hfz : ∀ s ∈ Icc (0 : ℝ) q, frozenDrive w t₂ s = w s.toNNReal := fun s hs =>
    frozenDrive_eq ⟨hs.1, hs.2.trans hqt₂.le⟩
  set X : ℝ → ℝ := fun s => frozenDrive w t₂ s - vL (Fin.last j) s.toNNReal with hX
  have hXpos : ∀ s ∈ Icc (0 : ℝ) q, 0 < X s := fun s hs => by
    simp only [hX, hfz s hs]
    exact sub_pos.2 (hgap _ (Real.toNNReal_le_iff_le_coe.2 hs.2))
  have hsol : IsPosSol (fun s => -frozenDrive w t₂ s) (-xL (Fin.last j)) q X := by
    refine ⟨hwf.continuousOn.sub ((hfp.continuousOn_vL _).comp continuous_real_toNNReal.continuousOn
      fun s hs => hlt s hs), fun s hs => ⟨hXpos s hs, ?_⟩⟩
    have hs' := hlt s hs
    have heq := hfp.vL_eq hs' (Fin.last j)
    rw [Real.coe_toNNReal _ hs.1] at heq
    have hint : (∫ r in (0 : ℝ)..s, 2 / X r) =
        -∫ r in (0 : ℝ)..s, 2 / (vL (Fin.last j) r.toNNReal - w r.toNNReal) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs.1] at hr
      simp only [hX, hfz r ⟨hr.1, hr.2.trans hs.2⟩]
      rw [← neg_sub, div_neg]
    simp only [hX] at hint ⊢
    rw [hint, hfz s hs, heq]
    ring
  have hwf' : Continuous fun s => -frozenDrive w t₂ s := hwf.neg
  refine ⟨⟨X, hsol⟩, ?_⟩
  rw [cflow_eq_of_isPosSol hwf' hsol ⟨q.coe_nonneg, le_rfl⟩]
  simp only [hX, hfz q ⟨q.coe_nonneg, le_rfl⟩, Real.toNNReal_coe]

/-- **`F̄_q` beyond the last left mark.** If the last left mark stays strictly left of the driver on `[0, q]`, `q < ζ`,
and `γ` generates the chain on `[0, q]` with its tip, then `F̄_q` sends every real point left of
`V^{L,last}_q − w_q` to a real point left of `x^{L,last}`. -/
theorem exists_extendFrom_eq_lt_last {k : ℝ} {j nR : ℕ} {xL : Fin (j + 1) → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin (j + 1) → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (j + 1) → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ)
    {q : ℝ≥0} (hqζ : (q : ℝ≥0∞) < ζ) (hgap : ∀ r : ℝ≥0, r ≤ q → vL (Fin.last j) r < w r) {γ : ℝ≥0 → ℂ}
    (hγ : Sec7.IsGeneratingTraceIcc w q γ) {yt : ℝ} (hyt : yt < vL (Fin.last j) q - w q) :
    ∃ x : ℝ, x < xL (Fin.last j) ∧ extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) q) yt = x := by
  have hfp := hp.isForcePath
  obtain ⟨t₂, hqt₂, ht₂⟩ := exists_real_btwn_of_lt hqζ
  have hwf : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hfp.continuousOn_w ht₂
  have ht₂0 : 0 ≤ t₂ := q.coe_nonneg.trans hqt₂.le
  have hW0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂0, hfp.w_zero]
  obtain ⟨hFeq0, -, hEq, hFc, -⟩ := hγ.extend_props hqt₂ hwf hfp.w_zero
  obtain ⟨hal, hcf⟩ := alive_last hp hqt₂ ht₂ hgap
  rw [hFeq0]
  obtain ⟨x, hx, hFx⟩ := exists_extendFrom_eq_lt (yt := yt) hwf hW0 q.coe_nonneg hEq hFc hal
    (by rw [hcf]; linarith)
  exact ⟨x, by linarith, hFx⟩

end Location

end InteractingSLE.ZhanGT4.A2P1
