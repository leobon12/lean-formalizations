/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactImgCode
import InteractingSLE.Spec.Sec7.ContinuityProb2Join
import InteractingSLE.Spec.Sec7.ContinuityProb2Restart
import InteractingSLE.Spec.Sec7.ContinuityProb4Band
import InteractingSLE.Spec.Sec7.ContinuityProb4Aux113
import InteractingSLE.Spec.Sec2.Assembly2Shift
import InteractingSLE.Spec.Sec2.PatchingConcat
import InteractingSLE.Spec.Sec7.Aux117

/-!
# The image driver of the contact step, part 5: continuation of a killed `SLE₄(ρ)` path

Packet PROVE-WW-B16, steps B6–B7 of PROVE-WW-B15's plan. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`,
ruling R31), proof of Proposition 4.18 (text dump L1629–L1636): "Hence its law is the nonnegative-cumulative force-point
law. The trace lemma and Corollary 4.13 imply that its first boundary limit is precisely `β(s)` … An interior endpoint
could be continued by the original continuous trace."

Let `(W, VL, VR)` satisfy the integrated `SLE₄(ρ)` equations of a random word with nonnegative cumulative weights on
`[0, T)`, driven by a Brownian motion `B` of a filtration to which the coordinates are adapted, strictly separated at
positive times before `T`, and let the driver have a simple trace in `ℍ` before `T`. Then almost surely the driver has
a continuation `X` (continuous, `X = W` before `T`) whose trace is a simple transient trace in `ℍ` (`GoodPath X ⊤`):
**`ae_exists_continuation`**.

**Proof.** Restart at a positive rational `q < T`: the state `V_q − W_q` is a strictly separated ordered word,
`𝓘_q`-measurable, and the future driving path `B_{q+·} − B_q` is independent of `𝓘_q` with Wiener law
(`joint_law_restart`). At every such word Wiener-almost every path drives a canonical solution with a good code
(`codeLaw_compl_goodCode_eq_zero` and the solvability of separated words), so almost surely the restarted path drives one,
which agrees with the restarted killed path before `T − q` (local pathwise uniqueness, `Sec7.Band.le_lifetime_of_upTo`).
Concatenate at `q` (`Sec2.concatAt`); the trace of the concatenation is the killed trace on `[0, q]` joined with the
`F_q`-image of the good trace (`Sec7.IsGeneratingTraceIcc.join`), simple and in `ℍ` because `F_q` maps `ℍ` injectively
into `ℍ \ K_q` (`goodPath_join`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

namespace ImgDrv

/-! ### Joining a simple trace with the image of a good trace -/

section Join

open Sec7

theorem IsGeneratingTraceIcc.congr_of_lt {w w' : ℝ≥0 → ℝ} {σ : ℝ≥0} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (h : IsGeneratingTraceIcc w σ η) (hσ : (σ : ℝ≥0∞) < T)
    (hww' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → w t = w' t) : IsGeneratingTraceIcc w' σ η := by
  obtain ⟨t₂, hσt₂, ht₂T⟩ := exists_real_btwn_of_lt hσ
  have heq : ∀ r ∈ Icc (0 : ℝ) t₂, w r.toNNReal = w' r.toNNReal := fun r hr =>
    hww' _ ((ENNReal.ofReal_le_ofReal hr.2).trans_lt ht₂T)
  refine ⟨Sec7.IsGeneratingTrace.congr_lt h.1 fun t ht => (hww' t (lt_trans ht hσ)).symm, ?_, ?_⟩
  · rw [← fwdHull_eq_of_eqOn σ.coe_nonneg hσt₂ heq]; exact h.2.1
  · rw [← fwdMapInv_eq_of_eqOn σ.coe_nonneg hσt₂ heq]; exact h.2.2

theorem subset_of_isFilling {K A : Set ℂ} (h : IsFilling K A) : A ∩ H ⊆ K := by
  intro z ⟨hzA, hzH⟩
  by_contra hzK
  obtain ⟨⟨z₀, -, hcc⟩, -⟩ := h
  have hz : z ∈ H \ K := ⟨hzH, hzK⟩
  rw [← hcc] at hz
  exact (connectedComponentIn_subset _ _ hz).2 hzA

/-- **The joined trace is good**: a continuous driver whose chain is generated on `[0, q]` (with tip) by a simple
trace in `ℍ`, and whose restarted driver at `q` has a simple transient trace in `ℍ` on `[0, ∞)`, is a good path. -/
theorem goodPath_join {X : ℝ≥0 → ℝ} (hXc : Continuous X) (hX0 : X 0 = 0) {q : ℝ≥0} {γ η₂ : ℝ≥0 → ℂ}
    (h₁ : IsGeneratingTraceIcc X q γ) (hγinj : ∀ s t : ℝ≥0, s ≤ q → t ≤ q → γ s = γ t → s = t)
    (hγH : ∀ t : ℝ≥0, 0 < t → t ≤ q → γ t ∈ H) (h₂ : IsGeneratingTrace (shiftNN X q) ⊤ η₂)
    (hinj₂ : Function.Injective η₂) (hH₂ : ∀ t, 0 < t → η₂ t ∈ H)
    (htend₂ : Tendsto (fun t => ‖η₂ t‖) atTop atTop) : GoodPath X ⊤ := by
  have hXon : ContinuousOn X {s : ℝ≥0 | (s : ℝ≥0∞) < q + ⊤} := hXc.continuousOn
  obtain ⟨hJ, hJt⟩ := IsGeneratingTraceIcc.join hXon hX0 h₁ h₂
  rw [add_top] at hJ
  set J := joinTrace X q γ η₂ with hJdef
  -- the inverse map at `q`
  set Wr : ℝ → ℝ := fun s : ℝ => X s.toNNReal with hWr
  have hWrc : Continuous Wr := hXc.comp continuous_real_toNNReal
  have hWr0 : Wr 0 = 0 := by simp [hWr, hX0]
  have hq0 : (0 : ℝ) ≤ q := q.coe_nonneg
  have hσt₂ : (q : ℝ) < (q : ℝ) + 1 := lt_add_one _
  have hwc₂ : Continuous (frozenDrive X ((q : ℝ) + 1)) :=
    continuous_frozenDrive_of_lt hXon (by simp)
  obtain ⟨hF, -, hEq, -, -, -, -⟩ := h₁.extend_props hσt₂ hwc₂ hX0
  -- after `q` the joined trace is `F_q(η₂(t − q)) ∈ ℍ \ K_q`
  have hafter : ∀ t : ℝ≥0, q < t → J t = fwdMapInv Wr q (η₂ (t - q)) ∧
      fwdMapInv Wr q (η₂ (t - q)) ∈ H \ fwdHull Wr q := by
    intro t ht
    have hpos : 0 < t - q := tsub_pos_of_lt ht
    have hmem := hH₂ _ hpos
    have e : J t = fwdMapInv Wr q (η₂ (t - q)) := by
      rw [hJdef, joinTrace_of_lt ht]
      show extendFrom H (fwdMapInv (fun s : ℝ => X s.toNNReal) q) (η₂ (t - q)) = _
      rw [hF, hEq hmem, ← hF]
    exact ⟨e, QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWrc hWr0 hq0 hmem⟩
  have hbefore : ∀ t : ℝ≥0, t ≤ q → J t = γ t := fun t ht => joinTrace_of_le ht
  -- before `q` the trace lies in the hull at `q`
  have hγK : ∀ t : ℝ≥0, 0 < t → t ≤ q → γ t ∈ fwdHull Wr q := fun t ht htq =>
    subset_of_isFilling h₁.2.1 ⟨⟨t, ⟨zero_le, htq⟩, rfl⟩, hγH t ht htq⟩
  refine goodPath_of_trace hXc hX0 hJ ?_ ?_ (hJt rfl htend₂)
  · intro s t hst
    rcases le_or_gt s q with hs | hs <;> rcases le_or_gt t q with ht | ht
    · rw [hbefore s hs, hbefore t ht] at hst
      exact hγinj s t hs ht hst
    · exfalso
      rw [hbefore s hs, (hafter t ht).1] at hst
      have h2 := (hafter t ht).2
      rw [← hst] at h2
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h0 | h0
      · rw [← h0, h₁.1.1] at h2
        have h3 : (0 : ℝ) < (0 : ℂ).im := h2.1
        simp at h3
      · exact h2.2 (hγK s h0 hs)
    · exfalso
      rw [hbefore t ht, (hafter s hs).1] at hst
      have h2 := (hafter s hs).2
      rw [hst] at h2
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | h0
      · rw [← h0, h₁.1.1] at h2
        have h3 : (0 : ℝ) < (0 : ℂ).im := h2.1
        simp at h3
      · exact h2.2 (hγK t h0 ht)
    · rw [(hafter s hs).1, (hafter t ht).1] at hst
      have hinj := QuantumZipper.RS.injOn_fwdMapInv_H hWrc hWr0 hq0 (hH₂ _ (tsub_pos_of_lt hs))
        (hH₂ _ (tsub_pos_of_lt ht)) hst
      have e := hinj₂ hinj
      have := congrArg (· + q) e
      simpa [tsub_add_cancel_of_le hs.le, tsub_add_cancel_of_le ht.le] using this
  · intro t ht
    rcases le_or_gt t q with htq | htq
    · rw [hbefore t htq]; exact hγH t ht htq
    · rw [(hafter t htq).1]; exact (hafter t htq).2.1

end Join

/-! ### The restart at a deterministic time -/

section Restart

open Sec2 Sec2.Restart QuantumZipper.StrongMarkov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓘 : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ}

/-- **The restart at a deterministic time `q`** (simple Markov property in law form): for an `𝓘_q`-measurable state `st`
and an event `A ∈ 𝓘_q`, `P(A ∩ {(st, B_{q+·} − B_q) ∈ E}) = ∫_A wienerPath(E_st) dP`. -/
theorem joint_law_restart (hB : IsFilteredBrownianReal 𝓘 B P) (hBc : ∀ ω, Continuous (B · ω)) (q : ℝ≥0)
    {α : Type*} [MeasurableSpace α] {st : Ω → α} (hst : Measurable[𝓘 q] st) {A : Set Ω}
    (hA : MeasurableSet[𝓘 q] A) {E : Set (α × (ℝ≥0 → ℝ))} (hE : MeasurableSet E) :
    P (A ∩ (fun ω => (st ω, smPath B (fun _ => q) ω)) ⁻¹' E) =
      ∫⁻ ω in A, wienerPath (Prod.mk (st ω) ⁻¹' E) ∂P := by
  have hBm : ∀ t, Measurable (B t) := fun t => (hB.2.1 t).mono (𝓘.le t) le_rfl
  set g : Ω → ℝ≥0 → ℝ := smPath B (fun _ => q) with hg
  have hgm : Measurable g := measurable_smPath hBc hBm measurable_const
  have hstm : Measurable st := hst.mono (𝓘.le q) le_rfl
  have hAm : MeasurableSet A := 𝓘.le q _ hA
  have hind := indep_future hB q
  have hlaw : P.map g = wienerPath :=
    map_path_eq_wienerPath (isBrownianReal_smShift hB.1.toIsPreBrownianReal hBc hBm (indep_future hB)
      (isStoppingTime_const 𝓘 q)).toIsPreBrownianReal hgm
  have hpair : Measurable fun ω => (st ω, g ω) := hstm.prodMk hgm
  have hjoint : (P.restrict A).map (fun ω => (st ω, g ω)) = ((P.restrict A).map st).prod wienerPath := by
    refine (Measure.prod_eq fun D F hD hF => ?_).symm
    rw [Measure.map_apply hpair (hD.prod hF), Measure.map_apply hstm hD, ← hlaw, Measure.map_apply hgm hF,
      Measure.restrict_apply (hpair (hD.prod hF)), Measure.restrict_apply (hstm hD)]
    have hDA : MeasurableSet[𝓘 q] (st ⁻¹' D ∩ A) := (hst hD).inter hA
    have e : (fun ω => (st ω, g ω)) ⁻¹' (D ×ˢ F) ∩ A = (st ⁻¹' D ∩ A) ∩ g ⁻¹' F := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_prod]
      tauto
    rw [e]
    exact (Indep_iff _ _ _).1 hind _ _ hDA ⟨F, hF, rfl⟩
  rw [inter_comm, ← Measure.restrict_apply (hpair hE), ← Measure.map_apply hpair hE, hjoint, Measure.prod_apply hE]
  rw [lintegral_map (measurable_measure_prodMk_left hE) hstm]

end Restart

/-! ### The continuation -/

section Continuation

open Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart QuantumZipper.StrongMarkov

variable {nL nR : ℕ}

theorem measurableSet_ordered :
    MeasurableSet {s : (Fin nL → ℝ) × (Fin nR → ℝ) | IsOrderedForceWord s.1 s.2} := by
  have e : {s : (Fin nL → ℝ) × (Fin nR → ℝ) | IsOrderedForceWord s.1 s.2} =
      ((⋂ i : Fin nL, ⋂ j : Fin nL, {s : (Fin nL → ℝ) × (Fin nR → ℝ) | i ≤ j → s.1 j ≤ s.1 i}) ∩
        ⋂ i : Fin nL, {s : (Fin nL → ℝ) × (Fin nR → ℝ) | s.1 i ≤ 0}) ∩
      ((⋂ i : Fin nR, ⋂ j : Fin nR, {s : (Fin nL → ℝ) × (Fin nR → ℝ) | i ≤ j → s.2 i ≤ s.2 j}) ∩
        ⋂ i : Fin nR, {s : (Fin nL → ℝ) × (Fin nR → ℝ) | 0 ≤ s.2 i}) := by
    ext s
    simp only [IsOrderedForceWord, Antitone, Monotone, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    tauto
  rw [e]
  have h1 : ∀ i : Fin nL, Measurable fun s : (Fin nL → ℝ) × (Fin nR → ℝ) => s.1 i := fun i =>
    (measurable_pi_apply i).comp measurable_fst
  have h2 : ∀ i : Fin nR, Measurable fun s : (Fin nL → ℝ) × (Fin nR → ℝ) => s.2 i := fun i =>
    (measurable_pi_apply i).comp measurable_snd
  refine ((MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_).inter
    (MeasurableSet.iInter fun i => measurableSet_le (h1 i) measurable_const)).inter
    ((MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_).inter
    (MeasurableSet.iInter fun i => measurableSet_le measurable_const (h2 i)))
  · by_cases hij : i ≤ j
    · simp only [hij, true_implies]; exact measurableSet_le (h1 j) (h1 i)
    · simp only [hij, false_implies, ofPred_true, MeasurableSet.univ]
  · by_cases hij : i ≤ j
    · simp only [hij, true_implies]; exact measurableSet_le (h2 i) (h2 j)
    · simp only [hij, false_implies, ofPred_true, MeasurableSet.univ]

/-- The bad pairs (separated ordered start, driving path) whose canonical solution, if any, is not good. -/
def badSet (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Set (((Fin nL → ℝ) × (Fin nR → ℝ)) × (ℝ≥0 → ℝ)) :=
  {p | SepStart p.1 ∧ IsOrderedForceWord p.1.1 p.1.2 ∧ (p.1, enc p.2) ∉ lawSetS 4 ρL ρR goodCode}

theorem measurableSet_badSet (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : MeasurableSet (badSet ρL ρR) :=
  (measurableSet_sepStart.preimage measurable_fst).inter ((measurableSet_ordered.preimage measurable_fst).inter
    ((measurable_fst.prodMk (measurable_enc.comp measurable_snd))
      (measurableSet_lawSetS (a := 4) (ρL := ρL) (ρR := ρR) measurableSet_goodCode)).compl)

/-- **At every start the bad driving paths are Wiener-null** (nonnegative cumulative weights). -/
theorem wienerPath_badSet_eq_zero {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hcum : HasNonnegCumWeights ρL ρR)
    (s : (Fin nL → ℝ) × (Fin nR → ℝ)) : wienerPath (Prod.mk s ⁻¹' badSet ρL ρR) = 0 := by
  by_cases hs : SepStart s ∧ IsOrderedForceWord s.1 s.2
  · obtain ⟨hsep, hF⟩ := hs
    obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ :=
      exists_isIntegratedSLEEvolution_assembled (a := 4) (by norm_num) hF
    have hsolv := Sec7.ae_solvable_of_isIntegratedSLEEvolution (by norm_num : (0 : ℝ) < 4) hsep hE₀
    have hcl := codeLaw_compl_goodCode_eq_zero hF hsep hcum
    refine measure_mono_null (t := {f | ¬ enc f ∈ Prod.fst '' CRel 4 s.1 s.2 ρL ρR} ∪
      Prod.mk s ⁻¹' restartSetS 4 ρL ρR goodCodeᶜ) ?_ (measure_union_null (ae_iff.1 hsolv) hcl)
    intro f hf
    obtain ⟨-, -, hnot⟩ := hf
    by_cases hc : enc f ∈ Prod.fst '' CRel 4 s.1 s.2 ρL ρR
    · right
      obtain ⟨x, hx, hxf⟩ := hc
      have hxg : x ∉ goodCode := fun hxg => hnot (by
        have := (mem_lawSetS_iff hsep hx).2 hxg
        rw [hxf] at this
        exact this)
      show (s, enc f) ∈ lawSetS 4 ρL ρR goodCodeᶜ
      have := (mem_lawSetS_iff hsep hx (S := goodCodeᶜ)).2 hxg
      rw [hxf] at this
      exact this
    · left; exact hc
  · refine measure_mono_null (fun f hf => ?_) measure_empty
    exact hs ⟨hf.1, hf.2.1⟩

/-- `Sec7.Aux117.IsWordEntrance` with the threshold condition excluded is a local integrated path. -/
theorem isSLEPathUpTo_of_isWordEntrance {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {T : ℝ≥0∞}
    (h : Sec7.Aux117.IsWordEntrance a xL xR ρL ρR w vL vR b T)
    (hnt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T →
      ¬ ForceWord.ThresholdCondition ρL ρR (w t) (fun i => vL i t) (fun j => vR j t)) :
    Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b T :=
  ⟨h.w_zero, h.vL_zero, h.vR_zero, h.continuousOn_w, h.continuousOn_vL, h.continuousOn_vR,
    fun {t} ht => h.antitone_vL t ht, fun {t} ht => h.vL_le_w t ht, fun {t} ht => h.w_le_vR t ht,
    fun {t} ht => h.monotone_vR t ht, fun {t} ht => h.integrable_gapL t ht, fun {t} ht => h.integrable_gapR t ht,
    fun {t} ht => h.w_eq t ht, fun {t} ht => h.vL_eq t ht, fun {t} ht => h.vR_eq t ht, h.volume_collisionL,
    h.volume_collisionR, fun {t} ht => hnt t ht⟩

/-- **Continuation of a killed `SLE₄(ρ)` path with nonnegative cumulative weights** (Wang–Wu, proof of Proposition
4.18, steps B6–B7). Let the coordinates be adapted to `𝓘`, satisfy the integrated equations of their random initial
word on `[0, T)` driven by a Brownian motion `B` of `𝓘` (`T > 0`, `{q < T} ∈ 𝓘_q`), be strictly separated from the driver
at positive times before `T`, and let the driver have a simple trace in `ℍ` before `T`. Then almost surely the driver
has a continuous continuation `X` (`X₀ = 0`, `X = W` before `T`) whose trace is a simple transient trace in `ℍ`. -/
theorem ae_exists_continuation {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓘 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓘 B P)
    (hBc : ∀ ω, Continuous (B · ω)) {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hWa : StronglyAdapted 𝓘 W) (hVLa : ∀ i, StronglyAdapted 𝓘 (VL i))
    (hVRa : ∀ j, StronglyAdapted 𝓘 (VR j)) {T : Ω → ℝ≥0∞}
    (hTq : ∀ q : ℝ≥0, MeasurableSet[𝓘 q] {ω | (q : ℝ≥0∞) < T ω}) (hT0 : ∀ ω, 0 < T ω)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hcum : HasNonnegCumWeights ρL ρR)
    (hE : ∀ᵐ ω ∂P, Sec7.Aux117.IsWordEntrance 4 (fun i => VL i 0 ω) (fun j => VR j 0 ω) ρL ρR
      (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (fun t => B t ω) (T ω))
    (hsepL : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < T ω → ∀ i, VL i t ω < W t ω)
    (hsepR : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < T ω → ∀ j, W t ω < VR j t ω)
    (hγ : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, (∀ σ : ℝ≥0, (σ : ℝ≥0∞) < T ω → Sec7.IsGeneratingTraceIcc (W · ω) σ γ) ∧
      (∀ s t : ℝ≥0, (s : ℝ≥0∞) < T ω → (t : ℝ≥0∞) < T ω → γ s = γ t → s = t) ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < T ω → γ t ∈ H) :
    ∀ᵐ ω ∂P, ∃ X : ℝ≥0 → ℝ, Continuous X ∧ X 0 = 0 ∧ (∀ t : ℝ≥0, (t : ℝ≥0∞) < T ω → X t = W t ω) ∧
      GoodPath X ⊤ := by
  have hq : ∀ q : ℚ, ∀ᵐ ω ∂P, 0 < q → (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < T ω →
      ∃ X : ℝ≥0 → ℝ, Continuous X ∧ X 0 = 0 ∧ (∀ t : ℝ≥0, (t : ℝ≥0∞) < T ω → X t = W t ω) ∧
        GoodPath X ⊤ := by
    intro q
    set q' : ℝ≥0 := (q : ℝ).toNNReal with hq'def
    set st : Ω → (Fin nL → ℝ) × (Fin nR → ℝ) := fun ω =>
      ((fun i => VL i q' ω - W q' ω), fun j => VR j q' ω - W q' ω) with hstdef
    have hst : Measurable[𝓘 q'] st := by
      exact Measurable.prodMk ((@measurable_pi_iff Ω (Fin nL) _ (𝓘 q') _ _).2 fun i =>
          (hVLa i q').measurable.sub (hWa q').measurable)
        ((@measurable_pi_iff Ω (Fin nR) _ (𝓘 q') _ _).2 fun j => (hVRa j q').measurable.sub (hWa q').measurable)
    have hlaw := joint_law_restart hB hBc q' hst (hTq q') (measurableSet_badSet ρL ρR)
    have hnull : P ({ω | (q' : ℝ≥0∞) < T ω} ∩
        (fun ω => (st ω, smPath B (fun _ => q') ω)) ⁻¹' badSet ρL ρR) = 0 := by
      rw [hlaw]
      simp only [wienerPath_badSet_eq_zero hcum, lintegral_zero]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull, hE, hγ] with ω hωbad hω hγω hq0 hωA
    have hq'0 : 0 < q' := Real.toNNReal_pos.2 (by exact_mod_cast hq0)
    -- the restarted state is a separated ordered word
    have hsep : SepStart (st ω) := fun i j => by
      show VL i q' ω - W q' ω < VR j q' ω - W q' ω
      linarith [hsepL ω q' hq'0 hωA i, hsepR ω q' hq'0 hωA j]
    have hord : IsOrderedForceWord (st ω).1 (st ω).2 :=
      ⟨fun i j hij => sub_le_sub_right (hω.antitone_vL q' hωA hij) _,
        fun i => sub_nonpos.2 (hω.vL_le_w q' hωA i),
        fun i j hij => sub_le_sub_right (hω.monotone_vR q' hωA hij) _,
        fun j => sub_nonneg.2 (hω.w_le_vR q' hωA j)⟩
    -- the restarted driving path drives a good canonical solution
    have hlS : (st ω, enc (smPath B (fun _ => q') ω)) ∈ lawSetS 4 ρL ρR goodCode := by
      by_contra hc
      exact hωbad ⟨hωA, hsep, hord, hc⟩
    obtain ⟨x, ⟨⟨hxF, -⟩, hxg⟩, hxe⟩ := hlS
    simp only [Prod.mk.injEq] at hxe
    have hxC : x ∈ CRel 4 (st ω).1 (st ω).2 ρL ρR := mem_cRelF_iff.1 ⟨hxF, hxe.1⟩
    have hxp : IsIntegratedSLEPath 4 (st ω).1 (st ω).2 ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) :=
      hxC.1.2.2
    have hgc : Continuous (smPath B (fun _ => q') ω) :=
      ((hBc ω).comp (continuous_const.add continuous_id)).sub continuous_const
    have hcb : cb x = Assembly2.shiftAt q' (fun t => B t ω) (B q' ω) := by
      funext t
      show dec x.1 t = _
      rw [hxe.2]
      exact dec_enc hgc.continuousWithinAt
    rw [hcb] at hxp
    -- the killed path as a local solution, restarted at `q'`
    have hT0' : ((0 : ℝ≥0) : ℝ≥0∞) < T ω := by simpa using hT0 ω
    have hord0 : IsOrderedForceWord (fun i => VL i 0 ω) (fun j => VR j 0 ω) := by
      have hw0 : W 0 ω = 0 := hω.w_zero
      refine ⟨fun i j hij => hω.antitone_vL 0 hT0' hij, fun i => ?_, fun i j hij => hω.monotone_vR 0 hT0' hij,
        fun j => ?_⟩
      · have := hω.vL_le_w 0 hT0' i; rwa [hw0] at this
      · have := hω.w_le_vR 0 hT0' j; rwa [hw0] at this
    have hup := isSLEPathUpTo_of_isWordEntrance hω fun t ht => by
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | h0
      · subst h0
        have h1 : (fun i => VL i 0 ω) = fun i => VL i 0 ω := rfl
        rw [show W 0 ω = 0 from hω.w_zero]
        exact hcum.not_thresholdCondition_zero hord0
      · simp only [ForceWord.ThresholdCondition, not_or, not_le]
        rw [Finset.filter_false_of_mem fun i _ => (hsepL ω t h0 ht i).ne,
          Finset.filter_false_of_mem fun j _ => (hsepR ω t h0 ht j).ne', Finset.sum_empty, Finset.sum_empty]
        norm_num
    have hsh := hup.shift hωA
    obtain ⟨hTle, hagree⟩ := Sec7.Band.le_lifetime_of_upTo hsep hsh hxp
    -- the good trace of the continuation after `q'`
    have hgood := mem_goodCode_iff.1 hxg
    have hζ : cζ x = ⊤ := hgood.1
    have hcwc : Continuous (cw x) := by
      have h := hxp.isForcePath.continuousOn_w
      rw [hζ] at h
      exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
    have hcw0 : cw x 0 = 0 := hxp.1
    rw [hζ] at hgood
    obtain ⟨η₂, hη₂, htend₂, -, -, hP₂⟩ := hgood.trace hcwc hcw0
    have hinj₂ : Function.Injective η₂ := fun a b hab => by
      have h := hP₂.inj (mem_Ici.2 a.coe_nonneg) (mem_Ici.2 b.coe_nonneg)
        (by simp only [Real.toNNReal_coe]; exact hab)
      exact NNReal.coe_injective h
    have hH₂ : ∀ t, 0 < t → η₂ t ∈ H := fun t ht => by
      have h := hP₂.mem_H (t : ℝ) (by exact_mod_cast ht)
      simpa only [Real.toNNReal_coe] using h
    -- the concatenation
    set X : ℝ≥0 → ℝ := concatAt q' (fun t => W t ω) (W q' ω) (cw x) with hXdef
    have hc : W q' ω + cw x 0 = W q' ω := by rw [hcw0, add_zero]
    have hXc : Continuous X := by
      have h := continuousOn_concatAt (τ₂ := ⊤) hωA hω.continuousOn_w hcwc.continuousOn hc
      rw [add_top] at h
      exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
    have hX0 : X 0 = 0 := by rw [hXdef, concatAt_of_lt hq'0]; exact hω.w_zero
    have hXW : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T ω → X t = W t ω := by
      intro t ht
      rcases lt_or_ge t q' with htq | htq
      · exact concatAt_of_lt htq
      · rw [hXdef, concatAt_of_le htq]
        have hlt : ((t - q' : ℝ≥0) : ℝ≥0∞) < T ω - q' := by
          rw [Assembly2.coe_lt_sub_iff, add_tsub_cancel_of_le htq]; exact ht
        have h := (hagree (t - q') hlt).1
        simp only [Assembly2.shiftAt, add_tsub_cancel_of_le htq] at h
        rw [← h]; ring
    have hshift : Sec7.shiftNN X q' = cw x := by
      funext s
      simp only [Sec7.shiftNN, hXdef, concatAt_of_le (le_add_of_nonneg_right zero_le : q' ≤ q' + s),
        concatAt_of_le (le_refl q'), add_tsub_cancel_left, tsub_self, hcw0]
      ring
    -- the trace before `q'`
    obtain ⟨γ, hγ1, hγ2, hγ3⟩ := hγω
    have h₁ : Sec7.IsGeneratingTraceIcc X q' γ :=
      IsGeneratingTraceIcc.congr_of_lt (hγ1 q' hωA) hωA fun t ht => (hXW t ht).symm
    have hle : ∀ t : ℝ≥0, t ≤ q' → (t : ℝ≥0∞) < T ω := fun t ht =>
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hωA
    refine ⟨X, hXc, hX0, hXW, goodPath_join hXc hX0 h₁ (fun s t hs ht => hγ2 s t (hle s hs) (hle t ht))
      (fun t ht htq => hγ3 t ht (hle t htq)) (by rw [hshift]; exact hη₂) hinj₂ hH₂ htend₂⟩
  filter_upwards [ae_all_iff.2 hq] with ω hω
  obtain ⟨q, -, hqpos, hqT⟩ := ENNReal.lt_iff_exists_rat_btwn.1 (hT0 ω)
  have hq0 : 0 < q := by
    have h : (0 : ℝ≥0) < (q : ℝ).toNNReal := by exact_mod_cast hqpos
    exact_mod_cast Real.toNNReal_pos.1 h
  exact hω q hq0 hqT

end Continuation

end ImgDrv

end InteractingSLE.WangWu
