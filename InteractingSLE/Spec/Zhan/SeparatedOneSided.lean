/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.SeparatedPair

/-!
# Transience for one mark on one side (`κ ≤ 4`)

Packet PROVE-ZHAN-B3. Astra, *Formalization proofs and dependency audit* (ruling R35), L1419: "Empty-side
one-force cases follow by inserting a zero-weight mark." Here the zero-weight mark is *removed* from a two-seed
evolution instead: the two-seed evolution with weights `(0, ρ)` (marks `0⁻, 0⁺`), whose trace is transient
(`Zhan.IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoSeed`), is on its infinite-lifetime event an evolution of the
one-mark seed word `(∅; 0⁺)` with weight `ρ` (`IsIntegratedSLEEvolution.dropLeft`: a zero-weight mark does not enter
the driving equation, and `ThresholdCondition` ignores it). The one-mark seed law is scale invariant in the
strongest sense: the word at any positive time is `(∅; R)` with `R > 0`, a dilation of every `(∅; x)`, `x > 0`, so
the restart at time `1` (`ae_codeLaw_compl_traceCodeSet_restart_one`) and dilation (`ae_tendsto_of_codeLaw_dilate`)
give transience for every one-sided word with one mark. The left case is the mirror image (`dropRight`).

## Main results

* `IsIntegratedSLEEvolution.dropLeft`, `IsIntegratedSLEEvolution.dropRight`: removing a zero-weight seed mark.
* `ae_codeLaw_compl_traceCodeSet_restart_one`: at time `1`, the canonical probability of no transient trace vanishes
  at almost every realized word, for every evolution with simple futures and a transient trace.
* `ae_tendsto_of_codeLaw_dilate`: transience from a vanishing canonical probability at a dilated word.
* `IsIntegratedSLEEvolution.ae_tendsto_norm_trace_right`, `…_left`: **one-force transience** for one mark
  `x_R > 0` (resp. `x_L < 0`) of weight `≥ κ/2 − 2`, `0 < κ ≤ 4`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Zhan

open Sec7.Dilation
open Sec7.RandRestart (TraceEvent traceCodeSet codeLaw wordAt)
open WangWu.TraceGlue (ShiftGood)

variable {κ : ℝ} {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-! ### Removing a zero-weight mark -/

/-- **Removing a zero-weight left mark** (single left mark, infinite lifetime almost surely): the remaining processes
are an integrated evolution of the right word. -/
theorem IsIntegratedSLEEvolution.dropLeft {xL ρL : Fin 1 → ℝ} {xR ρR : Fin nR → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hρ : ρL 0 = 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    IsIntegratedSLEEvolution κ (Fin.elim0 : Fin 0 → ℝ) xR Fin.elim0 ρR P 𝓕 W (fun i => i.elim0) VR B ζ := by
  obtain ⟨hB, hW, -, hVR, hpath⟩ := hE
  refine ⟨hB, hW, fun i => i.elim0, hVR, ?_⟩
  filter_upwards [hpath, hζ] with ω hp hζω
  obtain ⟨h1, -, h3, h4, -, h6, -, -, h9, h10, -, h12, h13, -, h15, -, h17, h18, -, -⟩ := hp
  refine ⟨h1, fun i => i.elim0, h3, h4, fun i => i.elim0, h6, fun _ _ i => i.elim0, fun _ _ i => i.elim0, h9,
    h10, fun _ _ i => i.elim0, h12, fun t ht => ?_, fun _ _ i => i.elim0, h15, fun i => i.elim0, h17,
    fun t ht h => ?_, fun h => ?_, fun T _ hT => ?_⟩
  · have e := h13 t ht
    rw [Fin.sum_univ_one, hρ] at e
    simp only [zero_div, intervalIntegral.integral_zero, add_zero] at e
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact e
  · refine h18 t ht (Or.inr (h.resolve_left ?_))
    simp only [Finset.univ_eq_empty, Finset.filter_empty, Finset.sum_empty]
    norm_num
  · rw [hζω] at h; exact absurd h ENNReal.top_ne_zero
  · rw [hζω] at hT; exact absurd hT ENNReal.coe_ne_top

/-- **Removing a zero-weight right mark** (single right mark, infinite lifetime almost surely). -/
theorem IsIntegratedSLEEvolution.dropRight {xL ρL : Fin nL → ℝ} {xR ρR : Fin 1 → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin 1 → ℝ≥0 → Ω → ℝ} (hρ : ρR 0 = 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    IsIntegratedSLEEvolution κ xL (Fin.elim0 : Fin 0 → ℝ) ρL Fin.elim0 P 𝓕 W VL (fun i => i.elim0) B ζ := by
  obtain ⟨hB, hW, hVL, -, hpath⟩ := hE
  refine ⟨hB, hW, hVL, fun i => i.elim0, ?_⟩
  filter_upwards [hpath, hζ] with ω hp hζω
  obtain ⟨h1, h2, -, h4, h5, -, h7, h8, -, -, h11, -, h13, h14, -, h16, -, h18, -, -⟩ := hp
  refine ⟨h1, h2, fun i => i.elim0, h4, h5, fun i => i.elim0, h7, h8, fun _ _ i => i.elim0,
    fun _ _ i => i.elim0, h11, fun _ _ i => i.elim0, fun t ht => ?_, h14, fun _ _ i => i.elim0, h16,
    fun i => i.elim0, fun t ht h => ?_, fun h => ?_, fun T _ hT => ?_⟩
  · have e := h13 t ht
    rw [Fin.sum_univ_one (f := fun i => ∫ s in (0 : ℝ)..t, ρR i / _), hρ] at e
    simp only [zero_div, intervalIntegral.integral_zero, add_zero] at e
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact e
  · refine h18 t ht (Or.inl (h.resolve_right ?_))
    simp only [Finset.univ_eq_empty, Finset.filter_empty, Finset.sum_empty]
    norm_num
  · rw [hζω] at h; exact absurd h ENNReal.top_ne_zero
  · rw [hζω] at hT; exact absurd hT ENNReal.coe_ne_top

/-! ### The restart at time `1` and the dilation transfer -/

/-- **The restart at time `1`.** For an evolution whose lifetime is almost surely infinite and whose driver almost
surely is continuous, has simple mapped-out futures after rational times and only transient traces, the canonical
probability of no transient trace vanishes at almost every realized word at time `1`. -/
theorem ae_codeLaw_compl_traceCodeSet_restart_one (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hgood : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      ShiftGood (fun s : ℝ => W s.toNNReal ω) (range ((↑) : ℚ → ℝ)) ∧
      ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop) :
    ∀ᵐ ω ∂P, codeLaw κ ρL ρR (traceCodeSet (nL := nL) (nR := nR))ᶜ (wordAt W VL VR (fun _ => 1) ω) = 0 := by
  have hT := isStoppingTime_const 𝓕 (1 : ℝ≥0)
  set A : Set Ω := {ω | ((1 : ℝ≥0) : ℝ≥0∞) < ζ ω} with hAdef
  have hA : MeasurableSet[hT.measurableSpace] A := by
    rw [IsStoppingTime.measurableSpace_const]
    have h := hE.2.1 1 univ MeasurableSet.univ
    simp only [mem_univ, and_true] at h
    exact h
  have hAT : ∀ ω ∈ A, (((fun _ => (1 : ℝ≥0)) ω : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      (0 < (fun _ => (1 : ℝ≥0)) ω ∨ ∀ i j, xL i < xR j) := fun ω hω => ⟨hω, Or.inl one_pos⟩
  have hlaw := Sec7.RandRestart.measure_restart_codeEvent hκ hE hT hA hAT
    (Φ := fun w τ => ¬ TraceEvent w τ) Sec7.RandRestart.measurableSet_traceCodeSet.compl
    Sec7.RandRestart.compl_traceCodeSet_iff Sec7.RandRestart.not_traceEvent_congr
  have hev : ∀ᵐ ω ∂P, TraceEvent (fun t => W ((1 : ℝ≥0) + t) ω - W (1 : ℝ≥0) ω)
      (ζ ω - ((1 : ℝ≥0) : ℝ≥0∞)) := by
    filter_upwards [hgood] with ω ⟨hζ, hWc, hW0, hsg, htr⟩
    rw [hζ, ENNReal.top_sub_coe]
    exact traceEvent_shiftNN hWc hW0 hsg htr 1
  have hlaw0 : ∫⁻ ω in A, codeLaw κ ρL ρR (traceCodeSet (nL := nL) (nR := nR))ᶜ
      (wordAt W VL VR (fun _ => 1) ω) ∂P = 0 := by
    rw [← hlaw]
    exact measure_mono_null (fun ω h => h.2) (ae_iff.1 hev)
  obtain ⟨st, _, _, hstm, _, _, hid⟩ := Sec7.RandRestart.restart_core hκ hE hT hA hAT
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  have hcongr : (fun ω => codeLaw κ ρL ρR (traceCodeSet (nL := nL) (nR := nR))ᶜ
      (wordAt W VL VR (fun _ => 1) ω)) =ᵐ[P.restrict A]
      fun ω => codeLaw κ ρL ρR (traceCodeSet (nL := nL) (nR := nR))ᶜ (st ω) := by
    filter_upwards [(ae_restrict_iff' hAm).2 hid] with ω h
    rw [h.1]
  have hmeas : Measurable fun ω => codeLaw κ ρL ρR (traceCodeSet (nL := nL) (nR := nR))ᶜ (st ω) :=
    (Sec7.RandRestart.measurable_codeLaw Sec7.RandRestart.measurableSet_traceCodeSet.compl).comp hstm
  rw [lintegral_congr_ae hcongr, lintegral_eq_zero_iff hmeas] at hlaw0
  have hAfull : ∀ᵐ ω ∂P, ω ∈ A := hgood.mono fun ω h => by
    show ((1 : ℝ≥0) : ℝ≥0∞) < ζ ω
    rw [h.1]; exact ENNReal.coe_lt_top
  filter_upwards [(ae_restrict_iff' hAm).1 hlaw0, hid, hAfull] with ω h1 h2 h3
  rw [← (h2 h3).1]
  exact h1 h3

/-- **Transience from a vanishing canonical probability at a dilated word.** If the dilation by `c` of a separated
word has canonical probability `0` of no transient trace, then almost surely every generating trace of an evolution
of the word (infinite lifetime, continuous driver) tends to `∞`. -/
theorem ae_tendsto_of_codeLaw_dilate (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ W 0 ω = 0) {c : ℝ≥0} (hc : c ≠ 0)
    (hsep : ∀ i j, xL i < xR j)
    (hcode : codeLaw κ ρL ρR (traceCodeSet (nL := nL) (nR := nR))ᶜ
      ((fun i => (√(c : ℝ))⁻¹ * xL i), fun j => (√(c : ℝ))⁻¹ * xR j) = 0) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hsep' : ∀ i j, (√(c : ℝ))⁻¹ * xL i < (√(c : ℝ))⁻¹ * xR j := fun i j =>
    mul_lt_mul_of_pos_left (hsep i j) (inv_pos.2 (sqrt_pos_of_ne hc))
  have e := Sec7.RandRestart.measure_eventOf_eq_codeLaw hκ hsep' (hE.dilate hc)
    (Φ := fun w τ => ¬ TraceEvent w τ) Sec7.RandRestart.measurableSet_traceCodeSet.compl
    Sec7.RandRestart.compl_traceCodeSet_iff Sec7.RandRestart.not_traceEvent_congr
  rw [hcode] at e
  have hae : ∀ᵐ ω ∂P, TraceEvent (fun t => dilProc c W t ω) (ζ ω / c) := ae_iff.2 e
  filter_upwards [hae, hζ] with ω hω ⟨hζω, hWc, hW0⟩ η hη
  rw [hζω, ENNReal.top_div_of_ne_top ENNReal.coe_ne_top] at hω
  obtain ⟨η₀, hη₀, htr⟩ := traceEvent_of_dilPath (w := fun t => W t ω) hc hω
  have heq : η = η₀ := funext fun t => hη.eq_of_le hη₀ hWc.continuousOn hW0 le_top
  rw [heq]
  exact htr rfl

/-! ### One mark on one side -/

theorem hasAdmissiblePartialSums_right {k : ℝ} {ρL xL : Fin 0 → ℝ} {ρR : Fin 1 → ℝ} (hR : k / 2 - 2 ≤ ρR 0)
    (xR : Fin 1 → ℝ) : Sec4.HasAdmissiblePartialSums k ρL ρR xL xR := by
  refine ⟨fun x _ ⟨i, _⟩ => i.elim0, fun x _ ⟨i, hi⟩ => ?_⟩
  have e : (Finset.univ.filter fun j => xR j ≤ x) = Finset.univ := by
    ext j
    fin_cases j; fin_cases i
    simpa using hi
  rw [e, Fin.sum_univ_one]
  exact hR

theorem hasAdmissiblePartialSums_left {k : ℝ} {ρL : Fin 1 → ℝ} {ρR xR : Fin 0 → ℝ} (hL : k / 2 - 2 ≤ ρL 0)
    (xL : Fin 1 → ℝ) : Sec4.HasAdmissiblePartialSums k ρL ρR xL xR := by
  refine ⟨fun x _ ⟨i, hi⟩ => ?_, fun x _ ⟨i, _⟩ => i.elim0⟩
  have e : (Finset.univ.filter fun j => x < xL j) = Finset.univ := by
    ext j
    fin_cases j; fin_cases i
    simpa using hi
  rw [e, Fin.sum_univ_one]
  exact hL

/-- **One-force transience, one right mark** (`0 < κ ≤ 4`): no left mark, one right mark `x_R > 0` of weight
`≥ κ/2 − 2`. Almost surely every continuous generating trace on `[0, ∞)` tends to `∞`. -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_right (hκ : 0 < κ) (hκ4 : κ ≤ 4) {xL ρL : Fin 0 → ℝ}
    {xR ρR : Fin 1 → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 1 → ℝ≥0 → Ω → ℝ} (hρR : κ / 2 - 2 ≤ ρR 0)
    (hxR : 0 < xR 0) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  obtain rfl : ρL = Fin.elim0 := funext fun i => i.elim0
  obtain ⟨Ω₂, m₂, P₂, hP₂, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, hE₂⟩ :=
    Sec2.exists_isIntegratedSLEEvolution_twoSeed hκ (xL := fun _ => 0) (xR := fun _ => 0)
      (fun _ => rfl) (fun _ => rfl) (fun _ => 0) ρR
  have hgood₂ := IsIntegratedSLEEvolution.ae_seedGood hκ hκ4 (ρL := fun _ => 0) (by linarith) hρR hE₂
  have hE₁ := IsIntegratedSLEEvolution.dropLeft (ρL := fun _ => 0) rfl hE₂ (hgood₂.mono fun ω h => h.1)
  have hres := ae_codeLaw_compl_traceCodeSet_restart_one hκ hE₁
    (hgood₂.mono fun ω h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩)
  obtain ⟨ω, hω, hg⟩ := (hres.and hgood₂).exists
  have hR0 : 0 < VR₂ 0 1 ω - W₂ 1 ω := sub_pos.2 (hg.2.2.2.2.2.2.2.1 1 one_pos).2
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = xR 0 / (VR₂ 0 1 ω - W₂ 1 ω) := ⟨_, rfl⟩
  have hs0 : 0 < s := hs ▸ div_pos hxR hR0
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (c : ℝ) = s ^ 2 := ⟨⟨s ^ 2, sq_nonneg s⟩, rfl⟩
  have hcne : c ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hc
    exact (pow_pos hs0 2).ne' hc.symm
  have hsqrt : √(c : ℝ) = s := by rw [hc]; exact Real.sqrt_sq hs0.le
  have hxR0 : xR 0 ≠ 0 := hxR.ne'
  have hword : ((fun i => (√(c : ℝ))⁻¹ * xL i), fun j => (√(c : ℝ))⁻¹ * xR j) =
      wordAt W₂ (fun i => i.elim0) VR₂ (fun _ => 1) ω := by
    refine Prod.ext (funext fun i => i.elim0) (funext fun j => ?_)
    rw [Fin.fin_one_eq_zero j, hsqrt, hs]
    simp only [wordAt]
    field_simp
  have hadm := hasAdmissiblePartialSums_right (ρL := Fin.elim0) (xL := xL) hρR xR
  have hF : IsOrderedForceWord xL xR :=
    ⟨fun i => i.elim0, fun i => i.elim0, fun i j _ => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j],
      fun i => by rw [Fin.fin_one_eq_zero i]; exact hxR.le⟩
  refine ae_tendsto_of_codeLaw_dilate hκ hE ?_ hcne (fun i => i.elim0) (by rw [hword]; exact hω)
  filter_upwards [IsIntegratedSLEEvolution.ae_shiftGood hκ hκ4 hF hadm hE] with ω h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- **One-force transience, one left mark** (`0 < κ ≤ 4`): one left mark `x_L < 0` of weight `≥ κ/2 − 2`, no right
mark. Almost surely every continuous generating trace on `[0, ∞)` tends to `∞`. -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_left (hκ : 0 < κ) (hκ4 : κ ≤ 4) {xL ρL : Fin 1 → ℝ}
    {xR ρR : Fin 0 → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ} (hρL : κ / 2 - 2 ≤ ρL 0)
    (hxL : xL 0 < 0) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  obtain rfl : ρR = Fin.elim0 := funext fun i => i.elim0
  obtain ⟨Ω₂, m₂, P₂, hP₂, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, hE₂⟩ :=
    Sec2.exists_isIntegratedSLEEvolution_twoSeed hκ (xL := fun _ => 0) (xR := fun _ => 0)
      (fun _ => rfl) (fun _ => rfl) ρL (fun _ => 0)
  have hgood₂ := IsIntegratedSLEEvolution.ae_seedGood hκ hκ4 (ρR := fun _ => 0) hρL (by linarith) hE₂
  have hE₁ := IsIntegratedSLEEvolution.dropRight (ρR := fun _ => 0) rfl hE₂ (hgood₂.mono fun ω h => h.1)
  have hres := ae_codeLaw_compl_traceCodeSet_restart_one hκ hE₁
    (hgood₂.mono fun ω h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩)
  obtain ⟨ω, hω, hg⟩ := (hres.and hgood₂).exists
  have hL0 : 0 < W₂ 1 ω - VL₂ 0 1 ω := sub_pos.2 (hg.2.2.2.2.2.2.2.1 1 one_pos).1
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = -xL 0 / (W₂ 1 ω - VL₂ 0 1 ω) := ⟨_, rfl⟩
  have hs0 : 0 < s := hs ▸ div_pos (neg_pos.2 hxL) hL0
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (c : ℝ) = s ^ 2 := ⟨⟨s ^ 2, sq_nonneg s⟩, rfl⟩
  have hcne : c ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hc
    exact (pow_pos hs0 2).ne' hc.symm
  have hsqrt : √(c : ℝ) = s := by rw [hc]; exact Real.sqrt_sq hs0.le
  have hxL0 : xL 0 ≠ 0 := hxL.ne
  have hword : ((fun i => (√(c : ℝ))⁻¹ * xL i), fun j => (√(c : ℝ))⁻¹ * xR j) =
      wordAt W₂ VL₂ (fun i => i.elim0) (fun _ => 1) ω := by
    refine Prod.ext (funext fun i => ?_) (funext fun j => j.elim0)
    rw [Fin.fin_one_eq_zero i, hsqrt, hs]
    simp only [wordAt]
    field_simp
    ring
  have hadm := hasAdmissiblePartialSums_left (ρR := Fin.elim0) (xR := xR) hρL xL
  have hF : IsOrderedForceWord xL xR :=
    ⟨fun i j _ => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j], fun i => by
      rw [Fin.fin_one_eq_zero i]; exact hxL.le, fun i => i.elim0, fun i => i.elim0⟩
  refine ae_tendsto_of_codeLaw_dilate hκ hE ?_ hcne (fun _ j => j.elim0) (by rw [hword]; exact hω)
  filter_upwards [IsIntegratedSLEEvolution.ae_shiftGood hκ hκ4 hF hadm hE] with ω h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

end InteractingSLE.Zhan
