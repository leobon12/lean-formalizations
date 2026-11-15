/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHiReduce
import InteractingSLE.Spec.Sec7.ContinuityProb5Aux106
import InteractingSLE.Spec.Sec7.ContinuityProb4Aux113

/-!
# Aux. lemma 113, `τ = ∞`: the one-sided phases and the trials for separated starts

Packet PROVE-TRIALS-HI. Specification §7.3, Aux. lemma 101 (`source/spec/p337-384.md` L214–L262, pp. 346–348) and
Aux. lemma 113 (pp. 370–372): "After a failure, … use the appropriate one-sided-driver phase until its first subsequent
midpoint hit or `τ` … An infinite such phase is transient by Aux. lemma 101, since deleting the opposite group removes
at least one active mark."

* `ae_tendsto_of_eventualBand_imp`: PROVE-SEC7-C5's band transfer (`Band.ae_tendsto_of_eventualBand`) on the event
  of an eventual band, with the finite angular clock assumed only there (the same proof);
* **named input `Aux101BandClockStatement κ`** (Aux. lemma 101 for the bands `U < 3/4`, `U > 1/4`): on an infinite
  lifetime with an eventual band the angular clock is finite (every `κ > 0`, no restriction on the weights);
* **`ae_not_nonTransientEvent_sep`**: for a separated ordered word with `N` marks, at least one on each side, under the
  smaller-count hypothesis, Aux. lemma 101 and the uniform trial bound, the evolution is almost surely not
  non-transient (`ae_not_nonTransientEvent_of_trials` with the one-sided phases).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace TrialsHi

open ZhanGT4 Zhan Sec7.Dilation Sec7.RandRestart Sec2 Sec2.Assembly Sec2.Restart Band

/-! ### Transience on an eventual band, on its event -/

section BandEvent

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {i₀ : Fin nL} {j₀ : Fin nR}

/-- **Transience on a final infinite band, on its event** (PROVE-SEC7-C5's `Band.ae_tendsto_of_eventualBand` with
the band and the finite angular clock assumed only on the event of an eventual band; the same proof). -/
theorem ae_tendsto_of_eventualBand_imp [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hsep : ∀ i j, xL i < xR j)
    (hredR : ∀ s : (Fin nL → ℝ) × (Fin nR → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS κ ρL (0 : Fin nR → ℝ) (fullTraceSet (nL := nL) (nR := nR)))
    (hredL : ∀ s : (Fin nL → ℝ) × (Fin nR → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS κ (0 : Fin nL → ℝ) ρR (fullTraceSet (nL := nL) (nR := nR)))
    (hi₀ : ∀ i, i₀ ≤ i) (hj₀ : ∀ j, j₀ ≤ j)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    (hband : ∀ᵐ ω ∂P, ζ ω = ⊤ →
      ((∃ T : ℝ≥0, ∀ t, T ≤ t → VR j₀ t ω - VL i₀ t ω < 4 * (VR j₀ t ω - W t ω)) ∨
        (∃ T : ℝ≥0, ∀ t, T ≤ t → VR j₀ t ω - VL i₀ t ω < 4 * (W t ω - VL i₀ t ω))) →
      ∃ M : ℝ, ∀ t : ℝ≥0, ∫ s in (0 : ℝ)..t, (VR j₀ s.toNNReal ω - VL i₀ s.toNNReal ω)⁻¹ ^ 2 ≤ M) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ →
      ((∃ T : ℝ≥0, ∀ t, T ≤ t → VR j₀ t ω - VL i₀ t ω < 4 * (VR j₀ t ω - W t ω)) ∨
        (∃ T : ℝ≥0, ∀ t, T ≤ t → VR j₀ t ω - VL i₀ t ω < 4 * (W t ω - VL i₀ t ω))) →
      ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop := by
  have hbt := ae_bandTail_rational (i₀ := i₀) (j₀ := j₀) hκ hE hredR hredL hi₀ hj₀
  filter_upwards [hbt, htr, hband, hE.2.2.2.2] with ω hbω htrω hbandω hp hζ hside η hη
  obtain ⟨M, hM⟩ := hbandω hζ hside
  have hF := hp.isForcePath
  rw [hζ] at hp
  have hwc : Continuous fun t => W t ω := by
    have := hp.isForcePath.continuousOn_w
    simpa using this
  have hcD : Continuous (crossGap (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀) := by
    have h1 := hp.isForcePath.continuousOn_vR j₀
    have h2 := hp.isForcePath.continuousOn_vL i₀
    simp only [ENNReal.coe_lt_top, ofPred_true, continuousOn_univ] at h1 h2
    exact h1.sub h2
  have hmono : Monotone (crossGap (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀) := fun s t hst =>
    hp.isForcePath.crossGap_le i₀ j₀ hst ENNReal.coe_lt_top
  have hD0 : 0 < crossGap (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀ 0 := by
    simp only [crossGap, hp.isForcePath.vL_zero, hp.isForcePath.vR_zero]
    exact sub_pos.2 (hsep i₀ j₀)
  -- the trace on `[0, ∞)` given by finite-time continuity
  obtain ⟨η₁, hη₁⟩ := htrω
  rw [hζ] at hη₁
  have hw0 : W 0 ω = 0 := hp.1
  have hwcon : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ⊤} := hwc.continuousOn
  -- the restart time and the clock cutoff
  obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, (∀ t, T ≤ t → VR j₀ t ω - VL i₀ t ω < 4 * (VR j₀ t ω - W t ω)) ∨
      (∀ t, T ≤ t → VR j₀ t ω - VL i₀ t ω < 4 * (W t ω - VL i₀ t ω)) := by
    rcases hside with ⟨T, h⟩ | ⟨T, h⟩
    · exact ⟨T, Or.inl h⟩
    · exact ⟨T, Or.inr h⟩
  set N : ℕ := ⌈(T : ℝ)⌉₊ + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hTN : T ≤ (N : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast, hNdef]
    push_cast
    linarith [Nat.le_ceil (T : ℝ)]
  set m : ℕ := ⌈M⌉₊ + 1 with hmdef
  have hMm : M < m := by rw [hmdef]; push_cast; linarith [Nat.le_ceil M]
  have hclock : ∀ t : ℝ≥0, discClock (shiftMarks (fun i t => VL i t ω) (fun t => W t ω) N)
      (shiftMarks (fun j t => VR j t ω) (fun t => W t ω) N) i₀ j₀ t < m := fun t =>
    (discClock_shift_le hD0 hmono hcD hM hN1 t).trans_lt hMm
  have hq : Real.toNNReal ((N : ℚ) : ℝ) = (N : ℝ≥0) := by
    rw [Rat.cast_natCast, Real.toNNReal_natCast]
  obtain ⟨hR, hL⟩ := hbω (N : ℚ) m (Or.inr hsep) (by rw [hq, hζ]; exact ENNReal.coe_lt_top)
  rw [hq, hζ, ENNReal.top_sub_coe] at hR hL
  -- the band from `N` never ends: the shifted driver has a transient trace
  have hev : TraceEvent (shiftNN (fun t => W t ω) N) ⊤ := by
    rcases hT with hTR | hTL
    · convert hR using 1
      symm
      refine le_antisymm le_top (le_min (le_hitTime fun s _ _ hs => ?_) le_rfl)
      rcases hs with hs | hs
      · have h := hTR ((N : ℝ≥0) + s) (hTN.trans le_self_add)
        simp only [crossGap, shiftMarks] at hs
        unfold shiftNN at hs
        linarith
      · exact (not_le.2 (hclock s)) hs
    · convert hL using 1
      symm
      refine le_antisymm le_top (le_min (le_hitTime fun s _ _ hs => ?_) le_rfl)
      rcases hs with hs | hs
      · have h := hTL ((N : ℝ≥0) + s) (hTN.trans le_self_add)
        simp only [crossGap, shiftMarks] at hs
        unfold shiftNN at hs
        linarith
      · exact (not_le.2 (hclock s)) hs
  obtain ⟨η₂, hη₂, hη₂t⟩ := hev
  -- join with the trace on `[0, N]`
  have hIcc := IsGeneratingTrace.isGeneratingTraceIcc hη₁ hwcon hw0 (σ := (N : ℝ≥0)) ENNReal.coe_lt_top
  have hwcon' : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < (N : ℝ≥0) + ⊤} := by
    rw [add_top]; exact hwcon
  obtain ⟨hJ, hJt⟩ := IsGeneratingTraceIcc.join hwcon' hw0 hIcc hη₂
  rw [add_top] at hJ
  have hJt' := hJt rfl (hη₂t rfl)
  refine hJt'.congr fun t => ?_
  rw [IsGeneratingTrace.eq_of_le hη hJ hwcon hw0 le_top]

end BandEvent

/-! ### Aux. lemma 101 for the bands -/

/-- **Named input: Aux. lemma 101 for the bands `U < 3/4`, `U > 1/4`** (Specification pp. 346–348, Aux. lemma 101:
"On an interval during which the driver stays on one side of that midpoint, the angular clock `∫ D^{-2}` has finite
terminal value almost surely. No restriction on the two total weights is needed."; the proof (P1)–(P4) and the
Brownian increments of the angular-time martingale apply verbatim to a band `U ≤ θ`, `θ < 1`). For every `κ > 0`
and every evolution of a separated ordered word with at least one mark on each side: almost surely, if the lifetime
is infinite and the driver eventually stays at distance more than `D/4` from the nearest right mark (or from the
nearest left mark), the total angular clock of the nearest cross-gap `D = V^{R,0} − V^{L,0}` is finite. This is a
statement about the force-point equations; PROVE-SEC7-C7's Lyapunov method for Aux. lemma 102
(`Spec/Sec7/ContinuityProb7Clock`) proves statements of this form. -/
def Aux101BandClockStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin (nR + 1) → ℝ), IsOrderedForceWord xL xR → (∀ i j, xL i < xR j) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
      (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ζ ω = ⊤ → EventualBandPath (fun t => W t ω) (fun t => VL 0 t ω) (fun t => VR 0 t ω) →
        ∃ M : ℝ, ∀ t : ℝ≥0, ∫ s in (0 : ℝ)..t, (VR 0 s.toNNReal ω - VL 0 s.toNNReal ω)⁻¹ ^ 2 ≤ M

/-! ### The trials at a separated start -/

section Separated

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ}
  {ρR : Fin (nR + 1) → ℝ}

/-- Theorem 2.2's existence in the named form of Aux. lemmas 103 and 113. -/
theorem existsEvolutionStatement' : ExistsEvolutionStatement :=
  fun ha _ _ _ _ _ _ hF => exists_isIntegratedSLEEvolution_assembled ha hF

/-- **Aux. lemma 113, `τ = ∞`, at a separated start** (every `κ > 0`). For a separated ordered word with at least one
mark on each side and fewer than `N` marks on each side, under the smaller-count hypothesis, Aux. lemma 101 and the
uniform trial bound, every evolution is almost surely not non-transient. -/
theorem ae_not_nonTransientEvent_sep (hκ : 0 < κ) {N : ℕ} (hD : LP.DistinctCompleteBelow.{u} κ N)
    (h101 : Aux101BandClockStatement.{u} κ) (hF : IsOrderedForceWord xL xR) (hsep : ∀ i j, xL i < xR j)
    (hnL : nL + 1 < N) (hnR : nR + 1 < N) (hU : UniformTrialBound κ ρL ρR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ¬ NonTransientEvent (fun t => W t ω) (ζ ω) := by
  have hex : ExistsEvolutionStatement := existsEvolutionStatement'
  have htr := ae_isGeneratingTrace_lifetime hκ hex hD hE hF hnL hnR (Or.inl hsep)
  have hbandT := ae_tendsto_of_eventualBand_imp (i₀ := 0) (j₀ := 0) hκ hE hsep
    (ae_mem_lawSetS_zero_right hκ hex hD ρL hnL) (ae_mem_lawSetS_zero_left hκ hex hD ρR hnR)
    (fun i => Fin.zero_le i) (fun j => Fin.zero_le j) htr (h101 xL xR ρL ρR hF hsep P 𝓕 W VL VR B ζ hE)
  refine ae_not_nonTransientEvent_of_trials hκ hE hF hsep hU ?_
  filter_upwards [hbandT, hE.2.2.2.2] with ω h hp hζ hb
  have hwc : Continuous fun t => W t ω :=
    continuousOn_univ.1 (hp.isForcePath.continuousOn_w.mono fun t _ => by rw [hζ]; exact ENNReal.coe_lt_top)
  rw [hζ, not_nonTransientEvent_iff hwc hp.1]
  exact h hζ hb

end Separated

/-! ### From separated starts to every ordered start -/

section Restart

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **Restart at time `1`.** If the canonical probability of the non-transience event vanishes at every separated
ordered word, every evolution from every start is almost surely not non-transient (at time `1` the realized word is
separated, and non-transience passes to the restarted driver). -/
theorem ae_not_nonTransientEvent_of_codeLaw (hκ : 0 < κ)
    (h0 : ∀ (yL : Fin nL → ℝ) (yR : Fin nR → ℝ), IsOrderedForceWord yL yR → (∀ i j, yL i < yR j) →
      codeLaw κ ρL ρR ntCodeSet (yL, yR) = 0)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ¬ NonTransientEvent (fun t => W t ω) (ζ ω) := by
  set T : Ω → ℝ≥0 := fun _ => 1 with hTdef
  have hT : IsStoppingTime 𝓕 fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const 𝓕 (1 : ℝ≥0)
  set A : Set Ω := {ω | ((1 : ℝ≥0) : ℝ≥0∞) < ζ ω} with hAdef
  have hA1 : MeasurableSet[𝓕 1] A := by
    have h := hE.2.1 1 univ MeasurableSet.univ
    convert h using 1
    ext ω
    simp [hAdef]
  have hA : MeasurableSet[hT.measurableSpace] A := by
    rw [hT.measurableSet]
    refine ⟨le_iSup (fun t => 𝓕 t) 1 _ hA1, fun i => ?_⟩
    by_cases hi : (1 : ℝ≥0) ≤ i
    · have he : A ∩ {ω | ((T ω : ℝ≥0) : WithTop ℝ≥0) ≤ i} = A := inter_eq_left.2 fun ω _ => by
        show ((1 : ℝ≥0) : WithTop ℝ≥0) ≤ i
        exact_mod_cast hi
      rw [he]; exact 𝓕.mono hi _ hA1
    · have he : A ∩ {ω | ((T ω : ℝ≥0) : WithTop ℝ≥0) ≤ i} = ∅ := by
        refine eq_empty_iff_forall_notMem.2 fun ω hω => hi ?_
        have : ((1 : ℝ≥0) : WithTop ℝ≥0) ≤ i := hω.2
        exact_mod_cast this
      rw [he]; exact @MeasurableSet.empty Ω (𝓕 i)
  have hAT : ∀ ω ∈ A, ((T ω : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ (0 < T ω ∨ ∀ i j, xL i < xR j) :=
    fun ω hω => ⟨hω, Or.inl one_pos⟩
  have hlaw := measure_restart_codeEvent hκ hE hT hA hAT (Φ := NonTransientEvent)
    measurableSet_ntCodeSet (fun _ _ _ => Iff.rfl) nonTransientEvent_congr
  have hAm : MeasurableSet A := 𝓕.le 1 _ hA1
  have hzero : ∫⁻ ω in A, codeLaw κ ρL ρR ntCodeSet (wordAt W VL VR T ω) ∂P = 0 := by
    refine (setLIntegral_congr_fun_ae hAm ?_).trans (setLIntegral_const _ 0 |>.trans (zero_mul _))
    filter_upwards [hE.2.2.2.2] with ω hp hω
    refine h0 _ _ (isOrderedForceWord_at hp hω) fun i j => ?_
    have := hp.vL_lt_vR_of_pos hF one_pos hω i j
    simp only [hTdef]
    linarith
  rw [hzero] at hlaw
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) (measure_union_null hlaw (ae_iff.1 hE.2.2.2.2))
  have hnt : NonTransientEvent (fun t => W t ω) (ζ ω) := not_not.1 hω
  by_cases hp : IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
    (fun t => B t ω) (ζ ω)
  · left
    have hζ : ζ ω = ⊤ := hnt.1
    have hwc : Continuous fun t => W t ω :=
      continuousOn_univ.1 (hp.isForcePath.continuousOn_w.mono fun t _ => by rw [hζ]; exact ENNReal.coe_lt_top)
    refine ⟨by show ((1 : ℝ≥0) : ℝ≥0∞) < ζ ω; rw [hζ]; exact ENNReal.coe_lt_top, ?_⟩
    rw [hζ] at hnt
    have h2 := nonTransientEvent_shiftNN hwc hp.1 hnt 1
    show NonTransientEvent (fun t => W (1 + t) ω - W 1 ω) (ζ ω - 1)
    rw [hζ, ENNReal.top_sub ENNReal.one_ne_top]
    exact h2
  · right
    exact hp

end Restart

end TrialsHi

end Sec7

end InteractingSLE
