/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TwoForceBase

/-!
# Restarted drivers keep a transient trace (`κ ≤ 4`)

Packet PROVE-ZHAN-B3. For the transience transfer from the seed to separated pairs (Astra, *Formalization proofs
and dependency audit*, L1416–L1419: "Strong Markov and the inverse map's normalization at infinity transfer the proved
limit") the restarted driver `W_{T+·} − W_T` at a random time `T` must have a continuous generating trace on `[0, ∞)`
tending to `∞` whenever the original trace does. This file proves it pathwise, at **every** time `σ ≥ 0`
simultaneously, so that it applies at random times:

* `ae_shiftGood`: for an ordered admissible word and `0 < κ ≤ 4`, almost surely the mapped-out futures after all
  positive rational times are simple radial chains (the input of WangWu's gluing theorem; the proof of Remark 2.3,
  `Zhan.IsIntegratedSLEEvolution.ae_simple_trace`);
* `shiftGood_shiftNN`: this property passes to every restarted driver `Sec7.shiftNN w σ` (with the shifted dense set
  `ℚ − σ`), which therefore has a simple generating trace (`exists_isGeneratingTrace_shiftNN`);
* `tendsto_norm_shiftNN`: the restarted trace tends to `∞` if the original one does (`η(σ + s) = F̄_σ(η₂(s))` with
  `F̄_σ` at bounded distance from the identity on `ℍ̄`, the join of `TwoForceBase.lean`);
* `traceEvent_shiftNN`: the trace event `Sec7.RandRestart.TraceEvent (shiftNN w σ) ⊤` of the restart.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Zhan

open QuantumZipper (H Hbar fwdHull fwdMapInv)
open QuantumZipper.RS (shiftDrive continuous_shiftDrive)
open WangWu.TraceGlue (ShiftGood IsSimpleRadialChainOn IsSimpleRadialChain exists_isGeneratingTrace_of_shift)

variable {nL nR : ℕ}

/-! ### Simple mapped-out futures at all rational times -/

section Evolution

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Simple mapped-out futures at all positive rational times** (`κ ≤ 4`, ordered admissible word): almost surely
the lifetime is infinite, the driver is continuous, and `shiftDrive W q` is a simple radial chain for every rational
`q > 0` (the proof of Remark 2.3). -/
theorem IsIntegratedSLEEvolution.ae_shiftGood (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      ShiftGood (fun r : ℝ => W r.toNNReal ω) (range ((↑) : ℚ → ℝ)) := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have h6 := Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE
  have hloc : ∀ᵐ ω ∂P, ∀ q : ℚ, ∀ m n : ℕ, ζ ω = ⊤ → (∀ s : ℝ≥0, (q : ℝ).toNNReal ≤ s →
      s ≤ (q : ℝ).toNNReal + m →
        Dimension.GapsGE (1 / ((n : ℝ) + 1)) (W s ω) (fun i => VL i s ω) (fun i => VR i s ω)) →
      IsSimpleRadialChainOn (shiftDrive (fun r : ℝ => W r.toNNReal ω) ((q : ℝ).toNNReal : ℝ)) m := by
    rw [ae_all_iff]; intro q
    rw [ae_all_iff]; intro m
    rw [ae_all_iff]; intro n
    exact IsIntegratedSLEEvolution.ae_shift_isSimpleRadialChainOn hκ hκ4 hE _ m (by positivity)
  filter_upwards [h6, hloc, hE.2.2.2.2] with ω ⟨hζ, hsep⟩ hlω hp
  have hwc : Continuous fun t => W t ω := by
    have h := hp.2.2.2.1
    rw [hζ] at h
    exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
  refine ⟨hζ, hwc, hp.1, ?_⟩
  rintro _ ⟨q, rfl⟩ hq T
  obtain ⟨m, hm⟩ := exists_nat_ge T
  have ha : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq.le
  have ha0 : 0 < (q : ℝ).toNNReal := Real.toNNReal_pos.2 hq
  obtain ⟨δ, hδ, hgapδ⟩ := exists_gapsGE_Icc_of_sep hp hζ hsep ha0 (le_self_add (b := (m : ℝ≥0)))
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have h := hlω q m n hζ fun s h1 h2 =>
    ⟨fun i => hn.le.trans ((hgapδ s h1 h2).1 i), fun i => hn.le.trans ((hgapδ s h1 h2).2 i)⟩
  rw [ha] at h
  exact h.mono hm

end Evolution

/-! ### Restarted drivers -/

theorem continuous_real_shiftNN {w : ℝ≥0 → ℝ} (hw : Continuous w) (σ : ℝ≥0) :
    Continuous fun r : ℝ => Sec7.shiftNN w σ r.toNNReal :=
  ((hw.comp (continuous_const.add continuous_id)).sub continuous_const).comp continuous_real_toNNReal

/-- **Simple futures pass to restarted drivers**: if the mapped-out futures of `w` after all positive rational times
are simple radial chains, so are those of `w_{σ+·} − w_σ` after all positive times of `ℚ − σ`. -/
theorem shiftGood_shiftNN {w : ℝ≥0 → ℝ} (hw : Continuous w) (σ : ℝ≥0)
    (hg : ShiftGood (fun r : ℝ => w r.toNNReal) (range ((↑) : ℚ → ℝ))) :
    ShiftGood (fun r : ℝ => Sec7.shiftNN w σ r.toNNReal) (range fun q : ℚ => (q : ℝ) - σ) := by
  rintro _ ⟨q, rfl⟩ hpos T
  have hq : (0 : ℝ) < q := by linarith [σ.coe_nonneg]
  have hV : Continuous fun r : ℝ => w r.toNNReal := hw.comp continuous_real_toNNReal
  have hV' := continuous_real_shiftNN hw σ
  refine IsSimpleRadialChainOn.congr (continuous_shiftDrive hV _) (QuantumZipper.RS.shiftDrive_zero _ _)
    (continuous_shiftDrive hV' _) (QuantumZipper.RS.shiftDrive_zero _ _) (fun s hs => ?_)
    (hg q ⟨q, rfl⟩ hq T)
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have e1 : σ + ((q : ℝ) - σ + s).toNNReal = ((q : ℝ) + s).toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_add, Real.coe_toNNReal _ (by linarith), Real.coe_toNNReal _ (by linarith)]
    ring
  have e2 : σ + ((q : ℝ) - σ).toNNReal = (q : ℝ).toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_add, Real.coe_toNNReal _ hpos.le, Real.coe_toNNReal _ hq.le]
    ring
  simp only [shiftDrive, Sec7.shiftNN, e1, e2]
  ring

theorem dense_range_rat_sub (σ : ℝ≥0) : Dense (range fun q : ℚ => (q : ℝ) - σ) := by
  have hs : DenseRange fun x : ℝ => x - σ :=
    Function.Surjective.denseRange (f := fun x : ℝ => x - σ) fun y => ⟨y + σ, by ring⟩
  exact hs.comp Rat.denseRange_cast (continuous_id.sub continuous_const)

/-- **The restarted driver has a simple generating trace.** -/
theorem exists_isGeneratingTrace_shiftNN {w : ℝ≥0 → ℝ} (hw : Continuous w) (σ : ℝ≥0)
    (hg : ShiftGood (fun r : ℝ => w r.toNNReal) (range ((↑) : ℚ → ℝ))) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (Sec7.shiftNN w σ) ⊤ η := by
  obtain ⟨η, hη, -⟩ := exists_isGeneratingTrace_of_shift (continuous_real_shiftNN hw σ)
    (Sec7.shiftNN_zero w σ) (dense_range_rat_sub σ) (shiftGood_shiftNN hw σ hg)
  exact ⟨η, hη⟩

/-- **Transience passes to the restarted trace**: `η(σ + s) = F̄_σ(η₂(s))` with `‖F̄_σ y − y‖ ≤ C` on `ℍ̄`, so
`‖η₂(s)‖ ≥ ‖η(σ + s)‖ − C`. -/
theorem tendsto_norm_shiftNN {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) {σ : ℝ≥0} {η₂ : ℝ≥0 → ℂ} (hη₂ : IsGeneratingTrace (Sec7.shiftNN w σ) ⊤ η₂)
    (htr : Tendsto (fun t => ‖η t‖) atTop atTop) : Tendsto (fun t => ‖η₂ t‖) atTop atTop := by
  have hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ⊤} := hw.continuousOn
  have h₁ := Sec7.IsGeneratingTrace.isGeneratingTraceIcc hη hwc hw0 (σ := σ) ENNReal.coe_lt_top
  have hσt₂ : (σ : ℝ) < (σ : ℝ) + 1 := lt_add_one _
  have hfc : Continuous (frozenDrive w ((σ : ℝ) + 1)) := continuous_frozenDrive hw.continuousOn
  obtain ⟨hF, -, -, -, -, ⟨C, hC⟩, -⟩ := h₁.extend_props hσt₂ hfc hw0
  set Fb := extendFrom H (fwdMapInv (frozenDrive w ((σ : ℝ) + 1)) σ) with hFb
  have hwc' : ContinuousOn w {s | (s : ℝ≥0∞) < (σ : ℝ≥0∞) + ⊤} := by rw [add_top]; exact hwc
  obtain ⟨hjoin, -⟩ := h₁.join hwc' hw0 hη₂
  rw [add_top] at hjoin
  have hjoinF : ∀ t : ℝ≥0, σ < t → η t = Fb (η₂ (t - σ)) := by
    intro t ht
    rw [hη.eq_of_le hjoin hwc hw0 le_top, Sec7.joinTrace_of_lt ht, hF]
  have hη₂H : ∀ s, η₂ s ∈ Hbar := fun s =>
    Sec4.im_nonneg_of_isGeneratingTrace (continuous_real_shiftNN hw σ) (Sec7.shiftNN_zero w σ) hη₂ s
  have hlow : ∀ s : ℝ≥0, 0 < s → ‖η (σ + s)‖ - C ≤ ‖η₂ s‖ := by
    intro s hs
    have ht : σ < σ + s := lt_add_of_pos_right σ hs
    rw [hjoinF _ ht, add_tsub_cancel_left]
    have h1 := hC (η₂ s) (hη₂H s)
    have h2 := norm_sub_norm_le (Fb (η₂ s)) (η₂ s)
    linarith
  have hlim : Tendsto (fun s : ℝ≥0 => ‖η (σ + s)‖ - C) atTop atTop :=
    tendsto_atTop_add_const_right _ (-C) (htr.comp (tendsto_atTop_mono (fun s => le_add_self) tendsto_id))
  refine tendsto_atTop_mono' atTop ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with s hs
  exact hlow s hs

/-- **The trace event of a restarted driver** (`ζ − σ = ∞`): a continuous generating trace on `[0, ∞)` tending to
`∞`, whenever the mapped-out futures after rational times are simple and every trace of `w` is transient. -/
theorem traceEvent_shiftNN {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    (hg : ShiftGood (fun r : ℝ => w r.toNNReal) (range ((↑) : ℚ → ℝ)))
    (htr : ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace w ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop) (σ : ℝ≥0) :
    Sec7.RandRestart.TraceEvent (Sec7.shiftNN w σ) ⊤ := by
  have hw0' : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simp [hw0]
  obtain ⟨η, hη, -⟩ := exists_isGeneratingTrace_of_shift (hw.comp continuous_real_toNNReal) hw0
    Rat.denseRange_cast hg
  obtain ⟨η₂, hη₂⟩ := exists_isGeneratingTrace_shiftNN hw σ hg
  exact ⟨η₂, hη₂, fun _ => tendsto_norm_shiftNN hw hw0 hη hη₂ (htr η hη)⟩

end InteractingSLE.Zhan
