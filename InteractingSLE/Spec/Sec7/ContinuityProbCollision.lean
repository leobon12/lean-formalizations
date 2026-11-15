/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProbBase
import InteractingSLE.Spec.Dimension.FiniteGirsanov
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# §7.3: the trace is continuous before the first force collision

Packet PROVE-SEC7-C2. The finite-time continuity statements of §7.3 all start from the same observation:
before the first collision of the driver with a force coordinate the force drift is bounded on every
compact time interval, so Girsanov's theorem compares the driver with `√κ` times a Brownian motion and the
ordinary `SLE_κ` trace supplies a continuous trace (Specification §7.3: Aux. lemma 99, L89 "Its trace is
continuous up to and including the first swallow of that mark" — the part strictly before the swallow;
Aux. lemma 103, L292; Aux. lemma 107, L418; Aux. lemma 112, L656). The endpoint itself, a collision, is
the substance of those lemmas and is not claimed here.

* `exists_pos_le_of_continuousOn_Icc`: a continuous positive function on `[0, t]` has a positive lower
  bound there.
* `IsIntegratedSLEPath.exists_gapsGE_of_ne`: on a compact interval `[0, t]`, `t < ζ`, free of collisions,
  all force gaps are at least some `δ > 0` (`Dimension.GapsGE`).
* **`IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_of_forall_ne`**: almost surely, for every
  `t < ζ` such that no force coordinate meets the driver on `[0, t]`, the driver has a continuous
  generating trace on `[0, t]`. Proof: the localized comparison after the deterministic time `0`
  (`Dimension.exists_brownian_localization`, horizons and gap levels `n ∈ ℕ`) gives `W = √κ X` on `[0, t]`
  with the law of `X` absolutely continuous with respect to a Brownian law; the ordinary trace
  (`ae_exists_trace_all`) transfers through the law; `IsGeneratingTrace.of_eqOn_lt` identifies it.
* `IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_lt_of_forall_ne`: the same on the open interval
  `[0, τ)` before a collision-free horizon `τ ≤ ζ` (every compact `[0, t]`, `t < τ`, has its own trace,
  and generating traces agree where both are defined, `IsGeneratingTrace.eq_of_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

open QuantumZipper.RS

namespace Sec7

/-- A function continuous and positive on `[0, t]` has a positive lower bound there. -/
theorem exists_pos_le_of_continuousOn_Icc {f : ℝ≥0 → ℝ} {t : ℝ≥0} (hf : ContinuousOn f (Icc 0 t))
    (hpos : ∀ s ∈ Icc 0 t, 0 < f s) : ∃ ε > 0, ∀ s ∈ Icc 0 t, ε ≤ f s := by
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le) hf
  exact ⟨f s₀, hpos s₀ hs₀, fun s hs => hmin hs⟩

end Sec7

open Sec7

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- On a collision-free compact interval `[0, t]`, `t < ζ`, all force gaps are bounded below by some
`δ > 0`. -/
theorem IsIntegratedSLEPath.exists_gapsGE_of_ne (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ)
    (hne : ∀ s : ℝ≥0, s ≤ t → (∀ i, w s ≠ vL i s) ∧ ∀ i, w s ≠ vR i s) :
    ∃ δ > 0, ∀ s : ℝ≥0, s ≤ t → Dimension.GapsGE δ (w s) (fun i => vL i s) (fun i => vR i s) := by
  obtain ⟨-, -, -, hw, hvL, hvR, -⟩ := h
  have hsub : Icc (0 : ℝ≥0) t ⊆ {s | (s : ℝ≥0∞) < ζ} := fun s hs =>
    lt_of_le_of_lt (by exact_mod_cast hs.2) ht
  have hL : ∀ i, ∃ ε > 0, ∀ s ∈ Icc 0 t, ε ≤ |w s - vL i s| := fun i =>
    exists_pos_le_of_continuousOn_Icc (((hw.mono hsub).sub ((hvL i).mono hsub)).abs)
      fun s hs => abs_pos.2 (sub_ne_zero.2 ((hne s hs.2).1 i))
  have hR : ∀ i, ∃ ε > 0, ∀ s ∈ Icc 0 t, ε ≤ |w s - vR i s| := fun i =>
    exists_pos_le_of_continuousOn_Icc (((hw.mono hsub).sub ((hvR i).mono hsub)).abs)
      fun s hs => abs_pos.2 (sub_ne_zero.2 ((hne s hs.2).2 i))
  choose εL hεL hεL' using hL
  choose εR hεR hεR' using hR
  obtain ⟨δL, hδL, hδL'⟩ := Sec2.exists_pos_le_of_pos hεL
  obtain ⟨δR, hδR, hδR'⟩ := Sec2.exists_pos_le_of_pos hεR
  refine ⟨min δL δR, lt_min hδL hδR, fun s hs => ⟨fun i => ?_, fun i => ?_⟩⟩
  · exact (min_le_left _ _).trans ((hδL' i).trans (hεL' i s ⟨zero_le, hs⟩))
  · exact (min_le_right _ _).trans ((hδR' i).trans (hεR' i s ⟨zero_le, hs⟩))

/-- A generating trace on `[0, T]` is a generating trace on `[0, T']` for every `T' ≤ T`. -/
theorem IsGeneratingTrace.mono_horizon {w : ℝ≥0 → ℝ} {T T' : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w T η) (hT : T' ≤ T) : IsGeneratingTrace w T' η :=
  ⟨hη.1, hη.2.1.mono fun _ ht => le_trans ht hT, fun t ht => hη.2.2 t (lt_of_lt_of_le ht hT)⟩

section Evolution

variable {κ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}

/-- **The trace is continuous before the first collision.** For an integrated `SLE_κ(ρ)` evolution,
`κ > 0`: almost surely, for every time `t < ζ` such that no force coordinate meets the driver on
`[0, t]`, the driver has a continuous generating trace on `[0, t]`. -/
theorem IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_of_forall_ne [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ') :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' ω →
      (∀ s : ℝ≥0, s ≤ t → (∀ i, W s ω ≠ VL i s ω) ∧ ∀ i, W s ω ≠ VR i s ω) →
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun s => W s ω) t η := by
  have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hloc := fun n : ℕ => Dimension.exists_brownian_localization hκ hE 0 (n : ℝ≥0) (hδ n)
  choose X hXm μ hμprob hμBM hac hXeq using hloc
  have htr : ∀ n : ℕ, ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => Real.sqrt κ * (X n ω).1 t) ⊤ η := fun n => by
    have := hμprob n
    have h := ae_exists_trace_all (hμBM n) hκ
    exact ae_of_ae_map (hXm n).aemeasurable ((hac n).ae_le (h.mono fun f hf => hf.1))
  filter_upwards [ae_all_iff.2 htr, ae_all_iff.2 hXeq, hE.2.2.2.2] with ω htr hx hp t ht hne
  obtain ⟨δ, hδpos, hgap⟩ := hp.exists_gapsGE_of_ne ht hne
  -- `n` with gap level `1/(n+1) ≤ δ` and horizon `t ≤ n`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 / ((n : ℝ) + 1) ≤ δ ∧ (t : ℝ) ≤ n := by
    obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hδpos
    obtain ⟨n₂, hn₂⟩ := exists_nat_ge (t : ℝ)
    refine ⟨max n₁ n₂, (one_div_le_one_div_of_le (by positivity) ?_).trans hn₁.le, ?_⟩
    · exact_mod_cast Nat.add_le_add_right (le_max_left n₁ n₂) 1
    · exact hn₂.trans (by exact_mod_cast le_max_right n₁ n₂)
  obtain ⟨η, hη⟩ := htr n
  have hW0 : W 0 ω = 0 := hp.1
  refine ⟨η, hη.of_eqOn_lt fun s hs => ?_⟩
  have hst : s ≤ t := by exact_mod_cast hs.le
  have hsn : s ≤ (n : ℝ≥0) := by
    rw [← NNReal.coe_le_coe]; exact (NNReal.coe_le_coe.2 hst).trans (by exact_mod_cast hn.2)
  have hsζ : ((0 + s : ℝ≥0) : ℝ≥0∞) < ζ' ω := by
    rw [zero_add]; exact lt_of_le_of_lt (by exact_mod_cast hst) ht
  have key := hx n s hsn hsζ fun r _ hr => by
    rw [zero_add] at hr
    obtain ⟨hL, hR⟩ := hgap r (hr.trans hst)
    exact ⟨fun i => hn.1.trans (hL i), fun i => hn.1.trans (hR i)⟩
  rw [zero_add, hW0, sub_zero] at key
  exact key

/-- **The trace is continuous on `[0, τ)` before a collision-free horizon.** Almost surely, for every
`τ ≤ ζ` such that no force coordinate meets the driver before `τ`, there is one trace `η`, continuous
on `[0, τ)`, generating every hull `K_t`, `t < τ`. -/
theorem IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_lt_of_forall_ne
    [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ') :
    ∀ᵐ ω ∂P, ∀ τ : ℝ≥0∞, τ ≤ ζ' ω →
      (∀ s : ℝ≥0, (s : ℝ≥0∞) < τ → (∀ i, W s ω ≠ VL i s ω) ∧ ∀ i, W s ω ≠ VR i s ω) →
      ∃ η : ℝ≥0 → ℂ, η 0 = 0 ∧ ContinuousOn η {t | (t : ℝ≥0∞) < τ} ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ →
          IsFilling (QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) t) (η '' Icc 0 t) := by
  filter_upwards [hE.ae_exists_isGeneratingTrace_of_forall_ne hκ, hE.2.2.2.2] with ω hω hp τ hτ hne
  have hloc : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun s => W s ω) t η :=
    fun t ht => hω t (lt_of_lt_of_le ht hτ) fun s hs => hne s (lt_of_le_of_lt (by exact_mod_cast hs) ht)
  have hw : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ' ω} := hp.2.2.2.1
  have hw0 : W 0 ω = 0 := hp.1
  have hwt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ →
      ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < (t : ℝ≥0∞)} := fun t ht =>
    hw.mono fun s hs => lt_of_lt_of_le (lt_trans hs ht) hτ
  classical
  let η : ℝ≥0 → ℂ := fun t => if h : (t : ℝ≥0∞) < τ then (hloc t h).choose t else 0
  -- on `[0, t]`, `η` is the trace chosen at time `t`
  have hηeq : ∀ t : ℝ≥0, ∀ ht : (t : ℝ≥0∞) < τ, ∀ s : ℝ≥0, s ≤ t → η s = (hloc t ht).choose s := by
    intro t ht s hst
    have hs : (s : ℝ≥0∞) < τ := lt_of_le_of_lt (by exact_mod_cast hst) ht
    simp only [η, hs, ↓reduceDIte]
    exact IsGeneratingTrace.eq_of_le (hloc s hs).choose_spec
      ((hloc t ht).choose_spec.mono_horizon (by exact_mod_cast hst)) (hwt s hs) hw0 le_rfl
  refine ⟨η, ?_, fun t₀ ht₀ => ?_, fun t ht => ?_⟩
  · simp only [η]
    split_ifs with h
    · exact (hloc 0 h).choose_spec.1
    · rfl
  · obtain ⟨t₁, ht₀t₁, ht₁τ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₀
    have ht₀t₁' : t₀ < t₁ := by exact_mod_cast ht₀t₁
    have hc : ContinuousOn η (Iic t₁) :=
      ((hloc t₁ ht₁τ).choose_spec.2.1.mono fun s hs => show (s : ℝ≥0∞) ≤ t₁ by
        exact_mod_cast hs).congr fun s hs => hηeq t₁ ht₁τ s hs
    exact ((hc.continuousAt (Iic_mem_nhds ht₀t₁')).continuousWithinAt)
  · obtain ⟨t₁, htt₁, ht₁τ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    have himg : η '' Icc 0 t = (hloc t₁ ht₁τ).choose '' Icc 0 t :=
      image_congr fun s hs => hηeq t₁ ht₁τ s (hs.2.trans (by exact_mod_cast htt₁.le))
    rw [himg]
    exact (hloc t₁ ht₁τ).choose_spec.2.2 t htt₁

/-- **Separated marks with admissible partial sums: infinite lifetime and a continuous trace on
`[0, ∞)`** (Aux. lemma 6, `Sec4.aux6Statement`, and continuity before the first collision). For an
ordered force word whose marks are all strictly separated from the seed and whose side partial sums are
admissible (`Sec4.HasAdmissiblePartialSums`, the hypothesis of Aux. lemmas 6–7), almost surely the lifetime
is infinite and the driver has a continuous generating trace on `[0, ∞)` (transience is the remaining
assertion of Aux. lemma 7). -/
theorem IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_hasAdmissiblePartialSums
    [IsProbabilityMeasure P] (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) (hxL : ∀ i, xL i < 0) (hxR : ∀ i, 0 < xR i)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ') :
    ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η := by
  filter_upwards [Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ' hF hadm hE,
    hE.ae_exists_isGeneratingTrace_lt_of_forall_ne hκ, hE.2.2.2.2] with ω h6 hlt hp
  obtain ⟨hζ, hsep⟩ := h6
  obtain ⟨η, h0, hc, hfill⟩ := hlt ⊤ hζ.symm.le fun s _ => by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs | hs
    · subst hs
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have h0 : W 0 ω = 0 := hp.1
        have hv : VL i 0 ω = xL i := hp.2.1 i
        rw [h0, hv]; exact (hxL i).ne'
      · have h0 : W 0 ω = 0 := hp.1
        have hv : VR i 0 ω = xR i := hp.2.2.1 i
        rw [h0, hv]; exact (hxR i).ne
    · exact ⟨fun i => ((hsep s hs).1 i).ne', fun i => ((hsep s hs).2 i).ne⟩
  exact ⟨hζ, η, h0, hc.mono fun t _ => show (t : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top, hfill⟩

end Evolution

end InteractingSLE
