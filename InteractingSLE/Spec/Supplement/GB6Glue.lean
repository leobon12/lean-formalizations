/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6Disjoint
import InteractingSLE.Spec.Sec7.Lemma71Capacity
import InteractingSLE.Spec.Sec5.CrossRestartExit

/-!
# Proposition GB6: the relative Loewner chain up to the first contact

Packet PROVE-GB6C, item (c) of `planning/handoffs/PROVE-GB6B.md` §5. Supplement §8.6, proof of Proposition GB6
(`source/spec/p481-528.md` L935–L975, p. 519): "Fixed-hull restriction gives continuous relative Loewner growth
before `T`. […] Increasing rational time and positive-distance buffers supplies the whole open interval before `T`
and its relative capacity clock."

GB6B proved the fixed-hull restriction on every compact interval `[0, T]` before the first contact
(`exists_loewner_relMap`): with `Ψ = relMap U σ` (the chart of the flow's own component, read in the counterflow
chart), the hulls `Ψ(K'_t)`, `t ≤ T`, form a chordal Loewner chain after a capacity time change. Here the chains of
all compact intervals are glued into one chain on the whole open interval before the first contact `T_c`:

* the clock is **intrinsic**: `a(t) = hcap(Ψ(K'_t))/2` (`relClock`), so every interval's clock is `a`
  (`hcap_fwdHull`);
* the drivers of two intervals agree on the common capacity interval (`Sec6.eqOn_clock_and_driver_of_fwdHull_eq`),
  so they glue to one driver `W'` continuous before the relative lifetime `sup_{t < T_c} a(t)`.

When the relative lifetime is infinite, `a` is an exhausting clock before `T_c` (`Sec5.CrossRestart.IsExhaustingClock`)
and its inverse `clockInv a T_c` is the continuous strictly increasing clock of `IsGB6ChartContinuation`, onto
`[0, T_c)`.

## Main results

* `relClock`, `exists_relChain_Icc` (one compact interval, intrinsic clock);
* **`exists_glued_relChain`**: the glued chain before `T_c` (hulls and fillings);
* **`exists_glued_relChain_of_unbounded`**: with infinite relative lifetime, an exhausting clock and a driver
  continuous on `[0, ∞)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE

namespace Supp8

namespace GB6

/-! ### The intrinsic relative clock -/

/-- **The relative capacity clock**: half the half-plane capacity of the chart image `Ψ(K'_t)` of the counterflow
hull, `Ψ = relMap U σ`. -/
def relClock (U : ℝ → ℝ) (σ : ℝ) (W : ℝ → ℝ) (t : ℝ) : ℝ :=
  ConformalImage.hcapSet (relMap U σ '' QuantumZipper.fwdHull W t) / 2

/-- The image of a real time interval under a path read through `Real.toNNReal`. -/
theorem image_Icc_toNNReal (γ : ℝ≥0 → ℂ) (t : ℝ≥0) :
    (fun r : ℝ => γ r.toNNReal) '' Icc 0 (t : ℝ) = γ '' Icc 0 t := by
  ext z
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r.toNNReal, ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hr.2⟩, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, ⟨r.2, by exact_mod_cast hr.2⟩, by simp only [Real.toNNReal_coe]⟩

section Chain

variable {W U : ℝ → ℝ} {σ : ℝ} {p : ℂ}

/-- **The relative chain on one compact interval, with the intrinsic clock.** -/
theorem exists_relChain_Icc (hW : Continuous W) (hW0 : W 0 = 0) (hU : Continuous U) (hU0 : U 0 = 0)
    (hσ : 0 < σ) (htip : Tendsto (QuantumZipper.fwdMapInv U σ) (𝓝[H] 0) (𝓝 p)) {T : ℝ} (hT : 0 ≤ T)
    (hd : Disjoint (closure (QuantumZipper.fwdHull U σ))
      (closure ((fun w : ℂ => -w⁻¹) '' QuantumZipper.fwdHull W T)))
    {γ : ℝ → ℂ} (hγK : ∀ t ∈ Icc (0 : ℝ) T, IsFilling (QuantumZipper.fwdHull W t) (γ '' Icc 0 t)) :
    ∃ V : ℝ → ℝ, Continuous V ∧ V 0 = 0 ∧ relClock U σ W 0 = 0 ∧
      StrictMonoOn (relClock U σ W) (Icc 0 T) ∧ ContinuousOn (relClock U σ W) (Icc 0 T) ∧
      ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ relClock U σ W t ∧
        QuantumZipper.fwdHull V (relClock U σ W t) = relMap U σ '' QuantumZipper.fwdHull W t ∧
        IsFilling (QuantumZipper.fwdHull V (relClock U σ W t)) (relMap U σ '' (γ '' Icc 0 t ∩ H)) := by
  obtain ⟨τ, V, hVc, hV0, hτ0, hτm, hτc, hK, hF⟩ :=
    exists_loewner_relMap_filling hW hW0 hU hU0 hσ hT htip hd hγK
  have hτnn : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ τ t := fun t ht =>
    hτ0 ▸ hτm.monotoneOn ⟨le_rfl, hT⟩ ht ht.1
  have heq : EqOn τ (relClock U σ W) (Icc 0 T) := by
    intro t ht
    have h1 := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hVc hV0 (hτnn t ht) (hK t ht)
    rw [relClock, h1]
    ring
  refine ⟨V, hVc, hV0, ?_, hτm.congr heq, hτc.congr heq.symm, fun t ht => ?_⟩
  · rw [← heq ⟨le_rfl, hT⟩, hτ0]
  · rw [← heq ht]
    exact ⟨hτnn t ht, hK t ht, hF t ht⟩

end Chain

/-! ### Gluing the chains before the first contact -/

section Glue

variable {Wc : ℝ≥0 → ℝ} {U : ℝ → ℝ} {σ : ℝ} {p : ℂ} {Tc : ℝ≥0∞} {γ : ℝ≥0 → ℂ}

/-- The data of the relative chain on `[0, T]` for every `T < T_c` (a choice). -/
theorem exists_relChain_family (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) (hU : Continuous U) (hU0 : U 0 = 0)
    (hσ : 0 < σ) (htip : Tendsto (QuantumZipper.fwdMapInv U σ) (𝓝[H] 0) (𝓝 p))
    (hd : ∀ T : ℝ≥0, (T : ℝ≥0∞) < Tc → Disjoint (closure (QuantumZipper.fwdHull U σ))
      (closure ((fun w : ℂ => -w⁻¹) '' QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) T)))
    (hγK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
      IsFilling (QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) t) (γ '' Icc 0 t)) :
    ∃ V : ℝ≥0 → ℝ → ℝ, ∀ T : ℝ≥0, (T : ℝ≥0∞) < Tc →
      Continuous (V T) ∧ V T 0 = 0 ∧ relClock U σ (fun r : ℝ => Wc r.toNNReal) 0 = 0 ∧
      StrictMonoOn (relClock U σ (fun r : ℝ => Wc r.toNNReal)) (Icc 0 T) ∧
      ContinuousOn (relClock U σ (fun r : ℝ => Wc r.toNNReal)) (Icc 0 T) ∧
      ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ relClock U σ (fun r : ℝ => Wc r.toNNReal) t ∧
        QuantumZipper.fwdHull (V T) (relClock U σ (fun r : ℝ => Wc r.toNNReal) t) =
          relMap U σ '' QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) t ∧
        IsFilling (QuantumZipper.fwdHull (V T) (relClock U σ (fun r : ℝ => Wc r.toNNReal) t))
          (relMap U σ '' ((fun r : ℝ => γ r.toNNReal) '' Icc 0 t ∩ H)) := by
  have hW : Continuous fun r : ℝ => Wc r.toNNReal := hWc.comp continuous_real_toNNReal
  have hW0 : (fun r : ℝ => Wc r.toNNReal) 0 = 0 := by simp only [Real.toNNReal_zero, hWc0]
  have h : ∀ T : ℝ≥0, ∃ V : ℝ → ℝ, (T : ℝ≥0∞) < Tc → _ := fun T => by
    by_cases hT : (T : ℝ≥0∞) < Tc
    · refine (exists_relChain_Icc hW hW0 hU hU0 hσ htip T.2 (hd T hT) (γ := fun r : ℝ => γ r.toNNReal)
        fun t ht => ?_).imp fun V hV _ => hV
      have ht0 : (0 : ℝ) ≤ t := ht.1
      have hts : (t.toNNReal : ℝ≥0∞) < Tc :=
        lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 ht.2)) hT
      have := hγK t.toNNReal hts
      rwa [Real.coe_toNNReal _ ht0, ← image_Icc_toNNReal, Real.coe_toNNReal _ ht0] at this
    · exact ⟨0, fun h => absurd h hT⟩
  choose V hV using h
  exact ⟨V, fun T hT => hV T hT⟩

/-- **The glued relative chain before the first contact** (p. 519: "Increasing rational time and positive-distance
buffers supplies the whole open interval before `T` and its relative capacity clock"). Let the counterflow driver `Wc`
be continuous with `Wc 0 = 0` and `γ` a trace of its hulls (fillings) before `T_c`, and let the closed flow hull
`K_σ` and the closed inverted counterflow hulls `R(K'_T)` be disjoint for every `T < T_c` (`GB6Disjoint`). Then the
intrinsic clock `a(t) = hcap(Ψ(K'_t))/2` is continuous and strictly increasing before `T_c` with `a(0) = 0`, and one
driver `W'` with `W'(0) = 0`, continuous before the relative lifetime `sup_{t < T_c} a(t)`, has the hulls
`K^{W'}_{a(t)} = Ψ(K'_t)`, the fillings of `Ψ(γ([0, t]) ∩ ℍ)`, for every `t < T_c`. -/
theorem exists_glued_relChain (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) (hU : Continuous U) (hU0 : U 0 = 0)
    (hσ : 0 < σ) (htip : Tendsto (QuantumZipper.fwdMapInv U σ) (𝓝[H] 0) (𝓝 p)) (hTc : 0 < Tc)
    (hd : ∀ T : ℝ≥0, (T : ℝ≥0∞) < Tc → Disjoint (closure (QuantumZipper.fwdHull U σ))
      (closure ((fun w : ℂ => -w⁻¹) '' QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) T)))
    (hγK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
      IsFilling (QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) t) (γ '' Icc 0 t)) :
    ∃ W' : ℝ≥0 → ℝ, W' 0 = 0 ∧ relClock U σ (fun r : ℝ => Wc r.toNNReal) 0 = 0 ∧
      StrictMonoOn (fun t : ℝ≥0 => relClock U σ (fun r : ℝ => Wc r.toNNReal) t) {t | (t : ℝ≥0∞) < Tc} ∧
      ContinuousOn (fun t : ℝ≥0 => relClock U σ (fun r : ℝ => Wc r.toNNReal) t) {t | (t : ℝ≥0∞) < Tc} ∧
      ContinuousOn W' {u | ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ (u : ℝ) < relClock U σ (fun r : ℝ => Wc r.toNNReal) t} ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
        QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (relClock U σ (fun r : ℝ => Wc r.toNNReal) t) =
          relMap U σ '' QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) t ∧
        IsFilling (QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (relClock U σ (fun r : ℝ => Wc r.toNNReal) t))
          (relMap U σ '' (γ '' Icc 0 t ∩ H)) := by
  obtain ⟨V, hV⟩ := exists_relChain_family hWc hWc0 hU hU0 hσ htip hd hγK
  set a : ℝ → ℝ := relClock U σ (fun r : ℝ => Wc r.toNNReal) with ha
  have hTc0 : ((0 : ℝ≥0) : ℝ≥0∞) < Tc := by rwa [ENNReal.coe_zero]
  have ha0 : a 0 = 0 := (hV 0 hTc0).2.2.1
  -- the drivers of two intervals agree on the common capacity interval
  have hcons : ∀ T₁ T₂ : ℝ≥0, (T₁ : ℝ≥0∞) < Tc → (T₂ : ℝ≥0∞) < Tc → T₁ ≤ T₂ →
      EqOn (V T₁) (V T₂) (Icc 0 (a T₁)) := by
    intro T₁ T₂ h₁ h₂ h12
    have hsub : Icc (0 : ℝ) T₁ ⊆ Icc 0 T₂ := Icc_subset_Icc_right (by exact_mod_cast h12)
    refine (Sec6.eqOn_clock_and_driver_of_fwdHull_eq (hV T₁ h₁).1 (hV T₂ h₂).1 (hV T₁ h₁).2.1 (hV T₂ h₂).2.1
      T₁.2 ha0 (hV T₁ h₁).2.2.2.1.monotoneOn (hV T₁ h₁).2.2.2.2.1 (fun t ht => ((hV T₁ h₁).2.2.2.2.2 t ht).1)
      fun t ht => ?_).2
    rw [((hV T₁ h₁).2.2.2.2.2 t ht).2.1, ((hV T₂ h₂).2.2.2.2.2 t (hsub ht)).2.1]
  classical
  set W' : ℝ≥0 → ℝ := fun u =>
    if h : ∃ T : ℝ≥0, (T : ℝ≥0∞) < Tc ∧ (u : ℝ) < a T then V h.choose u else 0 with hW'
  have hkey : ∀ (u T : ℝ≥0), (T : ℝ≥0∞) < Tc → (u : ℝ) < a T → W' u = V T u := by
    intro u T hT hu
    have hex : ∃ T : ℝ≥0, (T : ℝ≥0∞) < Tc ∧ (u : ℝ) < a T := ⟨T, hT, hu⟩
    simp only [hW', hex, ↓reduceDIte]
    obtain ⟨hT', hu'⟩ := hex.choose_spec
    rcases le_total hex.choose T with h | h
    · exact hcons _ T hT' hT h ⟨u.2, hu'.le⟩
    · exact (hcons T _ hT hT' h ⟨u.2, hu.le⟩).symm
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → ∃ T' : ℝ≥0, (T' : ℝ≥0∞) < Tc ∧ t < T' := fun t ht => by
    obtain ⟨T', h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    exact ⟨T', h2, ENNReal.coe_lt_coe.1 h1⟩
  have hsm : StrictMonoOn (fun t : ℝ≥0 => a t) {t | (t : ℝ≥0∞) < Tc} := by
    intro t₁ _ t₂ ht₂ h
    exact (hV t₂ ht₂).2.2.2.1 ⟨t₁.2, by exact_mod_cast h.le⟩ ⟨t₂.2, le_rfl⟩ (by exact_mod_cast h)
  refine ⟨W', ?_, ha0, hsm, ?_, ?_, fun t ht => ?_⟩
  · by_cases hex : ∃ T : ℝ≥0, (T : ℝ≥0∞) < Tc ∧ ((0 : ℝ≥0) : ℝ) < a T
    · obtain ⟨T, hT, h0⟩ := hex
      rw [hkey 0 T hT h0]
      simpa using (hV T hT).2.1
    · simp only [hW', hex, ↓reduceDIte]
  · intro t₀ ht₀
    obtain ⟨T', hT', ht₀T'⟩ := hlt t₀ ht₀
    have hc : ContinuousOn (fun t : ℝ≥0 => a t) {t | t < T'} :=
      (hV T' hT').2.2.2.2.1.comp NNReal.continuous_coe.continuousOn fun t ht =>
        ⟨t.2, by exact_mod_cast (le_of_lt ht)⟩
    exact (hc.continuousAt ((isOpen_lt continuous_id continuous_const).mem_nhds ht₀T')).continuousWithinAt
  · rintro u₀ ⟨T₀, hT₀, hu₀⟩
    have hev : (fun u : ℝ≥0 => V T₀ u) =ᶠ[𝓝 u₀] W' := by
      have hopen : IsOpen {u : ℝ≥0 | (u : ℝ) < a T₀} := isOpen_lt NNReal.continuous_coe continuous_const
      exact Filter.mem_of_superset (hopen.mem_nhds hu₀) fun u hu => (hkey u T₀ hT₀ hu).symm
    exact (((hV T₀ hT₀).1.comp NNReal.continuous_coe).continuousAt.congr hev).continuousWithinAt
  · obtain ⟨T', hT', htT'⟩ := hlt t ht
    have htI : (t : ℝ) ∈ Icc (0 : ℝ) T' := ⟨t.2, by exact_mod_cast htT'.le⟩
    obtain ⟨hat, hK, hF⟩ := (hV T' hT').2.2.2.2.2 t htI
    have hat' : a t < a T' := hsm ht hT' htT'
    have hhull : QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (a t) = QuantumZipper.fwdHull (V T') (a t) := by
      refine fwdHull_eq_of_eqOn hat (t₂ := (a t + a T') / 2) (by linarith) fun r hr => ?_
      have hr0 : (0 : ℝ) ≤ r := hr.1
      have hrT : ((r.toNNReal : ℝ≥0) : ℝ) < a T' := by
        rw [Real.coe_toNNReal _ hr0]; linarith [hr.2]
      show W' r.toNNReal = V T' r
      rw [hkey _ T' hT' hrT, Real.coe_toNNReal _ hr0]
    rw [hhull]
    refine ⟨hK, ?_⟩
    rwa [image_Icc_toNNReal] at hF

/-- **The glued relative chain with infinite relative lifetime.** If the relative clock is unbounded before `T_c`
(the relative lifetime is infinite), it is an exhausting clock before `T_c` (`Sec5.CrossRestart.IsExhaustingClock`;
its inverse `clockInv` is a continuous strictly increasing map onto `[0, T_c)`), and the glued driver is continuous on
`[0, ∞)`. -/
theorem exists_glued_relChain_of_unbounded (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) (hU : Continuous U)
    (hU0 : U 0 = 0) (hσ : 0 < σ) (htip : Tendsto (QuantumZipper.fwdMapInv U σ) (𝓝[H] 0) (𝓝 p)) (hTc : 0 < Tc)
    (hd : ∀ T : ℝ≥0, (T : ℝ≥0∞) < Tc → Disjoint (closure (QuantumZipper.fwdHull U σ))
      (closure ((fun w : ℂ => -w⁻¹) '' QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) T)))
    (hγK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
      IsFilling (QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) t) (γ '' Icc 0 t))
    (hunb : ∀ u : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ u ≤ relClock U σ (fun r : ℝ => Wc r.toNNReal) t) :
    ∃ W' : ℝ≥0 → ℝ, W' 0 = 0 ∧ Continuous W' ∧
      Sec5.CrossRestart.IsExhaustingClock (fun t : ℝ≥0 => relClock U σ (fun r : ℝ => Wc r.toNNReal) t) Tc ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
        QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (relClock U σ (fun r : ℝ => Wc r.toNNReal) t) =
          relMap U σ '' QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) t ∧
        IsFilling (QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (relClock U σ (fun r : ℝ => Wc r.toNNReal) t))
          (relMap U σ '' (γ '' Icc 0 t ∩ H)) := by
  obtain ⟨W', hW'0, ha0, hsm, hac, hW'c, hK⟩ := exists_glued_relChain hWc hWc0 hU hU0 hσ htip hTc hd hγK
  refine ⟨W', hW'0, ?_, ⟨hTc, ha0, hsm, hac, hunb⟩, hK⟩
  rw [← continuousOn_univ]
  refine hW'c.mono fun u _ => ?_
  obtain ⟨t, ht, hut⟩ := hunb ((u : ℝ) + 1)
  exact ⟨t, ht, by linarith⟩

end Glue

end GB6

end Supp8

end InteractingSLE
