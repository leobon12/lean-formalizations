/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefK2
import InteractingSLE.Spec.Sec7.PocketCoupling
import InteractingSLE.Spec.Sec7.PocketMartLife

/-!
# The pocket's (S) and (L): restriction to subevents, and the threshold time of a both-low word

Packet PROVE-LEMMA725REF3. Aux. lemma 125's "The canonical law survives the exterior reveal" (`source/spec/p385-432.md`
L234–L250, p. 396) is proved on the ambient probability space, while the pocket evolution (E) of Lemma 7.25's proof
(Aux. lemma 122, pp. 389–391) is produced by the landed chain on successive restrictions: to the word-shape event of the
walls, to the event of infinite relative lifetime, and to Aux. lemma 122's event of full measure. This file provides the
generic transfer steps.

* `ae_mem_imp_of_ae_condSub`: an almost sure property under `condSub P S` holds `P`-almost surely on `S`;
* **`hasSafeLaw_subtype`**, **`hasSafeMembers_subtype`**: K2's inputs (S) and (L) restrict to a subevent `S`, for the
  trace filtration, as soon as every event of the filtration meets `S` in an event of the filtration up to a null set
  (`S` in the time-zero σ-algebra, or `S` of full measure: `subtype_cond_of_measurableSet_zero`,
  `subtype_cond_of_ae`);
* `hasSafeLaw_mono_life`, `hasSafeMembers_mono_life`: (S) and (L) pass to a smaller lifetime;
* `IsRandomWordEvolution.mono_sigma`: (E) for a smaller initial σ-algebra that still knows the event and the word;
* **`thresholdTime_eq_top_of_partialSums`**: an ordered state of a word whose side partial sums all exceed `−2` never
  meets the continuation threshold (Definition 2.1), so the threshold time of an ordered evolution is `∞`.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or a result taking them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma725RefSafe

open Restart.DomainMarkov Restart.DomainMarkov.K2 Aux122Disint PhaseSel PocketMartLife PocketCoupling LocalSets Coupling

/-! ### The threshold time of a both-low ordered word -/

section Threshold

/-- A downward-closed set of indices has weight sum `> −2` when every initial partial sum does. -/
theorem neg_two_lt_sum_filter_of_downward {n : ℕ} {ρ : Fin n → ℝ}
    (hs : ∀ m : Fin n, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρ i) (p : Fin n → Prop) [DecidablePred p]
    (hp : ∀ i j, i ≤ j → p j → p i) : -2 < ∑ i ∈ Finset.univ.filter p, ρ i := by
  by_cases hne : (Finset.univ.filter p).Nonempty
  · set m := (Finset.univ.filter p).max' hne with hm
    have hpm : p m := (Finset.mem_filter.1 (Finset.max'_mem _ hne)).2
    have e : Finset.univ.filter p = Finset.univ.filter (fun i => i ≤ m) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hi => Finset.le_max' _ i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩), fun hi => hp i m hi hpm⟩
    rw [e]
    exact hs m
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]
    norm_num

/-- **An ordered state of a word with all side partial sums `> −2` is never a threshold state**: the left marks equal
to the driver form an initial segment of the left word, and so do the right ones. -/
theorem not_thresholdCondition_of_partialSums {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hsL : ∀ m : Fin nL, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin nR, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i) {w : ℝ} {vL : Fin nL → ℝ}
    {vR : Fin nR → ℝ} (hL : ∀ i, vL i ≤ w) (hLa : Antitone vL) (hR : ∀ j, w ≤ vR j) (hRm : Monotone vR) :
    ¬ ForceWord.ThresholdCondition ρL ρR w vL vR := by
  classical
  rintro (h | h)
  · refine absurd h (not_le.2 (neg_two_lt_sum_filter_of_downward hsL _ fun i j hij hj => ?_))
    exact le_antisymm (hL i) (hj ▸ hLa hij)
  · refine absurd h (not_le.2 (neg_two_lt_sum_filter_of_downward hsR _ fun i j hij hj => ?_))
    exact le_antisymm (hj ▸ hRm hij) (hR i)

/-- **The threshold time of an ordered evolution of a word with all side partial sums `> −2` is `∞`.** -/
theorem thresholdTime_eq_top_of_partialSums {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hsL : ∀ m : Fin nL, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin nR, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i) {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} (hL : ∀ t i, vL i t ≤ w t)
    (hLa : ∀ t, Antitone fun i => vL i t) (hR : ∀ t j, w t ≤ vR j t) (hRm : ∀ t, Monotone fun j => vR j t) :
    MartChar.thresholdTime ρL ρR w vL vR = ⊤ := by
  have hempty : MartChar.thresholdSet ρL ρR w vL vR = ∅ :=
    eq_empty_iff_forall_notMem.2 fun t ht =>
      not_thresholdCondition_of_partialSums hsL hsR (hL t) (hLa t) (hR t) (hRm t) ht
  simp only [MartChar.thresholdTime, hempty, Set.not_nonempty_empty, ↓reduceIte]

end Threshold

/-! ### Restriction to a subevent -/

section Restrict

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {S : Set Ω}

/-- **An almost sure property under `condSub P S` holds `P`-almost surely on `S`.** -/
theorem ae_mem_imp_of_ae_condSub [IsFiniteMeasure P] (hS : MeasurableSet S) {p : S → Prop}
    (h : ∀ᵐ ω ∂(condSub P S), p ω) : ∀ᵐ ω ∂P, ∀ hω : ω ∈ S, p ⟨ω, hω⟩ := by
  have h' : ∀ᵐ ω : S ∂(condSub P S), (fun x : Ω => ∀ hx : x ∈ S, p ⟨x, hx⟩) (ω : Ω) := by
    filter_upwards [h] with ω hω _
    exact hω
  filter_upwards [ae_of_ae_condSub (p := fun x : Ω => ∀ hx : x ∈ S, p ⟨x, hx⟩) hS h'] with ω hω hωS
  exact hω hωS hωS

/-- The restriction condition for an event of the time-zero σ-algebra. -/
theorem subtype_cond_of_measurableSet_zero {𝓗 : Filtration ℝ≥0 mΩ} (hS0 : MeasurableSet[𝓗 0] S) :
    ∀ q D, MeasurableSet[𝓗 q] D → ∃ D₀, MeasurableSet[𝓗 q] D₀ ∧ D ∩ S =ᵐ[P] D₀ := fun q D hD =>
  ⟨D ∩ S, hD.inter (𝓗.mono (zero_le (a := q)) _ hS0), EventuallyEq.rfl⟩

/-- The restriction condition for an event of full measure. -/
theorem subtype_cond_of_ae {𝓗 : Filtration ℝ≥0 mΩ} (hS : ∀ᵐ ω ∂P, ω ∈ S) :
    ∀ q D, MeasurableSet[𝓗 q] D → ∃ D₀, MeasurableSet[𝓗 q] D₀ ∧ D ∩ S =ᵐ[P] D₀ := fun _ D hD => by
  refine ⟨D, hD, ?_⟩
  filter_upwards [hS] with ω hω
  exact propext ⟨fun h => h.1, fun h => ⟨h, hω⟩⟩

variable {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓗 : Filtration ℝ≥0 mΩ} {F : Set Ω}
  {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {X : Ω → DistOn upperHalfPlaneOpens}

/-- **(S) restricts to a subevent** (with the trace filtration). -/
theorem hasSafeLaw_subtype [IsFiniteMeasure P] (hS : MeasurableSet S)
    (hS𝓗 : ∀ q D, MeasurableSet[𝓗 q] D → ∃ D₀, MeasurableSet[𝓗 q] D₀ ∧ D ∩ S =ᵐ[P] D₀)
    (h : HasSafeLaw κ ρL ρR P 𝓗 F ζ W VL VR X) :
    HasSafeLaw κ ρL ρR (condSub P S) (subFilt 𝓗 S) (Subtype.val ⁻¹' F) (fun ω : S => ζ ω)
      (fun t (ω : S) => W t ω) (fun i t (ω : S) => VL i t ω) (fun j t (ω : S) => VR j t ω) fun ω : S => X ω := by
  intro ψ q D' hD' hin
  obtain ⟨D, hD, rfl⟩ := hD'
  obtain ⟨D₀, hD₀, hae⟩ := hS𝓗 q D hD
  have hDm : MeasurableSet D := 𝓗.le q _ hD
  have e1 := setIntegral_condSub (P := P) hS hDm fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ))
  have e2 := setIntegral_condSub (P := P) hS hDm fun ω => cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (fun _ => q) ω
  refine e1.trans (Eq.trans ?_ e2.symm)
  rw [setIntegral_congr_set hae, setIntegral_congr_set hae]
  congr 1
  refine h ψ q D₀ hD₀ ?_
  filter_upwards [ae_mem_imp_of_ae_condSub hS hin, hae] with ω h1 h2 hω₀
  have hω : ω ∈ D ∩ S := h2.mpr hω₀
  exact h1 hω.2 hω.1

/-- **(L) restricts to a subevent** (with the trace filtration). -/
theorem hasSafeMembers_subtype [IsFiniteMeasure P] (hS : MeasurableSet S)
    (hS𝓗 : ∀ q D, MeasurableSet[𝓗 q] D → ∃ D₀, MeasurableSet[𝓗 q] D₀ ∧ D ∩ S =ᵐ[P] D₀)
    (h : HasSafeMembers P 𝓗 F ζ W X) :
    HasSafeMembers (condSub P S) (subFilt 𝓗 S) (Subtype.val ⁻¹' F) (fun ω : S => ζ ω) (fun t (ω : S) => W t ω)
      fun ω : S => X ω := by
  intro s Fb hFb D' hD' hin f Ξ
  obtain ⟨D, hD, rfl⟩ := hD'
  obtain ⟨D₀, hD₀, hae⟩ := hS𝓗 s D hD
  have hDm : MeasurableSet D := 𝓗.le s _ hD
  have e1 := setIntegral_condSub (P := P) hS hDm fun ω =>
    Complex.exp (Complex.I * (X ω (lapTest (ballsOpen Fb) f + Ξ) : ℂ))
  have e2 := setIntegral_condSub (P := P) hS hDm fun ω => Complex.exp (Complex.I * (X ω Ξ : ℂ))
  have key : ∫ ω in D₀, Complex.exp (Complex.I * (X ω (lapTest (ballsOpen Fb) f + Ξ) : ℂ)) ∂P =
      projFactor (ballsOpen Fb) f Ξ * ∫ ω in D₀, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P := by
    refine h s Fb hFb D₀ hD₀ ?_ f Ξ
    filter_upwards [ae_mem_imp_of_ae_condSub hS hin, hae] with ω h1 h2 hω₀
    have hω : ω ∈ D ∩ S := h2.mpr hω₀
    exact h1 hω.2 hω.1
  refine e1.trans ?_
  rw [e2, setIntegral_congr_set hae, setIntegral_congr_set hae, key, Complex.real_smul, Complex.real_smul]
  ring

/-- (S) passes to a smaller lifetime. -/
theorem hasSafeLaw_mono_life {ζ' : Ω → ℝ≥0∞} (hζ : ∀ ω, ζ' ω ≤ ζ ω) (h : HasSafeLaw κ ρL ρR P 𝓗 F ζ W VL VR X) :
    HasSafeLaw κ ρL ρR P 𝓗 F ζ' W VL VR X := by
  intro ψ q D hD hsafe
  refine h ψ q D hD ?_
  filter_upwards [hsafe] with ω hω hωD
  obtain ⟨hF, hq, hd⟩ := hω hωD
  exact ⟨hF, lt_of_lt_of_le hq (hζ ω), hd⟩

/-- (L) passes to a smaller lifetime. -/
theorem hasSafeMembers_mono_life {ζ' : Ω → ℝ≥0∞} (hζ : ∀ ω, ζ' ω ≤ ζ ω) (h : HasSafeMembers P 𝓗 F ζ W X) :
    HasSafeMembers P 𝓗 F ζ' W X := by
  intro s Fb hFb D hD hsafe f Ξ
  refine h s Fb hFb D hD ?_ f Ξ
  filter_upwards [hsafe] with ω hω hωD
  obtain ⟨hF, hs, hd⟩ := hω hωD
  exact ⟨hF, lt_of_lt_of_le hs (hζ ω), hd⟩

end Restrict

/-! ### (E) for a smaller initial σ-algebra -/

section Mono

variable {Ω : Type*} {𝓔 𝓔' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {a : ℝ} {nL nR : ℕ}
  {F : Set Ω} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **(E) for a smaller initial σ-algebra** that still knows the selection event and the word. -/
theorem _root_.InteractingSLE.Sec7.Aux122Disint.IsRandomWordEvolution.mono_sigma
    (h : IsRandomWordEvolution a P 𝓔 F ΘL ΘR ρL ρR 𝓕 W VL VR B ζ) (hle : 𝓔' ≤ 𝓔) (hF : MeasurableSet[𝓔'] F)
    (hL : Measurable[𝓔'] ΘL) (hR : Measurable[𝓔'] ΘR) :
    IsRandomWordEvolution a P 𝓔' F ΘL ΘR ρL ρR 𝓕 W VL VR B ζ := by
  obtain ⟨h0, -, -, -, rest⟩ := h
  exact ⟨hle.trans h0, hF, hL, hR, rest⟩

end Mono

end InteractingSLE.Sec7.Lemma725RefSafe
