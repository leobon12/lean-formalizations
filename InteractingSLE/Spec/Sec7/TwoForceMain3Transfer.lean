/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.CounterflowProbTransfer
import InteractingSLE.Spec.Sec2.OneForceLaw

/-!
# §7.1: integrated driving uniqueness transfers coded driving events (any force word)

Packet PROVE-SEC7-A4. Proposition 7.3's proof (`source/spec/p241-288.md` L44, p. 242): "Integrated driving
uniqueness transfers its continuous simple trace and transience to the stated two-seed driving law." The same
transfer, through the one-force uniqueness, gives the one-force seed case (p. 378: "The one-force seed case is part
of that theorem").

PROVE-SEC7-D2 (`CounterflowProbTransfer.lean`) proved the transfer for the two-seed word. Here it is stated for any
force word whose killed-state laws agree (Theorem 2.2's uniqueness, in the frozen form) and whose lifetimes are
almost surely infinite:

* `measure_box_eq_killedState_gen`, `map_killedRestrict_eq_of_killedState`: equal killed-state laws and infinite
  lifetimes give equal laws of the driver at the nonnegative rational times;
* `ae_transfer_of_killedState`: **the transfer** of a driving-path event coded by a measurable set of rational-time
  values;
* `ae_lifetime_eq_top_oneForceRight`: a single mark of weight `> −2` on the right never reaches the
  continuation threshold (the construction (2.3) with `c = (ρ + 2)/a > 0`);
* `IsIntegratedSLEPath.forgetLeft_of_top`, `IsIntegratedSLEEvolution.forgetLeft_of_top`: forgetting left marks of
  weight zero on an infinite lifetime gives an evolution of the word without them (used with Theorem 2.2's one-force
  uniqueness, `OneForce.measure_killedState_eq_right`, for the one-force seed case).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal NNRat

namespace InteractingSLE

namespace Sec7

/-! ### Equal killed-state laws give equal rational-time driver laws -/

section General

variable {nL nR : ℕ}

/-- With infinite lifetime, a box event of the killed driver at finitely many rational times is a killed-state event
of Theorem 2.2's uniqueness statement, up to a null set (any force word). -/
theorem measure_box_eq_killedState_gen {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {I : Finset ℚ≥0} {n : ℕ} (e : Fin n ≃ I) (A : I → Set ℝ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    P {ω | ∀ i : I, killedProc W ζ (i : ℚ≥0) ω ∈ A i} =
      P {ω | ∀ j, (((e j : ℚ≥0) : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
        (W ((e j : ℚ≥0) : ℝ≥0) ω, (fun i => VL i ((e j : ℚ≥0) : ℝ≥0) ω),
          (fun i => VR i ((e j : ℚ≥0) : ℝ≥0) ω), B ((e j : ℚ≥0) : ℝ≥0) ω) ∈ A (e j) ×ˢ univ} := by
  refine measure_congr ?_
  filter_upwards [hζ] with ω hω
  apply propext
  simp only [killedProc, hω, ENNReal.coe_lt_top, ↓reduceIte, true_and, mem_prod, mem_univ, and_true]
  exact ⟨fun h j => h (e j), fun h i => by simpa using h (e.symm i)⟩

/-- The killed-state equality of Theorem 2.2's uniqueness statement (frozen form) for two given evolutions. -/
def KilledStateLawEq {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} (P₁ : Measure Ω₁) (W₁ : ℝ≥0 → Ω₁ → ℝ)
    (VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ) (VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ)
    (ζ₁ : Ω₁ → ℝ≥0∞) {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂)
    (W₂ : ℝ≥0 → Ω₂ → ℝ) (VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ) (VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ)
    (B₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞) : Prop :=
  ∀ (n : ℕ) (ts : Fin n → ℝ≥0) (A : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
    (∀ j, MeasurableSet (A j)) →
    P₁ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₁ ω ∧
        (W₁ (ts j) ω, (fun i => VL₁ i (ts j) ω), (fun i => VR₁ i (ts j) ω), B₁ (ts j) ω) ∈ A j} =
      P₂ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₂ ω ∧
        (W₂ (ts j) ω, (fun i => VL₂ i (ts j) ω), (fun i => VR₂ i (ts j) ω), B₂ (ts j) ω) ∈ A j}

/-- **Equal killed-state laws and infinite lifetimes give equal rational-time driver laws** (any force word). -/
theorem map_killedRestrict_eq_of_killedState
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (hW₁ : AdaptedBefore 𝓕₁ ζ₁ W₁) (hζ₁ : ∀ᵐ ω ∂P₁, ζ₁ ω = ⊤)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (hW₂ : AdaptedBefore 𝓕₂ ζ₂ W₂) (hζ₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤)
    (hK : KilledStateLawEq P₁ W₁ VL₁ VR₁ B₁ ζ₁ P₂ W₂ VL₂ VR₂ B₂ ζ₂) :
    P₁.map (killedRestrict W₁ ζ₁) = P₂.map (killedRestrict W₂ ζ₂) := by
  have hm₁ := measurable_killedRestrict hW₁
  have hm₂ := measurable_killedRestrict hW₂
  -- the box probabilities agree
  have key : ∀ (I : Finset ℚ≥0) (A : I → Set ℝ), (∀ i, MeasurableSet (A i)) →
      P₁ {ω | ∀ i : I, killedProc W₁ ζ₁ (i : ℚ≥0) ω ∈ A i} =
        P₂ {ω | ∀ i : I, killedProc W₂ ζ₂ (i : ℚ≥0) ω ∈ A i} := by
    intro I A hA
    set e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
    set ts : Fin (Fintype.card I) → ℝ≥0 := fun j => ((e j : ℚ≥0) : ℝ≥0)
    set A' : Fin (Fintype.card I) → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ) :=
      fun j => A (e j) ×ˢ univ
    have hA' : ∀ j, MeasurableSet (A' j) := fun j => (hA _).prod MeasurableSet.univ
    rw [measure_box_eq_killedState_gen e A (VL := VL₁) (VR := VR₁) (B := B₁) hζ₁,
      measure_box_eq_killedState_gen e A (VL := VL₂) (VR := VR₂) (B := B₂) hζ₂]
    exact hK _ ts A' hA'
  have hfd : ∀ I : Finset ℚ≥0, (P₁.map (killedRestrict W₁ ζ₁)).map I.restrict =
      (P₂.map (killedRestrict W₂ ζ₂)).map I.restrict := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hm₁,
      Measure.map_map (Finset.measurable_restrict I) hm₂]
    refine ext_of_generate_finite _ generateFrom_pi.symm isPiSystem_pi (fun s hs => ?_) ?_
    · obtain ⟨A, hA', rfl⟩ := hs
      have hA : ∀ i, MeasurableSet (A i) := fun i => hA' i (mem_univ i)
      rw [Measure.map_apply ((Finset.measurable_restrict I).comp hm₁) (MeasurableSet.univ_pi hA),
        Measure.map_apply ((Finset.measurable_restrict I).comp hm₂) (MeasurableSet.univ_pi hA)]
      have h := key I A hA
      simpa [Set.preimage, Set.mem_univ_pi, killedRestrict] using h
    · rw [Measure.map_apply ((Finset.measurable_restrict I).comp hm₁) MeasurableSet.univ,
        Measure.map_apply ((Finset.measurable_restrict I).comp hm₂) MeasurableSet.univ]
      simp
  exact IsProjectiveLimit.unique (P := fun I => (P₁.map (killedRestrict W₁ ζ₁)).map I.restrict)
    (fun I => rfl) (fun I => (hfd I).symm)

/-- An integrated path with infinite lifetime has a continuous driver vanishing at `0`. -/
theorem IsIntegratedSLEPath.continuous_w_of_top {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} (hpath : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ⊤) :
    Continuous w ∧ w 0 = 0 :=
  ⟨continuousOn_univ.1 (by simpa using hpath.2.2.2.1), hpath.1⟩

/-- **Transfer of a coded driving-path event through integrated driving uniqueness** (any force word): if two
evolutions of the same word have equal killed-state laws and infinite lifetimes, an event of the driving path that is
coded by a measurable set of rational-time values and holds almost surely for the first holds almost surely for the
second. -/
theorem ae_transfer_of_killedState {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {p : (ℝ≥0 → ℝ) → Prop} {G : Set (ℚ≥0 → ℝ)} (hG : MeasurableSet G)
    (hGp : ∀ w : ℝ≥0 → ℝ, Continuous w → w 0 = 0 → ((fun q : ℚ≥0 => w q) ∈ G ↔ p w))
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution a xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁) (hζ₁ : ∀ᵐ ω ∂P₁, ζ₁ ω = ⊤)
    (hp₁ : ∀ᵐ ω ∂P₁, p fun t => W₁ t ω)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution a xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) (hζ₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤)
    (hK : KilledStateLawEq P₁ W₁ VL₁ VR₁ B₁ ζ₁ P₂ W₂ VL₂ VR₂ B₂ ζ₂) :
    ∀ᵐ ω ∂P₂, p fun t => W₂ t ω := by
  have hm₁ := measurable_killedRestrict h₁.2.1
  have hm₂ := measurable_killedRestrict h₂.2.1
  have hgood₁ : ∀ᵐ ω ∂P₁, killedRestrict W₁ ζ₁ ω ∈ G := by
    filter_upwards [hp₁, hζ₁, h₁.2.2.2.2] with ω hω hζω hpath
    rw [hζω] at hpath
    obtain ⟨hc, h0⟩ := IsIntegratedSLEPath.continuous_w_of_top hpath
    rw [killedRestrict_eq_of_top hζω]
    exact (hGp _ hc h0).2 hω
  have hgood₂ : ∀ᵐ ω ∂P₂, killedRestrict W₂ ζ₂ ω ∈ G := by
    have h := (ae_map_iff hm₁.aemeasurable hG).2 hgood₁
    rw [map_killedRestrict_eq_of_killedState h₁.2.1 hζ₁ h₂.2.1 hζ₂ hK] at h
    exact (ae_map_iff hm₂.aemeasurable hG).1 h
  filter_upwards [hgood₂, hζ₂, h₂.2.2.2.2] with ω hω hζω hpath
  rw [hζω] at hpath
  obtain ⟨hc, h0⟩ := IsIntegratedSLEPath.continuous_w_of_top hpath
  rw [killedRestrict_eq_of_top hζω] at hω
  exact (hGp _ hc h0).1 hω

end General

/-! ### One mark at the seed: infinite lifetime -/

/-- **A single mark of weight `> −2` on the right never reaches the continuation threshold**: almost surely `ζ = ∞`
(the evolution is the construction (2.3), whose Bessel dimension parameter `c = (ρ + 2)/a` is positive). -/
theorem ae_lifetime_eq_top_oneForceRight {a : ℝ} (ha : 0 < a) {xL : Fin 0 → ℝ} {xR : Fin 1 → ℝ}
    {ρL : Fin 0 → ℝ} {ρR : Fin 1 → ℝ} (hxR : 0 ≤ xR 0) (hρ : -2 < ρR 0) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
  obtain ⟨B', hm, hc, h0, hB', hae⟩ := QuantumZipper.RS.exists_good_version0 h.1.1
  filter_upwards [OneForce.ae_eq_construction_right ha hxR h hB'.toIsPreBrownianReal hm hc h0 hae]
    with ω hω
  rw [hω.1, OneForce.rightζ, OneForce.oneζ_of_pos (div_pos (by linarith) ha)]

/-! ### Forgetting a mark of weight zero -/

/-- With all weights on a side equal to zero, the threshold condition only sees the other side. -/
theorem thresholdCondition_iff_of_left_eq_zero {nL nR : ℕ} {ρL : Fin nL → ℝ} (ρR : Fin nR → ℝ)
    (hρL : ∀ i, ρL i = 0) (w : ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    ForceWord.ThresholdCondition ρL ρR w vL vR ↔
      (∑ i ∈ Finset.univ.filter (fun i => vR i = w), ρR i) ≤ -2 := by
  unfold ForceWord.ThresholdCondition
  have h0 : (∑ i ∈ Finset.univ.filter (fun i => vL i = w), ρL i) = 0 :=
    Finset.sum_eq_zero fun i _ => hρL i
  rw [h0]
  constructor
  · rintro (h | h)
    · norm_num at h
    · exact h
  · exact Or.inr

/-- **Forgetting the left marks of weight zero** on an infinite lifetime: an integrated path of a word whose left
weights all vanish is an integrated path of the word with no left marks (the zero drift terms disappear; the
maximality clauses are vacuous for `ζ = ∞`). -/
theorem IsIntegratedSLEPath.forgetLeft_of_top {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hρL : ∀ i, ρL i = 0) {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (hpath : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ⊤) (xL' ρL' : Fin 0 → ℝ)
    (vL' : Fin 0 → ℝ≥0 → ℝ) : IsIntegratedSLEPath a xL' xR ρL' ρR w vL' vR b ⊤ := by
  obtain ⟨hw0, -, hvR0, hwc, -, hvRc, -, -, hwvR, hmonoR, -, hintR, hweq, -, hvReq, -, hcolR,
    hnt, -, -⟩ := hpath
  refine ⟨hw0, fun i => i.elim0, hvR0, hwc, fun i => i.elim0, hvRc,
    fun _ _ i => i.elim0, fun _ _ i => i.elim0, hwvR, hmonoR, fun _ _ i => i.elim0, hintR,
    fun t ht => ?_, fun _ _ i => i.elim0, hvReq, fun i => i.elim0, hcolR, fun t ht => ?_,
    fun h => absurd h ENNReal.top_ne_zero, fun T _ hT => absurd hT.symm ENNReal.top_ne_coe⟩
  · have hz : (∑ i, ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal)) = 0 :=
      Finset.sum_eq_zero fun i _ => by simp [hρL i]
    have hz' : (∑ i : Fin 0, ∫ s in (0 : ℝ)..t, ρL' i / (w s.toNNReal - vL' i s.toNNReal)) = 0 :=
      Fin.sum_univ_zero _
    rw [hweq t ht, hz, hz']
  · rw [thresholdCondition_iff_of_left_eq_zero ρR (fun i => i.elim0)]
    rw [← thresholdCondition_iff_of_left_eq_zero ρR hρL (w t) (fun i => vL i t)]
    exact hnt t ht

/-- **Forgetting the left marks of weight zero** of an evolution with almost surely infinite lifetime. -/
theorem IsIntegratedSLEEvolution.forgetLeft_of_top {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hρL : ∀ i, ρL i = 0) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (xL' ρL' : Fin 0 → ℝ) (VL' : Fin 0 → ℝ≥0 → Ω → ℝ) :
    IsIntegratedSLEEvolution a xL' xR ρL' ρR P 𝓕 W VL' VR B ζ := by
  refine ⟨h.1, h.2.1, fun i => i.elim0, h.2.2.2.1, ?_⟩
  filter_upwards [h.2.2.2.2, hζ] with ω hpath hω
  rw [hω] at hpath ⊢
  exact IsIntegratedSLEPath.forgetLeft_of_top hρL hpath xL' ρL' _

end Sec7

end InteractingSLE
