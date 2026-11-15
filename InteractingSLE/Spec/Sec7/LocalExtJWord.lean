/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtJScale
import InteractingSLE.Spec.Sec4.ZeroMarks

/-!
# The seed-only word

Packet PROVE-LOCEXT-J, input (U) of Aux. lemma 54. Through its local stop, a stopped seed coupling is a local evolution
of the **seed-weight word** (every mark off the seed has weight `0`), while the reference is a **two-seed** evolution.
Both are compared as evolutions of the **seed-only word**: the marks of the original word that start at `0`, with their
original weights (`seedWord`):

* `seedEmb x`: the order embedding of the seed marks of one side (`x i = 0`);
* `Sec2.IsSLEPathUpTo.compEmb`: deleting zero-weight marks from a local path (the local form of
  `IsIntegratedSLEPath.compEmb`);
* `Sec2.IsSLEPathUpTo.splitSeed`: a two-seed local path with weights `r_∓` is a local path of every seed-only word whose
  weights sum to `r_∓` on each side (all seed marks of a side follow the merged seed mark);
* `isIntegratedSLEPath_top_of_isSLEPathUpTo`: with infinite lifetime the maximality clauses are vacuous;
* `IsIntegratedSLEEvolution.splitSeed`: the two-seed reference read as an evolution of the seed-only word;
* `map_stCode_eq_of_top`: two evolutions of an ordered word with infinite lifetimes have the same code law (Theorem
  2.2's uniqueness in law); `ae_lifetime_eq_top_of_twin`: an evolution of a word with the killed laws of one with infinite
  lifetime has infinite lifetime.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Sec2 Sec2.Assembly3

/-! ### The seed embedding -/

section SeedEmb

variable {n : ℕ}

/-- The number of seed marks of one side. -/
abbrev seedCount (x : Fin n → ℝ) : ℕ := (Finset.univ.filter fun i => x i = 0).card

/-- The seed marks of one side (`x i = 0`), in increasing index order. -/
def seedEmb (x : Fin n → ℝ) : Fin (seedCount x) ↪o Fin n :=
  (Finset.univ.filter fun i => x i = 0).orderEmbOfFin rfl

theorem range_seedEmb (x : Fin n → ℝ) : Set.range (seedEmb x) = {i | x i = 0} := by
  rw [seedEmb, Finset.range_orderEmbOfFin]
  ext i
  simp

theorem seedEmb_eq_zero (x : Fin n → ℝ) (j : Fin (seedCount x)) : x (seedEmb x j) = 0 := by
  have : seedEmb x j ∈ Set.range (seedEmb x) := ⟨j, rfl⟩
  rw [range_seedEmb] at this
  exact this

theorem ne_zero_of_notMem_range_seedEmb {x : Fin n → ℝ} {i : Fin n} (hi : i ∉ Set.range (seedEmb x)) : x i ≠ 0 := by
  rw [range_seedEmb] at hi
  exact hi

theorem seedWtL_eq_zero_of_notMem {xL ρL : Fin n → ℝ} {i : Fin n} (hi : i ∉ Set.range (seedEmb xL)) :
    seedWtL xL ρL i = 0 := by
  simp only [seedWtL, ne_zero_of_notMem_range_seedEmb hi, ↓reduceIte]

theorem seedWtR_eq_zero_of_notMem {xR ρR : Fin n → ℝ} {i : Fin n} (hi : i ∉ Set.range (seedEmb xR)) :
    seedWtR xR ρR i = 0 := by
  simp only [seedWtR, ne_zero_of_notMem_range_seedEmb hi, ↓reduceIte]

theorem seedWtL_seedEmb (xL ρL : Fin n → ℝ) (j : Fin (seedCount xL)) :
    seedWtL xL ρL (seedEmb xL j) = ρL (seedEmb xL j) := by
  simp only [seedWtL, seedEmb_eq_zero, ↓reduceIte]

theorem seedWtR_seedEmb (xR ρR : Fin n → ℝ) (j : Fin (seedCount xR)) :
    seedWtR xR ρR (seedEmb xR j) = ρR (seedEmb xR j) := by
  simp only [seedWtR, seedEmb_eq_zero, ↓reduceIte]

/-- The seed weights sum to the seed sum. -/
theorem sum_seedEmb_L (xL ρL : Fin n → ℝ) : ∑ j, ρL (seedEmb xL j) = seedSumL xL ρL := by
  have h := Sec4.sum_comp_embedding (seedEmb xL) (seedEmb xL).injective (seedWtL xL ρL)
    fun i hi => seedWtL_eq_zero_of_notMem hi
  simp only [seedWtL_seedEmb] at h
  rw [h]
  rfl

theorem sum_seedEmb_R (xR ρR : Fin n → ℝ) : ∑ j, ρR (seedEmb xR j) = seedSumR xR ρR := by
  have h := Sec4.sum_comp_embedding (seedEmb xR) (seedEmb xR).injective (seedWtR xR ρR)
    fun i hi => seedWtR_eq_zero_of_notMem hi
  simp only [seedWtR_seedEmb] at h
  rw [h]
  rfl

theorem exists_seed_iff_pos (x : Fin n → ℝ) : (∃ i, x i = 0) ↔ 0 < seedCount x := by
  rw [Finset.card_pos]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, by simp [hi]⟩
  · rintro ⟨i, hi⟩; exact ⟨i, by simpa using hi⟩

end SeedEmb

/-! ### Deleting zero-weight marks from a local path -/

section Delete

variable {a : ℝ} {nL nR mL mR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞}

/-- **Deleting zero-weight marks from a local path.** -/
theorem _root_.InteractingSLE.Sec2.IsSLEPathUpTo.compEmb (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ)
    (eL : Fin mL ↪o Fin nL) (eR : Fin mR ↪o Fin nR) (hL : ∀ i, i ∉ Set.range eL → ρL i = 0)
    (hR : ∀ i, i ∉ Set.range eR → ρR i = 0) :
    IsSLEPathUpTo a (fun j => xL (eL j)) (fun j => xR (eR j)) (fun j => ρL (eL j)) (fun j => ρR (eR j)) w
      (fun j => vL (eL j)) (fun j => vR (eR j)) b τ where
  w_zero := h.w_zero
  vL_zero _ := h.vL_zero _
  vR_zero _ := h.vR_zero _
  continuousOn_w := h.continuousOn_w
  continuousOn_vL _ := h.continuousOn_vL _
  continuousOn_vR _ := h.continuousOn_vR _
  antitone_vL ht := (h.antitone_vL ht).comp_monotone eL.monotone
  vL_le_w ht _ := h.vL_le_w ht _
  w_le_vR ht _ := h.w_le_vR ht _
  monotone_vR ht := (h.monotone_vR ht).comp eR.monotone
  integrable_gapL ht _ := h.integrable_gapL ht _
  integrable_gapR ht _ := h.integrable_gapR ht _
  w_eq {t} ht := by
    have e1 := Sec4.sum_comp_embedding eL eL.injective
      (fun i => ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal))
      (fun i hi => by simp [hL i hi])
    have e2 := Sec4.sum_comp_embedding eR eR.injective
      (fun i => ∫ s in (0 : ℝ)..t, ρR i / (w s.toNNReal - vR i s.toNNReal))
      (fun i hi => by simp [hR i hi])
    rw [h.w_eq ht, e1, e2]
  vL_eq ht _ := h.vL_eq ht _
  vR_eq ht _ := h.vR_eq ht _
  volume_collisionL _ := h.volume_collisionL _
  volume_collisionR _ := h.volume_collisionR _
  not_threshold {t} ht hth := h.not_threshold ht ((Sec4.thresholdCondition_compEmb_iff eL.injective eR.injective
    hL hR (w t) (fun i => vL i t) (fun i => vR i t)).1 hth)

end Delete

/-! ### Splitting the two seeds -/

section Split

variable {a : ℝ} {mL mR : ℕ} {rL rR : ℝ} {ρL : Fin mL → ℝ} {ρR : Fin mR → ℝ}
  {w : ℝ≥0 → ℝ} {vL vR : Fin 1 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞}

/-- The threshold condition of copies of one mark on each side, with total weights `r_∓`. -/
theorem thresholdCondition_split (hL : ∑ i, ρL i = rL) (hR : ∑ i, ρR i = rR) (w₀ uL uR : ℝ) :
    ForceWord.ThresholdCondition ρL ρR w₀ (fun _ => uL) (fun _ => uR) ↔
      ForceWord.ThresholdCondition (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) w₀ (fun _ => uL) (fun _ => uR) := by
  classical
  unfold ForceWord.ThresholdCondition
  have eL : (∑ i ∈ Finset.univ.filter (fun _ : Fin mL => uL = w₀), ρL i) =
      ∑ i ∈ Finset.univ.filter (fun _ : Fin 1 => uL = w₀), rL := by
    by_cases hu : uL = w₀ <;> simp [hu, hL]
  have eR : (∑ i ∈ Finset.univ.filter (fun _ : Fin mR => uR = w₀), ρR i) =
      ∑ i ∈ Finset.univ.filter (fun _ : Fin 1 => uR = w₀), rR := by
    by_cases hu : uR = w₀ <;> simp [hu, hR]
  rw [eL, eR]

theorem sum_integral_split {n : ℕ} (ρ : Fin n → ℝ) (r : ℝ) (hρ : ∑ i, ρ i = r) (g : ℝ → ℝ) (t : ℝ) :
    ∑ _i : Fin n, ∫ s in (0 : ℝ)..t, ρ _i / g s = ∑ _i : Fin 1, ∫ s in (0 : ℝ)..t, r / g s := by
  simp_rw [div_eq_mul_inv, intervalIntegral.integral_const_mul]
  rw [← Finset.sum_mul, hρ, Fin.sum_univ_one]

/-- **Splitting the seeds of a two-seed local path.** -/
theorem _root_.InteractingSLE.Sec2.IsSLEPathUpTo.splitSeed
    (h : IsSLEPathUpTo a (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) (fun _ => rL) (fun _ => rR) w vL vR b τ)
    (hL : ∑ i, ρL i = rL) (hR : ∑ i, ρR i = rR) :
    IsSLEPathUpTo a (fun _ : Fin mL => 0) (fun _ : Fin mR => 0) ρL ρR w (fun _ => vL 0) (fun _ => vR 0) b τ where
  w_zero := h.w_zero
  vL_zero _ := h.vL_zero 0
  vR_zero _ := h.vR_zero 0
  continuousOn_w := h.continuousOn_w
  continuousOn_vL _ := h.continuousOn_vL 0
  continuousOn_vR _ := h.continuousOn_vR 0
  antitone_vL _ _ _ _ := le_rfl
  vL_le_w ht _ := h.vL_le_w ht 0
  w_le_vR ht _ := h.w_le_vR ht 0
  monotone_vR _ _ _ _ := le_rfl
  integrable_gapL ht _ := h.integrable_gapL ht 0
  integrable_gapR ht _ := h.integrable_gapR ht 0
  w_eq {t} ht := by
    rw [h.w_eq ht, sum_integral_split ρL rL hL _ t, sum_integral_split ρR rR hR _ t]
    simp only [Fin.sum_univ_one]
  vL_eq ht _ := h.vL_eq ht 0
  vR_eq ht _ := h.vR_eq ht 0
  volume_collisionL _ := h.volume_collisionL 0
  volume_collisionR _ := h.volume_collisionR 0
  not_threshold {t} ht hth := h.not_threshold ht <| by
    have e1 : (fun i : Fin 1 => vL i t) = fun _ => vL 0 t := funext fun i => by rw [Subsingleton.elim i 0]
    have e2 : (fun i : Fin 1 => vR i t) = fun _ => vR 0 t := funext fun i => by rw [Subsingleton.elim i 0]
    rw [e1, e2]
    exact (thresholdCondition_split hL hR (w t) (vL 0 t) (vR 0 t)).1 hth

end Split

/-! ### Infinite lifetimes -/

section Top

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **With infinite lifetime the maximality clauses are vacuous**: a local path before `⊤` is an integrated path with
lifetime `⊤`. -/
theorem isIntegratedSLEPath_top_of_isSLEPathUpTo {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b ⊤) :
    IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ⊤ :=
  ⟨h.w_zero, h.vL_zero, h.vR_zero, h.continuousOn_w, h.continuousOn_vL, h.continuousOn_vR,
    fun _ ht => h.antitone_vL ht, fun _ ht => h.vL_le_w ht, fun _ ht => h.w_le_vR ht,
    fun _ ht => h.monotone_vR ht, fun _ ht => h.integrable_gapL ht, fun _ ht => h.integrable_gapR ht,
    fun _ ht => h.w_eq ht, fun _ ht => h.vL_eq ht, fun _ ht => h.vR_eq ht, h.volume_collisionL,
    h.volume_collisionR, fun _ ht => h.not_threshold ht, fun h0 => absurd h0 ENNReal.top_ne_zero,
    fun _ _ hT => absurd hT.symm ENNReal.top_ne_coe⟩

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The two-seed reference as an evolution of a seed-only word**: every seed mark of a side follows the merged
seed mark of that side; the weights of each side sum to the two-seed weight. -/
theorem IsIntegratedSLEEvolution.splitSeed {mL mR : ℕ} {rL rR : ℝ} {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ}
    {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ}
    (hE : IsIntegratedSLEEvolution a (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) (fun _ => rL) (fun _ => rR) P 𝓕
      W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hL : ∑ i, ρL' i = rL) (hR : ∑ i, ρR' i = rR) :
    IsIntegratedSLEEvolution a (fun _ : Fin mL => 0) (fun _ : Fin mR => 0) ρL' ρR' P 𝓕 W (fun _ => VL 0)
      (fun _ => VR 0) B ζ := by
  refine ⟨hE.1, hE.2.1, fun _ => hE.2.2.1 0, fun _ => hE.2.2.2.1 0, ?_⟩
  filter_upwards [hE.2.2.2.2, hζ] with ω hp hω
  rw [hω] at hp ⊢
  exact isIntegratedSLEPath_top_of_isSLEPathUpTo ((hp.isSLEPathUpTo le_rfl).splitSeed hL hR)

/-- **Two evolutions of an ordered word with infinite lifetimes have the same code law** (Theorem 2.2's uniqueness
in law). -/
theorem map_stCode_eq_of_top (ha : 0 < a) (hF : IsOrderedForceWord xL xR)
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ} {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ}
    {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞} (h₁ : IsIntegratedSLEEvolution a xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hζ₁ : ∀ᵐ ω ∂P₁, ζ₁ ω = ⊤)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ} {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ}
    {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞} (h₂ : IsIntegratedSLEEvolution a xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (hζ₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤) :
    P₁.map (stCode ζ₁ W₁ VL₁ VR₁ B₁) = P₂.map (stCode ζ₂ W₂ VL₂ VR₂ B₂) := by
  have hm₁ := measurable_stCode_of_evolution h₁
  have hm₂ := measurable_stCode_of_evolution h₂
  refine ext_of_generate_finite _ generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => MeasurableSpace.isPiSystem_measurableSet)
      fun _ => (MeasurableSet.univ : MeasurableSet (univ : Set (StateSp nL nR))))
    ?_ (by rw [measure_univ, measure_univ])
  rintro S ⟨s, t, ht, rfl⟩
  simp only [mem_univ_pi, mem_ofPred_eq] at ht
  have hS : MeasurableSet ((s : Set (ℕ × ℕ)).pi t) :=
    MeasurableSet.pi (Finset.countable_toSet _) fun p _ => ht p
  rw [Measure.map_apply hm₁ hS, Measure.map_apply hm₂ hS, measure_stCode_preimage_pi hζ₁,
    measure_stCode_preimage_pi hζ₂]
  exact IsIntegratedSLEEvolution.measure_killedState_eq_assembled ha hF h₁ h₂ (hA := fun j => ht _)

/-- **Infinite lifetime transfers along the killed laws**: an evolution of a word with an infinite-lifetime twin has
infinite lifetime. -/
theorem ae_lifetime_eq_top_of_twin (ha : 0 < a) (hF : IsOrderedForceWord xL xR)
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ} {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ}
    {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞} (h₁ : IsIntegratedSLEEvolution a xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hζ₁ : ∀ᵐ ω ∂P₁, ζ₁ ω = ⊤)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ} {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ}
    {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞} (h₂ : IsIntegratedSLEEvolution a xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) :
    ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ := by
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂P₂, ((n : ℝ≥0) : ℝ≥0∞) < ζ₂ ω := by
    intro n
    have e := IsIntegratedSLEEvolution.measure_killedState_eq_assembled ha hF h₁ h₂ (n := 1) (ts := fun _ => (n : ℝ≥0))
      (A := fun _ => univ) (hA := fun _ => MeasurableSet.univ)
    simp only [mem_univ, and_true, forall_const] at e
    have h1 : P₁ {ω | ((n : ℝ≥0) : ℝ≥0∞) < ζ₁ ω} = 1 := by
      rw [← prob_compl_eq_zero_iff (measurableSet_lt measurable_const (Sec2.Assembly.measurable_lifetime h₁.2.1))]
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hζ₁)
      simp only [mem_compl_iff, mem_ofPred_eq] at hω ⊢
      intro h
      rw [h] at hω
      exact hω ENNReal.coe_lt_top
    rw [h1] at e
    have h2 : P₂ {ω | ((n : ℝ≥0) : ℝ≥0∞) < ζ₂ ω}ᶜ = 0 :=
      (prob_compl_eq_zero_iff (measurableSet_lt measurable_const (Sec2.Assembly.measurable_lifetime h₂.2.1))).2 e.symm
    exact ae_iff.2 h2
  filter_upwards [ae_all_iff.2 hn] with ω hω
  refine ENNReal.eq_top_of_forall_nnreal_le fun x => ?_
  obtain ⟨n, hn⟩ := exists_nat_ge x
  exact (ENNReal.coe_le_coe.2 hn).trans (hω n).le

end Top

end LocalExt

end InteractingSLE
