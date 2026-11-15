/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CrosscutA2

/-!
# A.2, part 3: countably many times exhaust the small curve

Packet PROVE-ZHAN-A2P3. Source: Astra, *Follow-up proofs and dependency audit*, §A.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L597–L598; R38, R53): "Countably many capped rational times
exhaust the small curve; continuity gives `J ⊂ S`."

Part 3 of A.2 (`A2SmallInHullG3Statement`, `A2SmallInHullEightStatement`, PROVE-ZHAN-GT4-A2X) is proved here from
its per-time form: for every deterministic time `q`, almost surely on `{q < ζ₁}`, the tip `η₁(q)` of the small curve
(translated by its start) lies in `S` (`TipInHullG3Statement`, `TipInHullEightStatement`). Deterministic times are
stopping times of every filtration, so the conditioning of L563–L564 ("condition on a small-curve prefix stopped at a
rational own time") is available at each of them.

## Main results

* `image_Ioo_subset_of_forall_rat`: pathwise, if the translated tip lies in the closed set `S` at every rational time
  before `ζ₁`, then every small crosscut lies in `S` (continuity of the generating trace on `[0, ζ₁)`);
* **`smallInHullG3Statement_of_tip`**, **`smallInHullEightStatement_of_tip`**: part 3 of A.2 in both configurations
  from the per-time statements (countable intersection over `ℚ`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2X.P3

open QuantumZipper

/-! ### The per-time statements -/

/-- **A.2, part 3, at one time, (G3)** (L563–L596): for every (G3) dual pair and every deterministic time `q > 0`,
almost surely on `{q < ζ₁}`, every generating trace `η` of the small driver up to `ζ₁` has its translated tip
`η q + y` in the closure `S` of the large hulls over the strip life. -/
def TipInHullG3Statement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairG3 κ y x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ₁ ω → ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (W₁ · ω) (ζ₁ ω) η →
          η q + y ∈ lifeHullClosure (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)

/-- **A.2, part 3, at one time, (Eight)** (L563–L596). -/
def TipInHullEightStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairEight κ x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ₁ ω → ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (W₁ · ω) (ζ₁ ω) η →
          η q + x ∈ lifeHullClosure (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)

/-! ### The pathwise exhaustion -/

/-- `lifeHullClosure` is closed. -/
theorem isClosed_lifeHullClosure (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : IsClosed (lifeHullClosure w v ζ) :=
  isClosed_closure

/-- **Rational times exhaust the small curve** (L597–L598): if the translated tip `η q + x₁` lies in the closed set
`S` for every generating trace `η` and every rational time `0 < q < ζ₁`, then the open part of every small crosscut lies
in `S`. -/
theorem image_Ioo_subset_of_forall_rat {x₁ : ℝ} {w₁ : ℝ≥0 → ℝ} {ζ₁ : ℝ≥0∞} {S : Set ℂ} (hS : IsClosed S)
    (htip : ∀ r : ℚ, 0 < r → (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ₁ → ∀ η : ℝ≥0 → ℂ,
      IsGeneratingTrace w₁ ζ₁ η → η (r : ℝ).toNNReal + x₁ ∈ S)
    {γ : ℝ → ℂ} (hγ : IsSmallCrosscut x₁ w₁ ζ₁ γ) : γ '' Ioo 0 1 ⊆ S := by
  obtain ⟨-, -, -, η, hη, himg⟩ := hγ
  rw [himg]
  rintro _ ⟨_, ⟨t, ⟨ht0, htζ⟩, rfl⟩, rfl⟩
  -- the translated trace read on `ℝ`
  set g : ℝ → ℂ := fun r => η r.toNNReal + x₁ with hg
  set U : Set ℝ := {r | 0 < r ∧ ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ₁} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const continuous_id).inter
      (isOpen_lt (ENNReal.continuous_coe.comp continuous_real_toNNReal) continuous_const)
  have htU : (t : ℝ) ∈ U := ⟨by exact_mod_cast ht0, by simpa using htζ⟩
  have hηt : ContinuousAt η t := by
    have hV : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ₁} ∈ 𝓝 t :=
      (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds htζ
    exact (hη.2.1.mono fun s (hs : (s : ℝ≥0∞) < ζ₁) => hs.le).continuousAt
      (mem_of_superset hV fun s hs => hs)
  have hgt : ContinuousAt g t := by
    have h1 : ContinuousAt (fun r : ℝ => η r.toNNReal) t := by
      refine ContinuousAt.comp (f := Real.toNNReal) (g := η) ?_ continuous_real_toNNReal.continuousAt
      simpa using hηt
    exact h1.add continuousAt_const
  have hcl : (t : ℝ) ∈ closure (U ∩ range ((↑) : ℚ → ℝ)) :=
    (Rat.denseRange_cast (𝕜 := ℝ)).open_subset_closure_inter hUo htU
  have hmem := hgt.continuousWithinAt.mem_closure_image hcl
  have hsub : g '' (U ∩ range ((↑) : ℚ → ℝ)) ⊆ S := by
    rintro _ ⟨_, ⟨hrU, r, rfl⟩, rfl⟩
    exact htip r (by exact_mod_cast hrU.1) hrU.2 η hη
  have := closure_minimal hsub hS hmem
  simpa [hg] using this

/-! ### Part 3 from the per-time statements -/

/-- **A.2, part 3, (G3)** (`A2SmallInHullG3Statement`) from its per-time form. -/
theorem smallInHullG3Statement_of_tip {κ : ℝ} (h : TipInHullG3Statement.{u} κ) :
    A2SmallInHullG3Statement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair
  have hall : ∀ᵐ ω ∂P, ∀ r : ℚ, 0 < r → (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ₁ ω → ∀ η : ℝ≥0 → ℂ,
      IsGeneratingTrace (W₁ · ω) (ζ₁ ω) η →
        η (r : ℝ).toNNReal + y ∈ lifeHullClosure (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) :=
    ae_all_iff.2 fun r => by
      by_cases hr : 0 < r
      · filter_upwards [h hκ4 hκ8 y x hyx hx P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair ((r : ℝ).toNNReal)
          (by simpa using hr)] with ω hω _ using hω
      · exact Eventually.of_forall fun ω hr' => absurd hr' hr
  filter_upwards [hall] with ω hω γ hγ
  exact image_Ioo_subset_of_forall_rat (isClosed_lifeHullClosure _ _ _) hω hγ

/-- **A.2, part 3, (Eight)** (`A2SmallInHullEightStatement`) from its per-time form. -/
theorem smallInHullEightStatement_of_tip {κ : ℝ} (h : TipInHullEightStatement.{u} κ) :
    A2SmallInHullEightStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair
  have hall : ∀ᵐ ω ∂P, ∀ r : ℚ, 0 < r → (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ₁ ω → ∀ η : ℝ≥0 → ℂ,
      IsGeneratingTrace (W₁ · ω) (ζ₁ ω) η →
        η (r : ℝ).toNNReal + x ∈ lifeHullClosure (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) :=
    ae_all_iff.2 fun r => by
      by_cases hr : 0 < r
      · filter_upwards [h hκ8 x hx P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair ((r : ℝ).toNNReal)
          (by simpa using hr)]
          with ω hω _ using hω
      · exact Eventually.of_forall fun ω hr' => absurd hr' hr
  filter_upwards [hall] with ω hω γ hγ
  exact image_Ioo_subset_of_forall_rat (isClosed_lifeHullClosure _ _ _) hω hγ

end InteractingSLE.ZhanGT4.A2X.P3
