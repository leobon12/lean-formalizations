/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtBHist
import InteractingSLE.Spec.Sec7.LocalExtASetup
import InteractingSLE.Spec.Coupling.ResampleProjBridge
import InteractingSLE.Spec.Sec2.Assembly2Entr

/-!
# One stopped reference graph for all two-seed couplings (Aux. lemma 55, last paragraphs)

Packet PROVE-LOCEXT-B (step 7 of the split in `planning/handoffs/PROVE-AUX52-55.md`). Specification p. 250: "By the
assumed two-seed input the full reference history is determined by `h₀`. Its determining function is the same for
every such reference coupling. Indeed, if two couplings gave different functions, mixing them by an independent fair
coin would still satisfy the original hull specification and optional locality, but its conditional path law given the
field would not be a point mass. This would contradict the same two-seed input. Thus one reference version may be
fixed once and for all."

This file proves the **stopped** form used by Aux. 55: for the two-seed word with admissible weights `r_L, r_R > −2`
and a radius `r`, there is **one** measurable map `G` of the field such that every two-seed coupling has its history
stopped at the local stop `S = (r²/64) ∧ inf{t : |W_t| > r/4}` (`LocalExt.localStop`, capped at the lifetime:
`capStop`) equal to `G(h)` almost surely (`twoSeed_exists_stoppedGraph`).

* `capStop r G ζ W = min (localStop r G ζ W) ζ`: a stopping time of the frozen driving filtration
  (`isStoppingTime_capStop`), equal to the local stop on the good event (`capStop_eq_localStop`);
* `mixGood`, `localStop_mix_inl`, `stoppedHistory_capStop_mix_inl` (and `inr`): the local stop of a mixture of two
  couplings is the local stop of each piece;
* **`twoSeed_exists_stoppedGraph`**: the common stopped graph (the two-seed input, `LocalExt`'s determination of
  stopped histories `IsOptionalHullCoupling.isAEDeterminedBy_stoppedHistory`, and the mixture
  `Determination.IsOptionalHullCoupling.mix` with a fixed reference coupling from Theorem 1.1 and Theorem 2.2's
  existence, `Coupling.exists_isOptionalHullCoupling_of_thm22`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Determination

/-! ### The local stop capped at the lifetime -/

section Cap

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {G : Set Ω}

/-- The local stop of Aux. 55 capped at the lifetime (equal to the local stop on the good event, `localStop_lt`). -/
def capStop (r : ℝ) (G : Set Ω) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  min (localStop r G ζ W ω) (ζ ω : WithTop ℝ≥0)

theorem capStop_le (r : ℝ) (ω : Ω) : capStop r G ζ W ω ≤ (ζ ω : WithTop ℝ≥0) := min_le_right _ _

/-- **The capped local stop is a stopping time of the frozen driving filtration.** -/
theorem isStoppingTime_capStop (hX : IsMeasurableKilledDriving W VL VR ζ) (hGm : MeasurableSet G)
    (hG0 : P Gᶜ = 0) (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (r : ℝ) :
    IsStoppingTime (drivingFiltration P hX) (capStop r G ζ W) := by
  have hle : killedDrivingFiltration hX ≤ drivingFiltration P hX := Ito.le_usualAugmentation _ P
  exact (isStoppingTime_localStop_drivingFiltration hX hGm hG0 hG r).min
    (Ito.isStoppingTime_lifetime (Ito.adaptedBefore_mono hle (Coupling.adaptedBefore_killedDriving_W hX)))

/-- On the good event the capped local stop is the local stop. -/
theorem capStop_eq_localStop (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
    (hF : IsOrderedForceWord xL xR) {r : ℝ} (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {ω : Ω} (hω : ω ∈ G) :
    capStop r G ζ W ω = localStop r G ζ W ω :=
  min_eq_left (localStop_lt hG hF hr hseed hω).le

end Cap

/-! ### The local stop of a mixture -/

section Mix

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂} {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
  {W₁ : ℝ≥0 → Ω₁ → ℝ} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
  {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
  {ζ₁ : Ω₁ → ℝ≥0∞} {ζ₂ : Ω₂ → ℝ≥0∞} {G₁ : Set Ω₁} {G₂ : Set Ω₂}

/-- The good event of a mixture. -/
def mixGood (G₁ : Set Ω₁) (G₂ : Set Ω₂) : Set (Ω₁ ⊕ Ω₂) := Sum.inl '' G₁ ∪ Sum.inr '' G₂

theorem inl_mem_mixGood {ω : Ω₁} : Sum.inl ω ∈ mixGood G₁ G₂ ↔ ω ∈ G₁ := by simp [mixGood]

theorem inr_mem_mixGood {ω : Ω₂} : Sum.inr ω ∈ mixGood G₁ G₂ ↔ ω ∈ G₂ := by simp [mixGood]

theorem measurableSet_mixGood (h₁ : MeasurableSet G₁) (h₂ : MeasurableSet G₂) :
    MeasurableSet (mixGood G₁ G₂) :=
  h₁.inl_image.union h₂.inr_image

theorem mixMeasure_compl_mixGood (h₁ : P₁ G₁ᶜ = 0) (h₂ : P₂ G₂ᶜ = 0) :
    mixMeasure P₁ P₂ (mixGood G₁ G₂)ᶜ = 0 := by
  rw [mixMeasure_eq_zero_iff]
  have e₁ : Sum.inl ⁻¹' (mixGood G₁ G₂)ᶜ = G₁ᶜ := by ext; simp [mixGood]
  have e₂ : Sum.inr ⁻¹' (mixGood G₁ G₂)ᶜ = G₂ᶜ := by ext; simp [mixGood]
  rw [e₁, e₂]
  exact ⟨h₁, h₂⟩

theorem isGoodPath_mix (hG₁ : ∀ ω ∈ G₁, IsGoodPath κ xL xR ρL ρR W₁ VL₁ VR₁ B₁ ζ₁ ω)
    (hG₂ : ∀ ω ∈ G₂, IsGoodPath κ xL xR ρL ρR W₂ VL₂ VR₂ B₂ ζ₂ ω) :
    ∀ x ∈ mixGood G₁ G₂, IsGoodPath κ xL xR ρL ρR (mixProc W₁ W₂) (fun i => mixProc (VL₁ i) (VL₂ i))
      (fun i => mixProc (VR₁ i) (VR₂ i)) (mixProc B₁ B₂) (Sum.elim ζ₁ ζ₂) x := by
  rintro (ω | ω) hx
  · exact hG₁ ω (inl_mem_mixGood.1 hx)
  · exact hG₂ ω (inr_mem_mixGood.1 hx)

theorem capStop_mix_inl (r : ℝ) (ω : Ω₁) :
    capStop r (mixGood G₁ G₂) (Sum.elim ζ₁ ζ₂) (mixProc W₁ W₂) (Sum.inl ω) = capStop r G₁ ζ₁ W₁ ω := by
  unfold capStop localStop
  by_cases hω : ω ∈ G₁
  · rw [ite_eq_left (inl_mem_mixGood.2 hω), ite_eq_left hω]; rfl
  · rw [ite_eq_right (mt inl_mem_mixGood.1 hω), ite_eq_right hω]; rfl

theorem capStop_mix_inr (r : ℝ) (ω : Ω₂) :
    capStop r (mixGood G₁ G₂) (Sum.elim ζ₁ ζ₂) (mixProc W₁ W₂) (Sum.inr ω) = capStop r G₂ ζ₂ W₂ ω := by
  unfold capStop localStop
  by_cases hω : ω ∈ G₂
  · rw [ite_eq_left (inr_mem_mixGood.2 hω), ite_eq_left hω]; rfl
  · rw [ite_eq_right (mt inr_mem_mixGood.1 hω), ite_eq_right hω]; rfl

theorem stoppedHistory_capStop_mix_inl (r : ℝ) (ω : Ω₁) :
    stoppedHistory (completedState (mixProc W₁ W₂) (fun i => mixProc (VL₁ i) (VL₂ i))
        (fun i => mixProc (VR₁ i) (VR₂ i)) (Sum.elim ζ₁ ζ₂))
      (capStop r (mixGood G₁ G₂) (Sum.elim ζ₁ ζ₂) (mixProc W₁ W₂)) (Sum.inl ω) =
      stoppedHistory (completedState W₁ VL₁ VR₁ ζ₁) (capStop r G₁ ζ₁ W₁) ω := by
  simp only [stoppedHistory, stopAt, capStop_mix_inl]
  rfl

theorem stoppedHistory_capStop_mix_inr (r : ℝ) (ω : Ω₂) :
    stoppedHistory (completedState (mixProc W₁ W₂) (fun i => mixProc (VL₁ i) (VL₂ i))
        (fun i => mixProc (VR₁ i) (VR₂ i)) (Sum.elim ζ₁ ζ₂))
      (capStop r (mixGood G₁ G₂) (Sum.elim ζ₁ ζ₂) (mixProc W₁ W₂)) (Sum.inr ω) =
      stoppedHistory (completedState W₂ VL₂ VR₂ ζ₂) (capStop r G₂ ζ₂ W₂) ω := by
  simp only [stoppedHistory, stopAt, capStop_mix_inr]
  rfl

end Mix

/-! ### One stopped reference graph -/

/-- The two-seed word is ordered. -/
theorem isOrderedForceWord_twoSeed' : IsOrderedForceWord LP.twoSeedXL LP.twoSeedXR :=
  ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => le_rfl⟩

/-- The stopped histories of the two-seed state. -/
abbrev TwoSeedHist : Type := WithTop ℝ≥0 × (ℚ≥0 → ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ))

/-- Equality of two measurable maps into the two-seed histories is a measurable event. -/
theorem measurableSet_eq_twoSeedHist {α : Type*} [MeasurableSpace α] {f g : α → TwoSeedHist}
    (hf : Measurable f) (hg : Measurable g) : MeasurableSet {x | f x = g x} := by
  have e : {x | f x = g x} = {x | (f x).1 = (g x).1} ∩ {x | (f x).2 = (g x).2} := by
    ext x; simp only [mem_ofPred_eq, mem_inter_iff, Prod.ext_iff]
  rw [e]
  exact (measurableSet_eq_fun hf.fst hg.fst).inter (measurableSet_eq_fun hf.snd hg.snd)

/-- **One stopped reference graph for all two-seed couplings** (Aux. lemma 55, p. 250: "By the assumed two-seed input
the full reference history is determined by `h₀`. Its determining function is the same for every such reference
coupling … Thus one reference version may be fixed once and for all"). Under the two-seed input, for admissible seed
weights `r_L, r_R > −2` and every radius `r` there is one measurable `g` such that **every** two-seed coupling has its
history stopped at the capped local stop of radius `r` equal to `g(h)` almost surely, for every good event. -/
theorem twoSeed_exists_stoppedGraph {κ : ℝ} (hκ : 0 < κ) (h2 : LP.TwoSeedGraphInput.{u} κ) {rL rR : ℝ}
    (hL : -2 < rL) (hR : -2 < rR) (r : ℝ) :
    ∃ g : LQGMetric.DistOn upperHalfPlaneOpens → TwoSeedHist, Measurable g ∧
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
        (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h →
        ∀ G : Set Ω, MeasurableSet G → P Gᶜ = 0 →
          (∀ ω ∈ G, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) W VL VR B ζ ω) →
          stoppedHistory (completedState W VL VR ζ) (capStop r G ζ W) =ᵐ[P] fun ω => g (h ω) := by
  have hF2 := isOrderedForceWord_twoSeed'
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hC₀⟩ :=
    Coupling.exists_isOptionalHullCoupling_of_thm22.{u} hκ hF2
      (exists_isIntegratedSLEEvolution_assembled (ρL := fun _ => rL) (ρR := fun _ => rR) hκ hF2)
  obtain ⟨G₀, hG₀m, hG₀0, hG₀⟩ := exists_goodEvent hC₀.1 hκ
  obtain ⟨hX₀, -⟩ := hC₀.2.2.2
  obtain ⟨g, hg, hg₀⟩ := hC₀.isAEDeterminedBy_stoppedHistory hκ
    ((h2 rL rR hL hR).1 P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ hC₀) (isStoppingTime_capStop hX₀ hG₀m hG₀0 hG₀ r)
    (capStop_le r)
  refine ⟨g, hg, ?_⟩
  intro Ω mΩ P _ 𝓕 W VL VR B ζ h hC G hGm hG0 hG
  have hM := Determination.IsOptionalHullCoupling.mix hC₀ hC
  obtain ⟨hXM, -⟩ := hM.2.2.2
  obtain ⟨gM, hgM, hgMe⟩ := hM.isAEDeterminedBy_stoppedHistory hκ ((h2 rL rR hL hR).1 _ _ _ _ _ _ _ _ hM)
    (isStoppingTime_capStop hXM (measurableSet_mixGood hG₀m hGm) (mixMeasure_compl_mixGood hG₀0 hG0)
      (isGoodPath_mix hG₀ hG) r) (capStop_le r)
  obtain ⟨e₀, e⟩ := ae_mixMeasure_iff.1 hgMe
  have hagree₀ : ∀ᵐ ω ∂P₀, gM (h₀ ω) = g (h₀ ω) := by
    filter_upwards [e₀, hg₀] with ω h1 h1'
    rw [← h1', ← stoppedHistory_capStop_mix_inl (G₂ := G) (W₂ := W) (VL₂ := VL) (VR₂ := VR) (ζ₂ := ζ) r ω]
    exact h1.symm
  have hmeas : MeasurableSet {x | gM x = g x} := measurableSet_eq_twoSeedHist hgM hg
  have hagree : ∀ᵐ ω ∂P, gM (h ω) = g (h ω) := by
    have h1 : ∀ᵐ x ∂(P₀.map h₀), gM x = g x := (ae_map_iff hC₀.2.1.aemeasurable hmeas).2 hagree₀
    rw [map_field_eq hC₀ hC] at h1
    exact (ae_map_iff hC.2.1.aemeasurable hmeas).1 h1
  filter_upwards [e, hagree] with ω h1 h1'
  rw [← h1', ← stoppedHistory_capStop_mix_inr (G₁ := G₀) (W₁ := W₀) (VL₁ := VL₀) (VR₁ := VR₀) (ζ₁ := ζ₀) r ω]
  exact h1

end LocalExt

end InteractingSLE
