/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxRead
import InteractingSLE.Spec.Supplement.GW2OmxTip
import InteractingSLE.Spec.Supplement.GW2GmClock
import InteractingSLE.Spec.Supplement.GB6Disjoint

/-!
# GW2's open lines: the physical no-contact event, per sample

Packet PROVE-GW2-STAGEMEAN, R120 round (localization). At a sample where the original counterflow and the explored
path have generating traces `η`, `ηe`:

* `mem_gapEvent_congr`: a gap event reads its two families only on its two boxes;
* **`mem_noContact_iff`**: `noContact` is the separation `η t · ηe u + 1 ≠ 0` on `[0, s] × [0, T]`;
* **`mem_noContact_iff_lt_firstTipTime`**: it is `s < firstTipTime` of the counterflow on the explored trace image
  (the launch datum's range condition, with the retained prefix = the explored trace image);
* **`disjoint_closure_of_mem_noContact`**: on it the closures of the explored hull at `T` and of the retained hull
  are disjoint (GB6's `disjoint_closure_fwdHull_of_lt_firstContactTime`), the hypothesis `hd` of
  `launchUnion_eq_of_launch`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Omx

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rd Supp8.GB6 Exist.StagedLaw

/-- **A gap event reads its families only on its boxes.** -/
theorem mem_gapEvent_congr {Ω : Type*} {γ γ' α α' : Ω → ℝ≥0 → ℂ} {T s : ℝ≥0} {ω : Ω}
    (hγ : ∀ q ≤ T, γ ω q = γ' ω q) (hα : ∀ q ≤ s, α ω q = α' ω q) :
    ω ∈ gapEvent γ α T s ↔ ω ∈ gapEvent γ' α' T s := by
  unfold gapEvent gapAt
  simp only [mem_iUnion, mem_iInter, mem_ofPred_eq]
  refine exists_congr fun n => forall_congr' fun q₁ => forall_congr' fun q₂ => imp_congr_right fun hq => ?_
  have h1 : (q₁ : ℝ).toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hq.2.1
  have h2 : (q₂ : ℝ).toNNReal ≤ s := Real.toNNReal_le_iff_le_coe.2 hq.2.2.2
  rw [hγ _ h1, hα _ h2]

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **The physical no-contact event, per sample**: separation of the two traces on the boxes. -/
theorem mem_noContact_iff {ω : Ω} {η ηe : ℝ≥0 → ℂ} (hη : IsGeneratingTrace (fun u => c.W u ω) ⊤ η)
    (hc : Continuous fun u => c.W u ω) (h0 : c.W 0 ω = 0) (hs : (c.s : ℝ≥0∞) < c.ζ ω)
    (hηe : IsGeneratingTrace (fun u => schedW c r l a u ω) ⊤ ηe) (hce : Continuous fun u => schedW c r l a u ω)
    (h0e : schedW c r l a 0 ω = 0) :
    ω ∈ noContact c r l a ↔ ∀ t ∈ Icc 0 c.s, ∀ u ∈ Icc 0 (historyTime c r l), η t * ηe u + 1 ≠ 0 := by
  unfold noContact
  rw [mem_gapEvent_congr (γ' := fun _ => η) (α' := fun _ => ηe) (fun q hq => cfRead_eq_of_trace c hη hc h0 hs hq)
    (fun q _ => explRead_eq_of_trace c r l a hηe hce h0e q)]
  exact mem_gapEvent_iff (γ := fun _ => η) (α := fun _ => ηe)
    (continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top))
    (continuousOn_univ.1 (hηe.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top))

/-- **No contact is the launch datum's range condition**: the retained time `s` is before the counterflow's first tip
in the explored trace image. -/
theorem mem_noContact_iff_lt_firstTipTime {ω : Ω} {η ηe : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun u => c.W u ω) ⊤ η) (hc : Continuous fun u => c.W u ω) (h0 : c.W 0 ω = 0)
    (hs : (c.s : ℝ≥0∞) < c.ζ ω) (hηe : IsGeneratingTrace (fun u => schedW c r l a u ω) ⊤ ηe)
    (hce : Continuous fun u => schedW c r l a u ω) (h0e : schedW c r l a 0 ω = 0) :
    ω ∈ noContact c r l a ↔ (c.s : ℝ≥0∞) <
      firstTipTime infinitySourceChart (fun u => c.W u ω) (ηe '' Icc 0 (historyTime c r l)) := by
  have hηec : Continuous ηe := continuousOn_univ.1 (hηe.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  rw [mem_noContact_iff c r l a hη hc h0 hs hηe hce h0e]
  constructor
  · intro h
    refine lt_firstTipTime_of_noContact hη hc h0 (isCompact_Icc.image hηec) fun t ht hγt hmem => ?_
    obtain ⟨u, hu, hue⟩ := hmem
    refine h t ⟨zero_le, ht⟩ u hu ?_
    rw [hue, mul_neg, mul_inv_cancel₀ hγt]
    ring
  · intro h t ht u hu hzero
    have hγt : η t ≠ 0 := by
      intro h0'
      rw [h0', zero_mul, zero_add] at hzero
      exact one_ne_zero hzero
    refine noContact_of_lt_firstTipTime hη hc h0 h ht.2 hγt ⟨u, hu, ?_⟩
    have e : η t * ηe u = -1 := eq_neg_of_add_eq_zero_left hzero
    calc ηe u = (η t)⁻¹ * (η t * ηe u) := by field_simp
      _ = -(η t)⁻¹ := by rw [e]; ring

/-- **No contact separates the closures of the explored hull and of the retained hull.** -/
theorem disjoint_closure_of_mem_noContact {ω : Ω} {η ηe : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun u => c.W u ω) ⊤ η) (hc : Continuous fun u => c.W u ω) (h0 : c.W 0 ω = 0)
    (hs : (c.s : ℝ≥0∞) < c.ζ ω) (hηe : IsGeneratingTrace (fun u => schedW c r l a u ω) ⊤ ηe)
    (hce : Continuous fun u => schedW c r l a u ω) (h0e : schedW c r l a 0 ω = 0)
    (hω : ω ∈ noContact c r l a) :
    Disjoint (closure (fwdHull (fun u : ℝ => schedW c r l a u.toNNReal ω) (historyTime c r l : ℝ)))
      (closure (Supp8.Q3Rel.invHull (fun u : ℝ => c.W u.toNNReal ω) (c.s : ℝ))) := by
  have hηc : Continuous η := continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hηec : Continuous ηe := continuousOn_univ.1 (hηe.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have h := (mem_noContact_iff c r l a hη hc h0 hs hηe hce h0e).1 hω
  have hTc := (Gm.lt_firstContactTime_iff_noncontact hηc hηec c.s (historyTime c r l)).2 h
  exact disjoint_closure_fwdHull_of_lt_firstContactTime hηe hce.continuousOn h0e hη hc.continuousOn h0
    ENNReal.coe_lt_top ENNReal.coe_lt_top hTc

end InteractingSLE.Theorem14.GW2Omx
