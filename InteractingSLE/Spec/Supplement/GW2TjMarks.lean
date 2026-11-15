/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TjPast

/-!
# (T2): raw kernel marks agreeing with the stage filtration up to null sets

Packet PROVE-GW2-RELDET, ruling R117(b), item (T2) (`GW2Olm.KernelMarksAgree`). The instance's marks are the stage
filtration `ℋ t = stgFilt t` (counterflow record, explored path up to `T + t`, the encoded history record, null sets).
The raw kernel marks drop the null sets and read the explored path at rational times only:

  `kerMarks t = σ(counterflow record) ∨ σ(explored path at the rational times, frozen after T + t) ∨ c.sigma r l`.

* `kerMarks_le`, **`countablyGenerated_kerMarks`**, **`pastG_le_kerMarks`** (by `pastG_le_sigma`);
* `measurable_schedW_kerMarks`: the explored path up to `T + t` is read off the rational times (it is continuous at
  every sample);
* `kerMarks_le_stgFilt`, `stgFilt_le_kerMarks_sup`;
* **`kernelMarksAgree_stgFilt`**: `GW2Olm.KernelMarksAgree c r l a kerMarks (stgFilt …)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Sde
  Supp8.RelSafe Supp8.GB6

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- The explored path at the rational times, frozen after `q`. -/
def schedRatPath (q : ℝ≥0) (ω : Ω) : ℚ → ℝ := fun s => schedW c r l a (min (Real.toNNReal s) q) ω

theorem measurable_schedRatPath (q : ℝ≥0) : Measurable (schedRatPath c r l a q) :=
  measurable_pi_iff.2 fun _ => measurable_schedW c r l a _

/-- **The raw kernel marks at stage time `t`.** -/
@[instance_reducible]
def kerMarks (t : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (gb6Rec c.s c.W c.ζ) inferInstance ⊔
    MeasurableSpace.comap (schedRatPath c r l a (historyTime c r l + t)) inferInstance ⊔ c.sigma r l

theorem kerMarks_def (t : ℝ≥0) : kerMarks c r l a t =
    MeasurableSpace.comap (gb6Rec c.s c.W c.ζ) inferInstance ⊔
      MeasurableSpace.comap (schedRatPath c r l a (historyTime c r l + t)) inferInstance ⊔ c.sigma r l := rfl

omit mΩ in
theorem sigma_le {Ω : Type u} [mΩ : MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) : c.sigma r l ≤ mΩ :=
  stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _

theorem kerMarks_le (t : ℝ≥0) : kerMarks c r l a t ≤ mΩ := by
  rw [kerMarks_def]
  exact sup_le (sup_le (measurable_gb6Rec_src c).comap_le (measurable_schedRatPath c r l a _).comap_le)
    (sigma_le c r l)

theorem countablyGenerated_kerMarks (t : ℝ≥0) : @MeasurableSpace.CountablyGenerated Ω (kerMarks c r l a t) := by
  have h1 : @MeasurableSpace.CountablyGenerated Ω
      (MeasurableSpace.comap (gb6Rec c.s c.W c.ζ) inferInstance) := MeasurableSpace.CountablyGenerated.comap _
  have h2 : @MeasurableSpace.CountablyGenerated Ω
      (MeasurableSpace.comap (schedRatPath c r l a (historyTime c r l + t)) inferInstance) :=
    MeasurableSpace.CountablyGenerated.comap _
  have h3 : @MeasurableSpace.CountablyGenerated Ω (c.sigma r l) := by
    rw [← comap_stageEncRec_sigma c r l]
    exact MeasurableSpace.CountablyGenerated.comap _
  rw [kerMarks_def]
  exact MeasurableSpace.CountablyGenerated.sup (MeasurableSpace.CountablyGenerated.sup h1 h2) h3

theorem pastG_le_kerMarks (t : ℝ≥0) : GW2Olm.pastG c r l a ≤ kerMarks c r l a t := by
  rw [kerMarks_def]
  exact (pastG_le_sigma c r l a).trans le_sup_right

/-- **The explored path up to `T + t` is read off the rational times.** -/
theorem measurable_schedW_kerMarks (t : ℝ≥0) {s : ℝ≥0} (hs : s ≤ historyTime c r l + t) :
    Measurable[kerMarks c r l a t] (schedW c r l a s) := by
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℚ, Tendsto (fun n => (u n : ℝ)) atTop (𝓝 (s : ℝ)) := by
    have hmem : (s : ℝ) ∈ closure (range ((↑) : ℚ → ℝ)) := by
      rw [Rat.denseRange_cast.closure_eq]
      exact mem_univ _
    obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 hmem
    choose w hw using hv
    refine ⟨w, ?_⟩
    have e : (fun n => (w n : ℝ)) = v := funext hw
    rw [e]
    exact hlim
  have hpath : Measurable[kerMarks c r l a t] (schedRatPath c r l a (historyTime c r l + t)) := by
    rw [kerMarks_def]
    exact Measurable.of_comap_le (le_sup_right.trans le_sup_left)
  refine @measurable_of_tendsto_metrizable Ω ℝ (kerMarks c r l a t) _ _ _ _
    (fun n ω => schedRatPath c r l a (historyTime c r l + t) ω (u n)) (schedW c r l a s)
    (fun n => (measurable_pi_apply (u n)).comp hpath) (tendsto_pi_nhds.2 fun ω => ?_)
  have h1 : Tendsto (fun n => min (Real.toNNReal (u n : ℝ)) (historyTime c r l + t)) atTop (𝓝 s) := by
    have h2 : Tendsto (fun n => Real.toNNReal (u n : ℝ)) atTop (𝓝 (Real.toNNReal s)) :=
      (continuous_real_toNNReal.tendsto _).comp hu
    rw [Real.toNNReal_coe] at h2
    have h3 := h2.min (tendsto_const_nhds (x := historyTime c r l + t))
    rwa [min_eq_left hs] at h3
  exact ((continuous_schedW c r l a ω).tendsto s).comp h1

/-- The stage filtration at `t`, written out. -/
abbrev stgF (t : ℝ≥0) : MeasurableSpace Ω :=
  stgFilt (physFilt (measurable_gb6Rec_src c) (measurable_schedW c r l a) c.P)
    (historyTime c r l) (measurable_stageEncRec c r l) t

theorem physSigma_le_stgF (t : ℝ≥0) :
    physSigma (gb6Rec c.s c.W c.ζ) (schedW c r l a) (historyTime c r l + t) ≤ stgF c r l a t :=
  (physSigma_le_physFilt (measurable_gb6Rec_src c) (measurable_schedW c r l a) c.P _).trans le_sup_left

theorem nullSets_le_stgF (t : ℝ≥0) : Ito.nullSets c.P ≤ stgF c r l a t :=
  (nullSets_le_physFilt (measurable_gb6Rec_src c) (measurable_schedW c r l a) c.P _).trans le_sup_left

theorem sigma_le_stgF (t : ℝ≥0) : c.sigma r l ≤ stgF c r l a t := by
  rw [← comap_stageEncRec_sigma c r l]
  exact le_sup_right

theorem measurable_schedW_physSigma {q x : ℝ≥0} (hx : x ≤ q) :
    Measurable[physSigma (gb6Rec c.s c.W c.ζ) (schedW c r l a) q] (schedW c r l a x) := by
  refine Measurable.of_comap_le ?_
  have h : MeasurableSpace.comap (schedW c r l a x) inferInstance ≤
      ⨆ (y : ℝ≥0) (_ : y ≤ q), MeasurableSpace.comap (schedW c r l a y) inferInstance :=
    le_iSup₂ (f := fun (y : ℝ≥0) (_ : y ≤ q) => MeasurableSpace.comap (schedW c r l a y) inferInstance) x hx
  exact h.trans le_sup_right

theorem kerMarks_le_stgFilt (t : ℝ≥0) : kerMarks c r l a t ≤ stgF c r l a t := by
  have hA : MeasurableSpace.comap (gb6Rec c.s c.W c.ζ) inferInstance ≤ stgF c r l a t :=
    (measurable_rec_physSigma _ _ _).comap_le.trans (physSigma_le_stgF c r l a t)
  have hB : MeasurableSpace.comap (schedRatPath c r l a (historyTime c r l + t)) inferInstance ≤
      stgF c r l a t := by
    refine (@measurable_pi_iff _ _ _ (physSigma (gb6Rec c.s c.W c.ζ) (schedW c r l a) (historyTime c r l + t))
      _ _ |>.2 fun s => ?_).comap_le.trans (physSigma_le_stgF c r l a t)
    exact measurable_schedW_physSigma c r l a (min_le_right _ _)
  rw [kerMarks_def]
  exact sup_le (sup_le hA hB) (sigma_le_stgF c r l a t)

theorem stgFilt_le_kerMarks_sup (t : ℝ≥0) : stgF c r l a t ≤ kerMarks c r l a t ⊔ Ito.nullSets c.P := by
  have hK : kerMarks c r l a t ≤ kerMarks c r l a t ⊔ Ito.nullSets c.P := le_sup_left
  have hA : MeasurableSpace.comap (gb6Rec c.s c.W c.ζ) inferInstance ≤ kerMarks c r l a t := by
    rw [kerMarks_def]
    exact le_sup_left.trans le_sup_left
  have hS : c.sigma r l ≤ kerMarks c r l a t := by
    rw [kerMarks_def]
    exact le_sup_right
  have hP : physSigma (gb6Rec c.s c.W c.ζ) (schedW c r l a) (historyTime c r l + t) ≤ kerMarks c r l a t :=
    sup_le hA (iSup₂_le fun s hs => (measurable_schedW_kerMarks c r l a t hs).comap_le)
  have hE : MeasurableSpace.comap (stageEncRec c r l) inferInstance ≤ kerMarks c r l a t := by
    rw [comap_stageEncRec_sigma c r l]
    exact hS
  change physSigma (gb6Rec c.s c.W c.ζ) (schedW c r l a) (historyTime c r l + t) ⊔ Ito.nullSets c.P ⊔
    MeasurableSpace.comap (stageEncRec c r l) inferInstance ≤ _
  exact sup_le (sup_le (hP.trans hK) le_sup_right) (hE.trans hK)

/-- **(T2) for the stage filtration.** -/
theorem kernelMarksAgree_stgFilt : GW2Olm.KernelMarksAgree c r l a (kerMarks c r l a) (stgF c r l a) := by
  intro t
  have h1 : kerMarks c r l a t ⊔ Ito.nullSets c.P ≤ stgF c r l a t ⊔ Ito.nullSets c.P :=
    sup_le ((kerMarks_le_stgFilt c r l a t).trans le_sup_left) le_sup_right
  have h2 : stgF c r l a t ⊔ Ito.nullSets c.P ≤ kerMarks c r l a t ⊔ Ito.nullSets c.P :=
    sup_le (stgFilt_le_kerMarks_sup c r l a t) le_sup_right
  exact ⟨kerMarks_le c r l a t, countablyGenerated_kerMarks c r l a t, pastG_le_kerMarks c r l a t,
    le_antisymm h1 h2⟩

end InteractingSLE.Theorem14.GW2Rd
