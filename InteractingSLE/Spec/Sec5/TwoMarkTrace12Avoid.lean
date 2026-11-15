/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkTrace12Null
import InteractingSLE.Spec.Sec5.TwoMarkFreeze11First
import InteractingSLE.Spec.Sec5.TwoMarkVersion6Paths
import InteractingSLE.Spec.Sec5.TwoMarkImage4Visit

/-!
# Two-mark interval exclusion through an announced local stop

Each possible visit supplies its own finite completed image trace. The
deterministic contact comparison for that prefix contradicts one trace-independent
null event of the full image evolution. The visit time need not be a stopping time.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Trace12

open Zhan.Retarget

/-- The low-weight two-mark trace avoids the intervening interval, including the announced stop. -/
theorem ae_avoid_interval {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ a b r : ℝ}
    {xL ρL : Fin 0 → ℝ} {W B : ℝ≥0 → Ω → ℝ}
    {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ}
    {e : Ω → ℝ≥0∞} {A : ℕ → Ω → ℝ≥0} {η : Ω → ℝ≥0 → ℂ}
    (hκ : 0 < κ) (hκ4 : κ < 4) (ha : 0 < a) (hab : a < b) (hr : r ≤ κ / 2 - 4)
    (hE : Sec2.IsSLEEvolutionUpTo κ xL ![a, b] ρL ![r, -r] P 𝓕 W VL VR B e)
    (hA : Coupling.IsAnnouncingSeq 𝓕 P e A)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (W · ω) (e ω) (η ω))
    (hinj : ∀ᵐ ω ∂P, InjOn (η ω) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e ω}) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e ω → ∀ y ∈ Ioo a b, η ω t ≠ (y : ℂ) := by
  have := hE.brownian.isProbabilityMeasure'
  obtain ⟨𝓙, β, τ, Q, -, hτ, hQ, hImage⟩ := Freeze11.exists_first_retarget_evolution hκ ha hab hE hA
  obtain ⟨W', VL', VR', hImage', hW', hL', hR', hagree⟩ :=
    Version6.exists_continuous_state_modification hImage
  have hsum : κ / 2 - 2 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin 2 =>
      (![-1, Sec7.targetChangeReal a b] : Fin 2 → ℝ) 1 ≤
        (![-1, Sec7.targetChangeReal a b] : Fin 2 → ℝ) i), (![κ - 6, -r] : Fin 2 → ℝ) i := by
    rw [sum_retarget_left ha hab]
    linarith only [hr]
  have hNo := ae_no_left_comparison hκ hκ4.le hImage' hW' hL' hR'
    (Version6.isAnnouncingSeq_usualAugmentation hQ) (k := 1) hsum
  have hord := isOrderedForceWord_retarget ha hab (LP.retargetXR (j := 0) (m := 1) ![a, b])
  apply Restart.ConverseBefore.ae_of_ae_fst (P₀ := P)
  have hLift := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae
    (hE.ae_path.and (hη.and (hinj.and hτ)))
  filter_upwards [hLift, hImage'.ae_path, hagree, hNo] with p hp hpi heq hn t ht y hy he
  have hcov := Cover3.visit_le_sepTime hκ4 hr ha hp.1 hp.2.1 hp.2.2.1 t ht y hy he
  have hsmall : newHorizon a (W · p.1) (VR 0 · p.1) t ≤ τ p.1 :=
    (newHorizon_mono hcov).trans_eq hp.2.2.2.symm
  obtain ⟨hfin, Γ, hΓ, hi, hval, -⟩ :=
    Image4.exists_image_trace_at_visit hκ4 hr ha hab hp.1 hp.2.1 hp.2.2.1 ht hy he
  have hDrv : (W' · p) = newDrv a (W · p.1) (VR 0 · p.1) := heq.1
  have hΓ' : IsGeneratingTrace (W' · p) (newHorizon a (W · p.1) (VR 0 · p.1) t) Γ := by
    rw [hDrv]
    exact hΓ
  have hnext : ∀ j : Fin 2,
      (![-1, Sec7.targetChangeReal a b] : Fin 2 → ℝ) j <
        (![-1, Sec7.targetChangeReal a b] : Fin 2 → ℝ) 1 →
      (![-1, Sec7.targetChangeReal a b] : Fin 2 → ℝ) j ≤ Sec7.targetChangeReal a y - 1 :=
    fun j hj => (not_lt_of_ge (hord.1 (Fin.le_last j)) hj).elim
  have hvis : ∃ u : ℝ≥0, (u : ℝ≥0∞) ≤ newHorizon a (W · p.1) (VR 0 · p.1) t ∧
      ∃ z ∈ Ioo (Sec7.targetChangeReal a y - 1) (Sec7.targetChangeReal a b), Γ u = (z : ℂ) := by
    refine ⟨_, (ENNReal.coe_toNNReal hfin).le, Sec7.targetChangeReal a y,
      ⟨sub_one_lt _, targetChangeReal_lt_of_mem ha hy⟩, ?_⟩
    simpa only [Sec7.targetChange_ofReal] using hval
  obtain ⟨q, hq⟩ := left_comparison_of_completed_prefix hpi hsmall hord hΓ' hi hnext hvis
  exact hn q hq

end InteractingSLE.Sec5.TwoMark.Trace12
