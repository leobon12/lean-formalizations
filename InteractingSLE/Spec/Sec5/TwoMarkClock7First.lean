/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkClock7Filtration
import InteractingSLE.Spec.Sec5.TwoMarkLocal2Path

/-!
# The first-mark image clock of an announced local two-mark evolution

The inverse-clock filtration and an announcing sequence of its image horizon are
constructed from the original local evolution. Brownian image noise and adapted
image coordinates are separate obligations.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Clock7

open Zhan.Retarget

/-- The first-mark capacity clock has a canonical stopped inverse filtration and announcement. -/
theorem exists_announced_first_clock {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ a b : ℝ}
    {xL ρL : Fin 0 → ℝ} {ρR : Fin 2 → ℝ} {W B : ℝ≥0 → Ω → ℝ}
    {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ}
    {e : Ω → ℝ≥0∞} {A : ℕ → Ω → ℝ≥0} (ha : 0 < a) (hab : a < b)
    (hE : Sec2.IsSLEEvolutionUpTo κ xL ![a, b] ρL ρR P 𝓕 W VL VR B e)
    (hA : Coupling.IsAnnouncingSeq 𝓕 P e A) :
    ∃ (G : Set Ω) (S : ℕ → Ω → ℝ≥0)
      (hI : ∀ u, IsStoppingTime (usualAugmentation 𝓕 P)
        (inverseTime G a W (VR 0) (fun ω => sepTime (W · ω) (VR 0 · ω) (e ω)) u))
      (hmono : ∀ u v, u ≤ v → ∀ ω,
        inverseTime G a W (VR 0) (fun ω => sepTime (W · ω) (VR 0 · ω) (e ω)) u ω ≤
        inverseTime G a W (VR 0) (fun ω => sepTime (W · ω) (VR 0 · ω) (e ω)) v ω),
      (∀ᵐ ω ∂P, ω ∈ G) ∧
      Coupling.IsAnnouncingSeq (timeChangeFilt (usualAugmentation 𝓕 P) hI hmono) P
        (fun ω => if ω ∈ G then newHorizon a (W · ω) (VR 0 · ω)
          (sepTime (W · ω) (VR 0 · ω) (e ω)) else 0)
        (imageStop (a := a) (G := G) (W := W) (V := VR 0) (A := S)) := by
  classical
  let U := fun ω => sepTime (W · ω) (VR 0 · ω) (e ω)
  let 𝓖 := usualAugmentation 𝓕 P
  obtain ⟨S, hS⟩ := Version6.exists_isAnnouncingSeq_sepTime hE hA (k := 0) ha
  have hgoodae : ∀ᵐ ω ∂P,
      Sec2.IsSLEPathUpTo κ xL ![a, b] ρL ρR (W · ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (B · ω) (e ω) ∧
      (∀ n, (S n ω : ℝ≥0∞) < U ω) ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) < U ω → ∃ n, s ≤ S n ω) :=
    hE.ae_path.and ((ae_all_iff.2 hS.2.2.1).and hS.2.2.2)
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgoodae)
  let G := Nᶜ
  have hG : MeasurableSet[𝓖 0] G :=
    (Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hNm hN0 0).compl
  have hGa : ∀ᵐ ω ∂P, ω ∈ G := measure_eq_zero_iff_ae_notMem.1 hN0
  have hgood : ∀ ω ∈ G,
      Sec2.IsSLEPathUpTo κ xL ![a, b] ρL ρR (W · ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (B · ω) (e ω) ∧
      (∀ n, (S n ω : ℝ≥0∞) < U ω) ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) < U ω → ∃ n, s ≤ S n ω) := by
    intro ω hω
    by_contra hn
    exact hω (hNsub hn)
  have hs : ∀ ω ∈ G, SepUpTo (W · ω) (VR 0 · ω) (U ω) := by
    intro ω hω
    exact (Local2.retargetData_first ha hab ((hgood ω hω).1.mono (sepTime_le _ _ _))
      (fun _ ht => lt_of_lt_sepTime ht)).sep
  have hb : ∀ ω ∈ G, ∀ n, (S n ω : ℝ≥0∞) < U ω := fun ω hω => (hgood ω hω).2.1
  have hc : ∀ ω ∈ G, ∀ s : ℝ≥0, (s : ℝ≥0∞) < U ω → ∃ n, s ≤ S n ω :=
    fun ω hω => (hgood ω hω).2.2
  have hW : AdaptedBefore 𝓖 e W := Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) hE.adapted_W
  have hV : AdaptedBefore 𝓖 e (VR 0) :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) (hE.adapted_VR 0)
  have hm : ∀ n r, Measurable[𝓖 r] fun ω =>
      @ite ℝ (ω ∈ G) (Classical.propDecidable _)
        (clk (rate a (W · ω) (VR 0 · ω)) (min r (S n ω))) 0 := by
    intro n r
    have hσe : ∀ ω ∈ G, (S n ω : ℝ≥0∞) < e ω :=
      fun ω hω => (hb ω hω n).trans_le (sepTime_le _ _ _)
    refine measurable_stopped_clock (a := a) hW hV (hS.1 n) hG hσe ?_ ?_ r
    · intro ω hω
      exact (((hgood ω hω).1.continuousOn_vR 0).sub (hgood ω hω).1.continuousOn_w).mono
        (fun s hs' => (ENNReal.coe_le_coe.2 hs').trans_lt (hσe ω hω))
    · intro ω hω s hst
      exact sub_pos.2 (lt_of_lt_sepTime ((ENNReal.coe_le_coe.2 hst).trans_lt (hb ω hω n)))
  refine ⟨G, S, isStoppingTime_inverseTime ha hG hS.1 hs hb hc hm,
    inverseTime_mono ha hs, hGa, ?_⟩
  exact isAnnouncingSeq_imageStop ha hG hS.1 hs hb hc hm hGa hS.2.1

end InteractingSLE.Sec5.TwoMark.Clock7
