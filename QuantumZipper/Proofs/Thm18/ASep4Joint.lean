import QuantumZipper.Proofs.Thm18.ASep4Comm
import QuantumZipper.Proofs.Zipper.RegUnifDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP4 (step 2): regular samples uniformly over a parameter set; an everywhere continuous version

* `forall_isRegularWith_of_joint_gen`: `RegUnif.forall_isRegularWith_of_joint` (RegUnifDet) with
  the time interval `[0, T]` replaced by an arbitrary parameter set `A` of a topological space
  (the proof is the same: the raw identity and the commutation identity extend from countable
  dense sets by continuity; `RegUnif.isRegularWith_of_witness`).
* `exists_contMod_νT_rescale'`: the modification of `exists_contMod_νT_rescale` (ASep3InnerGlob)
  modified on a measurable null set so that it is continuous for **every** sample.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

open RegUnif

/-- **Regular samples uniformly over a parameter set** (deterministic). -/
theorem forall_isRegularWith_of_joint_gen {ι : Type*} [TopologicalSpace ι] {A : Set ι}
    {y : ι → FieldSample} {G : ι → ℂ × ℝ → ℝ}
    (hG : ContinuousOn (fun q : ι × (ℂ × ℝ) => G q.1 q.2) (A ×ˢ (Hbar ×ˢ Ioi 0)))
    (hyc : ∀ k : ℕ, ∀ d ∈ Dy, ContinuousOn (fun t => y t (foldedCircle d (radius k))) A)
    {D : Set ι} (hDT : D ⊆ A) (hTD : A ⊆ closure D)
    (hraw : ∀ t ∈ D, ∀ k : ℕ, ∀ d ∈ Dy, y t (foldedCircle d (radius k)) = G t (d, radius k))
    {D4 : Set (ι × ((ℂ × ℝ) × ℝ))}
    (hD4 : D4 ⊆ A ×ˢ ((Hbar ×ˢ Ioi 0) ×ˢ Ioi 0))
    (hD4d : A ×ˢ ((Hbar ×ˢ Ioi 0) ×ˢ Ioi 0) ⊆ closure D4)
    (hcomm : ∀ q ∈ D4, ∫ u, G q.1 (u, q.2.2) ∂foldedCircle q.2.1.1 q.2.1.2 =
      ∫ v, G q.1 (v, q.2.1.2) ∂foldedCircle q.2.1.1 q.2.2) :
    ∀ t ∈ A, IsRegularWith (y t) (G t) := by
  intro t ht
  set S4 : Set (ι × ((ℂ × ℝ) × ℝ)) := A ×ˢ ((Hbar ×ˢ Ioi 0) ×ˢ Ioi 0) with hS4
  have hL : ContinuousOn (fun q : ι × ((ℂ × ℝ) × ℝ) =>
      ∫ u, G q.1 (u, q.2.2) ∂foldedCircle q.2.1.1 q.2.1.2) S4 := by
    have hm : Continuous fun q : (ι × ((ℂ × ℝ) × ℝ)) × ℂ => (q.1.1, (q.2, q.1.2.2)) := by
      fun_prop
    exact RegClosure.continuousOn_integral_fc (P := ι × ((ℂ × ℝ) × ℝ))
      (H := fun q u => G q.1 (u, q.2.2)) (c := fun q => q.2.1.1) (r := fun q => q.2.1.2)
      (hG.comp hm.continuousOn fun q hq => ⟨hq.1.1, hq.2, hq.1.2.2⟩)
      (by fun_prop) (by fun_prop)
  have hR : ContinuousOn (fun q : ι × ((ℂ × ℝ) × ℝ) =>
      ∫ v, G q.1 (v, q.2.1.2) ∂foldedCircle q.2.1.1 q.2.2) S4 := by
    have hm : Continuous fun q : (ι × ((ℂ × ℝ) × ℝ)) × ℂ => (q.1.1, (q.2, q.1.2.1.2)) := by
      fun_prop
    exact RegClosure.continuousOn_integral_fc (P := ι × ((ℂ × ℝ) × ℝ))
      (H := fun q v => G q.1 (v, q.2.1.2)) (c := fun q => q.2.1.1) (r := fun q => q.2.2)
      (hG.comp hm.continuousOn fun q hq => ⟨hq.1.1, hq.2, hq.1.2.1.2⟩)
      (by fun_prop) (by fun_prop)
  have hcomm' := Set.EqOn.of_subset_closure (fun q hq => hcomm q hq) hL hR hD4 hD4d
  have hFt : ContinuousOn (G t) (Hbar ×ˢ Ioi 0) :=
    hG.comp (continuousOn_const.prodMk continuousOn_id) fun p hp => ⟨ht, hp⟩
  refine (isRegularWith_of_witness hFt (fun k d hd => ?_) fun w hw r ρ hr hρ =>
    hcomm' (show (t, ((w, r), ρ)) ∈ S4 from ⟨ht, ⟨hw, hr⟩, hρ⟩)).1
  have hGc : ContinuousOn (fun s => G s (d, radius k)) A :=
    hG.comp (continuousOn_id.prodMk continuousOn_const) fun s hs =>
      ⟨hs, Dy_subset_Hbar hd, radius_pos k⟩
  exact Set.EqOn.of_subset_closure (fun s hs => hraw s hs k d hd) (hyc k d hd) hGc hDT hTD ht

/-- **The dilated pushed-circle modification, continuous for every sample.** -/
theorem exists_contMod_νT_rescale' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {T a CH : ℝ} (hT : 0 < T) (ha : 0 < a) (ha1 : a ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a) :
    ∃ Y : (Fin 5 → ℝ) → Ω → ℝ,
      (∀ ω, ContinuousOn (fun q => Y q ω) {q | 0 < q 3 ∧ 0 < q 4}) ∧
      ∀ q ∈ {q : Fin 5 → ℝ | 0 < q 3 ∧ 0 < q 4},
        (fun ω => Y q ω) =ᵐ[P] fun ω => X ω (nu5 W T q) := by
  classical
  obtain ⟨Y, hYc, hYe⟩ := exists_contMod_νT_rescale hX hW hW0 hT ha ha1 hCH hH
  set N : Set Ω := toMeasurable P {ω | ¬ ContinuousOn (fun q => Y q ω) {q | 0 < q 3 ∧ 0 < q 4}}
  have hN : P N = 0 := by rw [measure_toMeasurable]; exact ae_iff.1 hYc
  refine ⟨fun q ω => if ω ∈ N then 0 else Y q ω, fun ω => ?_, fun q hq => ?_⟩
  · by_cases hω : ω ∈ N
    · simp only [hω, ite_true]; exact continuousOn_const
    · simp only [hω, ite_false]
      by_contra h
      exact hω (subset_toMeasurable _ _ h)
  · have hNc : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN
    filter_upwards [hYe q hq, hNc] with ω h1 h2
    simp only [h2, ite_false]
    exact h1

end ASep
end QuantumZipper
