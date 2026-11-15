/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2StmCompose
import InteractingSLE.Spec.Supplement.GW1PieceSimpleFiber
import InteractingSLE.Spec.Supplement.GB6LifeEnd
import InteractingSLE.Spec.Supplement.BW1DetWitness
import InteractingSLE.Spec.Supplement.GW2LaterMeas

/-!
# GW2's stage step, part 9: the first contact with the new piece, read through the launch chart

Packet PROVE-GW2-STAGEMEAN, step round. GB6's relative clock runs up to the first contact
`T_c = firstContactTime (sphereInv ∘ γ_k) (α '' [0, S])` of the conditional counterflow with the new piece, in the
coordinates of the launch chart `c`. The launch datum composes clocks through the physical tips of the new piece,
`c.tipSet` of its stopped driver. When `c` has a proper boundary extension `f` that is injective off the old union `A`
(`GW1Z.FiberGood`, `GW1Z.chartFiber_run`) and the counterflow's tips through `c` avoid `A` (they are original tips
before the old first visit, `GW1Z.notMem_of_clock`), the two first times agree and a finite one is attained:

* **`firstTipTime_piece_eq`**: `firstTipTime (c.trans R) W_k (c.tipSet piece) = T_c`, and the contact at a finite
  `T_c` is a physical tip of the piece.

Deterministic. Conditional helper with a distinct name.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW2Stm

open WangWu (negInv)

/-- **GB6's first contact is the first visit of the new piece's physical tips through the launch chart.** -/
theorem firstTipTime_piece_eq {c : Chart} {A : Set ℂ} (hc : GW1Z.FiberGood c A)
    {Wk : ℝ≥0 → ℝ} {γk : ℝ≥0 → ℂ} (hγk : IsGeneratingTrace Wk ⊤ γk) (hWk : Continuous Wk) (hWk0 : Wk 0 = 0)
    (hoff : ∀ (t : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt Wk t z → z ∉ A)
    {Wp : ℝ≥0 → ℝ} {S : ℝ≥0} {αp : ℝ≥0 → ℂ} (hαp : IsGeneratingTrace Wp S αp)
    (hWp : ContinuousOn Wp {t | (t : ℝ≥0∞) ≤ S}) (hWp0 : Wp 0 = 0) :
    firstTipTime (c.trans infinitySourceChart) Wk
        (c.tipSet (fun r : ℝ≥0 => Wp (min (r : ℝ≥0∞) S).toNNReal) S) =
      Supp8.GB6.firstContactTime (fun t => Supp8.GB6.sphereInv (γk t : OnePoint ℂ))
        ((fun t => (αp t : OnePoint ℂ)) '' Icc 0 S) ∧
    ∀ T' : ℝ≥0, (T' : ℝ≥0∞) = Supp8.GB6.firstContactTime (fun t => Supp8.GB6.sphereInv (γk t : OnePoint ℂ))
        ((fun t => (αp t : OnePoint ℂ)) '' Icc 0 S) →
      ∃ z ∈ c.tipSet (fun r : ℝ≥0 => Wp (min (r : ℝ≥0∞) S).toNNReal) S,
        (c.trans infinitySourceChart).tipAt Wk T' z := by
  obtain ⟨f, C, hf, hC, hinj⟩ := hc
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → αp t ∈ Hbar := fun t ht =>
    GW2Later.trace_mem_Hbar_of_le hαp hWp hWp0 ht
  have hP : c.tipSet (fun r : ℝ≥0 => Wp (min (r : ℝ≥0∞) S).toNNReal) S =
      f '' (αp '' {t | (t : ℝ≥0∞) ≤ (S : ℝ≥0∞)}) :=
    CounterflowRange.tipSet_stopped_eq_of_tendsto hαp hWp hWp0 fun t ht => hf _ (hαH t ht)
  have hγH : ∀ t, γk t ∈ Hbar := GW2aPiece.trace_mem_Hbar hγk hWk hWk0
  have key : ∀ t : ℝ≥0, (∃ z ∈ c.tipSet (fun r : ℝ≥0 => Wp (min (r : ℝ≥0∞) S).toNNReal) S,
      (c.trans infinitySourceChart).tipAt Wk t z) ↔
      Supp8.GB6.sphereInv (γk t : OnePoint ℂ) ∈ (fun t => (αp t : OnePoint ℂ)) '' Icc 0 S := by
    intro t
    rw [hP]
    constructor
    · rintro ⟨z, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, htip⟩
      obtain ⟨hne, hz⟩ := (BW1Det.tipAt_trans_iff_trace hf hC hγk hWk hWk0 t _).1 htip
      have hzA := hoff t _ htip
      have hxy : negInv (γk t) = αp u :=
        hinj _ (GW4Traverse.negInv_mem_Hbar (hγH t)) _ (hαH u hu) hz.symm (by rw [← hz]; exact hzA)
      refine ⟨u, ⟨zero_le, ?_⟩, ?_⟩
      · exact_mod_cast hu
      · rw [Supp8.GB6.sphereInv_coe_of_ne hne]
        exact congrArg _ hxy.symm
    · rintro ⟨u, hu, hequ⟩
      have hne : γk t ≠ 0 := fun h0 => by
        rw [h0] at hequ
        simp only [Supp8.GB6.sphereInv_coe, ↓reduceIte] at hequ
        exact OnePoint.coe_ne_infty _ hequ
      rw [Supp8.GB6.sphereInv_coe_of_ne hne] at hequ
      have hxy : αp u = negInv (γk t) := OnePoint.coe_injective hequ
      have hu' : (u : ℝ≥0∞) ≤ S := by exact_mod_cast hu.2
      refine ⟨f (αp u), ⟨αp u, ⟨u, hu', rfl⟩, rfl⟩, ?_⟩
      rw [hxy]
      exact (BW1Det.tipAt_trans_iff_trace hf hC hγk hWk hWk0 t _).2 ⟨hne, rfl⟩
  have heq : firstTipTime (c.trans infinitySourceChart) Wk
      (c.tipSet (fun r : ℝ≥0 => Wp (min (r : ℝ≥0∞) S).toNNReal) S) =
      Supp8.GB6.firstContactTime (fun t => Supp8.GB6.sphereInv (γk t : OnePoint ℂ))
        ((fun t => (αp t : OnePoint ℂ)) '' Icc 0 S) := by
    unfold firstTipTime Supp8.GB6.firstContactTime
    exact iInf_congr fun t => iInf_congr_Prop (key t) fun _ => rfl
  refine ⟨heq, fun T' hT' => (key T').2 ?_⟩
  have hηc : Continuous fun t => Supp8.GB6.sphereInv (γk t : OnePoint ℂ) := by
    have hγc : Continuous γk := by
      have := hγk.2.1
      simp only [le_top, ofPred_true] at this
      exact continuousOn_univ.1 this
    exact Supp8.GB6.continuous_sphereInv.comp (OnePoint.continuous_coe.comp hγc)
  have hK : IsClosed ((fun t => (αp t : OnePoint ℂ)) '' Icc 0 S) := by
    have hαc : ContinuousOn αp (Icc 0 S) := hαp.2.1.mono fun t ht => by
      show (t : ℝ≥0∞) ≤ S
      exact_mod_cast ht.2
    exact (isCompact_Icc.image_of_continuousOn (OnePoint.continuous_coe.comp_continuousOn hαc)).isClosed
  exact Supp8.GB6.firstContactTime_mem hηc hK hT'.symm

end InteractingSLE.Theorem14.GW2Stm
