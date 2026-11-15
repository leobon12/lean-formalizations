/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2ReadoutPiece
import InteractingSLE.Spec.Supplement.GW2aContPass

/-! # A measurable full-plane dense code for every launched ordinary piece

The physical tips at countably many available times are limits of the existing
measurable interior approximants. Times beyond the lifetime and absent launches
are replaced by the root. Finite lifetime endpoints are retained by continuity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.SB.Side

open Exist.Staged Exist.StagedLaw GW2aMulti GW2aCont WalkLaw

/-- Every ordinary piece has a measurable dense code in the whole plane,
including its real contacts. One common regularity event works for all indices. -/
theorem exists_measurable_piece_dense_code {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec)
    {Ω : Type u} [MeasurableSpace Ω] {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {M : Set Ω} (hM : MeasurableSet M)
    (hMreg : ∀ ω ∈ M, ∀ (j : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2)) :
    ∃ F : ℕ → Ω → Unit ⊕ (ℕ × ℕ) → ℂ,
      (∀ j i, Measurable fun ω => F j ω i) ∧ ∀ ω ∈ M, ∀ j,
        closure (range (F j ω)) = {(spec.1 : ℂ)} ∪ pieceTips κ b jumps spec (fun i => E i ω) j := by
  classical
  choose Y hYm hY using fun (j m N n : ℕ) =>
    exists_measurable_tipApprox hb spec hEm hreg hM hMreg j (qTime m N) n
  let V : ℕ → ℕ → ℕ → Ω → ℂ := fun j m N ω => limUnder atTop (fun n => Y j m N n ω)
  have hVm : ∀ j m N, Measurable (V j m N) := fun j m N =>
    (StronglyMeasurable.limUnder fun n => (hYm j m N n).stronglyMeasurable).measurable
  let Good : ℕ → ℕ → ℕ → Set Ω := fun j m N =>
    {ω | (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j ≠ none ∧
      (qTime m N : ℝ≥0∞) ≤ min (instrTime spec j) (E j ω).2}
  have hGm : ∀ j m N, MeasurableSet (Good j m N) := fun j m N =>
    ((runMeasStatement κ b jumps hb spec E hEm hreg j).1).inter
      (measurableSet_le measurable_const (measurable_const.min (measurable_snd.comp (hEm j))))
  let F : ℕ → Ω → Unit ⊕ (ℕ × ℕ) → ℂ := fun j ω =>
    Sum.elim (fun _ => (spec.1 : ℂ))
      (fun p => if ω ∈ Good j p.1 p.2 then V j p.1 p.2 ω else (spec.1 : ℂ))
  refine ⟨F, ?_, ?_⟩
  · intro j i
    cases i with
    | inl _ => exact measurable_const
    | inr p => exact Measurable.ite (hGm j p.1 p.2) (hVm j p.1 p.2) measurable_const
  · intro ω hω j
    by_cases hl : (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = none
    · have he : range (F j ω) = {(spec.1 : ℂ)} := by
        ext z
        constructor
        · rintro ⟨i, rfl⟩
          cases i <;> simp [F, Good, hl]
        · rintro rfl
          exact ⟨Sum.inl (), rfl⟩
      rw [he, isClosed_singleton.closure_eq]
      simp only [pieceTips, hl, ↓reduceIte, union_empty]
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
    obtain ⟨f, _, hf, _⟩ := (GW1P.isClosed_pieces_run spec (fun i => E i ω) (hMreg ω hω) j).1
    have hr := hMreg ω hω j c θ hcθ
    have hpc : IsClosed (pieceTips κ b jumps spec (fun i => E i ω) j) := by
      simp only [pieceTips, hl, ↓reduceIte]
      exact GW1P.isClosed_tipSet (GW1P.isClosed_pieces_run spec (fun i => E i ω) (hMreg ω hω) j).1 hr
    obtain ⟨hW0, hWc, α, hα, _⟩ := hr
    let S : ℝ≥0∞ := min (instrTime spec j) (E j ω).2
    have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
      Sec7.IsGeneratingTrace.mem_Hbar hα
        (hWc.mono fun t hs => show (t : ℝ≥0∞) ≤ S from hs.le) hW0 ht
    have hp : pieceTips κ b jumps spec (fun i => E i ω) j =
        (fun t => f (α t)) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S} := by
      simp only [pieceTips, hl, ↓reduceIte]
      unfold stoppedDriver pieceStop
      rw [CounterflowRange.tipSet_stopped_eq_of_tendsto hα hWc hW0
        (fun t ht => hf _ (hαH t ht)), image_image]
    have hFc : ContinuousOn (fun t => f (α t)) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S} :=
      (GW1P.continuousOn_of_tendsto hf).comp hα.2.1 (fun t ht => hαH t ht)
    have hy : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun n => (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))⟩
    have hV : ∀ m N, (qTime m N : ℝ≥0∞) ≤ S → V j m N ω = f (α (qTime m N)) := by
      intro m N ht
      have he : (fun n => Y j m N n ω) = fun n => tipApprox κ b jumps spec
          (fun i => E i ω) j (qTime m N) n :=
        funext fun n => (hY j m N n ω hω hl).symm
      change limUnder atTop (fun n => Y j m N n ω) = _
      rw [he]
      exact (((CounterflowRange.tendsto_tip_stopped_of_tendsto hα hWc hW0 ht
        (hf _ (hαH _ ht))).comp hy)).limUnder_eq
    refine subset_antisymm (closure_minimal ?_ (isClosed_singleton.union hpc)) (union_subset ?_ ?_)
    · rintro _ ⟨i, rfl⟩
      cases i with
      | inl _ => exact Or.inl rfl
      | inr p =>
        change (if ω ∈ Good j p.1 p.2 then V j p.1 p.2 ω else (spec.1 : ℂ)) ∈ _
        split_ifs with hG
        · right
          rw [hV p.1 p.2 hG.2, hp]
          exact mem_image_of_mem _ hG.2
        · exact Or.inl rfl
    · rintro _ rfl
      exact subset_closure ⟨Sum.inl (), rfl⟩
    · rw [hp]
      rintro _ ⟨t, ht, rfl⟩
      obtain ⟨m, hm, hmt⟩ := exists_qTime_tendsto t
      have hmS : ∀ N, (qTime (m N) N : ℝ≥0∞) ≤ S := fun N =>
        (ENNReal.coe_le_coe.2 (hm N)).trans ht
      have hlim : Tendsto (fun N => f (α (qTime (m N) N))) atTop (𝓝 (f (α t))) :=
        (hFc t ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hmt, Eventually.of_forall hmS⟩)
      apply mem_closure_of_tendsto hlim
      exact Eventually.of_forall fun N => ⟨Sum.inr (m N, N), by
        change (if ω ∈ Good j (m N) N then V j (m N) N ω else (spec.1 : ℂ)) = _
        rw [ite_eq_left (show ω ∈ Good j (m N) N from ⟨hl, hmS N⟩), hV _ _ (hmS N)]⟩

end InteractingSLE.Theorem14.SB.Side
