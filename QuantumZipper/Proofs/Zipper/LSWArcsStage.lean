import QuantumZipper.Proofs.Zipper.LSWArcsAlg
import QuantumZipper.Proofs.Zipper.LogShiftW2Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LSW-ARCS (2): one stage of the `Γ⁰` picture, deterministic

Task LSW-ARCS. At the stage `T = u + s`, let `A`, `B` be the boundary positions of the curve
points (continuous, strictly monotone on `[0, T]`, `A T = B T = 0`), and suppose that the pieces
`[A v, 0]`, `[0, B v]` carry the complementary lengths `L T − L v` (`L` continuous and finite),
and that the lengths of the stage restarted at `u` are the increments `M r = L (u + r) − L u`.
Then `LswArcs ν (A u, B u) s M Ψ (η (u + ·))` holds with `a r = A (u + r)`, `b r = B (u + r)`
(clamped), as soon as `Ψ (A v) = Ψ (B v) = η v`.

Sheffield, arXiv:1012.4797, §1.4 (lengths of the two sides of `η[0, t]` as boundary measures of
the unzipped field). Own bookkeeping (additivity, `LSWArcsAlg.lean`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F1

theorem lswa_clamp_eq {u T x : ℝ} (hx : x ∈ Icc u T) : lswClamp u T x = x := by
  unfold lswClamp
  rw [min_eq_left hx.2, max_eq_right hx.1]

/-- One side of a stage. -/
theorem lswa_side_len {ν : Measure ℝ} {A : ℝ → ℝ} {T u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T)
    (hAm : StrictMonoOn A (Icc 0 T)) (hAT : A T = 0) {L : ℝ → ℝ≥0∞} (hLT : L T ≠ ⊤)
    (hLc : ContinuousOn (fun v => (L v).toReal) (Icc 0 T))
    (hpc : ∀ v ∈ Icc 0 T, L v + ν (Icc (A v) 0) = L T) {M : ℝ → ℝ≥0∞}
    (hM : ∀ r, 0 ≤ r → u + r ≤ T → L (u + r) = L u + M r) {r : ℝ} (hr0 : 0 ≤ r)
    (hrT : u + r ≤ T) : ν (Icc (A u) (A (u + r))) = M r := by
  have hmu : u ∈ Icc 0 T := ⟨hu, huT⟩
  have hmw : u + r ∈ Icc 0 T := ⟨by linarith, hrT⟩
  have hf : ∀ v ∈ Icc 0 T, ν (Icc (A v) 0) = ν (Icc (A v) 0) := fun _ _ => rfl
  have hfin : ∀ v ∈ Icc 0 T, L v ≠ ⊤ ∧ ν (Icc (A v) 0) ≠ ⊤ := fun v hv =>
    ⟨ne_top_of_le_ne_top hLT (by rw [← hpc v hv]; exact le_self_add),
      ne_top_of_le_ne_top hLT (by rw [← hpc v hv]; exact le_add_self)⟩
  -- no atom at `A (u + r)`
  have hat : ν {A (u + r)} = 0 := by
    rcases hrT.lt_or_eq with hlt | heq
    · exact lswa_atom_left hAm hAT hf hpc hLT hLc ⟨hmw.1, hlt⟩
    · rw [heq, hAT]
      have h := hpc T ⟨hu.trans huT, le_rfl⟩
      rw [hAT, Icc_self] at h
      exact lsw2_cancel hLT (h.trans (add_zero _).symm)
  have hsp := lswa_split_left hAm.monotoneOn hAT hf hmu hmw (by linarith) hat
  have e1 := hpc u hmu
  have e2 := hpc (u + r) hmw
  rw [hM r hr0 hrT] at e2
  -- `L u + (ν [A u, A (u+r)] + f (u+r)) = L u + (M r + f (u+r))`
  have key : L u + (ν (Icc (A u) (A (u + r))) + ν (Icc (A (u + r)) 0)) =
      L u + (M r + ν (Icc (A (u + r)) 0)) := by
    rw [hsp, e1, ← e2, add_assoc]
  have k2 := lsw2_cancel (hfin u hmu).1 key
  rw [add_comm (ν _), add_comm (M r)] at k2
  exact lsw2_cancel (hfin _ hmw).2 k2

/-- **One stage of the `Γ⁰` picture** (deterministic). -/
theorem lswa_stage {ν : Measure ℝ} {A B : ℝ → ℝ} {T u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s)
    (hT : u + s = T) (hAc : ContinuousOn A (Icc 0 T)) (hBc : ContinuousOn B (Icc 0 T))
    (hAm : StrictMonoOn A (Icc 0 T)) (hBm : StrictAntiOn B (Icc 0 T)) (hAT : A T = 0)
    (hBT : B T = 0) {L : ℝ → ℝ≥0∞ × ℝ≥0∞} (hL1 : (L T).1 ≠ ⊤) (hL2 : (L T).2 ≠ ⊤)
    (hLc1 : ContinuousOn (fun v => (L v).1.toReal) (Icc 0 T))
    (hLc2 : ContinuousOn (fun v => (L v).2.toReal) (Icc 0 T))
    (hpA : ∀ v ∈ Icc 0 T, (L v).1 + ν (Icc (A v) 0) = (L T).1)
    (hpB : ∀ v ∈ Icc 0 T, (L v).2 + ν (Icc 0 (B v)) = (L T).2)
    {M : ℝ → ℝ≥0∞ × ℝ≥0∞}
    (hM : ∀ r, 0 ≤ r → u + r ≤ T → (L (u + r)).1 = (L u).1 + (M r).1 ∧
      (L (u + r)).2 = (L u).2 + (M r).2)
    {O : ℝ × ℝ} (hO : O = (A u, B u)) {Ψ η : ℝ → ℂ} (hΨ : Measurable Ψ)
    (hE : ∀ v ∈ Ioc 0 T, Ψ (A v) = η v ∧ Ψ (B v) = η v) :
    LswArcs ν O s M Ψ (fun r => η (u + r)) := by
  subst hO hT
  have huT : u ≤ u + s := by linarith
  have hsub : Icc u (u + s) ⊆ Icc 0 (u + s) := Icc_subset_Icc_left hu
  have hcl : ∀ r ∈ Icc 0 s, lswClamp u (u + s) (u + r) = u + r := fun r hr =>
    lswa_clamp_eq ⟨by linarith [hr.1], by linarith [hr.2]⟩
  refine ⟨hΨ, fun r => A (lswClamp u (u + s) (u + r)), fun r => B (lswClamp u (u + s) (u + r)),
    (continuous_comp_lswClamp huT (hAc.mono hsub)).comp (continuous_const.add continuous_id),
    (continuous_comp_lswClamp huT (hBc.mono hsub)).comp (continuous_const.add continuous_id),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [hcl x hx, hcl y hy]
    exact hAm ⟨by linarith [hx.1], by linarith [hx.2]⟩ ⟨by linarith [hy.1], by linarith [hy.2]⟩
      (by linarith)
  · intro x hx y hy hxy
    simp only [hcl x hx, hcl y hy]
    exact hBm ⟨by linarith [hx.1], by linarith [hx.2]⟩ ⟨by linarith [hy.1], by linarith [hy.2]⟩
      (by linarith)
  · show A _ = A u
    rw [hcl 0 ⟨le_rfl, hs⟩, add_zero]
  · show A _ = 0
    rw [hcl s ⟨hs, le_rfl⟩, hAT]
  · show B _ = B u
    rw [hcl 0 ⟨le_rfl, hs⟩, add_zero]
  · show B _ = 0
    rw [hcl s ⟨hs, le_rfl⟩, hBT]
  · intro r hr
    simp only [hcl r hr]
    refine ⟨lswa_side_len hu huT hAm hAT hL1 hLc1 hpA (fun r h0 h1 => (hM r h0 h1).1) hr.1
      (by linarith [hr.2]), ?_⟩
    -- the right side, by reflection
    obtain ⟨h1, h2, h3⟩ := lswa_neg_facts (ν := ν) hBm hBT (fun v _ => rfl)
    have h := lswa_side_len (ν := ν.map (fun x : ℝ => -x)) hu huT h1 h2 hL2 hLc2
      (fun v hv => by rw [h3 v hv]; exact hpB v hv) (fun r h0 h1 => (hM r h0 h1).2) hr.1
      (by linarith [hr.2])
    rwa [lswa_map_neg_Icc, neg_neg, neg_neg] at h
  · intro r hr
    have hr' : r ∈ Icc 0 s := ⟨hr.1.le, hr.2⟩
    simp only [hcl r hr']
    exact hE (u + r) ⟨by linarith [hr.1], by linarith [hr.2]⟩

end F1
end QuantumZipper
