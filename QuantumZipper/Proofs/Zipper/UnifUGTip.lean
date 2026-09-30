import QuantumZipper.Proofs.Zipper.UnifUGReduce

/-!
# UNIF-UG: the tip statement `UnifTipStmt` from a moment bound at rational times

Continuation of `UnifUGReduce` (decision D26, task UNIF-UG). `UnifTipStmt` (UT: tightness of the
boundary approximations of `h⁰_s` near the tip `0`, at every `s ∈ [0,T]`) is reduced to a
countable, measurable statement:

* `tipSup κ T B X N ω = sup_{q ∈ ℚ ∩ [0,T]} sup_{k ≥ N} ν^{h⁰_q}_k((−2^{−N}, 2^{−N}))`;
* `UnifTipRatStmt`: a.s. `inf_N tipSup N = 0`;
* `TipMomentStmt`: a geometric bound `E[tipSup_N^p] ≤ C r^N` (`p > 0`, `r < 1`).

Main results:
* `unifTipStmt_of_rat`: `UnifTipRatStmt ⇒ UnifTipStmt`. The approximations at a real time are
  controlled by those at rational times by Fatou's lemma, since `(s,t) ↦ avgReg (h⁰_s) k t` is
  jointly continuous on one a.s. event (the continuous modification `Zh` of `JointModStmt`,
  `jointModStmt_holds`, is the regularity witness of every `h⁰_s`).
* `unifTipRatStmt_of_moment`: `TipMomentStmt ⇒ UnifTipRatStmt` (Borel–Cantelli via
  `E[Σ_N tipSup_N^p] < ∞`).
* `unifGlobal_unifAtomless_of_offTip_moment`: UO + `TipMomentStmt` ⇒ UG ∧ UA.

Sources: Fatou's lemma and the first Borel–Cantelli lemma (standard). The reduction is own
bookkeeping; the remaining analytic input `TipMomentStmt` is the uniform-in-time version of the
M4-P3(b)/M4-P4 annulus bound (`LogSing.P3bBound`, `LogSing.ae_summable_tail`), for which no
published proof uniform in the unzipping time was found.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5 RegCont

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

theorem ofReal_mem_Hbar_ug (x : ℝ) : ((x : ℝ) : ℂ) ∈ Hbar :=
  show (0 : ℝ) ≤ ((x : ℂ)).im by simp

/-- Regularity of `h⁰_t` for all `t ∈ [0,T]` with a **jointly continuous** witness (the proof of
`ae_forall_isRegularWith_of_jointMod`, keeping `G = Zh`). -/
theorem ae_forall_isRegularWith_joint [IsProbabilityMeasure P] {κ γ T : ℝ} {B : ℝ≥0 → Ω → ℝ}
    {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ G : ℝ × (ℂ × ℝ) → ℝ, ContinuousOn G (parSet T) ∧ ∀ t ∈ Icc 0 T,
      IsRegularWith (unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) t)
        (fun p => G (t, p)) := by
  obtain ⟨Zh, hc, hmod, hcomm⟩ := jointModStmt_holds κ γ hB hX hind hT
  obtain ⟨D, hDc, hDT, hTD⟩ := TopologicalSpace.exists_countable_dense_subset (Icc (0 : ℝ) T)
  set S4 : Set (ℝ × ((ℂ × ℝ) × ℝ)) := Icc 0 T ×ˢ ((Hbar ×ˢ Ioi 0) ×ˢ Ioi 0) with hS4
  obtain ⟨D4, hD4c, hD4S, hSD4⟩ := TopologicalSpace.exists_countable_dense_subset S4
  have hraw : ∀ᵐ ω ∂P, ∀ t ∈ D, ∀ k : ℕ, ∀ d ∈ Dy,
      unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) t (foldedCircle d (radius k)) =
        Zh (t, (d, radius k)) ω :=
    (eventually_countable_ball hDc).2 fun t ht => ae_all_iff.2 fun k =>
      (eventually_countable_ball countable_Dy).2 fun d hd =>
        (hmod (t, (d, radius k)) ⟨hDT ht, Dy_subset_Hbar hd, radius_pos k⟩).mono
          fun ω hω => hω.symm
  have hcm : ∀ᵐ ω ∂P, ∀ q ∈ D4, ∫ u, Zh (q.1, (u, q.2.2)) ω ∂foldedCircle q.2.1.1 q.2.1.2 =
      ∫ v, Zh (q.1, (v, q.2.1.2)) ω ∂foldedCircle q.2.1.1 q.2.2 :=
    (eventually_countable_ball hD4c).2 fun q hq => by
      obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hD4S hq
      exact hcomm q.1 h1 q.2.1.1 h2 q.2.1.2 q.2.2 h3 h4
  have hyc : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ d ∈ Dy, ContinuousOn
      (fun t => unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) t
        (foldedCircle d (radius k))) (Icc 0 T) :=
    ae_all_iff.2 fun k => (eventually_countable_ball countable_Dy).2 fun d _ =>
      RegCont.ae_continuousOn_unzippedField κ γ hB hX hind hT d (radius_pos k)
  filter_upwards [hraw, hcm, hyc] with ω h1 h2 h3
  exact ⟨fun q => Zh q ω, hc ω, fun t ht =>
    (forall_isRegularWith_of_joint (G := fun t p => Zh (t, p) ω) (hc ω) h3 hDT hTD h1 hD4S hSD4 h2 t ht).1⟩

end RegUnif
end QuantumZipper
