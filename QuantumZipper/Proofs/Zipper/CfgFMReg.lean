import QuantumZipper.Proofs.Zipper.CfgFMDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-FIRSTMODE (2): the unzipped field with an explicit regular witness

`RegUnif.ae_forall_isRegularWith` gives some witness; for the first-mode bound we need the
explicit one, `(t, p) ↦ ZE(path, X)(pr4 (t, p)) + Ddet κ γ W (t, p)` (the continuous extension of
the free-field part, for a good continuous version `B'` of the Brownian motion, plus the
deterministic part). This file re-runs the proof of `RegUnif.jointModStmt_holds` and
`RegUnif.ae_forall_isRegularWith_of_jointMod` keeping the witness (`CfgFM.ae_regWith_ZE`).
Bookkeeping only (sources as in `JointModFinal.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper.E6
namespace CfgFM

open RegUnif CharFun RegCont RegSample

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Explicit regular witness of the unzipped field, all `t ∈ [0,T]` at once.** -/
theorem ae_regWith_ZE [IsProbabilityMeasure P] (κ γ : ℝ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    {T : ℝ} (hT : 0 < T) :
    ∃ B' : ℝ≥0 → Ω → ℝ, ∃ (hB'm : ∀ t, Measurable (B' t)) (hB'c : ∀ ω, Continuous fun t => B' t ω),
      IndepFun (pathC T B' hB'c) X P ∧
      (∀ᵐ ω ∂P, pathC T B' hB'c ω ∈ GoodP hT.le (1 / 3)) ∧
      ∀ᵐ ω ∂P, Continuous (drive κ B ω) ∧ drive κ B ω 0 = 0 ∧ ∀ t ∈ Icc (0 : ℝ) T,
        IsRegularWith (unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) t)
          (fun p => ZE hT.le κ (pathC T B' hB'c ω, X ω) (pr4 (t, p)) +
            Ddet κ γ (drive κ B ω) (t, p)) := by
  classical
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := exists_good_version hB
  have hpath : pathOf B =ᵐ[P] pathOf B' := hB'eq.mono fun ω h => funext fun t => (h t).symm
  have hind' : IndepFun (pathC T B' hB'c) X P :=
    indepFun_pathC T (hind.congr hpath (ae_eq_refl _)) hB'c
  refine ⟨B', hB'm, hB'c, hind', ae_pathC_good hB hB'c hB'eq hT, ?_⟩
  set Zr : (Fin 4 → ℝ) → Ω → ℝ := fun q ω => ZE hT.le κ (pathC T B' hB'c ω, X ω) q with hZr
  have hZc : ∀ ω, Continuous fun q => Zr q ω := fun ω => continuous_ZE hT.le κ _
  have hZt := ae_tendsto_ZE κ hB hX hB'm hB'c hB'eq hind' hT
  have hdet := detContStmt_holds κ γ T
  set Zh : ℝ × (ℂ × ℝ) → Ω → ℝ := fun p ω =>
    if Continuous (drive κ B ω) ∧ drive κ B ω 0 = 0 then
      Zr (pr4 p) ω + Ddet κ γ (drive κ B ω) p else 0 with hZh
  have hc : ∀ ω, ContinuousOn (fun q => Zh q ω) (parSet T) := fun ω => by
    by_cases h : Continuous (drive κ B ω) ∧ drive κ B ω 0 = 0
    · simp only [hZh, h, and_self, ↓reduceIte]
      exact ((hZc ω).comp_continuousOn (continuousOn_pr4 T)).add (hdet _ h.1 h.2)
    · simp only [hZh, h, ↓reduceIte]
      exact continuousOn_const
  have hmod : ∀ p ∈ parSet T, (fun ω => Zh p ω) =ᵐ[P] fun ω =>
      unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) p.1 (foldedCircle p.2.1 p.2.2) := by
    intro p hp
    filter_upwards [ae_raw_eq κ γ hB hX hZt hp, ae_drive_good hB κ] with ω h1 h2
    simp only [hZh, h2, and_self, ↓reduceIte]
    exact h1.symm
  have hcomm : ∀ t ∈ Icc 0 T, ∀ w ∈ Hbar, ∀ r ρ : ℝ, 0 < r → 0 < ρ → ∀ᵐ ω ∂P,
      ∫ u, Zh (t, (u, ρ)) ω ∂foldedCircle w r = ∫ v, Zh (t, (v, r)) ω ∂foldedCircle w ρ := by
    intro t ht w hw r ρ hr hρ
    filter_upwards [ae_comm_ZE κ hB hX hB'm hB'c hB'eq hind' hT ht hw hr hρ,
      ae_drive_good hB κ] with ω h1 h2
    simp only [hZh, h2, and_self, ↓reduceIte]
    have iZ : ∀ s a : ℝ, 0 < a → Integrable (fun u => Zr (pr4 (t, (u, s))) ω)
        (foldedCircle w a) := fun s a ha =>
      RegClosure.integrable_fc (((hZc ω).comp (continuous_pr_fst s t)).continuousOn) w ha.le
    have iD : ∀ s a : ℝ, 0 < s → 0 < a →
        Integrable (fun u => Ddet κ γ (drive κ B ω) (t, (u, s))) (foldedCircle w a) := by
      intro s a hs ha
      refine RegClosure.integrable_fc ?_ w ha.le
      exact (hdet _ h2.1 h2.2).comp (Continuous.continuousOn (by fun_prop))
        fun u hu => ⟨ht, hu, hs⟩
    rw [integral_add (iZ ρ r hr) (iD ρ r hρ hr), integral_add (iZ r ρ hρ) (iD r ρ hr hρ),
      integral_Ddet_swap κ γ h2.1 h2.2 ht.1 w hr hρ]
    congr 1
  -- the regularity argument of `ae_forall_isRegularWith_of_jointMod`, keeping the witness
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
  filter_upwards [hraw, hcm, hyc, ae_drive_good hB κ] with ω h1 h2 h3 hg
  have hreg := forall_isRegularWith_of_joint (G := fun t p => Zh (t, p) ω) (hc ω) h3 hDT hTD h1
    hD4S hSD4 h2
  refine ⟨hg.1, hg.2, fun t ht => ?_⟩
  have e : (fun p => Zh (t, p) ω) = fun p => ZE hT.le κ (pathC T B' hB'c ω, X ω) (pr4 (t, p)) +
      Ddet κ γ (drive κ B ω) (t, p) := by
    funext p; simp only [hZh, hg, and_self, ↓reduceIte]; rfl
  rw [← e]
  exact (hreg t ht).1

end CfgFM
end QuantumZipper.E6
