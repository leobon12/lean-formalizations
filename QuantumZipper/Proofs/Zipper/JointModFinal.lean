import QuantumZipper.Proofs.Zipper.JointModComm
import QuantumZipper.Proofs.Zipper.RegUnifCocycle

/-!
# JOINTMOD: `JointModStmt` proved

`jointModStmt_holds`: for a Brownian motion `B`, a free-boundary GFF `X` modulo constants with
`pathOf B ⟂ X`, and `T > 0`, the raw values `(t, c, r) ↦ y_t(fc(c,r))` of the unzipped field
`y_t = unzippedField γ (h⁰ + X, drive κ B) t` have a modification that is continuous on
`[0,T] × Hbar × (0,∞)` for every `ω` and satisfies the circle commutation a.s. at each
`(t, w, r, ρ)`, i.e. `RegUnif.JointModStmt κ γ T P B X`.

The modification is `Zh = ZE ∘ pr4 + Ddet` on the event that the driver is continuous and
vanishes at `0` (and `0` elsewhere): `ZE` is the continuous extension of the free-field part
(`JointModRandom`), `Ddet` the deterministic part (`JointModAssembly`, continuity
`detContStmt_holds`); commutation from `ae_comm_ZE` and `integral_Ddet_swap` (`JointModComm`).

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1; Revuz–Yor, 3rd ed., Ch. I,
Thm (2.1); see the component files for the own elementary arguments.
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Real ENNReal NNReal

namespace QuantumZipper
namespace RegUnif

open CharFun RegCont RegSample

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **`JointModStmt` holds.** -/
theorem jointModStmt_holds [IsProbabilityMeasure P] (κ γ : ℝ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    {T : ℝ} (hT : 0 < T) : JointModStmt κ γ T P B X := by
  classical
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := exists_good_version hB
  have hpath : pathOf B =ᵐ[P] pathOf B' := hB'eq.mono fun ω h => funext fun t => (h t).symm
  have hind' : IndepFun (pathC T B' hB'c) X P :=
    indepFun_pathC T (hind.congr hpath (ae_eq_refl _)) hB'c
  set Zr : (Fin 4 → ℝ) → Ω → ℝ := fun q ω => ZE hT.le κ (pathC T B' hB'c ω, X ω) q with hZr
  have hZc : ∀ ω, Continuous fun q => Zr q ω := fun ω => continuous_ZE hT.le κ _
  have hZt := ae_tendsto_ZE κ hB hX hB'm hB'c hB'eq hind' hT
  have hdet := detContStmt_holds κ γ T
  refine ⟨fun p ω => if Continuous (drive κ B ω) ∧ drive κ B ω 0 = 0 then
    Zr (pr4 p) ω + Ddet κ γ (drive κ B ω) p else 0, fun ω => ?_, fun p hp => ?_, ?_⟩
  · by_cases h : Continuous (drive κ B ω) ∧ drive κ B ω 0 = 0
    · simp only [h, and_self, ↓reduceIte]
      exact ((hZc ω).comp_continuousOn (continuousOn_pr4 T)).add (hdet _ h.1 h.2)
    · simp only [h, ↓reduceIte]
      exact continuousOn_const
  · filter_upwards [ae_raw_eq κ γ hB hX hZt hp, ae_drive_good hB κ] with ω h1 h2
    simp only [h2, and_self, ↓reduceIte]
    exact h1.symm
  · intro t ht w hw r ρ hr hρ
    filter_upwards [ae_comm_ZE κ hB hX hB'm hB'c hB'eq hind' hT ht hw hr hρ,
      ae_drive_good hB κ] with ω h1 h2
    simp only [h2, and_self, ↓reduceIte]
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

/-- **Regularity of the unzipped field for all `t ≥ 0` at once** (unconditional). -/
theorem ae_forall_isRegularSample [IsProbabilityMeasure P] {κ γ : ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      IsRegularSample (unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) t) ∧
      LocalRule.RawConverges (unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) t) univ :=
  ae_forall_isRegularSample_of_jointMod hB hX hind fun n =>
    jointModStmt_holds κ γ hB hX hind (by positivity)

/-- `B3d.CapCocycleRegStmt` from `UnifRC3Stmt` alone (`JointModStmt` now proved). -/
theorem capCocycleRegStmt_of_unifRC3' [IsProbabilityMeasure P] {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hT : 0 < T) (hU : UnifRC3Stmt κ T P B X) : B3d.CapCocycleRegStmt κ T P B X :=
  capCocycleRegStmt_of_unifRC3 hB hX hind hT (jointModStmt_holds κ _ hB hX hind hT) hU

end RegUnif
end QuantumZipper
