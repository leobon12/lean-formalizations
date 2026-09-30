import QuantumZipper.Proofs.NonVacuityFinal
import QuantumZipper.Proofs.Thm18.Assembly
import QuantumZipper.Proofs.Thm18.R18ReadMeas
import QuantumZipper.Proofs.Thm18.RT5OMain
import QuantumZipper.Proofs.Thm18.Thm18PaperMOBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Non-vacuity certificate for Theorem 1.8 (paper form, `Statements/Thm18PaperMO.lean`)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (p. 26). As
`Final13NonVacuity.lean` does for Theorems 1.3–1.5 (handoff/FINAL-13.md §2):

* **Hypotheses satisfiable** (`thm18_hypotheses_satisfiable`): for every `γ ∈ (0,2)` some
  probability space `Ω : Type` carries a Brownian motion `B` and an independent
  `(γ − 2/γ)`-quantum wedge `Y` (`NonVacuity.exists_wedge_indep_BM_uncond`), and then
  `Thm18Setting` and `Thm18Inputs` hold (`Thm18Asm.thm18Inputs_of_setting`).
* **Laws genuine** (`configLawOff_wedge_ne_dirac`, `aemeasurable_zip_of_lawInv`,
  `theorem1_8PaperMO_laws_genuine`): the law of the masked initial configuration is never a Dirac
  mass (its driver at time `1` is `γ B₁`, atomless), so clause (3) forces every zipped
  configuration to be a.e.-measurable, i.e. clause (3) is not the `Measure.map` junk
  (`map_of_not_aemeasurable_of_ne_zero` gives a Dirac mass at this pin).
* **Zip maps genuine** (`ae_lenWeldDriverO_eq_global`, `ae_isLenWeldingDriver_of_clause1`): a.s.
  the open-arc driver used by `Z^LEN_ℓ` at the wedge configuration is the global length-welding
  driver of `Y ω` (D86 bridge); under clause (1) it is a genuine length-welding driver (not the
  `Classical.epsilon` junk), with left welding point of quantum length `ℓ > 0`.
* **Lengths**: clause "lengths agree" itself asserts `0 < length < ⊤` for `t > 0`, so it cannot
  hold as `0 = 0` or `⊤ = ⊤`; nothing to certify separately.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Final18

open Thm18Asm

/-- **The hypotheses of Theorem 1.8 are satisfiable.** -/
theorem thm18_hypotheses_satisfiable {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
      (Y : Ω → FieldSample),
      IsProbabilityMeasure P ∧ IsBrownianReal B P ∧ IsQuantumWedge γ (γ - 2 / γ) Y P ∧
        IndepFun (pathOf B) Y P ∧ Thm18Setting γ P B Y ∧ Thm18Inputs γ P B Y := by
  obtain ⟨Ω, m, P, Y, B, hP, hY, hB, hI⟩ :=
    NonVacuity.exists_wedge_indep_BM_uncond (alpha_lt_Qc hγ hγ2)
  have hS : Thm18Setting γ P B Y := ⟨hγ, hγ2, hB, hY, hI⟩
  exact ⟨Ω, m, P, B, Y, hP, hB, hY, hI, hS, thm18Inputs_of_setting hS⟩

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}

/-- **The law compared in clause (3) is not a Dirac mass**: the masked law of the initial
configuration has an atomless coordinate (the driver at time `1`, `γ B₁ ∼ N(0, γ²)`). -/
theorem configLawOff_wedge_ne_dirac (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y)
    (d : Paper18.FullData) :
    configLawOff (fun ω => (wedgeAConfig γ B Y ω).toPair) P ≠ Measure.dirac d := by
  intro hEq
  set S : Set Paper18.FullData := {q | q.2 1 = d.2 1} with hSdef
  have hSm : MeasurableSet S :=
    (measurableSet_singleton (d.2 1)).preimage ((measurable_pi_apply 1).comp measurable_snd)
  have h1 : Measure.dirac d S = 1 := by
    rw [Measure.dirac_apply' _ hSm]
    simp [hSdef]
  have hsk : Real.sqrt (γ ^ 2) ≠ 0 := by
    rw [Real.sqrt_sq_eq_abs]; exact abs_ne_zero.2 hS.1.ne'
  have h0 : configLawOff (fun ω => (wedgeAConfig γ B Y ω).toPair) P S = 0 := by
    rw [R18.configLawOff_eq_map_offData,
      Measure.map_apply_of_aemeasurable (R18.aemeasurable_offData_wedgeAConfig hS hIn) hSm]
    have hsub : (fun ω => R18.offData (wedgeAConfig γ B Y ω).toPair) ⁻¹' S ⊆
        B 1 ⁻¹' {d.2 1 / Real.sqrt (γ ^ 2)} := by
      intro ω hω
      simp only [hSdef, Set.mem_preimage, Set.mem_ofPred_eq, R18.offData, AreaConfig.toPair,
        wedgeAConfig, drive] at hω
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      rw [eq_div_iff hsk, ← hω]
      simp [mul_comm]
    refine le_antisymm (le_trans (measure_mono hsub) ?_) bot_le
    have hlaw := hS.2.2.1.hasLaw_eval 1
    have hnull : gaussianReal 0 (1 : ℝ≥0) {d.2 1 / Real.sqrt (γ ^ 2)} = 0 := by
      have := nullSingletonClass_gaussianReal (μ := 0) (v := (1 : ℝ≥0)) one_ne_zero
      exact measure_singleton _
    rw [← hlaw.map_eq, Measure.map_apply_of_aemeasurable hlaw.aemeasurable
      (measurableSet_singleton _)] at hnull
    exact hnull.le
  rw [hEq, h1] at h0
  exact one_ne_zero h0

/-- **Clause (3) compares genuine laws**: if the law of the zipped configuration equals the law
of the initial one, the zipped configuration is a.e.-measurable (otherwise its law would be the
Dirac junk, which the initial law is not). -/
theorem aemeasurable_zip_of_lawInv (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y)
    (t : ℝ)
    (h3 : configLawOff (fun ω => (Paper18.zipLenMO γ t (wedgeAConfig γ B Y ω)).toPair) P =
      configLawOff (fun ω => (wedgeAConfig γ B Y ω).toPair) P) :
    AEMeasurable (fun ω => Paper18.offData (Paper18.zipLenMO γ t (wedgeAConfig γ B Y ω)).toPair)
      P := by
  by_contra hne
  have hmap : configLawOff (fun ω => (Paper18.zipLenMO γ t (wedgeAConfig γ B Y ω)).toPair) P =
      Measure.map (fun ω => Paper18.offData (Paper18.zipLenMO γ t (wedgeAConfig γ B Y ω)).toPair)
        P := rfl
  rw [hmap, Measure.map_of_not_aemeasurable_of_ne_zero hne (IsProbabilityMeasure.ne_zero P)]
    at h3
  exact configLawOff_wedge_ne_dirac hS hIn _ h3.symm

/-- **Theorem 1.8 (paper form) compares genuine laws**: in its setting, for every `t ∈ ℝ` the
zipped configuration `Z^LEN_t c₀` is a.e.-measurable (masked data), so clause (3) is not
satisfied by `Measure.map` junk. -/
theorem theorem1_8PaperMO_laws_genuine (hT : Paper18.theorem1_8PaperMO)
    (hS : Thm18Setting γ P B Y) (t : ℝ) :
    AEMeasurable (fun ω => Paper18.offData (Paper18.zipLenMO γ t (wedgeAConfig γ B Y ω)).toPair)
      P :=
  aemeasurable_zip_of_lawInv hS (thm18Inputs_of_setting hS) t
    ((hT γ hS.1 hS.2.1 P B Y hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2).2.2.2.2 t)

/-- **The maps weld along the global driver (D86 bridge, Statements form)**: a.s., for every
`ℓ`, the open-arc driver of the pieces of the wedge configuration, used by `Z^LEN_ℓ`, is the
global length-welding driver of `Y ω` read in clause (1). -/
theorem ae_lenWeldDriverO_eq_global (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) :
    ∀ᵐ ω ∂P, ∀ ℓ : ℝ,
      Paper18.lenWeldDriverO γ (Paper18.offConfig γ (wedgeAConfig γ B Y ω)).fld ℓ =
        lenWeldDriver γ (Y ω) ℓ :=
  R18.ae_lenWeldDriverO_offConfig_wedge hS hIn

/-- **The zip maps are not `Classical.epsilon` junk**: under clause (1) of Theorem 1.8, for
`ℓ > 0`, a.s. the driver along which `Z^LEN_ℓ` welds the pieces of the wedge configuration is a
genuine length-welding driver of `Y ω`, whose left welding point cuts off quantum length `ℓ > 0`. -/
theorem ae_isLenWeldingDriver_of_clause1 (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y)
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    (h1 : ∀ᵐ ω ∂P, (∃ p : ℝ × (ℝ → ℝ), IsLenWeldingDriver γ (Y ω) ℓ p) ∧
      qBoundaryMeasure γ (Y ω) (Set.Icc (lenWeldPoint γ (Y ω) ℓ) 0) = ENNReal.ofReal ℓ) :
    ∀ᵐ ω ∂P,
      IsLenWeldingDriver γ (Y ω) ℓ
          (Paper18.lenWeldDriverO γ (Paper18.offConfig γ (wedgeAConfig γ B Y ω)).fld ℓ) ∧
        0 < qBoundaryMeasure γ (Y ω) (Set.Icc (lenWeldPoint γ (Y ω) ℓ) 0) := by
  filter_upwards [h1, ae_lenWeldDriverO_eq_global hS hIn] with ω hω he
  rw [he ℓ, hω.2]
  exact ⟨Classical.epsilon_spec hω.1, ENNReal.ofReal_pos.2 hℓ⟩

end Final18
end QuantumZipper
