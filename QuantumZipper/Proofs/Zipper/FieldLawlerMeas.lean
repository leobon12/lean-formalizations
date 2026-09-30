import QuantumZipper.Proofs.Zipper.FieldLawlerDefs
import QuantumZipper.Proofs.Thm18.LWFarFjordRestart
import QuantumZipper.Proofs.Thm18.LWRenew2HitAdapt
import QuantumZipper.Proofs.Thm18.LWRenew2HitStop
import QuantumZipper.Proofs.Zipper.RegContDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM, strong Markov bookkeeping: natural filtration and the `𝓕_σ`-measurable target set

For the strong Markov step of Field–Lawler, *Escape probability and transience for SLE*,
EJP 20 (2015), proof of Prop. 3.4 (p. 8: "`P{γ(ρ,∞) ∩ C_r ≠ ∅ | γ_ρ}`"), the target set after the
stopping time `σ` is `V ω = Z_σ(H_σ ∩ B(0, ε)) = {p ∈ ℍ : ‖Z_σ⁻¹(p)‖ < ε}`. The restart estimate
`LWFar.lwf_restart_hit_le` needs `V` open and `𝓕_σ ⊗ Borel`-measurable. We prove:
* `natFilt`, `smSetup_natFilt`: the natural filtration of a Brownian motion with continuous paths;
* `measurable_fwdMapInv_stop`: `ω ↦ Z_σ⁻¹(p)` is `𝓕_σ`-measurable (`p ∈ ℍ` fixed): the process
  `t ↦ Z_t⁻¹(p)` is adapted (`measurable_fwdMapInv_adapt`) and continuous
  (`RegCont.continuousOn_fwdMapInv_time`), hence progressive;
* `measurableSet_invBall`, `isOpen_invBall`: joint measurability (Carathéodory,
  `measurable_uncurry_of_continuous_of_measurable`) and openness.
Own elementary bookkeeping (standard measure theory; FL do not discuss measurability).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- The natural filtration of a real process with measurable coordinates. -/
def natFilt {Ω : Type} [mΩ : MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (hBm : ∀ t, Measurable (B t)) : Filtration ℝ≥0 mΩ where
  seq t := MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi
  mono' s t hst := by
    have hf : (fun ω (r : Set.Iic s) => B r ω) =
        (fun (y : Set.Iic t → ℝ) (r : Set.Iic s) => y ⟨r, le_trans r.2 hst⟩) ∘
          (fun ω (r : Set.Iic t) => B r ω) := rfl
    show MeasurableSpace.comap _ _ ≤ MeasurableSpace.comap _ _
    rw [hf, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      (measurable_pi_iff.2 fun r => measurable_pi_apply _).comap_le
  le' t := (measurable_pi_iff.2 fun (r : Set.Iic t) => hBm (r : ℝ≥0)).comap_le

theorem smSetup_natFilt {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) : SMSetup P B (natFilt B hBm) :=
  ⟨hB, hBc, hBm, hB0, fun _ => rfl⟩

/-- `t ↦ Z_t⁻¹(p)` is continuous on `ℝ≥0` for `p ∈ ℍ`. -/
theorem continuous_fwdMapInv_nnreal {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {p : ℂ}
    (hp : 0 < p.im) : Continuous fun t : ℝ≥0 => fwdMapInv W t p := by
  rw [continuous_iff_continuousAt]
  intro t0
  have hon := RegCont.continuousOn_fwdMapInv_time hW hW0 (T := (t0 : ℝ) + 1) (u := p) hp
  have h2 : ContinuousOn (fun t : ℝ≥0 => fwdMapInv W (t : ℝ) p) (Set.Iic (t0 + 1)) :=
    hon.comp NNReal.continuous_coe.continuousOn fun t ht =>
      ⟨t.2, by simpa using (show (t : ℝ) ≤ ((t0 + 1 : ℝ≥0) : ℝ) from by exact_mod_cast ht)⟩
  exact h2.continuousAt (Iic_mem_nhds (lt_add_one t0))

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- `ω ↦ Z_σ⁻¹(p)` is `𝓕_σ`-measurable. -/
theorem measurable_fwdMapInv_stop (hS : SMSetup P B 𝓕) (κ : ℝ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ≥0))) {p : ℂ} (hp : 0 < p.im) :
    Measurable[hσ.measurableSpace] (fun ω => fwdMapInv (drive κ B ω) (σ ω) p) := by
  set X : ℝ≥0 → Ω → ℂ := fun t ω => fwdMapInv (drive κ B ω) t p with hX
  have hXc : ∀ ω, Continuous fun t => X t ω := fun ω =>
    continuous_fwdMapInv_nnreal (drive_continuous (hS.cont ω)) (drive_zero (hS.zero ω)) hp
  have hprog : IsStronglyProgressive 𝓕 X :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => (measurable_fwdMapInv_adapt hS κ t hp).stronglyMeasurable) hXc
  have h := measurable_stoppedValue hprog hσ
  convert h using 1
  funext ω
  rfl

/-- Carathéodory: the set `{(ω, p) : p ∈ ℍ, ‖F ω p‖ < ε}` is measurable when `F ω` is continuous
on `ℍ` and `F · p` is measurable. -/
theorem measurableSet_invBall_of {Ω' : Type} [MeasurableSpace Ω'] (F : Ω' → ℂ → ℂ)
    (hc : ∀ ω, ContinuousOn (F ω) H) (hm : ∀ p : ℂ, 0 < p.im → Measurable fun ω => F ω p)
    (ε : ℝ) : MeasurableSet {q : Ω' × ℂ | q.2 ∈ {p : ℂ | 0 < p.im ∧ ‖F q.1 p‖ < ε}} := by
  classical
  set u : {p : ℂ // 0 < p.im} → Ω' → ℂ := fun p ω => F ω p.1 with hu
  have hcont : ∀ ω, Continuous fun p => u p ω := fun ω =>
    (hc ω).comp_continuous continuous_subtype_val fun p => p.2
  have huu : Measurable (Function.uncurry u) :=
    measurable_uncurry_of_continuous_of_measurable hcont fun p => hm p.1 p.2
  set S : Set (Ω' × ℂ) := {q | 0 < q.2.im} with hSdef
  have hSm : MeasurableSet S :=
    measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_snd)
  set G : Ω' × ℂ → ℝ := fun q =>
    if hq : q ∈ S then ‖Function.uncurry u (⟨q.2, hq⟩, q.1)‖ else ε with hG
  have hGm : Measurable G := by
    refine Measurable.dite (f := fun x : S => ‖Function.uncurry u (⟨x.1.2, x.2⟩, x.1.1)‖)
      (g := fun _ => ε) ?_ measurable_const hSm
    refine (huu.comp ?_).norm
    exact ((measurable_snd.comp measurable_subtype_coe).subtype_mk).prodMk
      (measurable_fst.comp measurable_subtype_coe)
  have he : {q : Ω' × ℂ | q.2 ∈ {p : ℂ | 0 < p.im ∧ ‖F q.1 p‖ < ε}} = {q | G q < ε} := by
    ext q
    simp only [mem_setOf_eq, hG]
    by_cases hq : q ∈ S
    · rw [dif_pos hq]
      exact ⟨fun h => h.2, fun h => ⟨hq, h⟩⟩
    · rw [dif_neg hq]
      exact ⟨fun h => absurd h.1 hq, fun h => absurd h (lt_irrefl ε)⟩
  rw [he]
  exact measurableSet_lt hGm measurable_const

theorem isOpen_invBall {F : ℂ → ℂ} (hc : ContinuousOn F H) (ε : ℝ) :
    IsOpen {p : ℂ | 0 < p.im ∧ ‖F p‖ < ε} := by
  have h := hc.isOpen_inter_preimage isOpen_H (isOpen_ball (x := (0 : ℂ)) (ε := ε))
  convert h using 1
  ext p
  simp [H]

/-- `Z_t⁻¹` is continuous on `ℍ`. -/
theorem continuousOn_fwdMapInv_H' {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) : ContinuousOn (fwdMapInv W t) H := fun p hp =>
  (RS.continuousAt_fwdMapInv hW hW0 ht hp).continuousWithinAt

/-- **The target set after `σ` is `𝓕_σ ⊗ Borel`-measurable.** -/
theorem measurableSet_invBall (hS : SMSetup P B 𝓕) (κ : ℝ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ≥0))) (ε : ℝ) :
    MeasurableSet[@Prod.instMeasurableSpace Ω ℂ hσ.measurableSpace _]
      {q : Ω × ℂ | q.2 ∈ {p : ℂ | 0 < p.im ∧
        ‖fwdMapInv (drive κ B q.1) (σ q.1) p‖ < ε}} :=
  @measurableSet_invBall_of Ω hσ.measurableSpace (fun ω p => fwdMapInv (drive κ B ω) (σ ω) p)
    (fun ω => continuousOn_fwdMapInv_H' (drive_continuous (hS.cont ω))
      (drive_zero (hS.zero ω)) (σ ω).2)
    (fun _ hq => measurable_fwdMapInv_stop hS κ hσ hq) ε

end FieldLawler
end QuantumZipper
