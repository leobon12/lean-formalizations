/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CovCut

/-!
# The actual restart fibre: what the disintegration of the glued space must supply

Packet PROVE-AUX61-R2C. Astra's follow-up 4 §§1.1–1.3 (`source/external/AstraIG1/ig1_followup4_audited.txt`
L82–L262, ruling R71). PROVE-AUX61-R2's target `Aux61R2.RefClockFibreCoverOn` asks, per fibre, for a `RefFibre`
(with a fixed odd cutoff `Fq` of `q`), a clock source and a reference clock, and locality of the hulls under the
canonical tilt. Here every derived item is constructed, so that a fibre is exactly the data the regular conditional
law of the glued space at a separated rational restart provides:

* **`ActFibre S`**: a clock source started at `0` (the restarted path, its killed driver, lifetime and generating
  trace) with a reference clock of the reference word `b̂` (seed `0`, angle `0`) and window `V` (built by
  PROVE-AUX61-R45's `ClockSource.exists_referenceClock(_of_retained)`); the field read in the restart chart; the
  relative mean `q = M − M^c` at the restart, harmonic on `ℍ` with zero boundary values on a real window `O₀`; a
  buffer whose compact closure meets `ℝ` only in `O₀` and contains the pre-clock hulls; the **kernel** (Aux. lemma 61
  relative to the reference word, in cutoff form, for *every* cutoff of `q` on a neighbourhood of the buffer); the
  **actual locality** of the pre-clock hulls; and a.s. **injectivity** of the path through the clock;
* `ActFibre.toRefFibre`: the cutoff is chosen by `exists_cmCut_of_harmonic` (Schwarz reflection);
  **`ActFibre.exists_covFibre`**: the per-fibre clause of `HasCovFibreCover`;
* `HasActFibreCover`, **`hasCovFibreCover_of_act`**, `ActFibreCoverOn` (glued space),
  **`restartWindowNullQOn_of_actCover`**, **`fwdNoEastCrosscutTgtQOn_of_actCover_smallGap`**,
  `refClockFibreCoverOn_of_act` (PROVE-AUX61-R2's target follows).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Cov

open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open LocalExt (cfVal)
open Restart.FlowStopIdentCMI (CMCut)
open Aux61Win (meanF IsCutoffOn)
open Aux61R2
open Sec7.PocketTraversal

universe u

/-- **The actual restart fibre** (see the module docstring): the per-fibre output of the disintegration of the
glued space at one separated rational restart, before any choice of cutoff, tilt or clock data. -/
structure ActFibre (S : Type u) [m : MeasurableSpace S] where
  κ : ℝ
  κ_pos : 0 < κ
  bR : ℝ → ℝ
  JR : Finset ℝ
  CS : Aux61R45.ClockSource S
  y_zero : CS.y = 0
  V : Set ℂ
  RC : Aux61R45.ReferenceClock CS κ bR JR 0 V
  field : S → DistOn upperHalfPlaneOpens
  measurable_field : Measurable field
  q : ℂ → ℝ
  q_harm : InnerProductSpace.HarmonicOnNhd q H
  O₀ : Set ℝ
  O₀_open : IsOpen O₀
  q_zero : ∀ x ∈ O₀, Tendsto q (𝓝[H] (x : ℂ)) (𝓝 0)
  buffer : Set ℂ
  buffer_open : IsOpen buffer
  zero_mem : (0 : ℂ) ∈ buffer
  buffer_compact : IsCompact (closure buffer)
  buffer_real : ∀ z ∈ closure buffer, z.im = 0 → z.re ∈ O₀
  hull_buffer : ∀ᵐ ω ∂CS.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < RC.e ω →
    closure (fwdHull (Ito.rpath (RC.W · ω)) t) ⊆ buffer
  kernel : ∀ (F : CMCut) (N : Set ℂ), IsCutoffOn F q N O₀ → buffer ⊆ N →
    ∀ (τ : S → WithTop ℝ≥0) (hτ : IsStoppingTime CS.driving τ), (∀ᵐ ω ∂CS.P, (τ ω : ℝ≥0∞) < RC.e ω) →
    ∀ u : S → ℂ → ℝ, (∀ ω, RefExt κ bR JR RC.W ((τ ω).untopD 0) ω (u ω)) →
    ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂CS.P,
      Disjoint (tsupport ψ) (fwdHull (Ito.rpath (RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) →
      CS.P[fun ω' => Complex.exp (Complex.I * (field ω' ψ : ℂ)) | hτ.measurableSpace] ω =
        cfVal (∫ z, meanF κ (u ω) q F (Ito.rpath (RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0) z * ψ z)
          (loewnerGreenEnergy (Ito.rpath (RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0) ψ)
  locality : ∀ (τ : S → WithTop ℝ≥0) (_ : IsStoppingTime CS.driving τ),
    (∀ᵐ ω ∂CS.P, (τ ω : ℝ≥0∞) < RC.e ω) →
    IsLocalSet (fun ω => fwdHull (Ito.rpath (RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) field CS.P
  injective : ∀ᵐ ω ∂CS.P, InjOn (CS.Γ ω) {t | (t : ℝ≥0∞) ≤ RC.e ω}

namespace ActFibre

variable {S : Type u} [mS : MeasurableSpace S] (D : ActFibre S)

/-- The cutoff data of the fibre exist (Schwarz reflection of `q` across `O₀`). -/
theorem exists_cut : ∃ (N : Set ℂ) (F : CMCut) (C : ℝ), closure D.buffer ⊆ N ∧ IsCutoffOn F D.q N D.O₀ ∧
    ∀ z, F.src z ≠ 0 → |D.q z| ≤ C :=
  exists_cmCut_of_harmonic D.O₀_open D.q_harm D.q_zero D.buffer_compact D.buffer_real

/-- The chosen neighbourhood of the buffer. -/
def Nq : Set ℂ := D.exists_cut.choose

/-- The chosen cutoff of `q`. -/
def Fq : CMCut := D.exists_cut.choose_spec.choose

/-- The chosen bound of `q` on the source of the cutoff. -/
def Cq : ℝ := D.exists_cut.choose_spec.choose_spec.choose

theorem cut_spec : closure D.buffer ⊆ D.Nq ∧ IsCutoffOn D.Fq D.q D.Nq D.O₀ ∧
    ∀ z, D.Fq.src z ≠ 0 → |D.q z| ≤ D.Cq :=
  D.exists_cut.choose_spec.choose_spec.choose_spec

theorem buffer_sub : D.buffer ⊆ D.Nq := subset_closure.trans D.cut_spec.1

/-- **The corrected restart fibre of an actual fibre** (the chosen cutoff; driver, clock and filtration from the
reference clock and the clock source). -/
def toRefFibre : RefFibre S where
  κ := D.κ
  κ_pos := D.κ_pos
  bR := D.bR
  JR := D.JR
  P := D.CS.P
  prob := D.CS.prob
  field := D.field
  measurable_field := D.measurable_field
  q := D.q
  q_cont := D.q_harm.contDiffOn.continuousOn
  O₀ := D.O₀
  Fq := D.Fq
  Nq := D.Nq
  cut := D.cut_spec.2.1
  Cq := D.Cq
  q_bdd := D.cut_spec.2.2
  buffer := D.buffer
  buffer_open := D.buffer_open
  zero_mem := D.zero_mem
  buffer_sub := D.buffer_sub
  W := D.RC.W
  zero := D.RC.zero
  continuous := D.RC.continuous
  filt := D.CS.driving
  e := D.RC.e
  hull_buffer := D.hull_buffer
  kernel := fun τ hτ hτe u hu ψ => D.kernel D.Fq D.Nq D.cut_spec.2.1 D.buffer_sub τ hτ hτe u hu ψ

theorem toRefFibre_isActualLocal : D.toRefFibre.IsActualLocal := D.locality

/-- **The per-fibre clause of `HasCovFibreCover`** for an actual fibre. -/
theorem exists_covFibre : ∃ (R : RefFibre S) (CS : Aux61R45.ClockSource S) (V : Set ℂ)
    (RC : Aux61R45.ReferenceClock CS R.κ R.bR R.JR 0 V),
    R.P = D.CS.P ∧ CS.y = 0 ∧ R.P = CS.P ∧ R.W = RC.W ∧ R.e = RC.e ∧ R.filt = CS.driving ∧
      InnerProductSpace.HarmonicOnNhd R.q H ∧ R.IsActualLocal ∧
      (∀ᵐ ω ∂R.P, InjOn (CS.Γ ω) {t | (t : ℝ≥0∞) ≤ R.e ω}) ∧ R.κ = D.κ ∧ R.bR = D.bR ∧ R.JR = D.JR ∧
      CS = D.CS ∧ R.e = D.RC.e :=
  ⟨D.toRefFibre, D.CS, D.V, D.RC, rfl, D.y_zero, rfl, rfl, rfl, rfl, D.q_harm, D.toRefFibre_isActualLocal,
    D.injective, rfl, rfl, rfl, rfl, rfl⟩

end ActFibre

/-- **The cover by actual fibres** (the R2 target in the form the disintegration of the glued space produces). -/
def HasActFibreCover {X : Type u} [MeasurableSpace X] (μ : Measure X) (E : X → Prop)
    (Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (A : ι → Set X) (S : Type u) (_ : MeasurableSpace S) (κ : ι → Kernel X S)
    (L : ι → Set S),
    (∀ i, MeasurableSet (A i)) ∧ (∀ᵐ x ∂μ, E x → ∃ i, x ∈ A i) ∧
    (∀ i, μ (A i ∩ {x | E x}) ≤ ∫⁻ x in A i, κ i x (L i) ∂μ) ∧
    ∀ i, ∀ᵐ x ∂μ, x ∈ A i → ∃ (D : ActFibre S) (I : Set ℝ),
      D.CS.P = κ i x ∧ Ref D.κ D.bR D.JR I ∧
      ∀ ω ∈ L i, ∃ v : ℝ≥0, (v : ℝ≥0∞) ≤ D.RC.e ω ∧ ∃ y ∈ I, D.CS.Γ ω v = (y : ℂ)

/-- **Actual fibres give the cover with actual locality.** -/
theorem hasCovFibreCover_of_act {X : Type u} [MeasurableSpace X] {μ : Measure X} {E : X → Prop}
    {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop} (hcov : HasActFibreCover μ E Ref) :
    HasCovFibreCover μ E Ref := by
  obtain ⟨ι, hι, A, S, mS, κ, L, hAm, hcover, hdis, hfib⟩ := hcov
  refine ⟨ι, hι, A, S, mS, κ, L, hAm, hcover, hdis, fun i => ?_⟩
  filter_upwards [hfib i] with x hx hxA
  obtain ⟨D, I, hPx, hRef, hL⟩ := hx hxA
  exact ⟨D.toRefFibre, D.CS, D.V, D.RC, I, hPx, D.y_zero, rfl, rfl, rfl, rfl, D.q_harm,
    D.toRefFibre_isActualLocal, D.injective, hRef, hL⟩

/-! ### On the glued space -/

section Glued

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique Cond44Ref Prop51Q CfAvoidLeftQ Prop51G Aux61Kernel
open QuantumZipper (chiC)

/-- **The R2 target on the glued space by actual fibres**: same binders as `Aux61R2.RefClockFibreCoverOn`, with
`HasActFibreCover`. -/
def ActFibreCoverOn (G : ℝ → ℝ → ℝ → Prop) (Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop) : Prop :=
  ∀ (t : ℚ) (c : WinCode), 0 < t →
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ → G κ θ₁ θ₂ →
    sleLambda κ - θ₁ * chiC κ ≤ b → sleLambda κ - Real.pi * chiC κ + θ₂ * chiC κ ≤ a →
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ →
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
        P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂ →
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
          ∀ s : ℚ, 0 < s →
            HasActFibreCover.{u}
              (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
                ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)))
              (fun p => RestartWindowEvent (Prop411Q.cfDrv p.2) s (fun u : ℝ => η p.1 u.toNNReal) t c) Ref

theorem covFibreCoverOn_of_act {G : ℝ → ℝ → ℝ → Prop} {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop}
    (hcov : ActFibreCoverOn.{u} G Ref) : CovFibreCoverOn.{u} G Ref := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  exact hasCovFibreCover_of_act (hcov t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf
    hlaw k hk s hs)

/-- PROVE-AUX61-R2's target follows from the actual-fibre target. -/
theorem refClockFibreCoverOn_of_act {G : ℝ → ℝ → ℝ → Prop} {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop}
    (hcov : ActFibreCoverOn.{u} G Ref) : RefClockFibreCoverOn.{u} G Ref :=
  refClockFibreCoverOn_of_cov (covFibreCoverOn_of_act hcov)

/-- **R23's named input from actual fibres and R5 in reference-setting form.** -/
theorem restartWindowNullQOn_of_actCover {G : ℝ → ℝ → ℝ → Prop} {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop}
    (hcov : ActFibreCoverOn.{u} G Ref) (hR5 : IsSettingAvoiding.{u} Ref) : RestartWindowNullQOn.{u} G :=
  restartWindowNullQOn_of_covCover (covFibreCoverOn_of_act hcov) hR5

/-- **(E1) in target-component form for every angle pair** from actual fibres below the critical gap and R5 in
reference-setting form (with the counterflow regularity from Part A). -/
theorem fwdNoEastCrosscutTgtQOn_of_actCover_smallGap {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop}
    (hreg : Prop51Q.CfLineRegularQStatement.{u})
    (hcov : ActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) Ref) (hR5 : IsSettingAvoiding.{u} Ref) :
    FwdNoEastCrosscutTgtQOn.{u} fun _ _ _ => True :=
  fwdNoEastCrosscutTgtQOn_of_covCover_smallGap hreg (covFibreCoverOn_of_act hcov) hR5

end Glued

end InteractingSLE.Sec5.Aux61Cov
