/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R2Cover
import InteractingSLE.Spec.Sec5.Aux61R45Reference
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvWTilt

/-!
# The restart-fibre cover with actual locality and per-fibre GB7a (R2f and R5 discharged)

Packet PROVE-AUX61-R2C. Astra's follow-up 4 §1.3 (`source/external/AstraIG1/ig1_followup4_audited.txt` L190–L262,
ruling R71). Two of the per-fibre obligations of PROVE-AUX61-R2's target `Aux61R2.RefClockFibreCoverOn` are
discharged here:

* **R2f (locality under the tilt).** The canonical tilt of a fibre adds the deterministic function `Fq − q`; a local
  set of the fibre's own field stays local for the shifted field under the tilt
  (`Restart.FlowStopIdentCMI.isLocalSet_withDensity_cmiCut`), provided `q` is harmonic on `ℍ`. So
  `RefFibre.IsTiltLocal` follows from **actual locality** (`RefFibre.IsActualLocal`: the pre-clock hulls are local
  sets of the fibre's field under the fibre's law, which is what the union kernel on the glued space gives) and the
  harmonicity of `q` (`RefFibre.isTiltLocal_of_actual`).
* **R5 (reference avoidance), positive side.** Instead of `Aux61Win.IsAvoidingRef` (every stopped flow line of the
  reference word avoids `I`), each fibre already carries a reference clock, so the tilted fibre is a
  `Aux61R45.ReferenceSetting`, and PROVE-AUX61-R45's GB7a for announced stopped references
  (`ReferenceSetting.ae_avoid_intervals`) applies directly. The reference predicate is consumed in reference-setting
  form (`IsSettingAvoiding`); Aux. lemma 64's word (`RefPos`: an interval right of the seed whose reference height
  `v` has `κ/2 − 2 ≤ v/λ − 1`) satisfies it (`isSettingAvoiding_refPos`). The fibres must record a.s. injectivity of the
  path through the clock (flow lines below `κ = 4` are simple).

Main results: `HasCovFibreCover`, **`ae_not_of_hasCovFibreCover`**, `hasRefClockFibreCover_of_cov` (the new cover
implies PROVE-AUX61-R2's), `CovFibreCoverOn`, **`restartWindowNullQOn_of_covCover`**,
**`fwdNoEastCrosscutTgtQOn_of_covCover_smallGap`**, `IsSettingAvoiding.or`.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5

open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)
open Sec7.PocketTraversal

universe u

namespace Aux61R2.RefFibre

variable {S : Type u} [mS : MeasurableSpace S] (D : RefFibre S)

/-- **Actual locality of the pre-clock hulls**: at every stop `τ < e` of the fibre's filtration, the hull is a local
set of the fibre's own field under the fibre's own law (the union kernel's locality on the glued space). -/
def IsActualLocal : Prop :=
  ∀ (τ : S → WithTop ℝ≥0) (_ : IsStoppingTime D.filt τ), (∀ᵐ ω ∂D.P, (τ ω : ℝ≥0∞) < D.e ω) →
    IsLocalSet (fun ω => fwdHull (Ito.rpath (D.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) D.field D.P

variable {D}

/-- The canonical tilt and the fibre's law are equivalent. -/
theorem canonTilt_equivalent (he0 : ∀ᵐ ω ∂D.P, 0 < D.e ω) : D.canonTilt ≪ D.P ∧ D.P ≪ D.canonTilt := by
  rw [← D.tiltData_tilt he0]
  exact (tiltData he0).tilt_equivalent

/-- **R2f from actual locality**: if `q` is harmonic on `ℍ` and the pre-clock hulls are local for the fibre's field,
they are local for the shifted field `h + (Fq − q)` under the canonical tilt. -/
theorem isTiltLocal_of_actual (he0 : ∀ᵐ ω ∂D.P, 0 < D.e ω) (hq : InnerProductSpace.HarmonicOnNhd D.q H)
    (hloc : D.IsActualLocal) : D.IsTiltLocal := by
  intro τ hτ hτe
  let _ := D.prob
  have hA := hloc τ hτ ((canonTilt_equivalent he0).2.ae_le hτe)
  have hprob := isProbabilityMeasure_tilt he0
  have h := Restart.FlowStopIdentCMI.isLocalSet_withDensity_cmiCut hA D.measurable_field D.Fq.neg
    (fun n z => D.Fq.neg.abs_testSeq_le n z) (fun z => D.Fq.neg.tendsto_testSeq z) (ae_tendsto_Λ he0)
    (inv_pos.2 (integral_exp_neg_Λ_pos he0)) hprob hq.neg
  have hf : (fun z => (-D.q) z - D.Fq.neg.f z) = fun z => D.Fq.f z - D.q z := by
    funext z
    simp only [Pi.neg_apply, Restart.FlowStopIdentCMI.CMCut.neg_f]
    ring
  rw [hf] at h
  exact h

end Aux61R2.RefFibre

namespace Aux61Cov

open Aux61R2

/-! ### R5 in reference-setting form -/

/-- **Reference avoidance for announced stopped references** (R5 in the form the fibres use): every
`Aux61R45.ReferenceSetting` with seed `0` and angle `0` whose word satisfies `Ref` with the set `I`, and whose path is
a.s. injective through the clock, a.s. does not visit `I` up to and including the clock. -/
def IsSettingAvoiding (Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop) : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (R : Aux61R45.ReferenceSetting S) (I : Set ℝ), R.y = 0 → R.θ = 0 →
    Ref R.κ R.b R.J I → (∀ᵐ ω ∂R.P, InjOn (R.Γ ω) {t | (t : ℝ≥0∞) ≤ R.e ω}) →
    ∀ᵐ ω ∂R.P, ∀ v : ℝ≥0, (v : ℝ≥0∞) ≤ R.e ω → ∀ y ∈ I, R.Γ ω v ≠ (y : ℂ)

/-- Reference avoidance is closed under disjunction of the reference predicates. -/
theorem IsSettingAvoiding.or {Ref₁ Ref₂ : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop}
    (h₁ : IsSettingAvoiding.{u} Ref₁) (h₂ : IsSettingAvoiding.{u} Ref₂) :
    IsSettingAvoiding.{u} fun κ b J I => Ref₁ κ b J I ∨ Ref₂ κ b J I := by
  intro S _ R I hy hθ hRef hinj
  rcases hRef with h | h
  · exact h₁ R I hy hθ h hinj
  · exact h₂ R I hy hθ h hinj

/-- **Aux. lemma 64's reference word** (Astra's follow-up 4 L191–L195): `κ ≤ 4`, piecewise constant data, and `I` an
open interval right of the seed on which the reference height `v` satisfies `κ/2 − 2 ≤ v/λ − 1` (that is,
`v ≥ λ − πχ`). -/
def RefPos (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (I : Set ℝ) : Prop :=
  κ ≤ 4 ∧ IsPiecewiseConstantBoundaryData b J ∧ ∃ a a' v : ℝ, I = Ioo a a' ∧ 0 ≤ a ∧
    (∀ z ∈ Ioo a a', z ∉ J → b z = v) ∧ κ / 2 - 2 ≤ Sec4.cumWeightRight κ v

/-- **R5 for Aux. lemma 64's words**: GB7a for announced stopped references (PROVE-AUX61-R45). -/
theorem isSettingAvoiding_refPos : IsSettingAvoiding.{u} RefPos := by
  intro S _ R I hy hθ hRef hinj
  obtain ⟨hκ4, hb, a, a', v, rfl, ha, hv, hS⟩ := hRef
  have hya : R.y ≤ a := by rw [hy]; exact ha
  have hS' : R.κ / 2 - 2 ≤ Sec4.cumWeightRight R.κ (v + R.θ * QuantumZipper.chiC R.κ) := by
    rw [hθ, zero_mul, add_zero]; exact hS
  filter_upwards [(R.ae_avoid_intervals hκ4 hb hinj hv).1 hya hS'] with ω h t ht y hy'
  exact h t ht y hy'

/-! ### The cover and its glue -/

/-- **The measure-theoretic glue of a fibre cover**: if almost every fibre over each piece gives its exceptional set
measure zero, the covered event is null. -/
theorem ae_not_of_cover_null {X : Type u} [MeasurableSpace X] {μ : Measure X} {E : X → Prop} {ι : Type}
    [Countable ι] {A : ι → Set X} {S : Type u} [MeasurableSpace S] {κ : ι → Kernel X S} {L : ι → Set S}
    (hAm : ∀ i, MeasurableSet (A i)) (hcover : ∀ᵐ x ∂μ, E x → ∃ i, x ∈ A i)
    (hdis : ∀ i, μ (A i ∩ {x | E x}) ≤ ∫⁻ x in A i, κ i x (L i) ∂μ)
    (hnull : ∀ i, ∀ᵐ x ∂μ, x ∈ A i → κ i x (L i) = 0) : ∀ᵐ x ∂μ, ¬ E x := by
  have hpiece : ∀ i, μ (A i ∩ {x | E x}) = 0 := fun i => by
    refine le_antisymm ((hdis i).trans (le_of_eq ?_)) zero_le
    have h0 : ∀ᵐ x ∂μ.restrict (A i), κ i x (L i) = 0 := (ae_restrict_iff' (hAm i)).2 (hnull i)
    exact (lintegral_congr_ae h0).trans lintegral_zero
  rw [ae_iff]
  simp only [not_not]
  have hsub : {x | E x} ⊆ (⋃ i, A i ∩ {x | E x}) ∪ {x | ¬ (E x → ∃ i, x ∈ A i)} := fun x hx => by
    by_cases h : ∃ i, x ∈ A i
    · obtain ⟨i, hi⟩ := h
      exact Or.inl (mem_iUnion.2 ⟨i, hi, hx⟩)
    · exact Or.inr fun h' => h (h' hx)
  exact measure_mono_null hsub (measure_union_null (measure_iUnion_null hpiece) (ae_iff.1 hcover))

/-- **The fibre cover with actual locality** (the R2 target in the form the glued space produces): as
`Aux61R2.HasRefClockFibreCover`, but each fibre records actual locality of its pre-clock hulls, harmonicity of `q` on
`ℍ` and a.s. injectivity of its path through the clock, instead of locality under the tilt. -/
def HasCovFibreCover {X : Type u} [MeasurableSpace X] (μ : Measure X) (E : X → Prop)
    (Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (A : ι → Set X) (S : Type u) (_ : MeasurableSpace S) (κ : ι → Kernel X S)
    (L : ι → Set S),
    (∀ i, MeasurableSet (A i)) ∧ (∀ᵐ x ∂μ, E x → ∃ i, x ∈ A i) ∧
    (∀ i, μ (A i ∩ {x | E x}) ≤ ∫⁻ x in A i, κ i x (L i) ∂μ) ∧
    ∀ i, ∀ᵐ x ∂μ, x ∈ A i → ∃ (D : RefFibre S) (CS : Aux61R45.ClockSource S) (V : Set ℂ)
      (RC : Aux61R45.ReferenceClock CS D.κ D.bR D.JR 0 V) (I : Set ℝ),
      D.P = κ i x ∧ CS.y = 0 ∧ D.P = CS.P ∧ D.W = RC.W ∧ D.e = RC.e ∧ D.filt = CS.driving ∧
      InnerProductSpace.HarmonicOnNhd D.q H ∧ D.IsActualLocal ∧
      (∀ᵐ ω ∂D.P, InjOn (CS.Γ ω) {t | (t : ℝ≥0∞) ≤ D.e ω}) ∧ Ref D.κ D.bR D.JR I ∧
      ∀ ω ∈ L i, ∃ v : ℝ≥0, (v : ℝ≥0∞) ≤ D.e ω ∧ ∃ y ∈ I, CS.Γ ω v = (y : ℂ)

/-- **The new cover gives PROVE-AUX61-R2's cover** (R2f: tilt locality from actual locality). -/
theorem hasRefClockFibreCover_of_cov {X : Type u} [MeasurableSpace X] {μ : Measure X} {E : X → Prop}
    {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop} (hcov : HasCovFibreCover μ E Ref) :
    HasRefClockFibreCover μ E Ref := by
  obtain ⟨ι, hι, A, S, mS, κ, L, hAm, hcover, hdis, hfib⟩ := hcov
  refine ⟨ι, hι, A, S, mS, κ, L, hAm, hcover, hdis, fun i => ?_⟩
  filter_upwards [hfib i] with x hx hxA
  obtain ⟨D, CS, V, RC, I, hPx, hy, hP, hW, he, hfilt, hq, hloc, -, hRef, hL⟩ := hx hxA
  have he0 : ∀ᵐ ω ∂D.P, 0 < D.e ω := by
    rw [hP, he]
    exact (RC.announcing.2.2.1 0).mono fun _ h => lt_of_le_of_lt bot_le h
  exact ⟨D, CS, V, RC, I, hPx, hy, hP, hW, he, hfilt, RefFibre.isTiltLocal_of_actual he0 hq hloc, hRef, hL⟩

/-- **A cover with actual locality and reference avoidance make the event null** (R2 + R3 + R4 + R5). -/
theorem ae_not_of_hasCovFibreCover {X : Type u} [MeasurableSpace X] {μ : Measure X} {E : X → Prop}
    {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop} (hcov : HasCovFibreCover μ E Ref)
    (hR5 : IsSettingAvoiding.{u} Ref) : ∀ᵐ x ∂μ, ¬ E x := by
  obtain ⟨ι, hι, A, S, mS, κ, L, hAm, hcover, hdis, hfib⟩ := hcov
  refine ae_not_of_cover_null hAm hcover hdis fun i => ?_
  filter_upwards [hfib i] with x hx hxA
  obtain ⟨D, CS, V, RC, I, hPx, hy, hP, hW, he, hfilt, hq, hloc, hinj, hRef, hL⟩ := hx hxA
  have he0 : ∀ᵐ ω ∂D.P, 0 < D.e ω := by
    rw [hP, he]
    exact (RC.announcing.2.2.1 0).mono fun _ h => lt_of_le_of_lt bot_le h
  let T := RefFibre.tiltData he0
  have htl : ∀ (τ : S → WithTop ℝ≥0) (_ : IsStoppingTime D.filt τ),
      (∀ᵐ ω ∂T.tilt, (τ ω : ℝ≥0∞) < D.e ω) →
      IsLocalSet (fun ω => fwdHull (Ito.rpath (D.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) D.chartField T.tilt :=
    RefFibre.isTiltLocal_of_actual he0 hq hloc
  let K := T.clockOfReferenceClock CS hy RC hP hW he hfilt (RefFibre.isProbabilityMeasure_tilt he0) htl
  let R := K.toReferenceSetting
  have hinjT : ∀ᵐ ω ∂R.P, InjOn (R.Γ ω) {t | (t : ℝ≥0∞) ≤ R.e ω} := T.tilt_equivalent.1.ae_le hinj
  have hav : ∀ᵐ ω ∂D.P, ∀ v : ℝ≥0, (v : ℝ≥0∞) ≤ D.e ω → ∀ y ∈ I, CS.Γ ω v ≠ (y : ℂ) :=
    T.tilt_equivalent.2.ae_le (hR5 R I rfl rfl hRef hinjT)
  rw [← hPx]
  refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hav)
  obtain ⟨v, hv, y, hy', hΓ⟩ := hL ω hω
  simp only [Set.mem_ofPred_eq, not_forall, not_not]
  exact ⟨v, hv, y, hy', hΓ⟩

/-! ### On the glued space -/

section Glued

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique Cond44Ref Prop51Q CfAvoidLeftQ Prop51G Aux61Kernel
open QuantumZipper (chiC)

/-- **The R2 target on the glued space in actual-locality form**: same binders as
`Aux61R2.RefClockFibreCoverOn`, with `HasCovFibreCover`. -/
def CovFibreCoverOn (G : ℝ → ℝ → ℝ → Prop) (Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop) : Prop :=
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
            HasCovFibreCover.{u}
              (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
                ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)))
              (fun p => RestartWindowEvent (Prop411Q.cfDrv p.2) s (fun u : ℝ => η p.1 u.toNNReal) t c) Ref

/-- The actual-locality target implies PROVE-AUX61-R2's target. -/
theorem refClockFibreCoverOn_of_cov {G : ℝ → ℝ → ℝ → Prop} {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop}
    (hcov : CovFibreCoverOn.{u} G Ref) : RefClockFibreCoverOn.{u} G Ref := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  exact hasRefClockFibreCover_of_cov (hcov t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf
    hlaw k hk s hs)

/-- **R23's named input from the actual-locality cover and R5 in reference-setting form.** -/
theorem restartWindowNullQOn_of_covCover {G : ℝ → ℝ → ℝ → Prop} {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop}
    (hcov : CovFibreCoverOn.{u} G Ref) (hR5 : IsSettingAvoiding.{u} Ref) : RestartWindowNullQOn.{u} G := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  exact ae_not_of_hasCovFibreCover (hcov t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw
    k hk s hs) hR5

/-- **(E1) in target-component form for every angle pair** from the actual-locality cover below the critical gap
and R5 in reference-setting form (with the counterflow regularity from Part A). -/
theorem fwdNoEastCrosscutTgtQOn_of_covCover_smallGap {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop}
    (hreg : Prop51Q.CfLineRegularQStatement.{u})
    (hcov : CovFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) Ref) (hR5 : IsSettingAvoiding.{u} Ref) :
    FwdNoEastCrosscutTgtQOn.{u} fun _ _ _ => True :=
  fwdNoEastCrosscutTgtQOn_of_window_smallGap hreg (restartWindowNullQOn_of_covCover hcov hR5)

end Glued

end Aux61Cov

end InteractingSLE.Sec5
