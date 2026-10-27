import MatedCRTHarmonic.IGLaw.Rotation
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Group.AddCircle

/-!
# Reusable curve-law consequences for the IGC bundle

This module records the measurable-factor and coordinate-change steps that consume the IGC
bundle. The normalization decomposition is stated at LQGMetric's circle-average convention and
the MoTPort `φ₀` convention.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Distributions

namespace MatedCRTHarmonic.IGLaw

open LQGMetric
open MatedCRTHarmonic.MoTPort

/-- The draft bundle's circle-average process `circleAvg h + U`, as a function of its field and
uniform scalar. -/
def igCircleAvgInput (p : Field × ℝ) : ℝ → ℂ → ℝ :=
  fun ρ w => circleAvg p.1 ρ w + p.2

theorem measurable_igCircleAvgInput : Measurable igCircleAvgInput := by
  apply measurable_pi_iff.2
  intro ρ
  apply measurable_pi_iff.2
  intro w
  have harg : Measurable fun p : Field × ℝ => (p.1, (ρ, w)) := by
    exact measurable_fst.prodMk (measurable_const.prodMk measurable_const)
  exact (LQGMetric.measurable_circleAvg.comp harg).add measurable_snd

/-- Uniform measure on one period pushes forward to normalized Haar measure on the additive
circle. -/
theorem map_uniform_period_to_addCircle {Ω : Type*} [MeasurableSpace Ω]
    {r : ℝ} [Fact (0 < r)] {P : Measure Ω} {U : Ω → ℝ}
    (hU : P.map U = volume[|Ico (0 : ℝ) r]) :
    P.map (fun ω => (U ω : AddCircle r)) = AddCircle.haarAddCircle := by
  have hUm : AEMeasurable U P :=
    MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif Fact.out hU
  change P.map ((fun x : ℝ => (x : AddCircle r)) ∘ U) = _
  rw [← AEMeasurable.map_map_of_aemeasurable AddCircle.measurable_mk'.aemeasurable hUm, hU]
  ext s hs
  rw [Measure.map_apply AddCircle.measurable_mk' hs,
    ProbabilityTheory.cond_apply measurableSet_Ico]
  have hset : Ico (0 : ℝ) r ∩ (fun x : ℝ => (x : AddCircle r)) ⁻¹' s =ᵐ[volume]
      Ioc (0 : ℝ) r ∩ (fun x : ℝ => (x : AddCircle r)) ⁻¹' s := by
    filter_upwards [Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := r) (μ := (volume : Measure ℝ))]
      with x hx
    simp only [Set.mem_inter_iff, Set.mem_preimage, hx]
  rw [measure_congr hset, inter_comm]
  have hproj := AddCircle.add_projection_respects_measure r 0 hs
  rw [zero_add] at hproj
  rw [← hproj, AddCircle.volume_eq_smul_haarAddCircle, Measure.smul_apply]
  have hr0 : ENNReal.ofReal r ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr Fact.out)
  rw [Real.volume_Ico]
  simp only [sub_zero, smul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hr0 ENNReal.ofReal_ne_top, one_mul]

/-- Choose the representative of an additive-circle point in `[0,r)`. -/
def addCircleRepresentative {r : ℝ} [Fact (0 < r)] (x : AddCircle r) : ℝ :=
  (AddCircle.equivIco r 0 x).1

theorem measurable_addCircleRepresentative {r : ℝ} [Fact (0 < r)] :
    Measurable (addCircleRepresentative (r := r)) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco r 0).measurable

/-- Haar measure on the period circle, represented in `[0,r)`, is the usual uniform measure. -/
theorem map_addCircleRepresentative_haar {r : ℝ} [Fact (0 < r)] :
    AddCircle.haarAddCircle.map (addCircleRepresentative (r := r)) =
      volume[|Ico (0 : ℝ) r] := by
  let μ : Measure ℝ := volume[|Ico (0 : ℝ) r]
  let q : ℝ → AddCircle r := fun x => x
  have hq : μ.map q = AddCircle.haarAddCircle := by
    exact map_uniform_period_to_addCircle (r := r) (P := μ) (U := id) (by simp [μ])
  have hmem : ∀ᵐ x ∂μ, x ∈ Ico (0 : ℝ) r := by
    have hc : μ (Ico (0 : ℝ) r)ᶜ = 0 := by
      rw [show μ = volume[|Ico (0 : ℝ) r] from rfl,
        ProbabilityTheory.cond_apply measurableSet_Ico]
      rw [inter_compl_self, measure_empty, mul_zero]
    have hnot : ∀ᵐ x ∂μ, x ∉ (Ico (0 : ℝ) r)ᶜ :=
      measure_eq_zero_iff_ae_notMem.1 hc
    exact hnot.mono fun x hx => by simpa using hx
  have heq : (addCircleRepresentative (r := r) ∘ q) =ᵐ[μ] id := by
    filter_upwards [hmem] with x hx
    change (AddCircle.equivIco r 0 (x : AddCircle r)).1 = x
    have hx' : x ∈ Ico (0 : ℝ) (0 + r) := by simpa using hx
    rw [AddCircle.equivIco_coe_eq hx']
  calc
    AddCircle.haarAddCircle.map (addCircleRepresentative (r := r)) =
        (μ.map q).map (addCircleRepresentative (r := r)) := by rw [hq]
    _ = μ.map (addCircleRepresentative (r := r) ∘ q) :=
      Measure.map_map (measurable_addCircleRepresentative (r := r)) AddCircle.measurable_mk'
    _ = μ.map id := Measure.map_congr heq
    _ = μ := by simp

/-- A real period multiple is zero after projection to `AddCircle r`. -/
theorem addCircle_period_integer {r : ℝ} [Fact (0 < r)] (k : ℤ) :
    ((r * (k : ℝ) : ℝ) : AddCircle r) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨k, by ring⟩

/-- Recentering a modulo-period representative at `φ₀` gives the same oscillation as recentering
the original field. -/
theorem normMod_recenter_φ₀ {r : ℝ} (g : Field) :
    addConst (normMod r g) (-(normMod r g φ₀)) = addConst g (-(g φ₀)) := by
  rw [normMod, NormMod.addConst_addConst, NormMod.addConst_apply_φ₀]
  congr 1
  ring

/-- Adding a field-measurable shift on the period circle to an independent Haar variable keeps
the result Haar and independent of the field variable. -/
theorem indepFun_addCircleShift {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {r : ℝ} [Fact (0 < r)] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Ω → α} {U : Ω → AddCircle r} {V : α → AddCircle r}
    (hF : Measurable F) (hU : AEMeasurable U P) (hV : Measurable V)
    (hFU : IndepFun F U P) (hUlaw : P.map U = AddCircle.haarAddCircle) :
    IndepFun F (fun ω => V (F ω) + U ω) P ∧
      P.map (fun ω => V (F ω) + U ω) = AddCircle.haarAddCircle := by
  let μ := P.map F
  let sh : α × AddCircle r → α × AddCircle r := fun p => (p.1, V p.1 + p.2)
  let pr : Ω → α × AddCircle r := fun ω => (F ω, U ω)
  let ps : Ω → α × AddCircle r := fun ω => (F ω, V (F ω) + U ω)
  have hpr : AEMeasurable pr P := hF.aemeasurable.prodMk hU
  have hshift : AEMeasurable (fun ω => V (F ω) + U ω) P :=
    (hV.comp hF).aemeasurable.add hU
  have hps : AEMeasurable ps P := hF.aemeasurable.prodMk hshift
  have hsh : Measurable sh := measurable_fst.prodMk ((hV.comp measurable_fst).add measurable_snd)
  have hlaw : P.map pr = μ.prod AddCircle.haarAddCircle := by
    rw [← hUlaw]
    exact (indepFun_iff_map_prod_eq_prod_map_map hF.aemeasurable hU).mp hFU
  have hmp : MeasurePreserving sh (μ.prod AddCircle.haarAddCircle)
      (μ.prod AddCircle.haarAddCircle) := by
    refine MeasurePreserving.skew_product (μa := μ) (μb := μ)
      (μc := AddCircle.haarAddCircle) (μd := AddCircle.haarAddCircle)
      (f := id) (g := fun a u => V a + u) (MeasurePreserving.id μ) ?_ ?_
    · exact (hV.comp measurable_fst).add measurable_snd
    · exact ae_of_all _ fun a =>
        (MeasureTheory.measurePreserving_add_left AddCircle.haarAddCircle (V a)).map_eq
  have hpsLaw : P.map ps = μ.prod AddCircle.haarAddCircle := by
    calc
      P.map ps = P.map (sh ∘ pr) := by rfl
      _ = (P.map pr).map sh :=
        (AEMeasurable.map_map_of_aemeasurable hsh.aemeasurable hpr).symm
      _ = (μ.prod AddCircle.haarAddCircle).map sh := by rw [hlaw]
      _ = μ.prod AddCircle.haarAddCircle := hmp.map_eq
  have hUshift : P.map (fun ω => V (F ω) + U ω) = AddCircle.haarAddCircle := by
    calc
      P.map (fun ω => V (F ω) + U ω) = P.map (Prod.snd ∘ ps) := by rfl
      _ = (P.map ps).map Prod.snd :=
        (AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hps).symm
      _ = (μ.prod AddCircle.haarAddCircle).map Prod.snd := by rw [hpsLaw]
      _ = (μ univ) • AddCircle.haarAddCircle := Measure.map_snd_prod
      _ = AddCircle.haarAddCircle := by rw [measure_univ, one_smul]
  have hind : IndepFun F (fun ω => V (F ω) + U ω) P := by
    apply (indepFun_iff_map_prod_eq_prod_map_map hF.aemeasurable
      hshift).2
    change P.map ps = (P.map F).prod (P.map (fun ω => V (F ω) + U ω))
    rw [hpsLaw, hUshift]
  exact ⟨hind, hUshift⟩

/-- The LQGMetric circle-average representative and the MoTPort `φ₀`-centered representative
differ by the scalar pairing with `φ₀`. -/
theorem circleAvg_to_φ₀_decomposition (g : Field) (u : ℝ) :
    addConst g u = addConst (addConst g (-(g φ₀))) (g φ₀ + u) := by
  rw [NormMod.addConst_addConst]
  congr 1
  ring

/-- Recentring at `φ₀` preserves the whole-plane GFF law, and an independent scalar remains
independent of the recentered oscillation. This is the checked part of converting the draft's
circle-average normalization to the port's test-function normalization. -/
theorem IsNormalizedWPGFF.recenter_φ₀_independent
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → Field}
    (hh : IsNormalizedWPGFF h P) {U : Ω → ℝ} (hHU : IndepFun h U P) :
    IsWholePlaneGFF (fun ω => addConst (h ω) (-(h ω φ₀))) P ∧
      (∀ ω, (addConst (h ω) (-(h ω φ₀))) φ₀ = 0) ∧
      IndepFun (fun ω => addConst (h ω) (-(h ω φ₀))) U P := by
  let C : Ω → ℝ := fun ω => -(h ω φ₀)
  have hC : Measurable C := ((measurable_distOn_apply φ₀).comp hh.1.measurable).neg
  have hcenter : IsWholePlaneGFF (fun ω => addConst (h ω) (C ω)) P := hh.1.addConst hC
  have hzero (ω : Ω) : (addConst (h ω) (C ω)) φ₀ = 0 := by
    rw [GFFInv.addConst_apply, MoTPort.integral_φ₀]
    dsimp [C]
    ring
  have hind : IndepFun (fun ω => addConst (h ω) (C ω)) U P :=
    hHU.comp MoTPort.WPGFFMod.measurable_recenter measurable_id
  exact ⟨hcenter, hzero, hind⟩

/-- Convert the unit-circle-average normalization used in the S0Y draft into the port's
`φ₀`-normalization. The independent uniform scalar remains uniform and independent after the
field-dependent recentering, modulo the period `r`. -/
theorem IsNormalizedWPGFF.to_isWPGFFMod
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → Field} (hh : IsNormalizedWPGFF h P) {U : Ω → ℝ}
    {r : ℝ} [Fact (0 < r)] (hU : P.map U = volume[|Ico (0 : ℝ) r])
    (hHU : IndepFun h U P) :
    MoTPort.IsWPGFFMod r
      (fun ω => normMod r (addConst (h ω) (U ω))) P := by
  let F : Ω → Field := fun ω => addConst (h ω) (-(h ω φ₀))
  let X : Ω → Field := fun ω => normMod r (addConst (h ω) (U ω))
  let Y : Ω → ℝ := fun ω => X ω φ₀
  let Uc : Ω → AddCircle r := fun ω => U ω
  let V : Field → AddCircle r := fun g => (-(circleAvg g 1 0) : AddCircle r)
  let Z : Ω → AddCircle r := fun ω => V (F ω) + Uc ω
  have hrec := IsNormalizedWPGFF.recenter_φ₀_independent hh hHU
  have hF : Measurable F := hrec.1.measurable
  have hFwhole : IsWholePlaneGFF F P := hrec.1
  have hFU : IndepFun F U P := hrec.2.2
  have hUm : AEMeasurable U P :=
    MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif Fact.out hU
  have hUc : AEMeasurable Uc P := AddCircle.measurable_mk'.comp_aemeasurable hUm
  have hUcLaw : P.map Uc = AddCircle.haarAddCircle := by
    exact map_uniform_period_to_addCircle hU
  have hFUc : IndepFun F Uc P := by
    change IndepFun F (fun ω => (U ω : AddCircle r)) P
    exact hFU.comp measurable_id AddCircle.measurable_mk'
  have hV : Measurable V :=
    AddCircle.measurable_mk'.comp (LQGMetric.measurable_circleAvg_left 1 0).neg
  have hShift := indepFun_addCircleShift hF hUc hV hFUc hUcLaw
  have hOffset : ∀ᵐ ω ∂P, -(circleAvg (F ω) 1 0) = h ω φ₀ := by
    filter_upwards [CircleAvg.ae_tendsto_mollAvg hh.1 0 one_pos, hh.2]
      with ω ⟨a, ha⟩ hnorm
    have hlim := CircleAvg.circleAvg_eq_of_tendsto ha
    have ha0 : a = 0 := hlim.symm.trans hnorm
    rw [show F ω = addConst (h ω) (-(h ω φ₀)) from rfl,
      CircleAvg.circleAvg_addConst_of_tendsto ha, hlim, ha0]
    ring
  have hVoffset : ∀ᵐ ω ∂P, V (F ω) = (h ω φ₀ : AddCircle r) := by
    filter_upwards [hOffset] with ω hω
    dsimp [V]
    rw [← AddCircle.coe_neg]
    exact congrArg (fun x : ℝ => (x : AddCircle r)) hω
  have hYclass : (fun ω => (Y ω : AddCircle r)) =ᵐ[P] Z := by
    filter_upwards [hVoffset] with ω hω
    dsimp [Y, X, Z, Uc]
    have hx : h ω φ₀ + U ω = (addConst (h ω) (U ω)) φ₀ := by
      rw [NormMod.addConst_apply_φ₀]
    rw [normMod, NormMod.addConst_apply_φ₀]
    rw [show (addConst (h ω) (U ω) φ₀) = h ω φ₀ + U ω from hx.symm]
    have hk : ((-r * (⌊(h ω φ₀ + U ω) / r⌋ : ℝ) : ℝ) : AddCircle r) = 0 := by
      rw [show -r * (⌊(h ω φ₀ + U ω) / r⌋ : ℝ) =
        r * ((-⌊(h ω φ₀ + U ω) / r⌋ : ℤ) : ℝ) by push_cast; ring]
      exact addCircle_period_integer (r := r) (-⌊(h ω φ₀ + U ω) / r⌋)
    simp only [AddCircle.coe_add]
    rw [hk, add_zero, hω]
  have hYmem (ω : Ω) : Y ω ∈ Ico (0 : ℝ) r :=
    NormMod.normMod_apply_φ₀_mem Fact.out (addConst (h ω) (U ω))
  have hYrep : Y =ᵐ[P] fun ω => addCircleRepresentative (Z ω) := by
    filter_upwards [hYclass] with ω hω
    have hx' : Y ω ∈ Ico (0 : ℝ) (0 + r) := by simpa using hYmem ω
    have hrep : addCircleRepresentative (r := r) ((Y ω : ℝ) : AddCircle r) = Y ω := by
      change (AddCircle.equivIco r 0 (Y ω : AddCircle r)).1 = Y ω
      rw [AddCircle.equivIco_coe_eq hx']
    exact hrep.symm.trans (congrArg (addCircleRepresentative (r := r)) hω)
  have hYlaw : P.map Y = volume[|Ico (0 : ℝ) r] := by
    calc
      P.map Y = P.map (addCircleRepresentative (r := r) ∘ Z) := Measure.map_congr hYrep
      _ = (P.map Z).map (addCircleRepresentative (r := r)) :=
        (AEMeasurable.map_map_of_aemeasurable
          (measurable_addCircleRepresentative (r := r)).aemeasurable
          ((hV.comp hF).aemeasurable.add hUc)).symm
      _ = AddCircle.haarAddCircle.map (addCircleRepresentative (r := r)) := by
        rw [hShift.2]
      _ = volume[|Ico (0 : ℝ) r] := map_addCircleRepresentative_haar
  have hFY : IndepFun F Y P := by
    have hi := hShift.1.comp measurable_id (measurable_addCircleRepresentative (r := r))
    exact hi.congr (ae_of_all _ fun _ => rfl) hYrep.symm
  have hXcenter : (fun ω => addConst (X ω) (-(X ω φ₀))) = F := by
    funext ω
    rw [normMod_recenter_φ₀]
    change addConst (addConst (h ω) (U ω))
      (-((addConst (h ω) (U ω)) φ₀)) = addConst (h ω) (-(h ω φ₀))
    rw [NormMod.addConst_apply_φ₀, NormMod.addConst_addConst]
    congr 1
    ring
  apply (MoTPort.isWPGFFMod_iff (r := r) (X := X) (P := P)).2
  rw [hXcenter]
  exact ⟨hFwhole, hYlaw, hFY⟩

/-- The port's integer-period adapter applies to the S0Y draft field after converting its
circle-average normalization. This is the law of its normalized representative modulo `rℤ`. -/
theorem IsNormalizedWPGFF.map_uniform_mod_period
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → Field} (hh : IsNormalizedWPGFF h P) {U : Ω → ℝ}
    {r : ℝ} [Fact (0 < r)]
    (hU : P.map U = volume[|Ico (0 : ℝ) r]) (hHU : IndepFun h U P)
    (k : Ω → ℤ) :
    P.map (fun ω => normMod r
      (addConst (normMod r (addConst (h ω) (U ω))) (r * k ω))) =
      P.map (fun ω => normMod r (addConst (h ω) (U ω))) := by
  exact (IsNormalizedWPGFF.to_isWPGFFMod hh hU hHU).map_normMod_addConst_intMul Fact.out k

/-- Integer-period shifts leave the port's normalized representative unchanged pointwise. This
version does not require `IsWPGFFMod`, so it applies directly to the draft field `hIG₀ + U` after
its conversion to a `Field`. -/
theorem normMod_addConst_twoPiChi_eq {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → Field} {χ : ℝ} (hχ : 0 < χ) (k : Ω → ℤ) :
    (fun ω => normMod (2 * Real.pi * χ)
      (addConst (X ω) ((2 * Real.pi * χ) * k ω))) =
      fun ω => normMod (2 * Real.pi * χ) (X ω) := by
  funext ω
  exact NormMod.normMod_addConst_intMul (by positivity) (X ω) (k ω)

/-- Consequently, the law of the normalized representative is invariant under any samplewise
integer multiple of `2πχ`, regardless of which whole-plane normalization was used for `X`. -/
theorem map_normMod_addConst_twoPiChi_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → Field} {χ : ℝ} (hχ : 0 < χ) (k : Ω → ℤ) :
    P.map (fun ω => normMod (2 * Real.pi * χ)
      (addConst (X ω) ((2 * Real.pi * χ) * k ω))) =
      P.map (fun ω => normMod (2 * Real.pi * χ) (X ω)) := by
  rw [normMod_addConst_twoPiChi_eq hχ k]

/-- Measurable functions of the IG field and its auxiliary scalar remain independent of the cone
data. This is the abstract `igMap` step for `indep_curve`. -/
theorem indepFun_of_ae_factor {Ω α β γ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {P : Measure Ω}
    {F : Ω → α} {G : Ω → β} {Y : Ω → γ} {f : α → γ}
    (hFG : IndepFun F G P) (hf : Measurable f)
    (hY : Y =ᵐ[P] fun ω => f (F ω)) : IndepFun Y G P := by
  have hcomp : IndepFun (fun ω => f (F ω)) G P := hFG.comp hf measurable_id
  exact hcomp.congr hY.symm (ae_of_all _ fun _ => rfl)

/-- The draft bundle's `igMap` factorization and `indep_curve` imply that `ηL` is independent of
the complete tuple of both cones. -/
theorem indepFun_igCurve_of_draft_factor {Ω β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] {P : Measure Ω} {h : Ω → Field} {U : Ω → ℝ}
    {C : Ω → β} {η : Ω → C(ℝ, ℂ)}
    {Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ)} (hpair : IndepFun (fun ω => (h ω, U ω)) C P)
    (hΦ : Measurable Φ)
    (hη : η =ᵐ[P] fun ω => Φ (igCircleAvgInput (h ω, U ω))) : IndepFun η C P :=
  indepFun_of_ae_factor hpair (hΦ.comp measurable_igCircleAvgInput) hη

/-- A coordinate-change identity transports the law of the input field to the law of the
re-rooted curve, provided the transformed input has the original law. -/
theorem map_eq_of_coordinate_change {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] {P : Measure Ω}
    {H : Ω → α} {η : Ω → β} {Φ : α → β} {T : α → α} {R : β → β}
    (hΦ : Measurable Φ) (hT : Measurable T) (hH : Measurable H)
    (hηΦ : η =ᵐ[P] fun ω => Φ (H ω))
    (hcoord : (fun ω => Φ (T (H ω))) =ᵐ[P] fun ω => R (η ω))
    (hinput : P.map (fun ω => T (H ω)) = P.map H) :
    P.map (fun ω => R (η ω)) = P.map η := by
  have hTcomp : Measurable (fun ω => T (H ω)) := hT.comp hH
  calc
    P.map (fun ω => R (η ω)) = P.map (fun ω => Φ (T (H ω))) := Measure.map_congr hcoord.symm
    _ = (P.map (fun ω => T (H ω))).map Φ := by
      exact (Measure.map_map hΦ hTcomp).symm
    _ = (P.map H).map Φ := by rw [hinput]
    _ = P.map (fun ω => Φ (H ω)) := Measure.map_map hΦ hH
    _ = P.map η := Measure.map_congr hηΦ.symm

end MatedCRTHarmonic.IGLaw
