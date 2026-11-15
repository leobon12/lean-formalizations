/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CrosscutA3MeasurableMap
import InteractingSLE.Spec.ZhanGT4.CrosscutA3MeasurableBdry
import InteractingSLE.Spec.ZhanGT4.CrosscutA3
import InteractingSLE.Foundations.SLE.All
import QuantumZipper.Proofs.Zipper.F1ReadMeasPath

/-!
# A.3.2 for `4 < κ < 8` with a measurable crosscut event

Packet PROVE-ZHAN-A35. Source: Astra, *Follow-up proofs and dependency audit*, §A.3.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L686–L720, ruling R38): "Consequently the original strip law is
the mixture … Each mixture component therefore has a crosscut outer boundary from `y < x` to a positive point. The
mixture identity proves the ordinary first-swallow claim."

PROVE-ZHAN-A34 (`CrosscutA3.lean`) proved A.3 for `4 < κ < 8` from A.2 over the strip life and the measurability of
the set of strip paths `{ξ | StripCrosscutGood ξ}` (product σ-algebra). That set is not known to be measurable (it
reads uncountably many coordinates of an arbitrary path). This file removes the measurability input by replacing it
with a **measurable** property `StripCodeGood` that is implied by `StripCrosscutGood` on continuous paths and
implies the crosscut property on continuous paths:

* `regPath ξ`: the dyadic read-off of `ξ` on QuantumZipper's countable continuity certificate `DyUC` (`0` off it); a
  continuous path with measurable coordinates, equal to `ξ` when `ξ` is continuous;
* `StripCodeGood ξ`: if the read-off starts at `0`, has finite total chordal time and a convergent driver
  (`CodeAnte`), the boundary values `bdryVal` of the inverse map at the end of its strip life satisfy the boundary code
  `BdryCode`; **`measurableSet_stripCodeGood`**;
* `stripCodeGood_of_stripCrosscutGood` (A.2's component crosscut ⇒ code) and `exists_crosscut_of_stripCodeGood` (code ⇒
  crosscut, given a boundary extension, e.g. from the ordinary `SLE_κ` trace);
* **`firstSwallowCrosscutStatement_of_life_meas`**: `FirstSwallowCrosscutStatement κ` for `4 < κ < 8` from A.2 over the
  strip life (`FourForceCrosscutG3LifeStatement`) alone.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A35

open A34 QuantumZipper

/-! ### The dyadic regularization of a path -/

open Classical in
/-- **The dyadic regularization** of a path: its dyadic read-off on the countable continuity certificate `DyUC`, the
zero path otherwise. -/
def regPath (ξ : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun t => if F1.DyUC ξ then F1.readDrv ξ t else 0

theorem measurable_regPath_apply (t : ℝ≥0) : Measurable fun ξ : ℝ≥0 → ℝ => regPath ξ t := by
  classical
  have h : Measurable fun ξ : ℝ≥0 → ℝ => F1.readDrv ξ t := by
    have h1 : Measurable fun p : ℝ≥0 → ℝ => ((fun r : ℝ => p r.toNNReal), (t : ℝ)) :=
      (measurable_pi_iff.2 fun r => measurable_pi_apply _).prodMk measurable_const
    exact F1.B4d.measurable_pathExt.comp h1
  exact Measurable.ite F1.measurableSet_dyUC h measurable_const

theorem continuous_regPath (ξ : ℝ≥0 → ℝ) : Continuous (regPath ξ) := by
  classical
  by_cases h : F1.DyUC ξ
  · have : regPath ξ = fun t : ℝ≥0 => F1.readDrv ξ (t : ℝ) := funext fun t => by simp [regPath, h]
    rw [this]; exact (F1.continuous_readDrv_of_dyUC h).comp NNReal.continuous_coe
  · have : regPath ξ = fun _ => 0 := funext fun t => by simp [regPath, h]
    rw [this]; exact continuous_const

theorem regPath_of_continuous {ξ : ℝ≥0 → ℝ} (hξ : Continuous ξ) : regPath ξ = ξ := by
  classical
  have hd := F1.dyUC_of_continuous hξ
  have hW : Continuous fun s : ℝ => ξ s.toNNReal := hξ.comp continuous_real_toNNReal
  have h := F1.readDrv_eq hW (fun s => by rw [Real.toNNReal_coe])
  have e : (fun t : ℝ≥0 => (fun s : ℝ => ξ s.toNNReal) (t : ℝ)) = ξ := funext fun t => by simp
  rw [e] at h
  funext t
  simp only [regPath, hd, ite_true, h, Real.toNNReal_coe]

/-! ### The measurable crosscut property -/

/-- The countable conditions under which the boundary code of a continuous strip path is read: it starts at `0`, its
total chordal time is finite, and the reconstructed driver converges (along rational strip times). -/
def CodeAnte (η : ℝ≥0 → ℝ) : Prop := η 0 = 0 ∧ reconEnd η < ⊤ ∧ ValCauchy η

/-- **The measurable crosscut property of a strip path**: under `CodeAnte` for its regularization, the boundary values
of the inverse Loewner map at the end of the strip life satisfy the boundary code. -/
def StripCodeGood (ξ : ℝ≥0 → ℝ) : Prop := CodeAnte (regPath ξ) → BdryCode fun v => bdryVal regPath v ξ

theorem measurableSet_stripCodeGood : MeasurableSet {ξ : ℝ≥0 → ℝ | StripCodeGood ξ} := by
  have hXm : ∀ t, Measurable fun ξ : ℝ≥0 → ℝ => regPath ξ t := measurable_regPath_apply
  have hXc : ∀ ξ, Continuous (regPath ξ) := continuous_regPath
  have hA : Measurable fun ξ : ℝ≥0 → ℝ => CodeAnte (regPath ξ) := by
    refine Measurable.and ?_ (Measurable.and ?_ ?_)
    · exact measurableSet_setOfPred.1 (measurableSet_eq_fun (hXm 0) measurable_const)
    · exact measurableSet_setOfPred.1 (measurableSet_lt (measurable_reconEnd hXm hXc) measurable_const)
    · refine Measurable.forall fun k => Measurable.exists fun m => Measurable.forall fun q =>
        Measurable.forall fun q' => measurable_const.imp (measurable_const.imp ?_)
      exact measurableSet_setOfPred.1 (measurableSet_le (continuous_abs.measurable.comp
        ((measurable_reconVal hXm hXc q).sub (measurable_reconVal hXm hXc q'))) measurable_const)
  have hB : Measurable fun ξ : ℝ≥0 → ℝ => BdryCode fun v => bdryVal regPath v ξ :=
    measurableSet_setOfPred.1 (measurableSet_bdryCode (G := fun ξ v => bdryVal regPath v ξ)
      fun q => measurable_bdryVal hXm hXc q)
  exact measurableSet_setOfPred.2 (hA.imp hB)

/-- **A.2's crosscut property gives the code** on a continuous strip path. -/
theorem stripCodeGood_of_stripCrosscutGood {ξ : ℝ≥0 → ℝ} (hξ : Continuous ξ) (hgood : StripCrosscutGood ξ) :
    StripCodeGood ξ := by
  intro hante
  have hreg := regPath_of_continuous hξ
  rw [hreg] at hante
  obtain ⟨h0, hfin, hcau⟩ := hante
  obtain ⟨L, hL⟩ := exists_tendsto_of_valCauchy hξ hcau
  obtain ⟨W, hWc, hW0, hWeq⟩ := exists_continuous_extension hξ h0 hfin hL
  have hσ : 0 < (reconEnd ξ).toReal := toReal_reconEnd_pos hξ hfin
  have hend : ENNReal.ofReal (reconEnd ξ).toReal = reconEnd ξ := ENNReal.ofReal_toReal hfin.ne
  obtain ⟨γ, hγ, hγ0, hγ1, hfr⟩ := hgood W _ hσ hend hWc hW0 hWeq
  obtain ⟨F, hF⟩ := exists_isBdryExt_of_crosscut hWc hW0 hσ hγ (by linarith) hfr
  have hcode := bdryCode_of_crosscut hWc hW0 hσ hF hγ hγ0 hγ1 hfr
  have heq : ∀ v, bdryVal regPath v ξ = F v := fun v =>
    bdryVal_eq (X := regPath) continuous_regPath (a := ξ) (by rw [hreg]; exact h0) (by rw [hreg]; exact hfin)
      hWc hW0 (by rw [hreg]; exact hWeq) (by rw [hreg]; exact hF.eqOn) hF.contOn v
  have : (fun v => bdryVal regPath v ξ) = fun v : ℝ => F v := funext heq
  rw [this]
  exact hcode

/-- **The code gives the crosscut** on a continuous strip path, at the end `σ` of its strip life, for any continuous
driver extending the reconstruction and any boundary extension of `f_σ`. -/
theorem exists_crosscut_of_stripCodeGood {ξ : ℝ≥0 → ℝ} (hξ : Continuous ξ) (hgood : StripCodeGood ξ)
    {W : ℝ → ℝ} {σ : ℝ} (hσ : 0 < σ) (hend : ENNReal.ofReal σ = reconEnd ξ) (hWc : Continuous W) (hW0 : W 0 = 0)
    (hWeq : ∀ s ∈ Ico (0 : ℝ) σ, W s = reconDrv ξ s) {F : ℂ → ℂ} (hF : IsBdryExt W σ F) :
    ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re < -1 ∧ 0 < (γ 1).re ∧
      frontier (H \ fwdHull W σ) ∩ H = γ '' Ioo 0 1 := by
  have hreg := regPath_of_continuous hξ
  have hfin : reconEnd ξ < ⊤ := by rw [← hend]; exact ENNReal.ofReal_lt_top
  have hσeq : (reconEnd ξ).toReal = σ := by rw [← hend, ENNReal.toReal_ofReal hσ.le]
  have hWeq' : ∀ s ∈ Ico (0 : ℝ) (reconEnd ξ).toReal, W s = reconDrv ξ s := by rw [hσeq]; exact hWeq
  have h0 : ξ 0 = 0 := by
    have h1 := hWeq 0 ⟨le_rfl, hσ⟩
    have h2 := reconDrv_reconClock hξ (le_refl (0 : ℝ))
    rw [reconClock_zero, reconVal_zero] at h2
    rw [hW0, h2] at h1
    have h3 : Real.exp (ξ 0) = 1 := by linarith
    exact Real.exp_eq_one_iff _ |>.1 h3
  have hL : Tendsto (reconVal ξ) atTop (𝓝 (W σ)) := by
    have h1 : Tendsto (fun t => W (reconClock ξ t)) atTop (𝓝 (W σ)) := by
      have := (hWc.tendsto _).comp (tendsto_reconClock hξ hfin); rwa [hσeq] at this
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [hWeq' _ ⟨reconClock_nonneg hξ ht, reconClock_lt_toReal hξ hfin ht⟩, reconDrv_reconClock hξ ht]
  have hante : CodeAnte (regPath ξ) := by rw [hreg]; exact ⟨h0, hfin, valCauchy_of_tendsto hL⟩
  have hcode := hgood hante
  have heq : ∀ v, bdryVal regPath v ξ = F v := fun v =>
    bdryVal_eq (X := regPath) continuous_regPath (a := ξ) (by rw [hreg]; exact h0) (by rw [hreg]; exact hfin)
      hWc hW0 (by rw [hreg]; exact hWeq') (by rw [hreg, hσeq]; exact hF.eqOn) hF.contOn v
  have : (fun v => bdryVal regPath v ξ) = fun v : ℝ => F v := funext heq
  rw [this] at hcode
  exact exists_crosscut_of_bdryCode hWc hW0 hσ hF hcode

/-! ### Continuity of strip paths -/

/-- A strip path separated on its strip life, with an unbounded strip clock, is continuous. -/
theorem continuous_stripPath {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hsep : ∀ s, Strip.IsStripLife w v ζ s → Strip.IsSepMark (Strip.extPath w) (Strip.extPath v) s)
    (hcl : Zhan.HasUnboundedStripClock w v ζ) : Continuous (stripPath w v) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  obtain ⟨S, -, hS, htS⟩ := exists_isStripLife_mem_Icc hsep hcl (show (0 : ℝ) ≤ (t₀ : ℝ) + 1 by positivity)
  have hc : ContinuousOn (Strip.stripDriver (Strip.extPath w) (Strip.extPath v)) (Icc 0 ((t₀ : ℝ) + 1)) :=
    hS.continuousOn_stripDriver.mono (Icc_subset_Icc_right htS.2)
  have hw : ContinuousWithinAt (Strip.stripDriver (Strip.extPath w) (Strip.extPath v)) (Ici 0) (t₀ : ℝ) := by
    refine (hc (t₀ : ℝ) ⟨t₀.coe_nonneg, by linarith⟩).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin.2 ⟨Iio ((t₀ : ℝ) + 1), isOpen_Iio, by simp, fun x hx => ⟨hx.2, hx.1.le⟩⟩
  have h := hw.comp NNReal.continuous_coe.continuousWithinAt (s := univ) (fun x _ => x.coe_nonneg)
  exact (continuousWithinAt_univ _ _).1 h

/-! ### The mixture transfer -/

/-- **Each mixture component has the measurable crosscut property almost surely.** -/
theorem ae_stripCodeGood_component {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8)
    (hA2 : FourForceCrosscutG3LifeStatement.{u} κ) (u' : ℝ) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin 2 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ (UpMark.upWordXL ![u']) ![] (UpMark.a33RhoL κ) ![] P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, StripCodeGood (stripPath (W · ω) (VL 0 · ω)) := by
  filter_upwards [ae_stripCrosscutGood_component hκ4 hκ8 hA2 u' hE,
    UpMark.ae_hasUnboundedStripClock_a33 hκ4.le hE, hE.2.2.2.2] with ω hgood hcl hp
  have hsep : ∀ s, Strip.IsStripLife (W · ω) (VL 0 · ω) (ζ ω) s →
      Strip.IsSepMark (Strip.extPath (W · ω)) (Strip.extPath (VL 0 · ω)) s :=
    fun s hs => UpMark.isSepMark_of_up hp (UpMark.upWordXL_zero _) hs
  exact stripCodeGood_of_stripCrosscutGood (continuous_stripPath hsep hcl) hgood

/-- The forced law of every `u` gives measure zero to the complement of the measurable crosscut property. -/
theorem forcedLaw_compl_stripCodeGood_eq_zero {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8)
    (hA2 : FourForceCrosscutG3LifeStatement.{0} κ) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {β : ℝ≥0 → Ω → ℝ} (hβ : IsPreBrownianReal β P) (hβm : ∀ t, Measurable (β t)) (u' : ℝ) :
    (P.map (Mix.pathOf β)) {γ | Mix.forcedPath κ (3 - κ / 2) u' γ ∈ {ξ | StripCodeGood ξ}ᶜ} = 0 := by
  have hκ0 : 0 < κ := by linarith
  obtain ⟨Ω₁, m₁, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, hE₁⟩ :=
    exists_isIntegratedSLEEvolution_assembled (a := κ) (xL := UpMark.upWordXL ![u']) (xR := ![])
      (ρL := UpMark.a33RhoL κ) (ρR := ![]) hκ0 (isOrderedForceWord_up u')
  have hcomp := ae_stripCodeGood_component hκ4 hκ8 hA2 u' hE₁
  have hlaw₁ := UpMark.map_stripDriver_eq_forcedLaw_a33 hκ4.le hE₁ hβ hβm
  have hNm : MeasurableSet {ξ : ℝ≥0 → ℝ | StripCodeGood ξ}ᶜ := measurableSet_stripCodeGood.compl
  show (P.map (Mix.pathOf β)) (Mix.forcedPath κ (3 - κ / 2) u' ⁻¹' {ξ | StripCodeGood ξ}ᶜ) = 0
  rw [Measure.map_apply (Mix.measurable_pathOf hβm) (Mix.measurable_forcedPath u' hNm)]
  have hmeas : Measurable fun ω' => Mix.forcedPath κ (3 - κ / 2) u' (Mix.pathOf β ω') :=
    (Mix.measurable_forcedPath u').comp (Mix.measurable_pathOf hβm)
  have e1 : P (Mix.pathOf β ⁻¹' (Mix.forcedPath κ (3 - κ / 2) u' ⁻¹' {ξ | StripCodeGood ξ}ᶜ)) =
      (P.map fun ω' => Mix.forcedPath κ (3 - κ / 2) u' (Mix.pathOf β ω')) {ξ | StripCodeGood ξ}ᶜ := by
    rw [Measure.map_apply hmeas hNm]
    rfl
  rw [e1, ← hlaw₁]
  obtain ⟨𝓗₁, B₂, hB₂, -, -, hae₁⟩ := UpMark.exists_stripDriver_eq_forcedDrv_a33 hκ4.le hE₁
  have hB₂m : ∀ t, Measurable (B₂ t) := fun t => (hB₂.2.1 t).mono (𝓗₁.le t) le_rfl
  have hm : AEMeasurable (fun ω (t : ℝ≥0) =>
      Strip.stripDriver (Strip.extPath (W₁ · ω)) (Strip.extPath (VL₁ 0 · ω)) t) P₁ :=
    ⟨fun ω t => Mix.forcedDrv κ (3 - κ / 2) (fun _ => u') B₂ t ω,
      Measurable.of_eval fun t => Mix.measurable_forcedDrv (κ := κ) (σ := 3 - κ / 2) measurable_const hB₂m t,
      hae₁.mono fun ω hω => funext hω⟩
  rw [Measure.map_apply_of_aemeasurable hm hNm]
  exact ae_iff.1 hcomp

/-- **Ordinary `SLE_κ` at the point `−1`**, `4 < κ < 8`: on a filtered probability space carrying a Brownian motion
with continuous paths started at `0`, almost surely the first-swallow conclusion holds at `−1`. The strip driver law is
the mixture of the forced laws; every forced law gives measure zero to the measurable set of strip paths without the
code (`forcedLaw_compl_stripCodeGood_eq_zero`); the strip life of ordinary `SLE_κ` ends at the first swallowing time
of `−1`, its driver is the reconstruction before that time, and its trace gives the boundary extension
(`ae_isLoewnerTrace_sleTrace`), so the code gives the crosscut (`exists_crosscut_of_stripCodeGood`). -/
theorem ae_firstSwallowGood_neg_one_ord_meas {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8)
    (hA2 : FourForceCrosscutG3LifeStatement.{0} κ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) :
    ∀ᵐ ω ∂P, FirstSwallowGood κ (drive κ B ω) (-1) := by
  have hκ0 : 0 < κ := by linarith
  have hσ : |3 - κ / 2| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hP : IsProbabilityMeasure P := hB.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hBm : ∀ t, Measurable (B t) := fun t => (hB.2.1 t).mono (𝓕.le t) le_rfl
  set Ξ : Ω → ℝ≥0 → ℝ := fun ω => stripPath (ordW κ B · ω) (ordV κ B · ω) with hΞ
  have hE := isStripSLEEvolution_ord hκ0 hB hBc hB0
  have hsepw : Strip.IsSeparatedStripWord (![] : Fin 0 → ℝ) (![] : Fin 0 → ℝ) :=
    ⟨fun a => a.elim0, fun i => i.elim0, fun a => a.elim0, fun i => i.elim0⟩
  have hpre : Strip.HasStripPrefixSums κ (![] : Fin 0 → ℝ) (![] : Fin 0 → ℝ) :=
    ⟨fun j => j.elim0, fun j => j.elim0⟩
  -- the strip driver law, and the strip driver path is a.e. measurable
  obtain ⟨𝓗, B', hB', -, -, hlaw⟩ := exists_map_stripDriver_ord_eq_mixLaw hκ4 hκ8 hB hBc hB0
  have hB'm : ∀ t, Measurable (B' t) := fun t => (hB'.2.1 t).mono (𝓗.le t) le_rfl
  obtain ⟨𝓗₂, B₂, hB₂, hae₂⟩ := Zhan.exists_stripBrownian_of_prefixSums hκ0 hsepw hpre hE
  have hB₂m : ∀ t, Measurable (B₂ t) := fun t => (hB₂.2.1 t).mono (𝓗₂.le t) le_rfl
  have hΞm : AEMeasurable Ξ P := by
    refine ⟨fun ω t => Real.sqrt κ * B₂ t ω + ((0 : ℝ) - Strip.tauPlus κ (![] : Fin 0 → ℝ) ![] 0) / 2 * t,
      Measurable.of_eval fun t => ((hB₂m t).const_mul _).add measurable_const,
      hae₂.mono fun ω hω => funext fun t => ?_⟩
    have h := (hω t).2
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero] at h
    exact h
  -- the complement of the code is null for the strip driver law
  have hNm : MeasurableSet {ξ : ℝ≥0 → ℝ | StripCodeGood ξ}ᶜ := measurableSet_stripCodeGood.compl
  have hnull : P (Ξ ⁻¹' {ξ | StripCodeGood ξ}ᶜ) = 0 := by
    rw [← Measure.map_apply_of_aemeasurable hΞm hNm]
    have hlaw' : P.map Ξ = Mix.mixLaw P κ (3 - κ / 2) B' := hlaw
    rw [hlaw', Mix.mixLaw_eq_map_prod hκ0 hσ hB'm, Measure.map_apply Mix.measurable_forcedPath_uncurry hNm,
      Measure.prod_apply (Mix.measurable_forcedPath_uncurry hNm)]
    have h0 : ∀ u', (P.map (Mix.pathOf B')) (Prod.mk u' ⁻¹' ((fun p : ℝ × (ℝ≥0 → ℝ) =>
        Mix.forcedPath κ (3 - κ / 2) p.1 p.2) ⁻¹' {ξ | StripCodeGood ξ}ᶜ)) = 0 :=
      fun u' => forcedLaw_compl_stripCodeGood_eq_zero hκ4 hκ8 hA2 hB'.1.toIsPreBrownianReal hB'm u'
    simp only [h0, lintegral_zero]
  have hgoodae : ∀ᵐ ω ∂P, StripCodeGood (Ξ ω) := ae_iff.2 hnull
  -- `−1` is swallowed
  have hsw : ∀ᵐ ω ∂P, ∃ σ, RealSwallowAt (drive κ B ω) (-1) σ := by
    have hnB : IsBrownianReal (-B) P := hB.1.neg
    filter_upwards [ae_exists_realSwallowAt hnB (fun t => (hBm t).neg) (fun ω => (hBc ω).neg)
      (fun ω => by simp [hB0 ω]) hκ4 one_pos] with ω ⟨σ, hσ⟩
    rw [drive_neg_eq, show (1 : ℝ) = -(-1) by norm_num] at hσ
    exact ⟨σ, realSwallowAt_neg_iff.1 hσ⟩
  filter_upwards [hgoodae, hsw, ae_ordW_eq hκ0 hB hBc hB0, hE.2.2.2.2,
    Zhan.ae_hasUnboundedStripClock hκ0 hsepw hpre hE, ae_isLoewnerTrace_sleTrace hB.1 hκ0]
    with ω hgood ⟨σ, hσ⟩ hW hp hcl htr
  set w : ℝ≥0 → ℝ := fun t => ordW κ B t ω with hw
  set v : ℝ≥0 → ℝ := fun t => ordV κ B t ω with hv
  have hdrive : Strip.extPath w = drive κ B ω := funext fun r => by simp [Strip.extPath, drive, hw, hW]
  have hwc : Continuous w := by
    have : w = fun t => Real.sqrt κ * B t ω := funext hW
    rw [this]; exact continuous_const.mul (hBc ω)
  have hw0 : w 0 = 0 := by simp [hw, hW, hB0]
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} = univ := eq_univ_of_forall fun t => ENNReal.coe_lt_top
  have hvc : Continuous v := by
    have h := hp.2.2.2.2.1 0
    rw [hset, continuousOn_univ] at h
    exact h
  have hle : ∀ t, v t ≤ w t := fun t => hp.2.2.2.2.2.2.2.1 t ENNReal.coe_lt_top 0
  have hveq : ∀ t : ℝ≥0, v t = -1 + ∫ r in (0 : ℝ)..t, 2 / (v r.toNNReal - w r.toNNReal) := fun t => by
    have h := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t ENNReal.coe_lt_top 0
    rwa [show Strip.wordXL (![] : Fin 0 → ℝ) 0 = -1 from Strip.wordXL_last _] at h
  have hσ' : RealSwallowAt (Strip.extPath w) (-1) σ := by rw [hdrive]; exact hσ
  have hlife := isStripLife_iff_lt_of_realSwallowAt hwc hvc hw0 hveq hle hσ'
  have hsep : ∀ s, Strip.IsStripLife w v ⊤ s → Strip.IsSepMark (Strip.extPath w) (Strip.extPath v) s :=
    fun s hs => Strip.isSepMark_of_isIntegratedSLEPath hp hs
  have hend : ENNReal.ofReal σ = reconEnd (stripPath w v) :=
    eq_ofReal_of_forall_lt_iff fun s => by rw [← isStripLife_iff_lt_reconEnd hsep hcl, hlife s]
  have hagree : ∀ s ∈ Ico (0 : ℝ) σ, drive κ B ω s = reconDrv (stripPath w v) s := fun s hs => by
    have hl : Strip.IsStripLife w v ⊤ s.toNNReal :=
      (hlife _).2 (by rw [Real.coe_toNNReal _ hs.1]; exact hs.2)
    have h := eq_reconDrv_of_isStripLife hsep hcl hl
    rw [Real.coe_toNNReal _ hs.1] at h
    rw [← h, ← hdrive]
    rfl
  have hdc : Continuous (drive κ B ω) := by rw [← hdrive]; exact hwc.comp continuous_real_toNNReal
  have hd0 : drive κ B ω 0 = 0 := by simp [drive, hB0]
  have hξc : Continuous (stripPath w v) := continuous_stripPath hsep hcl
  obtain ⟨F, hF1, hF2, hF3⟩ := htr.exists_extension hdc hd0 hσ.1.le
  obtain ⟨γ, hγ, hγ0, hγ1, hfr⟩ := exists_crosscut_of_stripCodeGood hξc hgood hσ.1 hend hdc hd0 hagree
    (F := F) ⟨hF1, hF2, hF3⟩
  refine ⟨σ, hσ, γ, hγ, by linarith, hγ1, hfr,
    fun _ => ⟨fun h8 => absurd h8 (not_le.2 hκ8), fun _ => hγ0⟩, fun h => absurd h (by norm_num)⟩

/-- **A.3 for `4 < κ < 8`** (§A.3.2): `FirstSwallowCrosscutStatement κ` follows from A.2 in the (G3) configuration
over the strip life (`FourForceCrosscutG3LifeStatement`) alone; the measurability input of
`A34.firstSwallowCrosscutStatement_of_life` is replaced by the measurable code `StripCodeGood`. -/
theorem firstSwallowCrosscutStatement_of_life_meas {κ : ℝ} (hκ8 : κ < 8)
    (hA2 : FourForceCrosscutG3LifeStatement.{0} κ) : FirstSwallowCrosscutStatement.{u} κ := by
  refine firstSwallowCrosscutStatement_of_neg_one fun hκ4 {Ω} _ P B hB => ?_
  obtain ⟨B'', hB''m, hB''c, hB''0, hB'', hae⟩ := RS.exists_good_version0 hB
  have hF := OneForce.isFilteredBrownianReal_natFilt hB'' hB''m
  filter_upwards [ae_firstSwallowGood_neg_one_ord_meas hκ4 hκ8 hA2 hF hB''c hB''0, hae] with ω hω hae
  have : drive κ B ω = drive κ B'' ω := funext fun t => by simp [drive, hae]
  rwa [this]

end InteractingSLE.ZhanGT4.A35
