/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CrosscutA3Strip
import InteractingSLE.Spec.ZhanGT4.CrosscutA3Scale
import InteractingSLE.Spec.ZhanGT4.CrosscutA3Swallow
import InteractingSLE.Spec.ZhanGT4.CrosscutA3SwallowKernel
import InteractingSLE.Spec.ZhanGT4.MixtureA33ChordalMain
import InteractingSLE.Spec.Sec2.Assembly2Entr
import InteractingSLE.Spec.Sec2.OneForceLaw
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowBessel
import QuantumZipper.Proofs.RS.TransienceCanon

/-!
# A.3.2: the first-swallow crosscut for `4 < κ < 8` from A.2

Packet PROVE-ZHAN-A34. Source: Astra, *Follow-up proofs and dependency audit*, §A.3.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L686–L720, ruling R38): "Consequently the original strip law is
the mixture, with density `f(u) du`, of these forced laws … Each mixture component therefore has a crosscut outer
boundary from `y < x` to a positive point. The mixture identity proves the ordinary first-swallow claim. Reflection
treats `x > 0`."

## The two inputs

* **A.2 for the component word**, `FourForceCrosscutG3LifeStatement κ`: for `4 < κ < 8`, `y < x < 0` and every integrated
  `SLE_κ(κ − 4, −4)` evolution from `(0; x, y)`, almost surely the outer boundary in `ℍ` of the closure of the union of
  its hulls **during the strip life of `x`** (the times before the driver first meets the flow of `x`, A.2's "before its
  first force collision") is `γ((0, 1))` for a simple crosscut from `y` to a positive point.

  This differs from `DualA2.FourForceCrosscutG3Statement`, which uses the frozen lifetime `ζ` of the amalgamated word:
  at the first collision the threshold sum is `(κ − 4) + (−4) = κ − 8`, which is `> −2` for `6 < κ < 8`, so there `ζ`
  goes past the first force collision (the evolution continues as `SLE_κ(κ − 8)` and its terminal hull grows); the
  frozen-lifetime form is then not A.2's assertion (handoff).
* **Measurability of the crosscut event** as a set of strip paths, `MeasurableSet {ξ | StripCrosscutGood ξ}`: the
  mixture identity transfers null *measurable* sets only (a non-measurable set can be outer-null for every component law
  but not for the mixture).

## Main results

* `StripCrosscutGood ξ`: the first-swallow crosscut property of the chordal driver `reconDrv ξ` reconstructed from a
  strip path `ξ`, at the end of its strip life;
* `ae_stripCrosscutGood_component`: each mixture component satisfies it almost surely (A.2, the reconstruction
  `eq_reconDrv_of_isStripLife`, and the kernel identity `frontier_compl_fwdHull_eq_outerBoundary`);
* `ae_firstSwallowGood_neg_one_ord`: ordinary `SLE_κ` satisfies the first-swallow conclusion at `−1`;
* **`firstSwallowCrosscutStatement_of_life`**: `FirstSwallowCrosscutStatement κ` for `4 < κ < 8` from the two inputs.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A34

open QuantumZipper

/-! ### The two inputs -/

/-- **A.2's crosscut assertion in the (G3) configuration, over the strip life of the inner mark** (§A.2 L519–L521,
§A.3.2 L694–L705): for `4 < κ < 8`, `y < x < 0` and every integrated `SLE_κ(κ − 4, −4)` evolution from `(0; x, y)`,
almost surely the outer boundary in `ℍ` of the closure of the union of its hulls before the driver first meets the
flow of `x` is `γ((0, 1))` for a simple crosscut `γ` with `γ(0) = y` and `γ(1) > 0`. -/
def FourForceCrosscutG3LifeStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 2 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 0 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ ![x, y] ![] ![κ - 4, -4] ![] P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re = y ∧ 0 < (γ 1).re ∧
          outerBoundary (closure (⋃ (t : ℝ≥0) (_ : Strip.IsStripLife (W · ω) (VL 0 · ω) (ζ ω) t),
            fwdHull (fun s : ℝ => W s.toNNReal ω) t)) = γ '' Ioo 0 1

/-- **The first-swallow crosscut property of a strip path**: for every continuous driver `W` that agrees with the
reconstruction `reconDrv ξ` before the end `σ` of the strip life, `∂(ℍ \ K_σ) ∩ ℍ` is the open part of a simple crosscut
from a point left of `−1` to a positive point. -/
def StripCrosscutGood (ξ : ℝ≥0 → ℝ) : Prop :=
  ∀ (W : ℝ → ℝ) (σ : ℝ), 0 < σ → ENNReal.ofReal σ = reconEnd ξ → Continuous W → W 0 = 0 →
    (∀ s ∈ Ico (0 : ℝ) σ, W s = reconDrv ξ s) →
      ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re < -1 ∧ 0 < (γ 1).re ∧
        frontier (H \ fwdHull W σ) ∩ H = γ '' Ioo 0 1

/-! ### Common deterministic steps -/

/-- An extended real with the same `ℝ≥0`-points strictly below as `ofReal σ` is `ofReal σ`. -/
theorem eq_ofReal_of_forall_lt_iff {e : ℝ≥0∞} {σ : ℝ} (h : ∀ s : ℝ≥0, (s : ℝ≥0∞) < e ↔ (s : ℝ) < σ) :
    ENNReal.ofReal σ = e := by
  have h' : ∀ s : ℝ≥0, (s : ℝ≥0∞) < e ↔ (s : ℝ≥0∞) < ENNReal.ofReal σ := fun s => by
    rw [h s, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg s.coe_nonneg]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hfin : ENNReal.ofReal σ ≠ ⊤ := ENNReal.ofReal_ne_top
    have h1 := (h' (ENNReal.ofReal σ).toNNReal).1
    rw [ENNReal.coe_toNNReal hfin] at h1
    exact lt_irrefl _ (h1 hlt)
  · have hfin : e ≠ ⊤ := ne_top_of_lt hlt
    have h1 := (h' e.toNNReal).2
    rw [ENNReal.coe_toNNReal hfin] at h1
    exact lt_irrefl _ (h1 hlt)

theorem upWordXL_eq (u : ℝ) : UpMark.upWordXL ![u] = ![-1, -1 - Real.exp u] := by
  funext i; fin_cases i <;> simp [UpMark.upWordXL]

/-! ### Each mixture component -/

/-- **Each mixture component has the strip crosscut property almost surely** (A.2 over the strip life, the
reconstruction of the driver on the strip life and the kernel identity at the end of the strip life). -/
theorem ae_stripCrosscutGood_component {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8)
    (hA2 : FourForceCrosscutG3LifeStatement.{u} κ) (u' : ℝ) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin 2 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ (UpMark.upWordXL ![u']) ![] (UpMark.a33RhoL κ) ![] P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, StripCrosscutGood (stripPath (W · ω) (VL 0 · ω)) := by
  have hE' : IsIntegratedSLEEvolution κ ![-1, -1 - Real.exp u'] ![] ![κ - 4, -4] ![] P 𝓕 W VL VR B ζ := by
    rw [← upWordXL_eq]; exact hE
  have hy : -1 - Real.exp u' < -1 := by linarith [Real.exp_pos u']
  filter_upwards [hA2 hκ4 hκ8 (-1 - Real.exp u') (-1) hy (by norm_num) P 𝓕 W VL VR B ζ hE',
    UpMark.ae_hasUnboundedStripClock_a33 hκ4.le hE, hE.2.2.2.2] with ω hγ hcl hp
  obtain ⟨γ, hγc, hγ0, hγ1, hob⟩ := hγ
  intro W' σ hσ hσend hW'c hW'0 hW'eq
  have hsep : ∀ s, Strip.IsStripLife (W · ω) (VL 0 · ω) (ζ ω) s →
      Strip.IsSepMark (Strip.extPath (W · ω)) (Strip.extPath (VL 0 · ω)) s :=
    fun s hs => UpMark.isSepMark_of_up hp (UpMark.upWordXL_zero _) hs
  have hlife : ∀ s : ℝ≥0, Strip.IsStripLife (W · ω) (VL 0 · ω) (ζ ω) s ↔ (s : ℝ) < σ := fun s => by
    rw [isStripLife_iff_lt_reconEnd hsep hcl, ← hσend, ← ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_lt_ofReal_iff hσ]
  have hagree : ∀ r ∈ Ico (0 : ℝ) σ, W' r = (fun s : ℝ => W s.toNNReal ω) r := fun r hr => by
    rw [hW'eq r hr]
    have hl : Strip.IsStripLife (W · ω) (VL 0 · ω) (ζ ω) r.toNNReal :=
      (hlife _).2 (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2)
    have := eq_reconDrv_of_isStripLife hsep hcl hl
    rw [Real.coe_toNNReal _ hr.1] at this
    exact this.symm
  have hU : (⋃ (t : ℝ≥0) (_ : Strip.IsStripLife (W · ω) (VL 0 · ω) (ζ ω) t),
      fwdHull (fun s : ℝ => W s.toNNReal ω) t) = hullBefore W' σ := by
    ext z
    simp only [mem_iUnion, hullBefore]
    constructor
    · rintro ⟨t, ht, hz⟩
      have htσ := (hlife t).1 ht
      exact ⟨t, ⟨t.coe_nonneg, htσ⟩, by rwa [fwdHull_congr_of_lt t.coe_nonneg htσ hagree]⟩
    · rintro ⟨t, ht, hz⟩
      refine ⟨t.toNNReal, (hlife _).2 (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2), ?_⟩
      rw [Real.coe_toNNReal _ ht.1, ← fwdHull_congr_of_lt ht.1 ht.2 hagree]
      exact hz
  refine ⟨γ, hγc, by rw [hγ0]; exact hy, hγ1, ?_⟩
  rw [frontier_compl_fwdHull_eq_outerBoundary hW'c hW'0 hσ, ← hU, hob]

/-! ### Ordinary `SLE_κ` at the point `−1` -/

theorem isOrderedForceWord_up (u' : ℝ) : IsOrderedForceWord (UpMark.upWordXL ![u']) (![] : Fin 0 → ℝ) := by
  rw [upWordXL_eq]
  refine ⟨fun i j hij => ?_, fun i => ?_, fun i => i.elim0, fun i => i.elim0⟩
  · have he := Real.exp_pos u'
    fin_cases i <;> fin_cases j <;> simp_all
    positivity
  · have he := Real.exp_pos u'
    fin_cases i <;> simp
    linarith

/-- The forced law of every `u` gives measure zero to the complement of the strip crosscut property. -/
theorem forcedLaw_compl_eq_zero {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hA2 : FourForceCrosscutG3LifeStatement.{0} κ)
    (hM : MeasurableSet {ξ : ℝ≥0 → ℝ | StripCrosscutGood ξ}) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {β : ℝ≥0 → Ω → ℝ} (hβ : IsPreBrownianReal β P) (hβm : ∀ t, Measurable (β t)) (u' : ℝ) :
    (P.map (Mix.pathOf β)) {γ | Mix.forcedPath κ (3 - κ / 2) u' γ ∈ {ξ | StripCrosscutGood ξ}ᶜ} = 0 := by
  have hκ0 : 0 < κ := by linarith
  obtain ⟨Ω₁, m₁, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, hE₁⟩ :=
    exists_isIntegratedSLEEvolution_assembled (a := κ) (xL := UpMark.upWordXL ![u']) (xR := ![])
      (ρL := UpMark.a33RhoL κ) (ρR := ![]) hκ0 (isOrderedForceWord_up u')
  have hcomp := ae_stripCrosscutGood_component hκ4 hκ8 hA2 u' hE₁
  have hlaw₁ := UpMark.map_stripDriver_eq_forcedLaw_a33 hκ4.le hE₁ hβ hβm
  have hNm : MeasurableSet {ξ : ℝ≥0 → ℝ | StripCrosscutGood ξ}ᶜ := hM.compl
  show (P.map (Mix.pathOf β)) (Mix.forcedPath κ (3 - κ / 2) u' ⁻¹' {ξ | StripCrosscutGood ξ}ᶜ) = 0
  rw [Measure.map_apply (Mix.measurable_pathOf hβm) (Mix.measurable_forcedPath u' hNm)]
  have hmeas : Measurable fun ω' => Mix.forcedPath κ (3 - κ / 2) u' (Mix.pathOf β ω') :=
    (Mix.measurable_forcedPath u').comp (Mix.measurable_pathOf hβm)
  have e1 : P (Mix.pathOf β ⁻¹' (Mix.forcedPath κ (3 - κ / 2) u' ⁻¹' {ξ | StripCrosscutGood ξ}ᶜ)) =
      (P.map fun ω' => Mix.forcedPath κ (3 - κ / 2) u' (Mix.pathOf β ω')) {ξ | StripCrosscutGood ξ}ᶜ := by
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
the mixture of the forced laws (`exists_map_stripDriver_ord_eq_mixLaw`); every forced law gives measure zero to the
measurable set of strip paths without the crosscut property (`forcedLaw_compl_eq_zero`); the strip life of ordinary
`SLE_κ` ends at the first swallowing time of `−1` (`isStripLife_iff_lt_of_realSwallowAt`), and its driver is the
reconstruction from its strip path before that time (`eq_reconDrv_of_isStripLife`). -/
theorem ae_firstSwallowGood_neg_one_ord {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8)
    (hA2 : FourForceCrosscutG3LifeStatement.{0} κ) (hM : MeasurableSet {ξ : ℝ≥0 → ℝ | StripCrosscutGood ξ})
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
  -- the complement of the crosscut property is null for the strip driver law
  have hNm : MeasurableSet {ξ : ℝ≥0 → ℝ | StripCrosscutGood ξ}ᶜ := hM.compl
  have hnull : P (Ξ ⁻¹' {ξ | StripCrosscutGood ξ}ᶜ) = 0 := by
    rw [← Measure.map_apply_of_aemeasurable hΞm hNm]
    have hlaw' : P.map Ξ = Mix.mixLaw P κ (3 - κ / 2) B' := hlaw
    rw [hlaw', Mix.mixLaw_eq_map_prod hκ0 hσ hB'm, Measure.map_apply Mix.measurable_forcedPath_uncurry hNm,
      Measure.prod_apply (Mix.measurable_forcedPath_uncurry hNm)]
    have h0 : ∀ u', (P.map (Mix.pathOf B')) (Prod.mk u' ⁻¹' ((fun p : ℝ × (ℝ≥0 → ℝ) =>
        Mix.forcedPath κ (3 - κ / 2) p.1 p.2) ⁻¹' {ξ | StripCrosscutGood ξ}ᶜ)) = 0 :=
      fun u' => forcedLaw_compl_eq_zero hκ4 hκ8 hA2 hM hB'.1.toIsPreBrownianReal hB'm u'
    simp only [h0, lintegral_zero]
  have hgoodae : ∀ᵐ ω ∂P, StripCrosscutGood (Ξ ω) := ae_iff.2 hnull
  -- `−1` is swallowed
  have hsw : ∀ᵐ ω ∂P, ∃ σ, RealSwallowAt (drive κ B ω) (-1) σ := by
    have hnB : IsBrownianReal (-B) P := hB.1.neg
    filter_upwards [ae_exists_realSwallowAt hnB (fun t => (hBm t).neg) (fun ω => (hBc ω).neg)
      (fun ω => by simp [hB0 ω]) hκ4 one_pos] with ω ⟨σ, hσ⟩
    rw [drive_neg_eq, show (1 : ℝ) = -(-1) by norm_num] at hσ
    exact ⟨σ, realSwallowAt_neg_iff.1 hσ⟩
  filter_upwards [hgoodae, hsw, ae_ordW_eq hκ0 hB hBc hB0, hE.2.2.2.2,
    Zhan.ae_hasUnboundedStripClock hκ0 hsepw hpre hE] with ω hgood ⟨σ, hσ⟩ hW hp hcl
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
  obtain ⟨γ, hγ, hγ0, hγ1, hfr⟩ := hgood (drive κ B ω) σ hσ.1 hend hdc hd0 hagree
  refine ⟨σ, hσ, γ, hγ, by linarith, hγ1, hfr,
    fun _ => ⟨fun h8 => absurd h8 (not_le.2 hκ8), fun _ => hγ0⟩, fun h => absurd h (by norm_num)⟩

/-- **A.3 for `4 < κ < 8`** (§A.3.2): `FirstSwallowCrosscutStatement κ` follows from A.2 in the (G3) configuration
over the strip life (`FourForceCrosscutG3LifeStatement`) and the measurability of the strip crosscut property. -/
theorem firstSwallowCrosscutStatement_of_life {κ : ℝ} (hκ8 : κ < 8) (hA2 : FourForceCrosscutG3LifeStatement.{0} κ)
    (hM : MeasurableSet {ξ : ℝ≥0 → ℝ | StripCrosscutGood ξ}) : FirstSwallowCrosscutStatement.{u} κ := by
  refine firstSwallowCrosscutStatement_of_neg_one fun hκ4 {Ω} _ P B hB => ?_
  obtain ⟨B'', hB''m, hB''c, hB''0, hB'', hae⟩ := RS.exists_good_version0 hB
  have hF := OneForce.isFilteredBrownianReal_natFilt hB'' hB''m
  filter_upwards [ae_firstSwallowGood_neg_one_ord hκ4 hκ8 hA2 hM hF hB''c hB''0, hae] with ω hω hae
  have : drive κ B ω = drive κ B'' ω := funext fun t => by simp [drive, hae]
  rwa [this]

end InteractingSLE.ZhanGT4.A34
