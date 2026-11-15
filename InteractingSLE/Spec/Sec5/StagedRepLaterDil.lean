/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedKillTrace
import InteractingSLE.Spec.ZhanGT4.MixtureA33ChordalScale
import InteractingSLE.Spec.Sec7.CounterflowProbDilation

/-!
# Prop 5.9's killed comparison clause under a start-dependent dilation

Packet PROVE-STAGED-REP2. PROVE-PROP59-PIECES' candidate pieces are the joint-chart images **dilated** by a factor
`λ` that is a function of the stage start (the root experiment normalizes the far marks to `∓3`). The comparison
clause of the killed stage law (`IsStageLawFarK`, ruling R78) is a law statement about the rational-time samples of a
piece; the samples of a dilated piece are not a function of the rational samples of the undilated one by evaluation,
but they are by **continuous extension** (`sampExt`, a measurable limit along lower dyadic rationals). This file
proves:

* `sampExt_samp`: the continuous extension of the samples of a path continuous before its lifetime recovers the path;
* `samp_scale`: the samples of `t ↦ (√c)⁻¹ X(c t)` with lifetime `ζ/c` are `dilSamp c` of the samples of `X`;
* `farLife_scale`: the killed lifetime scales;
* `compPremiseFarK_dil`: the killed premise (evolutions traced up to the kill) is invariant under the Borel map
  `dilRec C` (start-dependent dilation of start and samples), by Brownian scaling of integrated evolutions
  (`ZhanGT4.UpMark.isIntegratedSLEEvolution_scale`) and of traces (`IsGeneratingTrace.dilate`);
* **`CompClauseK.dilate`**: the comparison clause of a piece passes to the piece dilated by `C (y ω)`, `C` a Borel
  function of the start.

R48: nothing here uses Theorem 1.2/1.3 or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedRepLater

open Prop59Stage Prop59Nodes StagedKill

/-! ### The continuous extension of rational samples -/

section Ext

variable {nL nR : ℕ}

/-- The values of a stage state: driver, left marks, right marks. -/
abbrev SV (nL nR : ℕ) := ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)

/-- The lower dyadic rational `⌊2ⁿ x⌋ / 2ⁿ`. -/
def lowQ (n : ℕ) (x : ℝ≥0) : ℚ≥0 := (⌊(2 : ℝ≥0) ^ n * x⌋₊ : ℚ≥0) / 2 ^ n

theorem lowQ_coe (n : ℕ) (x : ℝ≥0) : ((lowQ n x : ℚ≥0) : ℝ≥0) = (⌊(2 : ℝ≥0) ^ n * x⌋₊ : ℝ≥0) / 2 ^ n := by
  simp only [lowQ, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_pow, NNRat.cast_ofNat]

theorem lowQ_le (n : ℕ) (x : ℝ≥0) : ((lowQ n x : ℚ≥0) : ℝ≥0) ≤ x := by
  rw [lowQ_coe, div_le_iff₀ (pow_pos two_pos n), mul_comm]
  exact Nat.floor_le zero_le

theorem tendsto_lowQ (x : ℝ≥0) : Tendsto (fun n => ((lowQ n x : ℚ≥0) : ℝ≥0)) atTop (𝓝 x) := by
  rw [← NNReal.tendsto_coe]
  have hlow : ∀ n : ℕ, x - 1 / 2 ^ n ≤ (((lowQ n x : ℚ≥0) : ℝ≥0) : ℝ) := by
    intro n
    have h2 : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
    rw [lowQ_coe, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
    rw [le_div_iff₀ h2, sub_mul, one_div, inv_mul_cancel₀ h2.ne']
    have hf := Nat.lt_floor_add_one ((2 : ℝ≥0) ^ n * x)
    have hf' : (((2 : ℝ≥0) ^ n * x : ℝ≥0) : ℝ) < (⌊(2 : ℝ≥0) ^ n * x⌋₊ : ℝ) + 1 := by exact_mod_cast hf
    simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat] at hf'
    linarith
  have hup : ∀ n : ℕ, (((lowQ n x : ℚ≥0) : ℝ≥0) : ℝ) ≤ x := fun n => by exact_mod_cast lowQ_le n x
  have hl : Tendsto (fun n : ℕ => (x : ℝ) - 1 / 2 ^ n) atTop (𝓝 x) := by
    have h : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have e : (fun n : ℕ => (x : ℝ) - 1 / 2 ^ n) = fun n => (x : ℝ) - ((1 : ℝ) / 2) ^ n := by
      funext n; rw [div_pow, one_pow]
    rw [e]
    simpa using (tendsto_const_nhds (x := (x : ℝ))).sub h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlow hup

/-- **The continuous extension of rational samples** at a time `x`: the limit superior along the lower dyadic
rationals, coordinatewise. -/
def sampExt (f : ℚ≥0 → SV nL nR) (x : ℝ≥0) : SV nL nR :=
  (limsup (fun n => (f (lowQ n x)).1) atTop, fun i => limsup (fun n => (f (lowQ n x)).2.1 i) atTop,
    fun k => limsup (fun n => (f (lowQ n x)).2.2 k) atTop)

theorem measurable_eval_lowQ {α : Type*} {mα : MeasurableSpace α} {g : α → ℚ≥0 → SV nL nR} (hg : Measurable g)
    {x : α → ℝ≥0} (hx : Measurable x) (n : ℕ) : Measurable fun a => g a (lowQ n (x a)) := by
  have hF : Measurable fun p : (ℚ≥0 → SV nL nR) × ℕ => p.1 ((p.2 : ℚ≥0) / 2 ^ n) :=
    measurable_from_prod_countable_left fun k => measurable_pi_apply (((k : ℚ≥0) / 2 ^ n : ℚ≥0))
  exact hF.comp (hg.prodMk ((measurable_const.mul hx).nat_floor))

/-- The continuous extension is jointly measurable in the samples and the time. -/
theorem measurable_sampExt {α : Type*} {mα : MeasurableSpace α} {g : α → ℚ≥0 → SV nL nR} (hg : Measurable g)
    {x : α → ℝ≥0} (hx : Measurable x) : Measurable fun a => sampExt (g a) (x a) := by
  have h := measurable_eval_lowQ hg hx
  refine Measurable.prodMk (Measurable.limsup fun n => (h n).fst) (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_iff.2 fun i => Measurable.limsup fun n => (measurable_pi_apply i).comp (h n).snd.fst
  · exact measurable_pi_iff.2 fun k => Measurable.limsup fun n => (measurable_pi_apply k).comp (h n).snd.snd

/-- **The continuous extension recovers a path continuous before its lifetime.** -/
theorem sampExt_samp {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ})
    (hvR : ∀ k, ContinuousOn (vR k) {t | (t : ℝ≥0∞) < ζ}) {x : ℝ≥0} (hx : (x : ℝ≥0∞) < ζ) :
    sampExt (samp w vL vR ζ).2 x = (w x, fun i => vL i x, fun k => vR k x) := by
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hnhds : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} ∈ 𝓝 x := hopen.mem_nhds hx
  have hlt : ∀ n, (((lowQ n x : ℚ≥0) : ℝ≥0) : ℝ≥0∞) < ζ := fun n =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (lowQ_le n x)) hx
  have hval : ∀ n, (samp w vL vR ζ).2 (lowQ n x) =
      (w (lowQ n x), fun i => vL i (lowQ n x), fun k => vR k (lowQ n x)) := fun n =>
    samp_snd_of_lt w vL vR (hlt n)
  have hT := tendsto_lowQ x
  have hlim : ∀ {g : ℝ≥0 → ℝ}, ContinuousOn g {t | (t : ℝ≥0∞) < ζ} →
      limsup (fun n => g (lowQ n x)) atTop = g x := fun hg =>
    ((hg.continuousAt hnhds).tendsto.comp hT).limsup_eq
  simp only [sampExt, hval]
  exact Prod.ext (hlim hw) (Prod.ext (funext fun i => hlim (hvL i)) (funext fun k => hlim (hvR k)))

end Ext

/-! ### Dilated samples -/

section Dil

variable {nL nR : ℕ}

/-- The dilation of a state value by `(√c)⁻¹` (Brownian scaling with time factor `c`). -/
def dilV (c : ℝ≥0) (v : SV nL nR) : SV nL nR :=
  ((√(c : ℝ))⁻¹ * v.1, fun i => (√(c : ℝ))⁻¹ * v.2.1 i, fun k => (√(c : ℝ))⁻¹ * v.2.2 k)

/-- **The dilated samples**: the samples of `t ↦ (√c)⁻¹ X(c t)` with lifetime `ζ/c`, read from the samples of `X`
through the continuous extension. -/
def dilSamp (c : ℝ≥0) (s : Samp nL nR) : Samp nL nR :=
  (s.1 / c, fun q => if ((q : ℝ≥0) : ℝ≥0∞) < s.1 / c then dilV c (sampExt s.2 (c * q)) else 0)

/-- **The samples of a scaled path** (continuous before its lifetime) are the dilated samples. -/
theorem samp_scale {c : ℝ≥0} (hc : c ≠ 0) {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ})
    (hvR : ∀ k, ContinuousOn (vR k) {t | (t : ℝ≥0∞) < ζ}) :
    samp (fun t => (√(c : ℝ))⁻¹ * w (c * t)) (fun i t => (√(c : ℝ))⁻¹ * vL i (c * t))
      (fun k t => (√(c : ℝ))⁻¹ * vR k (c * t)) (ζ / c) = dilSamp c (samp w vL vR ζ) := by
  refine Prod.ext rfl (funext fun q => ?_)
  show (if ((q : ℝ≥0) : ℝ≥0∞) < ζ / c then _ else 0) =
    (if ((q : ℝ≥0) : ℝ≥0∞) < ζ / c then dilV c (sampExt (samp w vL vR ζ).2 (c * q)) else 0)
  by_cases hq : ((q : ℝ≥0) : ℝ≥0∞) < ζ / c
  · simp only [hq, ↓reduceIte]
    rw [sampExt_samp hw hvL hvR ((ZhanGT4.UpMark.coe_lt_div_iff hc).1 hq)]
    rfl
  · simp only [hq, ↓reduceIte]

/-- **The first far contact of a scaled path** is the scaled first far contact. -/
theorem farHit_scale {c : ℝ≥0} (hc : c ≠ 0) (iL : Fin nL) (iR : Fin nR) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) :
    farHit iL iR (fun t => (√(c : ℝ))⁻¹ * w (c * t)) (fun i t => (√(c : ℝ))⁻¹ * vL i (c * t))
      (fun k t => (√(c : ℝ))⁻¹ * vR k (c * t)) = farHit iL iR w vL vR / c := by
  have ha : (√(c : ℝ))⁻¹ ≠ 0 := (ZhanGT4.UpMark.scaleFactor_pos hc).ne'
  have hiff : ∀ t : ℝ≥0, ((√(c : ℝ))⁻¹ * w (c * t) = (√(c : ℝ))⁻¹ * vL iL (c * t) ∨
      (√(c : ℝ))⁻¹ * w (c * t) = (√(c : ℝ))⁻¹ * vR iR (c * t)) ↔
      (w (c * t) = vL iL (c * t) ∨ w (c * t) = vR iR (c * t)) := fun t => by
    rw [mul_right_inj' ha, mul_right_inj' ha]
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
  have hct : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  apply le_antisymm
  · rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct)]
    conv_rhs => unfold farHit
    refine le_iInf₂ fun s hs => ?_
    have h1 : farHit iL iR (fun t => (√(c : ℝ))⁻¹ * w (c * t)) (fun i t => (√(c : ℝ))⁻¹ * vL i (c * t))
        (fun k t => (√(c : ℝ))⁻¹ * vR k (c * t)) ≤ ((s / c : ℝ≥0) : ℝ≥0∞) := by
      refine iInf₂_le (s / c) ?_
      rw [hiff, mul_div_cancel₀ s hc]
      exact hs
    calc _ ≤ ((s / c : ℝ≥0) : ℝ≥0∞) * c := mul_le_mul_left h1 _
      _ = s := by rw [← ENNReal.coe_mul, div_mul_cancel₀ s hc]
  · conv_rhs => unfold farHit
    refine le_iInf₂ fun t ht => ?_
    rw [ENNReal.div_le_iff_le_mul (Or.inl hc0) (Or.inl hct)]
    have h1 : farHit iL iR w vL vR ≤ ((c * t : ℝ≥0) : ℝ≥0∞) := iInf₂_le (c * t) ((hiff t).1 ht)
    rwa [ENNReal.coe_mul, mul_comm] at h1

/-- **The killed lifetime of a scaled path** is the scaled killed lifetime. -/
theorem farLife_scale {c : ℝ≥0} (hc : c ≠ 0) (iL : Fin nL) (iR : Fin nR) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) :
    farLife iL iR (fun t => (√(c : ℝ))⁻¹ * w (c * t)) (fun i t => (√(c : ℝ))⁻¹ * vL i (c * t))
      (fun k t => (√(c : ℝ))⁻¹ * vR k (c * t)) (ζ / c) = farLife iL iR w vL vR ζ / c := by
  have hmono : Monotone fun x : ℝ≥0∞ => x / (c : ℝ≥0∞) := fun a b h => ENNReal.div_le_div_right h _
  simp only [farLife, farHit_scale hc]
  exact hmono.map_min.symm

/-- **The dilation of a record** (start, samples) by the start-dependent time factor `C`. -/
def dilRec (C : Start nL nR → ℝ≥0) (r : Start nL nR × Samp nL nR) : Start nL nR × Samp nL nR :=
  (dilV (C r.1) r.1, dilSamp (C r.1) r.2)

end Dil

/-! ### The killed premise and the comparison clause under dilation -/

section Clause

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL} {iR : Fin nR}

theorem measurable_dilV {α : Type*} {mα : MeasurableSpace α} {c : α → ℝ≥0} (hc : Measurable c)
    {v : α → SV nL nR} (hv : Measurable v) : Measurable fun a => dilV (c a) (v a) := by
  have hs : Measurable fun a => (√(c a : ℝ))⁻¹ := (measurable_coe_nnreal_real.comp hc).sqrt.inv
  refine (hs.mul hv.fst).prodMk ((measurable_pi_iff.2 fun i => hs.mul ((measurable_pi_apply i).comp hv.snd.fst)).prodMk
    (measurable_pi_iff.2 fun k => hs.mul ((measurable_pi_apply k).comp hv.snd.snd)))

/-- The record dilation is Borel. -/
theorem measurable_dilRec {C : Start nL nR → ℝ≥0} (hC : Measurable C) : Measurable (dilRec C) := by
  have hc : Measurable fun r : Start nL nR × Samp nL nR => C r.1 := hC.comp measurable_fst
  have hz : Measurable fun r : Start nL nR × Samp nL nR => r.2.1 / ((C r.1 : ℝ≥0) : ℝ≥0∞) :=
    measurable_snd.fst.div (measurable_coe_nnreal_ennreal.comp hc)
  refine (measurable_dilV hc measurable_fst).prodMk (hz.prodMk (measurable_pi_iff.2 fun q => ?_))
  refine Measurable.ite (measurableSet_lt measurable_const hz) ?_ measurable_const
  exact measurable_dilV hc (measurable_sampExt measurable_snd.snd (hc.mul_const _))

/-- **The killed premise is invariant under the record dilation**: if every evolution from every start, traced up to
its killed lifetime, charges `S` with probability at least `p`, then it charges `dilRec C ⁻¹' S` with probability at
least `p` (Brownian scaling of the evolution by the time factor `C y₀`, of its trace, and of its killed lifetime). -/
theorem compPremiseFarK_dil {C : Start nL nR → ℝ≥0} (hC0 : ∀ y, C y ≠ 0) {S : Set (Start nL nR × Samp nL nR)}
    {p : ℝ≥0∞} (h : CompPremiseFarK κ ρL ρR iL iR univ S p) :
    CompPremiseFarK κ ρL ρR iL iR univ (dilRec C ⁻¹' S) p := by
  intro y₀ _ Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE htr
  have hc := hC0 y₀
  have hE' := ZhanGT4.UpMark.isIntegratedSLEEvolution_scale hc hE
  have htr' : ∀ᵐ ω' ∂P', ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => ZhanGT4.UpMark.scaleProc (C y₀) W' t ω')
      (farLife iL iR (ZhanGT4.UpMark.scaleProc (C y₀) W' · ω')
        (fun i t => ZhanGT4.UpMark.scaleProc (C y₀) (VL' i) t ω')
        (fun k t => ZhanGT4.UpMark.scaleProc (C y₀) (VR' k) t ω') (ζ' ω' / C y₀)) η := by
    filter_upwards [htr] with ω' hω'
    obtain ⟨η, hη⟩ := hω'
    refine ⟨fun t => (((√(C y₀ : ℝ))⁻¹ : ℝ) : ℂ) * η (C y₀ * t), ?_⟩
    have hd := hη.dilate hc
    have hfl := farLife_scale hc iL iR (fun t => W' t ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω')
    simp only [ZhanGT4.UpMark.scaleProc]
    rw [hfl]
    exact hd
  have hb := h (dilV (C y₀) y₀) (mem_univ _) Ω' mΩ' P' _ _ _ _ _ _ hE' htr'
  refine hb.trans (le_of_eq (measure_congr ?_))
  filter_upwards [hE.2.2.2.2] with ω' hω'
  have hp := hω'.isSLEPathUpTo (le_refl _)
  have hsub : {t : ℝ≥0 | (t : ℝ≥0∞) < farLife iL iR (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω')
      (ζ' ω')} ⊆ {t | (t : ℝ≥0∞) < ζ' ω'} := fun t ht => lt_of_lt_of_le ht farLife_le
  have hfl := farLife_scale hc iL iR (fun t => W' t ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω')
  have e : samp (fun t => (√(C y₀ : ℝ))⁻¹ * W' (C y₀ * t) ω') (fun i t => (√(C y₀ : ℝ))⁻¹ * VL' i (C y₀ * t) ω')
      (fun k t => (√(C y₀ : ℝ))⁻¹ * VR' k (C y₀ * t) ω')
      (farLife iL iR (fun t => (√(C y₀ : ℝ))⁻¹ * W' (C y₀ * t) ω')
        (fun i t => (√(C y₀ : ℝ))⁻¹ * VL' i (C y₀ * t) ω') (fun k t => (√(C y₀ : ℝ))⁻¹ * VR' k (C y₀ * t) ω')
        (ζ' ω' / C y₀)) =
      dilSamp (C y₀) (samp (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω')
        (farLife iL iR (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω'))) := by
    rw [hfl]
    exact samp_scale hc (hp.continuousOn_w.mono hsub) (fun i => (hp.continuousOn_vL i).mono hsub)
      (fun k => (hp.continuousOn_vR k).mono hsub)
  show ((dilV (C y₀) y₀, samp (fun t => (√(C y₀ : ℝ))⁻¹ * W' (C y₀ * t) ω')
      (fun i t => (√(C y₀ : ℝ))⁻¹ * VL' i (C y₀ * t) ω') (fun k t => (√(C y₀ : ℝ))⁻¹ * VR' k (C y₀ * t) ω')
      (farLife iL iR (fun t => (√(C y₀ : ℝ))⁻¹ * W' (C y₀ * t) ω')
        (fun i t => (√(C y₀ : ℝ))⁻¹ * VL' i (C y₀ * t) ω') (fun k t => (√(C y₀ : ℝ))⁻¹ * VR' k (C y₀ * t) ω')
        (ζ' ω' / C y₀))) ∈ S) =
    ((y₀, samp (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω')
        (farLife iL iR (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω'))) ∈ dilRec C ⁻¹' S)
  rw [e]
  rfl

/-- **The comparison clause of the killed stage law** (the second clause of `IsStageLawFarK`). -/
def CompClauseK (κ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (𝓠 : MeasurableSpace Ω) (R : Set Ω)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (iL : Fin nL) (iR : Fin nR) (y : Ω → Start nL nR) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  ∀ S : Set (Start nL nR × Samp nL nR), MeasurableSet S → ∀ p : ℝ≥0∞, CompPremiseFarK κ ρL ρR iL iR univ S p →
    ∀ A : Set Ω, MeasurableSet[𝓠] A → A ⊆ R →
      p * P A ≤ P (A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S})

variable {Ω : Type*} {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {R : Set Ω}
  {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem _root_.InteractingSLE.Sec5.CrossCond.StagedKill.IsStageLawFarK.compClauseK
    (h : IsStageLawFarK κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ) : CompClauseK κ P 𝓠 R ρL ρR iL iR y W VL VR ζ := h.2

/-- `IsStageLawFarK` is its pathwise clause together with the comparison clause. -/
theorem isStageLawFarK_of_compClauseK
    (h1 : ∀ᵐ ω ∂P, ω ∈ R → IsOrderedForceWord (y ω).2.1 (y ω).2.2 ∧ StrictAnti (y ω).2.1 ∧ StrictMono (y ω).2.2 ∧
      Sec2.IsSLEPathUpTo κ (y ω).2.1 (y ω).2.2 ρL ρR (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω)
        (B · ω) (ζ ω))
    (h2 : CompClauseK κ P 𝓠 R ρL ρR iL iR y W VL VR ζ) : IsStageLawFarK κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ :=
  ⟨h1, h2⟩

/-- **The comparison clause of a dilated piece.** If a piece obeys the comparison clause and is continuous before its
lifetime almost surely on the stage event, then the piece dilated by the time factor `C (y ω)` (a Borel function of
the start; the start is dilated too) obeys the comparison clause: `(y, samples) ↦ dilRec C (y, samples)` is Borel
(`measurable_dilRec`) and the premise is dilation invariant (`compPremiseFarK_dil`). -/
theorem CompClauseK.dilate (h : CompClauseK κ P 𝓠 R ρL ρR iL iR y W VL VR ζ) {C : Start nL nR → ℝ≥0}
    (hC : Measurable C) (hC0 : ∀ y, C y ≠ 0)
    (hcont : ∀ᵐ ω ∂P, ω ∈ R → ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      (∀ i, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
      ∀ k, ContinuousOn (VR k · ω) {t | (t : ℝ≥0∞) < ζ ω}) :
    CompClauseK κ P 𝓠 R ρL ρR iL iR (fun ω => dilV (C (y ω)) (y ω))
      (fun t ω => (√(C (y ω) : ℝ))⁻¹ * W (C (y ω) * t) ω)
      (fun i t ω => (√(C (y ω) : ℝ))⁻¹ * VL i (C (y ω) * t) ω)
      (fun k t ω => (√(C (y ω) : ℝ))⁻¹ * VR k (C (y ω) * t) ω) (fun ω => ζ ω / C (y ω)) := by
  intro S hS p hp A hA hAR
  have h' := h (dilRec C ⁻¹' S) (measurable_dilRec hC hS) p (compPremiseFarK_dil hC0 hp) A hA hAR
  refine h'.trans (le_of_eq (measure_congr ?_))
  filter_upwards [hcont] with ω hω
  show (ω ∈ A ∧ dilRec C (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S) =
    (ω ∈ A ∧ (dilV (C (y ω)) (y ω), samp (fun t => (√(C (y ω) : ℝ))⁻¹ * W (C (y ω) * t) ω)
      (fun i t => (√(C (y ω) : ℝ))⁻¹ * VL i (C (y ω) * t) ω)
      (fun k t => (√(C (y ω) : ℝ))⁻¹ * VR k (C (y ω) * t) ω) (ζ ω / C (y ω))) ∈ S)
  by_cases hωA : ω ∈ A
  · obtain ⟨hw, hvL, hvR⟩ := hω (hAR hωA)
    rw [samp_scale (hC0 (y ω)) hw hvL hvR]
    rfl
  · simp only [hωA, false_and]

end Clause

end InteractingSLE.Sec5.CrossCond.StagedRepLater
