/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactImgCont

/-!
# The restart of a killed word at general `κ`

Packet PROVE-GLUECOND9 (G6 of Proposition 4.9's direction, specification §4.2, proof of Proposition 4.9, p. 120:
"Aux. lemma 22 … gives an actual finite first upper endpoint"). The image word of the flow line in the counterflow
chart (`Sec5.CrossCond.Word49`) is only a **killed** word: it satisfies the integrated equations of an
`SLE_κ(ρ′)` word before its killing time `T` (`Sec7.Aux117.IsWordEntrance`), driven by a Brownian motion of a
filtration (PROVE-GLUECOND7's `exists_isWordEntrance_of_filtW`). Endpoint theorems such as Aux. lemma 22 are stated
for integrated evolutions (Definition 2.1). This file transfers almost sure properties of evolutions to a killed
word, at every `κ > 0`, by restarting it at the positive rational times before `T` — the general-`κ` form of
PROVE-WW-B16's continuation (`WangWu.ImgDrv.ae_exists_continuation`, there for `κ = 4` and one event).

* `measure_eventOf_eq_codeLaw_of_start`: PROVE-RANDRESTART's canonical law of a coded path event, with the coding
  required only on the canonical solution codes **from the given start** (so the coded event may depend on the start);
  `codeLaw_compl_eq_zero_of_ae`: an almost sure property of one evolution from a separated start has a Wiener-null
  exceptional set of driving paths for the canonical solution from that start.
* `badSetS`, `wienerPath_badSetS_eq_zero`: the pairs (separated ordered start, driving path) whose canonical solution
  is not in a Borel code event `S` are Wiener-null at every start, as soon as `S` has full canonical law at every
  separated ordered start.
* **`ae_restart_code`**: for a killed word before `T` (integrated equations before `T`, driven by a Brownian motion of
  a filtration to which the coordinates are adapted, `{q < T} ∈ 𝓘_q`, the marks strictly separated from the driver at
  positive times before `T`, the start below the continuation threshold), almost surely, at every positive rational
  `q < T` the restarted state `V_q − W_q` has a canonical solution driven by `B_{q+·} − B_q` whose code lies in `S`,
  whose lifetime is at least `T − q`, and which agrees with the killed word restarted at `q` before `T − q`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop49Exit

open Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart QuantumZipper.StrongMarkov

variable {nL nR : ℕ}

/-! ### Coded events from one start -/

section Start

/-- **The canonical law of a coded path event, coding from one start** (PROVE-RANDRESTART's
`measure_eventOf_eq_codeLaw`, with the coding `x ∈ S ↔ Φ (cw x) (cζ x)` asked only for the canonical solution codes
from `(xL, xR)`). -/
theorem measure_eventOf_eq_codeLaw_of_start {a : ℝ} (ha : 0 < a) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hsep : ∀ i j, xL i < xR j) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {S : Set (XCode nL nR)}
    {Φ : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop} (hS : MeasurableSet S)
    (hSΦ : ∀ x ∈ CRel a xL xR ρL ρR, HasLimW x → (x ∈ S ↔ Φ (cw x) (cζ x)))
    (hΦ : ∀ (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞), (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) →
      Φ w τ → Φ w' τ) :
    P {ω | Φ (fun t => W t ω) (ζ ω)} = codeLaw a ρL ρR S (xL, xR) := by
  obtain ⟨B', hm, hc, -, hbm, hae⟩ := QuantumZipper.RS.exists_good_version0 h.1.1
  have hpm : Measurable fun ω (s : ℝ≥0) => B' s ω := measurable_pi_iff.2 hm
  rw [codeLaw, ← map_path_eq_wienerPath hbm.toIsPreBrownianReal hpm,
    Measure.map_apply hpm ((measurableSet_restartSetS hS).preimage measurable_prodMk_left)]
  refine measure_congr ?_
  filter_upwards [ae_codeOf_mem ha h hc hae, h.ae_tendsto_threshold ha] with ω ⟨hmem, hdec⟩ hl
  set x := codeOf xL xR B' W VL VR ζ ω with hx
  have hx1 : x.1 = enc (B' · ω) := rfl
  have hxζ : cζ x = ζ ω := rfl
  have hxl : HasLimW x := hasLimW_of_tendsto (fun t ht => (hdec t ht).1) hl
  refine propext ?_
  show Φ (fun t => W t ω) (ζ ω) ↔ ((xL, xR), enc (B' · ω)) ∈ lawSetS a ρL ρR S
  rw [← hx1, mem_lawSetS_iff hsep hmem, hSΦ x hmem hxl, hxζ]
  exact ⟨hΦ _ _ _ fun t ht => ((hdec t ht).1).symm, hΦ _ _ _ fun t ht => (hdec t ht).1⟩

/-- **An almost sure property of one evolution has a Wiener-null exceptional set** for the canonical solution from
its (separated) start: if `S` codes `Φ` on the canonical codes from `(xL, xR)` and one integrated evolution from
`(xL, xR)` satisfies `Φ` almost surely, then the canonical law of `Sᶜ` at `(xL, xR)` vanishes. -/
theorem codeLaw_compl_eq_zero_of_ae {a : ℝ} (ha : 0 < a) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hsep : ∀ i j, xL i < xR j) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {S : Set (XCode nL nR)}
    {Φ : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop} (hS : MeasurableSet S)
    (hSΦ : ∀ x ∈ CRel a xL xR ρL ρR, HasLimW x → (x ∈ S ↔ Φ (cw x) (cζ x)))
    (hΦ : ∀ (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞), (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) →
      Φ w τ → Φ w' τ)
    (hae : ∀ᵐ ω ∂P, Φ (fun t => W t ω) (ζ ω)) :
    codeLaw a ρL ρR Sᶜ (xL, xR) = 0 := by
  have hS1 := measure_eventOf_eq_codeLaw_of_start ha hsep h hS hSΦ hΦ
  have hSc := measure_eventOf_eq_codeLaw_of_start ha hsep h hS.compl (Φ := fun w τ => ¬ Φ w τ)
    (fun x hx hxl => by rw [mem_compl_iff, hSΦ x hx hxl])
    (fun w w' τ hww' hn hw' => hn (hΦ w' w τ (fun t ht => (hww' t ht).symm) hw'))
  rw [← hSc]
  exact ae_iff.1 hae

end Start

/-! ### The bad pairs of a code event -/

section Bad

/-- The bad pairs (separated ordered start, driving path) whose canonical solution, if any, is not in `S`. -/
def badSetS (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (S : Set (XCode nL nR)) :
    Set (((Fin nL → ℝ) × (Fin nR → ℝ)) × (ℝ≥0 → ℝ)) :=
  {p | SepStart p.1 ∧ IsOrderedForceWord p.1.1 p.1.2 ∧ (p.1, enc p.2) ∉ lawSetS a ρL ρR S}

theorem measurableSet_badSetS {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {S : Set (XCode nL nR)}
    (hS : MeasurableSet S) : MeasurableSet (badSetS a ρL ρR S) :=
  (measurableSet_sepStart.preimage measurable_fst).inter
    ((WangWu.ImgDrv.measurableSet_ordered.preimage measurable_fst).inter
      ((measurable_fst.prodMk (measurable_enc.comp measurable_snd)) (measurableSet_lawSetS hS)).compl)

/-- **At every start the bad driving paths of a code event of full canonical law are Wiener-null.** -/
theorem wienerPath_badSetS_eq_zero {a : ℝ} (ha : 0 < a) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {S : Set (XCode nL nR)}
    (hS : ∀ s : (Fin nL → ℝ) × (Fin nR → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      codeLaw a ρL ρR Sᶜ s = 0)
    (s : (Fin nL → ℝ) × (Fin nR → ℝ)) : wienerPath (Prod.mk s ⁻¹' badSetS a ρL ρR S) = 0 := by
  by_cases hs : SepStart s ∧ IsOrderedForceWord s.1 s.2
  · obtain ⟨hsep, hF⟩ := hs
    obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ :=
      exists_isIntegratedSLEEvolution_assembled (a := a) ha hF
    have hsolv := Sec7.ae_solvable_of_isIntegratedSLEEvolution ha hsep hE₀
    have hcl := hS s hsep hF
    refine measure_mono_null (t := {f | ¬ enc f ∈ Prod.fst '' CRel a s.1 s.2 ρL ρR} ∪
      Prod.mk s ⁻¹' restartSetS a ρL ρR Sᶜ) ?_ (measure_union_null (ae_iff.1 hsolv) hcl)
    intro f hf
    obtain ⟨-, -, hnot⟩ := hf
    by_cases hc : enc f ∈ Prod.fst '' CRel a s.1 s.2 ρL ρR
    · right
      obtain ⟨x, hx, hxf⟩ := hc
      have hxS : x ∉ S := fun hxS => hnot (by
        have := (mem_lawSetS_iff hsep hx).2 hxS
        rw [hxf] at this
        exact this)
      show (s, enc f) ∈ lawSetS a ρL ρR Sᶜ
      have := (mem_lawSetS_iff hsep hx (S := Sᶜ)).2 hxS
      rw [hxf] at this
      exact this
    · left; exact hc
  · refine measure_mono_null (fun f hf => ?_) measure_empty
    exact hs ⟨hf.1, hf.2.1⟩

end Bad

/-! ### The restart of a killed word -/

section Restart

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓘 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- The restarted state `V_q − W_q` of a word at the time `q`. -/
def stAt (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (q : ℝ≥0) (ω : Ω) :
    (Fin nL → ℝ) × (Fin nR → ℝ) :=
  ((fun i => VL i q ω - W q ω), fun j => VR j q ω - W q ω)

/-- **The restart of a killed word at general `κ`.** Let the driver and the marks be adapted to `𝓘`, satisfy the
integrated equations of their (random) initial word before `T` driven by a Brownian motion `B` of `𝓘` with continuous
paths (`T > 0`, `{q < T} ∈ 𝓘_q`), let the marks be strictly separated from the driver at positive times before `T`,
and let the initial word be below the continuation threshold. Let `S` be a Borel set of solution codes with full
canonical law at every separated ordered start. Then almost surely, at every positive rational `q < T`, the
restarted state has a canonical solution in `S` driven by `B_{q+·} − B_q`, of lifetime at least `T − q`, which agrees
with the restarted killed word before `T − q`. -/
theorem ae_restart_code {a : ℝ} (ha : 0 < a) (hB : IsFilteredBrownianReal 𝓘 B P)
    (hBc : ∀ ω, Continuous (B · ω)) {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hWa : StronglyAdapted 𝓘 W) (hVLa : ∀ i, StronglyAdapted 𝓘 (VL i))
    (hVRa : ∀ j, StronglyAdapted 𝓘 (VR j)) {T : Ω → ℝ≥0∞}
    (hTq : ∀ q : ℝ≥0, MeasurableSet[𝓘 q] {ω | (q : ℝ≥0∞) < T ω}) (hT0 : ∀ ω, 0 < T ω)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {S : Set (XCode nL nR)} (hSm : MeasurableSet S)
    (hS : ∀ s : (Fin nL → ℝ) × (Fin nR → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      codeLaw a ρL ρR Sᶜ s = 0)
    (hE : ∀ᵐ ω ∂P, Sec7.Aux117.IsWordEntrance a (fun i => VL i 0 ω) (fun j => VR j 0 ω) ρL ρR
      (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (fun t => B t ω) (T ω))
    (hsepL : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < T ω → ∀ i, VL i t ω < W t ω)
    (hsepR : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < T ω → ∀ j, W t ω < VR j t ω)
    (hthr : ∀ᵐ ω ∂P, ¬ ForceWord.ThresholdCondition ρL ρR (W 0 ω) (fun i => VL i 0 ω) (fun j => VR j 0 ω)) :
    ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < q → (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < T ω →
      ∃ x : XCode nL nR, x ∈ CRel a (stAt W VL VR (q : ℝ).toNNReal ω).1
          (stAt W VL VR (q : ℝ).toNNReal ω).2 ρL ρR ∧ x ∈ S ∧
        T ω - (q : ℝ).toNNReal ≤ cζ x ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < T ω - (q : ℝ).toNNReal →
          cw x t = W ((q : ℝ).toNNReal + t) ω - W (q : ℝ).toNNReal ω ∧
          (∀ i, cvL x i t = VL i ((q : ℝ).toNNReal + t) ω - W (q : ℝ).toNNReal ω) ∧
          ∀ j, cvR x j t = VR j ((q : ℝ).toNNReal + t) ω - W (q : ℝ).toNNReal ω := by
  rw [ae_all_iff]
  intro q
  set q' : ℝ≥0 := (q : ℝ).toNNReal with hq'def
  set st : Ω → (Fin nL → ℝ) × (Fin nR → ℝ) := stAt W VL VR q' with hstdef
  have hst : Measurable[𝓘 q'] st := by
    exact Measurable.prodMk ((@measurable_pi_iff Ω (Fin nL) _ (𝓘 q') _ _).2 fun i =>
        (hVLa i q').measurable.sub (hWa q').measurable)
      ((@measurable_pi_iff Ω (Fin nR) _ (𝓘 q') _ _).2 fun j => (hVRa j q').measurable.sub (hWa q').measurable)
  have hlaw := WangWu.ImgDrv.joint_law_restart hB hBc q' hst (hTq q') (measurableSet_badSetS (a := a)
    (ρL := ρL) (ρR := ρR) hSm)
  have hnull : P ({ω | (q' : ℝ≥0∞) < T ω} ∩
      (fun ω => (st ω, smPath B (fun _ => q') ω)) ⁻¹' badSetS a ρL ρR S) = 0 := by
    rw [hlaw]
    simp only [wienerPath_badSetS_eq_zero ha hS, lintegral_zero]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull, hE, hthr] with ω hωbad hω hthr0 hq0 hωA
  have hq'0 : 0 < q' := Real.toNNReal_pos.2 (by exact_mod_cast hq0)
  -- the restarted state is a separated ordered word
  have hsep : SepStart (st ω) := fun i j => by
    show VL i q' ω - W q' ω < VR j q' ω - W q' ω
    linarith [hsepL ω q' hq'0 hωA i, hsepR ω q' hq'0 hωA j]
  have hord : IsOrderedForceWord (st ω).1 (st ω).2 :=
    ⟨fun i j hij => sub_le_sub_right (hω.antitone_vL q' hωA hij) _,
      fun i => sub_nonpos.2 (hω.vL_le_w q' hωA i),
      fun i j hij => sub_le_sub_right (hω.monotone_vR q' hωA hij) _,
      fun j => sub_nonneg.2 (hω.w_le_vR q' hωA j)⟩
  -- the restarted driving path drives a canonical solution in `S`
  have hlS : (st ω, enc (smPath B (fun _ => q') ω)) ∈ lawSetS a ρL ρR S := by
    by_contra hc
    exact hωbad ⟨hωA, hsep, hord, hc⟩
  obtain ⟨x, ⟨⟨hxF, -⟩, hxS⟩, hxe⟩ := hlS
  simp only [Prod.mk.injEq] at hxe
  have hxC : x ∈ CRel a (st ω).1 (st ω).2 ρL ρR := mem_cRelF_iff.1 ⟨hxF, hxe.1⟩
  have hxp : IsIntegratedSLEPath a (st ω).1 (st ω).2 ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) :=
    hxC.1.2.2
  have hgc : Continuous (smPath B (fun _ => q') ω) :=
    ((hBc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hcb : cb x = Assembly2.shiftAt q' (fun t => B t ω) (B q' ω) := by
    funext t
    show dec x.1 t = _
    rw [hxe.2]
    exact dec_enc hgc.continuousWithinAt
  rw [hcb] at hxp
  -- the killed path as a local solution, restarted at `q'`
  have hT0' : ((0 : ℝ≥0) : ℝ≥0∞) < T ω := by simpa using hT0 ω
  have hup := WangWu.ImgDrv.isSLEPathUpTo_of_isWordEntrance hω fun t ht => by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | h0
    · subst h0
      exact hthr0
    · simp only [ForceWord.ThresholdCondition, not_or, not_le]
      rw [Finset.filter_false_of_mem fun i _ => (hsepL ω t h0 ht i).ne,
        Finset.filter_false_of_mem fun j _ => (hsepR ω t h0 ht j).ne', Finset.sum_empty, Finset.sum_empty]
      norm_num
  have hsh := hup.shift hωA
  obtain ⟨hTle, hagree⟩ := Sec7.Band.le_lifetime_of_upTo hsep hsh hxp
  refine ⟨x, hxC, hxS, hTle, fun t ht => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hagree t ht
  exact ⟨h1.symm, fun i => (h2 i).symm, fun j => (h3 j).symm⟩

end Restart

end InteractingSLE.Sec5.Prop49Exit
