/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76FStop
import InteractingSLE.Spec.Coupling.WholeField9Entr
import InteractingSLE.Spec.Sec7.TwoHist

/-!
# Lemma 7.6: (R1) at a disjoint pair from the mean identification

Packet PROVE-T15-CLOSE1 (2). (R1) of `Lemma76CondDetHeightsStatement`: given a sub-σ-algebra `𝒢`, on a `𝒢`-event
`M`, the retained chart field `hd.chartField κ h` has the Gaussian characteristic functional of a `𝒢`-measurable word
`β`. Specification §7.2, proof of Lemma 7.6, pp. 267–268 ("Retain the two labelled histories and their canonical germs
… The stopping-time local-set theorem gives their joint Gaussian conditional law in each complementary component …
After this coordinate change and addition of `θ₂χ`, the conditional field has the form `h⁰_D + M`").

This file proves (R1) from the identification of the conditional mean in the chart (`IsRetMeanIdent`, the analogue of
Lemma 7.8's `IsBoxMeanIdentification` for G7's retained chart at a disjoint pair):

* `cappedPath`, `capR`, **`retSigma76`**: the retained σ-algebra of the two killed histories at `(u, r)` (choice-free:
  the flow lines capped at `capR = u + r + 1`, completed by null sets inside `mΩ`);
* **`IsRetMeanIdent`**: for every pair of capped versions and every version `g` of the local-set mean of their stopped
  union, almost surely at a disjoint pair the chart transport of `g + 𝔥₀` is the word mean of `β`;
* **`exists_r1_of_meanIdent`**: for `β` measurable for `retSigma76` with `IsRetMeanIdent`, there are `𝒢 ≥ retSigma76`
  and a `𝒢`-event `M`, almost surely equal to the disjoint-pair event, on which (R1) holds.

Ingredients: the marked locality at deterministic stops with killing records (`Lemma76FMark.lean`), the stopped
retained data (`Lemma76FStop.lean`) and its chart congruence (`Lemma76FChart.lean`), and PROVE-RESTART-CPL7's random
chart transport (`Restart.ae_condExp_cexp_chartTransport_eq_gaussCF_on`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Sec7

namespace Lemma76F

open Supp7 Restart Sec6 LocalSets LQGMetric

/-! ### Small facts -/

/-- The cap used for the retained histories at `(u, r)`. -/
def capR (u r : ℝ≥0) : ℝ≥0 := u + r + 1

theorem lt_capR_left (u r : ℝ≥0) : u < capR u r := by
  unfold capR
  calc u ≤ u + r := le_self_add
    _ < u + r + 1 := lt_add_one _

theorem lt_capR_right (u r : ℝ≥0) : r < capR u r := by
  unfold capR
  calc r ≤ u + r := le_add_self
    _ < u + r + 1 := lt_add_one _

/-- The killing record through `u` of the lifetime capped at `m > u` reads `u < ζ`. -/
theorem lt_lifeRec_cutLife_iff {u m : ℝ≥0} (hum : u < m) (ζ : ℝ≥0∞) :
    (u : ℝ≥0∞) < lifeRec (cutLife ζ m) u ↔ (u : ℝ≥0∞) < ζ := by
  have hum' : (u : ℝ≥0∞) < m := ENNReal.coe_lt_coe.2 hum
  unfold lifeRec cutLife
  split_ifs with h1 h2 h2
  · exact ⟨fun h => absurd h (not_lt.2 h2), fun h => absurd h (not_lt.2 h2)⟩
  · exact ⟨fun _ => not_le.1 h2, fun _ => ENNReal.coe_lt_top⟩
  · exact absurd h2 (not_le.2 (lt_of_lt_of_le hum' le_top))
  · exact ⟨fun _ => lt_of_lt_of_le hum' (not_le.1 h1).le, fun _ => ENNReal.coe_lt_top⟩

/-- The capped path agrees with the path up to times before the lifetime and the cap. -/
theorem capTime_eq_of_lt {m : ℝ≥0} {ζ : ℝ≥0∞} {a t : ℝ≥0} (ha : (a : ℝ≥0∞) < ζ) (ham : a < m) (ht : t ≤ a) :
    capTime m ζ t = t :=
  capTime_of_le m ζ (le_min ((ENNReal.coe_le_coe.2 ht).trans ha.le)
    (ENNReal.coe_le_coe.2 (ht.trans ham.le)))

/-- **The disjoint-pair predicate only reads the prefixes and whether the cutoffs precede the lifetimes.** -/
theorem isDisjointPair_congr {α α' β β' : ℝ≥0 → ℂ} {ζ₁ ζ₁' ζ₂ ζ₂' : ℝ≥0∞} {a b : ℝ≥0}
    (h₁ : ∀ s ≤ a, α' s = α s) (h₂ : ∀ t ≤ b, β' t = β t) (hz₁ : (a : ℝ≥0∞) < ζ₁' ↔ (a : ℝ≥0∞) < ζ₁)
    (hz₂ : (b : ℝ≥0∞) < ζ₂' ↔ (b : ℝ≥0∞) < ζ₂) :
    Lemma76Exit.IsDisjointPair α' ζ₁' a β' ζ₂' b ↔ Lemma76Exit.IsDisjointPair α ζ₁ a β ζ₂ b := by
  have e₁ : α' '' Icc 0 a = α '' Icc 0 a := image_congr fun s hs => h₁ s hs.2
  have e₂ : β' '' Icc 0 b = β '' Icc 0 b := image_congr fun t ht => h₂ t ht.2
  have eD : activeDomain α' a β' b = activeDomain α a β b :=
    activeDomain_congr_Icc (fun s hs => h₁ s hs.2) (fun t ht => h₂ t ht.2)
  unfold Lemma76Exit.IsDisjointPair
  rw [e₁, e₂, eD, h₁ a le_rfl, h₂ b le_rfl, hz₁, hz₂]

/-! ### The retained σ-algebra and the mean identification -/

section Defs

variable {Ω : Type*}

/-- The path capped at its lifetime and at `m` (`η(t ∧ ζ ∧ m)`). -/
def cappedPath (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (m : ℝ≥0) : Ω → ℝ≥0 → ℂ := fun ω t => η ω (capTime m (ζ ω) t)

/-- The retained killed histories of two paths at the cutoffs `(u, r)`, with the cap `capR u r`. -/
def retHist76 (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u r : ℝ≥0) : Ω → KHist × KHist :=
  cstHist (cappedPath η₁ ζ₁ (capR u r)) (cappedPath η₂ ζ₂ (capR u r)) (fun ω => cutLife (ζ₁ ω) (capR u r))
    (fun ω => cutLife (ζ₂ ω) (capR u r)) u r

/-- **The retained σ-algebra at `(u, r)`**: the measurable events almost surely equal to an event of the two retained
killed histories. -/
@[instance_reducible]
def retSigma76 [mΩ : MeasurableSpace Ω] (P : Measure Ω) (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u r : ℝ≥0) :
    MeasurableSpace Ω :=
  mΩ ⊓ aeSigma (MeasurableSpace.comap (retHist76 η₁ η₂ ζ₁ ζ₂ u r) inferInstance) P

theorem retSigma76_le [mΩ : MeasurableSpace Ω] (P : Measure Ω) (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞)
    (u r : ℝ≥0) : retSigma76 P η₁ η₂ ζ₁ ζ₂ u r ≤ mΩ := inf_le_left

/-- **The mean identification at a disjoint pair** (the analogue of Lemma 7.8's `IsBoxMeanIdentification` for G7's
retained chart; specification pp. 268–269): for every pair of capped versions of the two flow lines (cap `capR u r`)
and every version `g` of the local-set mean of the centred field for their stopped union, almost surely at a disjoint
pair the chart transport of the conditional mean `g + 𝔥₀` of the field is the word mean of the datum `β`. -/
def IsRetMeanIdent [MeasurableSpace Ω] (κ : ℝ) (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens)
    (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u₀ : ℂ → ℝ) {d : RetData Ω} (hd : d.IsMeasGood)
    (β : Ω → BoundaryWord) : Prop :=
  ∀ (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (g : Ω → DistOn upperHalfPlaneOpens),
    (∀ ω, Continuous (ηc₁ ω)) → (∀ ω, Continuous (ηc₂ ω)) → (∀ t, Measurable fun ω => ηc₁ ω t) →
    (∀ t, Measurable fun ω => ηc₂ ω t) → (∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime (capR d.u d.r) (ζ₁ ω) t)) →
    (∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime (capR d.u d.r) (ζ₂ ω) t)) →
    IsLocalSetMean (cstUnion ηc₁ ηc₂ d.u d.r) (WholeField.centredField h u₀) P g →
    ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → ∀ φ : TestOn upperHalfPlaneOpens,
      Chart.chartTransport (hd.isConformal_chart ω) 1 0 (QuantumZipper.chiC κ)
        (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ z, (β ω).mean z * φ z

end Defs

/-- Measurability of retained data is monotone in the σ-algebra. -/
theorem RetData.IsMeasGood.mono_sigma {Ω : Type*} {𝒢 𝒦 : MeasurableSpace Ω} {d : RetData Ω}
    (hd : @RetData.IsMeasGood Ω 𝒢 d) (h : 𝒢 ≤ 𝒦) : @RetData.IsMeasGood Ω 𝒦 d :=
  @RetData.IsMeasGood.mk Ω 𝒦 d (h _ (@RetData.IsMeasGood.measurableSet_G Ω 𝒢 d hd))
    (fun t => (@RetData.IsMeasGood.meas₁ Ω 𝒢 d hd t).mono h le_rfl)
    (fun t => (@RetData.IsMeasGood.meas₂ Ω 𝒢 d hd t).mono h le_rfl)
    (@RetData.IsMeasGood.good Ω 𝒢 d hd)

/-! ### (R1) from the mean identification -/

section Main

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **(R1) at a disjoint pair from the mean identification.** For two flow lines (seeds `x₂ < x₁` not needed here),
retained data `d` agreeing with them, and a datum `β` with the mean identification `IsRetMeanIdent`, there are a
sub-σ-algebra `𝒢` containing the retained σ-algebra `retSigma76` and a `𝒢`-event `M`, almost surely equal to the
disjoint-pair event, such that on `M`, conditionally on `𝒢`, the retained chart field has the Gaussian characteristic
functional of `β`. Inputs: Lemma 7.5 (field determination); Aux. lemma 56 at first entrances is
`WholeField.retainedRangeEntranceStatement`. -/
theorem exists_r1_of_meanIdent (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω → BoundaryWord}
    (hmean : IsRetMeanIdent κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β) :
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω), retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r ≤ 𝒢.1 ∧
      MeasurableSet[𝒢.1] M ∧
      (∀ᵐ ω ∂P, ω ∈ M ↔ Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ)) | 𝒢.1] ω = gaussCF (β ω) φ := by
  classical
  set m := capR d.u d.r with hmdef
  have hum : d.u < m := lt_capR_left d.u d.r
  have hrm : d.r < m := lt_capR_right d.u d.r
  obtain ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, h0₁, h0₂, hag₁, hag₂, g, hg, hlaw⟩ :=
    exists_cstUnion_marked_of_isFlowLine hL75 WholeField.retainedRangeEntranceStatement hκ hκ4 hb hh hη₁ hη₂ hu₀
      m d.u d.r
  set h₀ := WholeField.centredField h u₀ with hh₀
  set S := SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ with hS
  set F := cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) m) (fun ω => cutLife (ζ₂ ω) m) d.u d.r with hF
  set 𝒦 := germSigma (cstUnion ηc₁ ηc₂ d.u d.r) h₀ ⊔ MeasurableSpace.comap F inferInstance with h𝒦def
  set R := @retSigma76 Ω mΩ P η₁ η₂ ζ₁ ζ₂ d.u d.r with hRdef
  let _ : MeasurableSpace Ω := mΩ
  have hhm : Measurable h := hh.1
  have hh₀m : Measurable h₀ := WholeField.measurable_centredField hhm u₀
  have hζm₁ := measurable_lifetime_of_isFlowLine hη₁
  have hζm₂ := measurable_lifetime_of_isFlowLine hη₂
  have hFm : Measurable F := measurable_cstHist hm₁ hm₂ ((measurable_cutLife m).comp hζm₁)
    ((measurable_cutLife m).comp hζm₂) d.u d.r
  have h𝒦 : 𝒦 ≤ mΩ := sup_le (germSigma_le (measurable_cstUnion hc₁ hc₂ hm₁ hm₂ d.u d.r) hh₀m) hFm.comap_le
  have h𝒦R : 𝒦 ⊔ R ≤ mΩ := sup_le h𝒦 (retSigma76_le P η₁ η₂ ζ₁ ζ₂ d.u d.r)
  -- the stopped retained data, measurable for `𝒦`
  set d' := stopRet ηc₁ ηc₂ d.u d.r with hd'def
  have hd' : @RetData.IsMeasGood Ω 𝒦 d' :=
    isMeasGood_stopRet (ζ₁ := fun ω => cutLife (ζ₁ ω) m) (ζ₂ := fun ω => cutLife (ζ₂ ω) m) le_sup_right hc₁ hc₂
      h0₁ h0₂
  have hd'Ω : @RetData.IsMeasGood Ω mΩ d' := RetData.IsMeasGood.mono_sigma hd' h𝒦
  -- the lifetime records
  set L₁ : Ω → ℝ≥0∞ := fun ω => (F ω).1.2 with hL₁def
  set L₂ : Ω → ℝ≥0∞ := fun ω => (F ω).2.2 with hL₂def
  have hFm𝒦 : Measurable[𝒦] F := (comap_measurable F).mono le_sup_right le_rfl
  have hL₁m : Measurable[𝒦] L₁ := measurable_snd.comp (measurable_fst.comp hFm𝒦)
  have hL₂m : Measurable[𝒦] L₂ := measurable_snd.comp (measurable_snd.comp hFm𝒦)
  have hL₁ : ∀ ω, (d.u : ℝ≥0∞) < L₁ ω ↔ (d.u : ℝ≥0∞) < ζ₁ ω := fun ω => lt_lifeRec_cutLife_iff hum (ζ₁ ω)
  have hL₂ : ∀ ω, (d.r : ℝ≥0∞) < L₂ ω ↔ (d.r : ℝ≥0∞) < ζ₂ ω := fun ω => lt_lifeRec_cutLife_iff hrm (ζ₂ ω)
  set M := pairSet d' L₁ L₂ with hMdef
  have hM : MeasurableSet[𝒦] M := @measurableSet_pairSet Ω 𝒦 d' hd' L₁ L₂ hL₁m hL₂m
  -- almost sure pathwise facts
  have hstop₁ : ∀ ω, ∀ s ≤ d.u, d'.η₁ ω s = hproj (ηc₁ ω s) := fun ω s hs => by
    show hproj (ηc₁ ω (min s d.u)) = _
    rw [min_eq_left hs]
  have hstop₂ : ∀ ω, ∀ t ≤ d.r, d'.η₂ ω t = hproj (ηc₂ ω t) := fun ω t ht => by
    show hproj (ηc₂ ω (min t d.r)) = _
    rw [min_eq_left ht]
  have hgood : ∀ᵐ ω ∂P, ((∀ s ≤ d.u, d'.η₁ ω s = ηc₁ ω s) ∧ (∀ t ≤ d.r, d'.η₂ ω t = ηc₂ ω t)) ∧
      ((d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧ ω ∈ d'.G ∧
        (∀ s ≤ d.u, d'.η₁ ω s = d.η₁ ω s) ∧ (∀ t ≤ d.r, d'.η₂ ω t = d.η₂ ω t) ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) := by
    filter_upwards [hag, hag₁, hag₂, ae_im_nonneg_of_isFlowLine' hη₁, ae_im_nonneg_of_isFlowLine' hη₂,
      ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂] with ω hagω e₁ e₂ hi₁ hi₂ hp₂
    have hA₁ : ∀ s ≤ d.u, d'.η₁ ω s = ηc₁ ω s := fun s hs => by
      rw [hstop₁ ω s hs, hproj_of_im_nonneg]
      rw [e₁ s]
      exact hi₁ _ (capTime_le m (ζ₁ ω) s)
    have hA₂ : ∀ t ≤ d.r, d'.η₂ ω t = ηc₂ ω t := fun t ht => by
      rw [hstop₂ ω t ht, hproj_of_im_nonneg]
      rw [e₂ t]
      exact hi₂ _ (capTime_le m (ζ₂ ω) t)
    refine ⟨⟨hA₁, hA₂⟩, fun hu hr => ?_⟩
    obtain ⟨hG, a₁, a₂⟩ := hagω hu hr
    have b₁ : ∀ s ≤ d.u, d'.η₁ ω s = η₁ ω s := fun s hs => by
      rw [hA₁ s hs, e₁ s, capTime_eq_of_lt hu hum hs]
    have b₂ : ∀ t ≤ d.r, d'.η₂ ω t = η₂ ω t := fun t ht => by
      rw [hA₂ t ht, e₂ t, capTime_eq_of_lt hr hrm ht]
    refine ⟨hG, ?_, fun s hs => (b₁ s hs).trans (a₁ s hs).symm, fun t ht => (b₂ t ht).trans (a₂ t ht).symm, a₁, a₂⟩
    intro t ht he
    have he' : d'.η₂ ω t = d'.η₂ ω d.r := he
    rw [b₂ t ht.le, b₂ d.r le_rfl] at he'
    exact ht.ne (hp₂.1 ((ENNReal.coe_le_coe.2 ht.le).trans hr.le) hr.le he')
  -- the event `M` is the disjoint-pair event
  have hMiff : ∀ᵐ ω ∂P, ω ∈ M ↔ Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r := by
    filter_upwards [hgood] with ω hω
    have hB := hω.2
    constructor
    · intro hωM
      have hu : (d.u : ℝ≥0∞) < ζ₁ ω := (hL₁ ω).1 hωM.2.1
      have hr : (d.r : ℝ≥0∞) < ζ₂ ω := (hL₂ ω).1 hωM.2.2
      obtain ⟨-, hG', c₁, c₂, a₁, a₂⟩ := hB hu hr
      have hp := (@mem_pairSet_iff Ω 𝒦 d' hd' L₁ L₂ ω hG').1 hωM
      exact (isDisjointPair_congr (fun s hs => (c₁ s hs).trans (a₁ s hs)) (fun t ht => (c₂ t ht).trans (a₂ t ht))
        (hL₁ ω) (hL₂ ω)).1 hp
    · intro hp
      obtain ⟨-, hG', c₁, c₂, a₁, a₂⟩ := hB hp.1 hp.2.1
      refine (@mem_pairSet_iff Ω 𝒦 d' hd' L₁ L₂ ω hG').2 ?_
      exact (isDisjointPair_congr (fun s hs => (c₁ s hs).trans (a₁ s hs)) (fun t ht => (c₂ t ht).trans (a₂ t ht))
        (hL₁ ω) (hL₂ ω)).2 hp
  -- on `M` the two retained charts agree
  have hchart : ∀ᵐ ω ∂P, ω ∈ M → d'.chart ω = d.chart ω := by
    filter_upwards [hgood] with ω hω hωM
    obtain ⟨hG, hG', c₁, c₂, -, -⟩ := hω.2 ((hL₁ ω).1 hωM.2.1) ((hL₂ ω).1 hωM.2.2)
    exact (RetData.chart_eq_of_agree (G' := d'.G) (η₁' := d'.η₁) (η₂' := d'.η₂) hG hG' c₁ c₂).2.2
  -- the conditional law of the field on `M`, for test functions in the chart domain
  have hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M → tsupport φ ⊆ (d'.chart ω).dom →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒦] ω =
        Complex.exp (Complex.I * ((g ω + S) φ : ℂ) -
          (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov ((d'.chart ω).dom : Set ℂ) φ φ : ℝ) : ℂ)) := by
    intro φ
    have hsplit : (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) =
        Complex.exp (Complex.I * (S φ : ℂ)) • fun ω' => Complex.exp (Complex.I * (h₀ ω' φ : ℂ)) := by
      funext ω'
      simp only [Pi.smul_apply, smul_eq_mul, hh₀, WholeField.centredField, ← Complex.exp_add]
      congr 1
      rw [sub_apply]
      push_cast
      ring
    have h2 := condExp_smul (μ := P) (Complex.exp (Complex.I * (S φ : ℂ)))
      (fun ω' => Complex.exp (Complex.I * (h₀ ω' φ : ℂ))) 𝒦
    filter_upwards [h2, hlaw φ, hgood] with ω e2 e3 hω hωM hsupp
    rw [hsplit]
    refine (e2.trans ?_)
    have hωE : ω ∈ d'.E := hωM.1.1.1
    have hdom : ((d'.chart ω).dom : Set ℂ) = d'.D ω := @RetData.IsMeasGood.coe_dom_chart Ω 𝒦 d' hd' ω
    have hK := @RetData.IsMeasGood.isCompact_K Ω 𝒦 d' hd' ω
    obtain ⟨R0, hR0, hKR, hEq⟩ := HalfPlaneSep.exists_H_diff_fillH_eq hK.isClosed hK.isBounded
    have hDdef : d'.D ω = H \ fillH (d'.K ω) := rfl
    have hKU : d'.K ω ∩ H = cstUnion ηc₁ ηc₂ d.u d.r ω := by
      rw [RetData.K_of_mem hωE, cstUnion_eq, prefixSet, image_congr fun s hs => hω.1.1 s hs.2,
        image_congr fun t ht => hω.1.2 t ht.2]
      rfl
    have hcc : connectedComponentIn (H \ cstUnion ηc₁ ηc₂ d.u d.r ω) (((R0 + 1 : ℝ) : ℂ) * I) = d'.D ω := by
      rw [← hKU, H_diff_inter_H, hDdef, hEq]
    have hz₀D : ((R0 + 1 : ℝ) : ℂ) * I ∈ d'.D ω := by
      rw [hDdef, hEq]
      refine mem_connectedComponentIn ⟨?_, fun hz => ?_⟩
      · show (0 : ℝ) < (((R0 + 1 : ℝ) : ℂ) * I).im
        simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
        linarith
      · have h1 := hKR hz
        rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith)] at h1
        linarith
    have hz₀ : ((R0 + 1 : ℝ) : ℂ) * I ∈ H \ cstUnion ηc₁ ηc₂ d.u d.r ω := by
      have := hz₀D
      rw [← hcc] at this
      exact connectedComponentIn_subset _ _ this
    rw [hdom] at hsupp ⊢
    rw [Pi.smul_apply, smul_eq_mul, e3 _ hz₀ (hcc ▸ hsupp), hcc, add_apply,
      Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- the mean identification in the stopped chart
  have hmean' : ∀ᵐ ω ∂P, ω ∈ M → ∀ φ : TestOn upperHalfPlaneOpens,
      Chart.chartTransport (@RetData.IsMeasGood.isConformal_chart Ω 𝒦 d' hd' ω) 1 0 (QuantumZipper.chiC κ)
        (g ω + S) φ = ∫ z, (β ω).mean z * φ z := by
    filter_upwards [hmean ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg, hMiff, hchart] with ω e hiff hch hωM φ
    rw [chartTransport_congr_chart (hch hωM) _ (hd.isConformal_chart ω)]
    exact e (hiff.1 hωM) φ
  -- (R1) for the stopped chart field given `𝒦`
  obtain ⟨hdomm, hfwdm, hliftm⟩ := @RetData.IsMeasGood.chart_measurability Ω 𝒦 d' hd'
  have hR1' := fun φ => ae_condExp_cexp_chartTransport_eq_gaussCF_on (𝒢 := 𝒦) h𝒦
    (@RetData.IsMeasGood.isConformal_chart Ω 𝒦 d' hd') hdomm hfwdm hliftm
    (@RetData.IsMeasGood.continuousOn_lift_chart Ω 𝒦 d' hd') hhm (QuantumZipper.chiC κ) hM hcond hmean' φ
  -- the retained σ-algebra adds only null-set information
  have hΨF : ∀ᵐ ω ∂P, retHist76 η₁ η₂ ζ₁ ζ₂ d.u d.r ω = F ω := by
    filter_upwards [hag₁, hag₂] with ω e₁ e₂
    have p₁ : cappedPath η₁ ζ₁ (capR d.u d.r) ω = ηc₁ ω := funext fun t => (e₁ t).symm
    have p₂ : cappedPath η₂ ζ₂ (capR d.u d.r) ω = ηc₂ ω := funext fun t => (e₂ t).symm
    simp only [retHist76, cstHist, hF, p₁, p₂]
    rfl
  have htr : ∀ B, MeasurableSet[𝒦 ⊔ R] B → MeasurableSet[aeSigma 𝒦 P] (B ∩ univ) := by
    intro B hB
    have := measurableSet_aeSigma_inter_of_ae (Ψ := retHist76 η₁ η₂ ζ₁ ζ₂ d.u d.r) (F := F) (𝒦 := 𝒦) (P := P)
      le_sup_right MeasurableSet.univ (by filter_upwards [hΨF] with ω hω; exact ⟨by simp, fun _ => hω⟩) B hB
    rwa [preimage_univ] at this
  refine ⟨⟨𝒦 ⊔ R, h𝒦R⟩, M, le_sup_right, (le_sup_left : 𝒦 ≤ 𝒦 ⊔ R) _ hM, hMiff, fun φ => ?_⟩
  have hXi : Integrable (fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp (hd.measurable_chartField κ hhm))
  have hXi' : Integrable (fun ω' => Complex.exp (Complex.I *
      (Chart.chartTransport (@RetData.IsMeasGood.isConformal_chart Ω 𝒦 d' hd' ω') 1 0 (QuantumZipper.chiC κ)
        (h ω') φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp (hd'Ω.measurable_chartField κ hhm))
  have hloc := ae_condExp_congr_on (𝒦 := 𝒦) hM hXi hXi'
    (by
      filter_upwards [hchart] with ω hch hωM
      show Complex.exp (Complex.I * (Chart.chartTransport (hd.isConformal_chart ω) 1 0 (QuantumZipper.chiC κ)
        (h ω) φ : ℂ)) = _
      rw [chartTransport_congr_chart (hch hωM).symm (hd.isConformal_chart ω)
        (@RetData.IsMeasGood.isConformal_chart Ω 𝒦 d' hd' ω)])
  have hup := ae_condExp_eq_of_trace (P := P) le_sup_left h𝒦R htr hXi
  filter_upwards [hup, hloc, hR1' φ] with ω e1 e2 e3 hωM
  rw [e1 (mem_univ ω), e2 hωM, e3 hωM]

end Main

end Lemma76F

end Sec7

end InteractingSLE
