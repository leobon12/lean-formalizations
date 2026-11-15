/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TwoForceBase
import InteractingSLE.Spec.Sec2.TwoSeedLaw
import InteractingSLE.Spec.Sec7.CounterflowProbDilation

/-!
# Two-force transience in the seed case (`κ ≤ 4`)

Packet PROVE-ZHAN-B2. Astra, *Formalization proofs and dependency audit* (ruling R35), "Two-force transience,
including the seed case" (L1382–L1415): for seed forces at `0⁻`, `0⁺` with weights `ρ_L, ρ_R ≥ c = κ/2 − 2`, the trace
tends to `∞`. The source argues with the terminal cluster set `Q`: `0 ∉ Q` (the future after a restart stays away from
the seed), and by scale invariance of the two-seed law `Z = inf{|z| : z ∈ Q ∖ {∞}}` has the law of `rZ` for every
`r > 0`, so `Z = ∞`. The proof here is the same scaling argument in Rohde–Schramm's form ([RS05, proof of Theorem 7.1],
QuantumZipper's `RS.transience_of_avoid_zero` for ordinary SLE):

* `0 ∉ closure η[1, ∞)` almost surely: `Zhan.IsIntegratedSLEEvolution.ae_exists_pos_le_norm_trace`
  (`TwoForceBase.lean`);
* **scale invariance**: the dilation `t ↦ c^{−1/2} W_{ct}` of a two-seed evolution is a two-seed evolution
  (`IsIntegratedSLEEvolution.dilate_zero`, PROVE-T14-IN), whose trace is `t ↦ c^{−1/2} η(ct)`
  (`IsGeneratingTrace.dilate`); the two-seed law is unique (`Sec2.TwoSeed.measure_killedState_eq_twoSeed_of_gt`), so
  the laws of the rational-time driver values agree (`map_ratProc_eq_twoSeed`, square cylinders);
* hence `P(∃ t ≥ c, |η(t)| < M) ≤ P(∃ rational q ≥ 1, |η(q)| < M/√c) → 0` as `c → ∞`.

## Main results

* `map_ratProc_eq_twoSeed`: two two-seed evolutions with infinite lifetimes have the same law of rational-time driver
  values.
* `Zhan.IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoSeed`: **two-force transience, seed case**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Zhan

open QuantumZipper (H)
open Sec7.Dilation

/-! ### The rational-time driver values -/

/-- The killed driver at rational times. -/
def ratProc {Ω : Type*} (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℚ≥0 → ℝ :=
  fun q => killedProc ζ W q ω

theorem measurable_ratProc {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞}
    {W : ℝ≥0 → Ω → ℝ} (hW : AdaptedBefore 𝓕 ζ W) : Measurable (ratProc ζ W) :=
  measurable_pi_iff.2 fun q => (measurable_killedProc hW q).mono (𝓕.le _) le_rfl

theorem ratProc_of_eq_top {Ω : Type*} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {ω : Ω} (h : ζ ω = ⊤) :
    ratProc ζ W ω = fun q : ℚ≥0 => W q ω :=
  funext fun q => killedProc_of_eq_top h q

section Law

variable {κ : ℝ} {ρL ρR : Fin 1 → ℝ}
  {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
  {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ}
  {VR₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
  {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ}
  {VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- A square cylinder event of the rational-time driver values, in the form of the two-seed uniqueness theorem. -/
theorem measure_ratProc_pi_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ζ : Ω → ℝ≥0∞}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ} {VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (s : Finset ℚ≥0) (t : ℚ≥0 → Set ℝ) :
    P (ratProc ζ W ⁻¹' (s : Set ℚ≥0).pi t) =
      P {ω | ∀ j : Fin s.card, (((s.equivFin.symm j : ℚ≥0) : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
        (W ((s.equivFin.symm j : ℚ≥0) : ℝ≥0) ω, (fun i => VL i ((s.equivFin.symm j : ℚ≥0) : ℝ≥0) ω),
          (fun i => VR i ((s.equivFin.symm j : ℚ≥0) : ℝ≥0) ω), B ((s.equivFin.symm j : ℚ≥0) : ℝ≥0) ω) ∈
          {p : ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ | p.1 ∈ t (s.equivFin.symm j)}} := by
  refine measure_congr ?_
  filter_upwards [hζ] with ω hω
  refine propext ⟨fun h j => ⟨by rw [hω]; exact ENNReal.coe_lt_top, ?_⟩, fun h q hq => ?_⟩
  · have := h _ (s.equivFin.symm j).2
    simpa [ratProc, killedProc_of_eq_top hω] using this
  · have := (h (s.equivFin ⟨q, hq⟩)).2
    simpa [ratProc, killedProc_of_eq_top hω] using this

/-- **The law of the rational-time driver values of a two-seed evolution is unique** (weights `> −2`, infinite
lifetimes). -/
theorem map_ratProc_eq_twoSeed (hκ : 0 < κ) (hρL : -2 < ρL 0) (hρR : -2 < ρR 0)
    (h₁ : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (h₂ : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (hζ₁ : ∀ᵐ ω ∂P₁, ζ₁ ω = ⊤) (hζ₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤) :
    P₁.map (ratProc ζ₁ W₁) = P₂.map (ratProc ζ₂ W₂) := by
  have hm₁ := measurable_ratProc h₁.2.1
  have hm₂ := measurable_ratProc h₂.2.1
  refine ext_of_generate_finite _ generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => @MeasurableSpace.isPiSystem_measurableSet ℝ _)
      fun _ => by simp) ?_
    (by rw [measure_univ, measure_univ])
  rintro S ⟨s, t, ht, rfl⟩
  have htm : ∀ q, MeasurableSet (t q) := fun q => (mem_univ_pi.1 ht) q
  have hpi : MeasurableSet ((s : Set ℚ≥0).pi t) := MeasurableSet.pi s.countable_toSet fun q _ => htm q
  rw [Measure.map_apply hm₁ hpi, Measure.map_apply hm₂ hpi,
    measure_ratProc_pi_eq (VL := VL₁) (VR := VR₁) (B := B₁) hζ₁,
    measure_ratProc_pi_eq (VL := VL₂) (VR := VR₂) (B := B₂) hζ₂]
  exact Sec2.TwoSeed.measure_killedState_eq_twoSeed_of_gt hκ hρL hρR h₁ h₂ s.card _ _
    fun j => measurable_fst (htm _)

end Law

/-! ### Rational-time trace events -/

/-- Some rational time `≥ c` at which the (measurable) trace is within `r` of `0`. -/
def nearSet (r : ℝ) (c : ℝ≥0) : Set (ℚ≥0 → ℝ) :=
  ⋃ q : ℚ≥0, {v | c ≤ (q : ℝ≥0) ∧ ‖LP.traceAt q (Sec7.extendRat v)‖ < r}

theorem measurableSet_nearSet (r : ℝ) (c : ℝ≥0) : MeasurableSet (nearSet r c) :=
  MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter
    (measurableSet_lt ((LP.measurable_traceAt (q : ℝ≥0)).comp Sec7.measurable_extendRat).norm
      measurable_const)

theorem nearSet_mono {r r' : ℝ} (h : r ≤ r') (c : ℝ≥0) : nearSet r c ⊆ nearSet r' c := by
  intro v hv
  obtain ⟨q, hq⟩ := mem_iUnion.1 hv
  exact mem_iUnion.2 ⟨q, hq.1, hq.2.trans_le h⟩

theorem mem_nearSet_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) {r : ℝ} {c : ℝ≥0} :
    (fun q : ℚ≥0 => w q) ∈ nearSet r c ↔ ∃ q : ℚ≥0, c ≤ (q : ℝ≥0) ∧ ‖η q‖ < r := by
  have htr : ∀ q : ℚ≥0, LP.traceAt q (Sec7.extendRat fun q : ℚ≥0 => w q) = η q := fun q => by
    rw [Sec7.extendRat_eq hw]
    exact LP.traceAt_eq_of_isGeneratingTrace hη hw.continuousOn hw0 ENNReal.coe_lt_top
  simp only [nearSet, mem_iUnion, mem_ofPred_eq, htr]

/-- A real time `t ≥ c` with `‖η t‖ < r` gives a rational one (continuity). -/
theorem exists_rat_of_norm_lt {η : ℝ≥0 → ℂ} (hηc : Continuous η) {r : ℝ} {c t : ℝ≥0} (hct : c ≤ t)
    (h : ‖η t‖ < r) : ∃ q : ℚ≥0, c ≤ (q : ℝ≥0) ∧ ‖η q‖ < r := by
  have hlim : Tendsto (fun m => ‖η (Sec7.ratAbove t m)‖) atTop (𝓝 ‖η t‖) :=
    ((hηc.tendsto t).comp (Sec7.tendsto_ratAbove t)).norm
  obtain ⟨m, hm⟩ := (hlim.eventually (gt_mem_nhds h)).exists
  exact ⟨Sec7.ratAbove t m, hct.trans (Sec7.le_ratAbove t m), hm⟩

/-! ### Transience -/

section Transience

variable {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {ρL ρR : Fin 1 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ} {VR : Fin 1 → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem isOrderedForceWord_zero : IsOrderedForceWord (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) :=
  ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => le_rfl⟩

/-- **Two-force transience, seed case** (`κ ≤ 4`; Astra L1382–L1415). For an integrated `SLE_κ(ρ_L; ρ_R)`
evolution with seed forces at `0⁻`, `0⁺` and `ρ_L, ρ_R ≥ κ/2 − 2` (the admissible side partial sums), almost surely
every continuous generating trace on `[0, ∞)` tends to `∞`. -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoSeed (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR (fun _ => 0) (fun _ => 0))
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hF := isOrderedForceWord_zero
  have hρL : -2 < ρL 0 := by
    have h := hadm.1 (-1) (by norm_num) ⟨0, by norm_num⟩
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.filter_true_of_mem,
      Finset.mem_singleton, forall_eq, Finset.sum_singleton, show (-1 : ℝ) < 0 by norm_num] at h
    linarith
  have hρR : -2 < ρR 0 := by
    have h := hadm.2 0 le_rfl ⟨0, le_rfl⟩
    simp only [Finset.univ_unique, Fin.default_eq_zero, le_refl, Finset.filter_true_of_mem,
      Finset.mem_singleton, forall_eq, Finset.sum_singleton] at h
    linarith
  have h6 := Sec4.aux6Statement hκ _ _ ρL ρR P 𝓕 W VL VR B ζ hF hadm hE
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := h6.mono fun _ h => h.1
  set X := ratProc ζ W with hX
  have hXm : Measurable X := measurable_ratProc hE.2.1
  -- the dilated evolutions have the same law of rational-time values
  have hlaw : ∀ c : ℝ≥0, c ≠ 0 → P.map (ratProc (fun ω => ζ ω / c) (dilProc c W)) = P.map X :=
    fun c hc => map_ratProc_eq_twoSeed hκ hρL hρR (hE.dilate_zero hc) hE
      (hζ.mono fun ω h => by simp only [h]; exact ENNReal.top_div_of_ne_top ENNReal.coe_ne_top) hζ
  -- the good event
  have hgood : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      ∃ ηs : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ ηs ∧
        ∃ d > 0, ∀ t : ℝ≥0, 1 ≤ t → d ≤ ‖ηs t‖ := by
    filter_upwards [IsIntegratedSLEEvolution.ae_simple_trace hκ hκ4 hF hadm hE,
      IsIntegratedSLEEvolution.ae_exists_pos_le_norm_trace hκ hκ4 hF hadm hE, hE.2.2.2.2] with ω
      ⟨hζω, _, ηs, hηs, _⟩ hbase hp
    have hwc : Continuous fun t => W t ω := by
      have h := hp.2.2.2.1
      rw [hζω] at h
      exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
    exact ⟨hζω, hwc, hp.1, ηs, hηs, hbase 1 one_pos ηs hηs⟩
  -- `μ(nearSet r 1) → 0` as `r → 0`
  have hsmall : Tendsto (fun n : ℕ => P (X ⁻¹' nearSet (1 / ((n : ℝ) + 1)) 1)) atTop (𝓝 0) := by
    have hanti : Antitone fun n : ℕ => X ⁻¹' nearSet (1 / ((n : ℝ) + 1)) 1 := fun n m hnm =>
      preimage_mono (nearSet_mono (one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hnm 1)) 1)
    have hlim := tendsto_measure_iInter_atTop (μ := P)
      (fun n => (hXm (measurableSet_nearSet _ _)).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    have h0 : P (⋂ n : ℕ, X ⁻¹' nearSet (1 / ((n : ℝ) + 1)) 1) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hgood] with ω ⟨hζω, hwc, hw0, ηs, hηs, d, hd, hbd⟩ hmem
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hd
      have h1 := mem_iInter.1 hmem n
      rw [mem_preimage, hX, ratProc_of_eq_top hζω, mem_nearSet_iff hwc hw0 hηs] at h1
      obtain ⟨q, hq1, hqn⟩ := h1
      linarith [hbd q hq1]
    rwa [h0] at hlim
  -- for each level `m`, the trace eventually stays outside the disk of radius `m`
  have hm : ∀ m : ℕ, ∀ᵐ ω ∂P, ∃ k : ℕ, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      ∀ t : ℝ≥0, ((k : ℝ≥0) + 1) ^ 2 ≤ t → (m : ℝ) ≤ ‖η t‖ := by
    intro m
    rw [ae_iff]
    refine le_antisymm (ge_of_tendsto' hsmall fun n => ?_) bot_le
    set k : ℕ := (n + 1) * (m + 1) with hk
    set c : ℝ≥0 := ((k : ℝ≥0) + 1) ^ 2 with hc
    have hc0 : c ≠ 0 := by positivity
    have hsc : √(c : ℝ) = (k : ℝ) + 1 := by
      rw [hc]
      push_cast
      exact Real.sqrt_sq (by positivity)
    set Xc := ratProc (fun ω => ζ ω / c) (dilProc c W) with hXc
    have hXcm : Measurable Xc := measurable_ratProc (hE.dilate_zero hc0).2.1
    have hr : (m : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), hk]
      push_cast
      nlinarith
    refine (measure_mono_ae (t := Xc ⁻¹' nearSet ((m : ℝ) / ((k : ℝ) + 1)) 1) ?_).trans ?_
    · filter_upwards [hgood] with ω ⟨hζω, hwc, hw0, ηs, hηs, _⟩ hbad
      have hb : ¬∃ k : ℕ, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
          ∀ t : ℝ≥0, ((k : ℝ≥0) + 1) ^ 2 ≤ t → (m : ℝ) ≤ ‖η t‖ := hbad
      push Not at hb
      obtain ⟨η, hη, t, ht, hlt⟩ := hb k
      rw [hη.eq_of_le hηs hwc.continuousOn hw0 le_top] at hlt
      have hdil := hηs.dilate hc0
      rw [ENNReal.top_div_of_ne_top ENNReal.coe_ne_top] at hdil
      have hdc : Continuous (dilPath c fun t => W t ω) :=
        continuous_const.mul (hwc.comp (continuous_const.mul continuous_id))
      have hd0 : dilPath c (fun t => W t ω) 0 = 0 := by simp [dilPath, hw0]
      have hXcω : Xc ω = fun q : ℚ≥0 => dilPath c (fun t => W t ω) q := by
        rw [hXc, ratProc_of_eq_top (ζ := fun ω => ζ ω / c) (W := dilProc c W) (ω := ω) (show ζ ω / c = ⊤ by
          rw [hζω]; exact ENNReal.top_div_of_ne_top ENNReal.coe_ne_top)]
        rfl
      rw [mem_preimage, hXcω, mem_nearSet_iff hdc hd0 hdil]
      have hηc : Continuous fun s : ℝ≥0 => (((√(c : ℝ))⁻¹ : ℝ) : ℂ) * ηs (c * s) :=
        continuousOn_univ.1 (hdil.2.1.mono fun s _ => show (s : ℝ≥0∞) ≤ ⊤ from le_top)
      refine exists_rat_of_norm_lt hηc (t := t / c) ?_ ?_
      · rw [le_div_iff₀ (pos_iff_ne_zero.2 hc0), one_mul]
        exact ht
      · have hct : c * (t / c) = t := by rw [mul_comm, div_mul_cancel₀ t hc0]
        show ‖(((√(c : ℝ))⁻¹ : ℝ) : ℂ) * ηs (c * (t / c))‖ < (m : ℝ) / ((k : ℝ) + 1)
        rw [hct, norm_mul, Complex.norm_of_nonneg (by positivity), hsc, inv_mul_eq_div]
        exact div_lt_div_of_pos_right hlt (by positivity)
    · rw [← Measure.map_apply hXcm (measurableSet_nearSet _ _), hlaw c hc0,
        Measure.map_apply hXm (measurableSet_nearSet _ _)]
      exact measure_mono (preimage_mono (nearSet_mono hr 1))
  filter_upwards [ae_all_iff.2 hm] with ω hω η hη
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨k, hk⟩ := hω ⌈b⌉₊
  exact eventually_atTop.2 ⟨((k : ℝ≥0) + 1) ^ 2, fun t ht => (Nat.le_ceil b).trans (hk η hη t ht)⟩

end Transience

end InteractingSLE.Zhan
