/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.OneForceSeed
import InteractingSLE.Spec.Supplement.LPProbReflect
import InteractingSLE.Spec.Sec2.Assembly3Entr

/-!
# One-force transience for `κ > 4`: scaling, restart, reflection (Part B.2)

Packet PROVE-ZHAN-GT4-B3. Source: Astra, *Follow-up proofs*, §B.2 L1189–L1198 (ruling R38); additional note
Proposition 3.3
and Lemma 1.6 (ruling R39). See `OneForceSeed.lean` for the plan.

## Main results

* `map_ratProc_eq_of_ordered`: the law of the rational-time driver values of an evolution with infinite lifetime is
that of
  the word (Theorem 2.2, uniqueness in law, for every ordered word).
* `IsIntegratedSLEEvolution.ae_tendsto_norm_trace_seed_of_noCluster`: **seed transience from the absence of a terminal
  cluster point at the seed**, for every word with all marks at the seed (GT4-B's two-seed argument).
* `codeLaw_nt_eq_zero_oneForce`, `IsIntegratedSLEEvolution.ae_tendsto_norm_trace_oneForce`,
  `IsIntegratedSLEEvolution.ae_tendsto_norm_trace_oneForce_right`: **transience of every separated one-force law,
  `κ > 4`**, given (G5).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart QuantumZipper Sec7.Dilation

/-! ### Uniqueness of the law of the rational-time driver values -/

section Law

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- A square cylinder event of the rational-time driver values, in the form of the uniqueness theorem (any word). -/
theorem measure_ratProc_pi_eq_gen {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ζ : Ω → ℝ≥0∞}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (s : Finset ℚ≥0) (t : ℚ≥0 → Set ℝ) :
    P (ratProc ζ W ⁻¹' (s : Set ℚ≥0).pi t) =
      P {ω | ∀ j : Fin s.card, (((s.equivFin.symm j : ℚ≥0) : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
        (W ((s.equivFin.symm j : ℚ≥0) : ℝ≥0) ω, (fun i => VL i ((s.equivFin.symm j : ℚ≥0) : ℝ≥0) ω),
          (fun i => VR i ((s.equivFin.symm j : ℚ≥0) : ℝ≥0) ω), B ((s.equivFin.symm j : ℚ≥0) : ℝ≥0) ω) ∈
          {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ | p.1 ∈ t (s.equivFin.symm j)}} := by
  refine measure_congr ?_
  filter_upwards [hζ] with ω hω
  refine propext ⟨fun h j => ⟨by rw [hω]; exact ENNReal.coe_lt_top, ?_⟩, fun h q hq => ?_⟩
  · have := h _ (s.equivFin.symm j).2
    simpa [ratProc, killedProc_of_eq_top hω] using this
  · have := (h (s.equivFin ⟨q, hq⟩)).2
    simpa [ratProc, killedProc_of_eq_top hω] using this

/-- **The law of the rational-time driver values is that of the word** (infinite lifetimes; Theorem 2.2, uniqueness in
law, `measure_killedState_eq_assembled`). -/
theorem map_ratProc_eq_of_ordered (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR)
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution κ xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (h₂ : IsIntegratedSLEEvolution κ xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
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
    measure_ratProc_pi_eq_gen (VL := VL₁) (VR := VR₁) (B := B₁) hζ₁,
    measure_ratProc_pi_eq_gen (VL := VL₂) (VR := VR₂) (B := B₂) hζ₂]
  exact IsIntegratedSLEEvolution.measure_killedState_eq_assembled hκ hF h₁ h₂
    (fun j => measurable_fst (htm _))

end Law

/-! ### Seed transience by scaling -/

section Transience

variable {nL nR : ℕ} {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Seed transience from the absence of a terminal cluster point at the seed** (B.2 L1189–L1198; additional note
Lemma 1.6), every `κ > 0` and every word with all its marks at the seed (GT4-B's two-seed argument, with the
uniqueness in
law of Theorem 2.2). -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_seed_of_noCluster (hκ : 0 < κ)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR (fun _ => 0) (fun _ => 0))
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ)
    (hno : ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      ∃ d > (0 : ℝ), ∀ᶠ t in atTop, d ≤ ‖η t‖) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hF : IsOrderedForceWord (fun _ : Fin nL => (0 : ℝ)) (fun _ : Fin nR => (0 : ℝ)) :=
    ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  have h6 := Sec4.aux6Statement hκ _ _ ρL ρR P 𝓕 W VL VR B ζ hF hadm hE
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := h6.mono fun _ h => h.1
  set X := ratProc ζ W with hX
  have hXm : Measurable X := measurable_ratProc hE.2.1
  -- the dilated evolutions have the same law of rational-time values
  have hlaw : ∀ c : ℝ≥0, c ≠ 0 → P.map (ratProc (fun ω => ζ ω / c) (dilProc c W)) = P.map X :=
    fun c hc => map_ratProc_eq_of_ordered hκ hF (hE.dilate_zero hc) hE
      (hζ.mono fun ω h => by simp only [h]; exact ENNReal.top_div_of_ne_top ENNReal.coe_ne_top) hζ
  -- the good event
  have hgood : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      ∃ ηs : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ ηs ∧
        ∃ d > (0 : ℝ), ∀ᶠ t in atTop, d ≤ ‖ηs t‖ := by
    filter_upwards [IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hκ hF hadm hE,
      hno, hE.2.2.2.2] with ω ⟨hζω, _, ηs, hηs⟩ hnoω hp
    have hwc : Continuous fun t => W t ω := by
      have h := hp.2.2.2.1
      rw [hζω] at h
      exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
    exact ⟨hζω, hwc, hp.1, ηs, hηs, hnoω ηs hηs⟩
  -- `μ(farSet r) → 0` as `r → 0`
  have hsmall : Tendsto (fun n : ℕ => P (X ⁻¹' farSet (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    have hanti : Antitone fun n : ℕ => X ⁻¹' farSet (1 / ((n : ℝ) + 1)) := fun n m hnm =>
      preimage_mono (farSet_mono (one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hnm 1)))
    have hlim := tendsto_measure_iInter_atTop (μ := P)
      (fun n => (hXm (measurableSet_farSet _)).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    have h0 : P (⋂ n : ℕ, X ⁻¹' farSet (1 / ((n : ℝ) + 1))) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hgood] with ω ⟨hζω, hwc, hw0, ηs, hηs, d, hd, hbd⟩ hmem
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hd
      obtain ⟨T, hT⟩ := eventually_atTop.1 hbd
      obtain ⟨N, hN⟩ := exists_nat_ge (T : ℝ)
      have h1 := mem_iInter.1 hmem n
      rw [mem_preimage, hX, ratProc_of_eq_top hζω, mem_farSet_iff hwc hw0 hηs] at h1
      obtain ⟨q, hqN, hqn⟩ := h1 N
      have hTq : T ≤ (q : ℝ≥0) := by
        rw [← NNReal.coe_le_coe]; exact hN.trans (by exact_mod_cast hqN)
      linarith [hT _ hTq]
    rwa [h0] at hlim
  -- for each level `m`, the trace eventually stays outside the disk of radius `m`
  have hm : ∀ m : ℕ, ∀ᵐ ω ∂P, ∃ T : ℝ≥0, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      ∀ t : ℝ≥0, T ≤ t → (m : ℝ) ≤ ‖η t‖ := by
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
    refine (measure_mono_ae (t := Xc ⁻¹' farSet ((m : ℝ) / ((k : ℝ) + 1))) ?_).trans ?_
    · filter_upwards [hgood] with ω ⟨hζω, hwc, hw0, ηs, hηs, _⟩ hbad
      have hb : ¬∃ T : ℝ≥0, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
          ∀ t : ℝ≥0, T ≤ t → (m : ℝ) ≤ ‖η t‖ := hbad
      push Not at hb
      have hdil := hηs.dilate hc0
      rw [ENNReal.top_div_of_ne_top ENNReal.coe_ne_top] at hdil
      have hdc : Continuous (dilPath c fun t => W t ω) :=
        continuous_const.mul (hwc.comp (continuous_const.mul continuous_id))
      have hd0 : dilPath c (fun t => W t ω) 0 = 0 := by simp [dilPath, hw0]
      have hXcω : Xc ω = fun q : ℚ≥0 => dilPath c (fun t => W t ω) q := by
        rw [hXc, ratProc_of_eq_top (ζ := fun ω => ζ ω / c) (W := dilProc c W) (ω := ω) (show ζ ω / c = ⊤ by
          rw [hζω]; exact ENNReal.top_div_of_ne_top ENNReal.coe_ne_top)]
        rfl
      rw [mem_preimage, hXcω, mem_farSet_iff hdc hd0 hdil]
      intro N
      obtain ⟨η, hη, t, ht, hlt⟩ := hb (c * N)
      rw [hη.eq_of_le hηs hwc.continuousOn hw0 le_top] at hlt
      have hηc : Continuous fun s : ℝ≥0 => (((√(c : ℝ))⁻¹ : ℝ) : ℂ) * ηs (c * s) :=
        continuousOn_univ.1 (hdil.2.1.mono fun s _ => show (s : ℝ≥0∞) ≤ ⊤ from le_top)
      refine exists_rat_of_norm_lt hηc (t := t / c) ?_ ?_
      · rw [le_div_iff₀ (pos_iff_ne_zero.2 hc0), mul_comm]
        exact ht
      · have hct : c * (t / c) = t := by rw [mul_comm, div_mul_cancel₀ t hc0]
        show ‖(((√(c : ℝ))⁻¹ : ℝ) : ℂ) * ηs (c * (t / c))‖ < (m : ℝ) / ((k : ℝ) + 1)
        rw [hct, norm_mul, Complex.norm_of_nonneg (by positivity), hsc, inv_mul_eq_div]
        exact div_lt_div_of_pos_right hlt (by positivity)
    · rw [← Measure.map_apply hXcm (measurableSet_farSet _), hlaw c hc0,
        Measure.map_apply hXm (measurableSet_farSet _)]
      exact measure_mono (preimage_mono (farSet_mono hr))
  filter_upwards [ae_all_iff.2 hm] with ω hω η hη
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨T, hT⟩ := hω ⌈b⌉₊
  exact eventually_atTop.2 ⟨T, fun t ht => (Nat.le_ceil b).trans (hT η hη t ht)⟩

end Transience

/-! ### Separated one-force transience -/

/-- **The canonical one-force law is transient** (`κ > 4`, given (G5)): at every separated one-force word with weight
`≥ κ/2 − 2`, the canonical probability of a non-transient trace is zero. Restart the canonical seed law at time `1`: its
future word is a positive multiple of the target word, the canonical non-transience probability is dilation invariant,
and the future of a transient trace is transient. -/
theorem codeLaw_nt_eq_zero_oneForce {κ : ℝ} (hκ4 : 4 < κ) (hG5 : StoppingInverseBoundaryStatement.{0} κ)
    {ρL : Fin 1 → ℝ} {ρR : Fin 0 → ℝ} (hρ : κ / 2 - 2 ≤ ρL 0) {s : (Fin 1 → ℝ) × (Fin 0 → ℝ)} (hs : s.1 0 < 0) :
    codeLaw κ ρL ρR ntCodeSet s = 0 := by
  have hκ : 0 < κ := by linarith
  -- the canonical evolution at `s` (for the dilation invariance)
  obtain ⟨Ω₁, m₁, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, hE₁⟩ :=
    Sec2.Assembly2.exists_isIntegratedSLEEvolution_of_ordered (ρL := ρL) (ρR := ρR) hκ
      (isOrderedForceWord_oneLeft (xL := s.1) (xR := s.2) hs.le)
  have hζ₁ : ∀ᵐ ω ∂P₁, ζ₁ ω = ⊤ := (IsIntegratedSLEEvolution.ae_good_oneForce hκ hs hρ hE₁).mono fun _ h => h.1
  set K := codeLaw κ ρL ρR ntCodeSet s with hK
  have hdil : ∀ G : ℝ, 0 < G → ∀ s₂ : Fin 0 → ℝ, codeLaw κ ρL ρR ntCodeSet ((fun _ => -G), s₂) = K := by
    intro G hG s₂
    have hxL0 : 0 < -s.1 0 := neg_pos.2 hs
    set c : ℝ≥0 := ⟨((-s.1 0) / G) ^ 2, by positivity⟩ with hcdef
    have hc : c ≠ 0 := by
      intro h
      have : ((-s.1 0) / G) ^ 2 = 0 := congrArg NNReal.toReal h
      exact (pow_pos (div_pos hxL0 hG) 2).ne' this
    have hsc : (√(c : ℝ))⁻¹ = G / (-s.1 0) := by
      rw [show (c : ℝ) = ((-s.1 0) / G) ^ 2 from rfl, Real.sqrt_sq (div_pos hxL0 hG).le, inv_div]
    rw [hK, ← codeLaw_nt_dilate hκ (fun _ j => j.elim0) hE₁ hζ₁ hc]
    congr 1
    refine Prod.ext (funext fun i => ?_) (funext fun j => j.elim0)
    rw [Fin.fin_one_eq_zero i]
    show -G = (√(c : ℝ))⁻¹ * s.1 0
    have hx0 : s.1 0 ≠ 0 := hs.ne
    rw [hsc]
    field_simp
  -- the canonical seed evolution, transient by scaling
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    Sec2.Assembly2.exists_isIntegratedSLEEvolution_of_ordered (ρL := ρL) (ρR := ρR) hκ
      (isOrderedForceWord_oneLeft (xL := fun _ : Fin 1 => (0 : ℝ)) (xR := fun _ : Fin 0 => (0 : ℝ)) le_rfl)
  have hF : IsOrderedForceWord (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 0 => (0 : ℝ)) :=
    isOrderedForceWord_oneLeft le_rfl
  have hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 0 => (0 : ℝ)) :=
    hasAdmissiblePartialSums_oneLeft hρ
  have htr := IsIntegratedSLEEvolution.ae_tendsto_norm_trace_seed_of_noCluster hκ hadm hE
    (IsIntegratedSLEEvolution.ae_noCluster_zero_oneSeed hκ4 hG5 hρ hE)
  -- the restart at time `1`
  have hT := isStoppingTime_const 𝓕 (1 : ℝ≥0)
  have hA : MeasurableSet[hT.measurableSpace] (restartEventTies 1 (fun _ => 0) (fun _ => 0) W VL VR ζ) := by
    rw [IsStoppingTime.measurableSpace_const]
    exact measurableSet_restartEventTies 1 hE
  have hAT : ∀ ω ∈ restartEventTies 1 (fun _ => 0) (fun _ => 0) W VL VR ζ,
      (((fun _ => (1 : ℝ≥0)) ω : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ (0 < (fun _ => (1 : ℝ≥0)) ω ∨
        ∀ i j, (fun _ : Fin 1 => (0 : ℝ)) i < (fun _ : Fin 0 => (0 : ℝ)) j) :=
    fun ω hω => ⟨hω.1, Or.inl one_pos⟩
  have hlaw := measure_restart_codeEvent hκ hE hT hA hAT (Φ := fun w τ => NonTransientEvent w τ)
    measurableSet_ntCodeSet (fun _ _ _ => Iff.rfl) nonTransientEvent_congr
  have hAm : MeasurableSet (restartEventTies 1 (fun _ => 0) (fun _ => 0) W VL VR ζ) := hT.measurableSpace_le _ hA
  have hmem := Zhan.IsIntegratedSLEEvolution.ae_mem_restartEventTies hκ hF hadm hE
  have hPA : P (restartEventTies 1 (fun _ => 0) (fun _ => 0) W VL VR ζ) = 1 := by
    exact (prob_compl_eq_zero_iff hAm).1 (ae_iff.1 (hmem.mono fun ω h => h.2 1 one_pos))
  have hRHS : ∫⁻ ω in restartEventTies 1 (fun _ => 0) (fun _ => 0) W VL VR ζ,
      codeLaw κ ρL ρR ntCodeSet (wordAt W VL VR (fun _ => 1) ω) ∂P = K := by
    rw [← mul_one K, ← hPA, ← setLIntegral_const]
    refine setLIntegral_congr_fun hAm fun ω hω => ?_
    obtain ⟨-, -, hxL', -⟩ := word_of_mem_restartEventTies hF hadm hω
    have hword : wordAt W VL VR (fun _ => 1) ω = ((fun _ => -(W 1 ω - VL 0 1 ω)),
        fun j => VR j 1 ω - W 1 ω) := by
      simp only [wordAt]
      refine Prod.ext (funext fun i => ?_) rfl
      rw [Fin.fin_one_eq_zero i]; simp only; ring
    rw [hword, hdil _ (by linarith [hxL' 0])]
  have hLHS : P (restartEventTies 1 (fun _ => 0) (fun _ => 0) W VL VR ζ ∩
      {ω | NonTransientEvent (fun t => W ((fun _ => (1 : ℝ≥0)) ω + t) ω - W ((fun _ => (1 : ℝ≥0)) ω) ω)
        (ζ ω - ((fun _ => (1 : ℝ≥0)) ω))}) = 0 := by
    refine measure_mono_null (fun ω hω => hω.2) ?_
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [htr, hmem, IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hκ hF hadm hE,
      hE.2.2.2.2]
      with ω htrω ⟨hζ, _⟩ ⟨_, _, η, hη⟩ hp hnt
    have hwc : Continuous fun t => W t ω := by
      have h := hp.2.2.2.1
      rw [hζ] at h
      exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
    have hwc₂ : Continuous (Sec7.shiftNN (fun t => W t ω) 1) :=
      (hwc.comp (continuous_const.add continuous_id)).sub continuous_const
    have hnt' : NonTransientEvent (Sec7.shiftNN (fun t => W t ω) 1) ⊤ := by
      have e : ζ ω - (((fun _ => (1 : ℝ≥0)) ω : ℝ≥0) : ℝ≥0∞) = ⊤ := by rw [hζ]; exact ENNReal.top_sub_coe
      rw [e] at hnt
      exact hnt
    rw [nonTransientEvent_iff hwc₂ (Sec7.shiftNN_zero _ _)] at hnt'
    obtain ⟨⟨η₂, hη₂⟩, hno⟩ := hnt'
    exact hno ⟨η₂, hη₂, tendsto_norm_of_shift hwc hp.1 hη (htrω η hη) hη₂⟩
  rw [hlaw, hRHS] at hLHS
  exact hLHS

section OneForce

variable {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Transience of a separated one-force law** (B.2; additional note Proposition 3.3), `κ > 4`, given (G5): one left
mark `p < 0` of weight `≥ κ/2 − 2`, no right mark; almost surely every continuous generating trace on `[0, ∞)` tends to
`∞`. -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_oneForce (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) {xL ρL : Fin 1 → ℝ} {xR ρR : Fin 0 → ℝ}
    {VL : Fin 1 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ} (hx : xL 0 < 0) (hρ : κ / 2 - 2 ≤ ρL 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hκ : 0 < κ := by linarith
  have hK := codeLaw_nt_eq_zero_oneForce hκ4 hG5 (ρR := ρR) hρ (s := (xL, xR)) hx
  rw [← measure_nonTransient_eq_codeLaw hκ (fun _ j => j.elim0) hE] at hK
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hK,
    hE.ae_exists_isGeneratingTrace_top_of_hasAdmissiblePartialSums hκ (isOrderedForceWord_oneLeft hx.le)
      (hasAdmissiblePartialSums_oneLeft hρ) (fun i => by rw [Fin.fin_one_eq_zero i]; exact hx) (fun j => j.elim0),
    IsIntegratedSLEEvolution.ae_good_oneForce hκ hx hρ hE] with ω hnt ⟨hζω, η₀, hη₀⟩ ⟨_, hwc, hw0, _⟩ η hη
  have hnt' : ¬ NonTransientEvent (fun t => W t ω) ⊤ := by
    rw [← hζω]; exact hnt
  rw [nonTransientEvent_iff hwc hw0] at hnt'
  obtain ⟨η₁, hη₁, htr₁⟩ : HasTransTrace (fun t => W t ω) := by
    by_contra h
    exact hnt' ⟨⟨η₀, hη₀⟩, h⟩
  refine htr₁.congr fun t => ?_
  rw [hη.eq_of_le hη₁ hwc.continuousOn hw0 le_top]

/-- **Transience of a separated one-force law with its mark on the right**, by reflection. -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_oneForce_right (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) {xL ρL : Fin 0 → ℝ} {xR ρR : Fin 1 → ℝ}
    {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 1 → ℝ≥0 → Ω → ℝ} (hx : 0 < xR 0) (hρ : κ / 2 - 2 ≤ ρR 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  have hEr := IsIntegratedSLEEvolution.reflect hE
  filter_upwards [IsIntegratedSLEEvolution.ae_tendsto_norm_trace_oneForce hκ4 hG5
    (xL := -xR) (show (-xR) 0 < 0 by simp only [Pi.neg_apply]; linarith) hρ hEr] with ω h η hη
  have hη' := LP.isGeneratingTrace_reflect hη
  have h' := h _ hη'
  simpa only [LP.norm_reflectC] using h'

end OneForce

end InteractingSLE.ZhanGT4
