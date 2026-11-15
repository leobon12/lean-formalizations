/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.OneForceTrans

/-!
# A transient seed trace does not return to its starting point

Packet PROVE-SEC5-R. Specification §5, p. 129 ("`η′` intersects `∂_L𝒮` only when it terminates at `0`"), for the
counterflow of Proposition 5.5's configuration read in the chart `R`: an integrated `SLE_κ(ρ)` evolution whose marks
all sit at the seed (`0⁻`, `0⁺`) and whose side partial sums are admissible. Its trace is continuous on `[0, ∞)`
(`ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible`).

**Statement** (`ae_trace_ne_zero_of_seed`): if moreover the trace is almost surely transient, then almost surely it
never returns to `0` at a positive time. This holds for every `κ > 0`; it is used at `κ′ = 16/κ > 4`, where the trace
is not simple.

**Proof (scaling).** Let `Z_c` be the event "`|η(q)| < 1/(k+1)` at some rational `q ≥ c`, for every `k`" (`zeroSet`, a
Borel set of rational driver values; for a continuous trace it says `inf_{t ≥ c} |η(t)| = 0`). The seed word is
invariant under the dilation `W ↦ c^{−1/2} W(c ·)`, and by Theorem 2.2's uniqueness in law the dilated driver has the
law of the driver (`ZhanGT4.map_ratProc_eq_of_ordered`); the trace dilates to `c^{−1/2} η(c ·)`. Hence
`P(Z_c) = P(Z_1)` for every `c > 0`. The events `Z_{N+1}` decrease, and their intersection is null by transience, so
`P(Z_1) = lim P(Z_{N+1}) = 0`, and `P(Z_c) = 0` for every `c > 0`. A return `η(t) = 0` at `t ≥ 1/(n+1)` lies in
`Z_{1/(n+1)}`. No collision or boundary-correspondence argument is needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CfLineRegQ

open Zhan ZhanGT4 Sec7.Dilation

/-! ### The event of small values at late rational times -/

/-- Rational driver values whose trace has values of norm `< 1/(k+1)` at rational times `≥ c`, for every `k`. -/
def zeroSet (c : ℝ≥0) : Set (ℚ≥0 → ℝ) := ⋂ k : ℕ, nearSet (1 / ((k : ℝ) + 1)) c

theorem measurableSet_zeroSet (c : ℝ≥0) : MeasurableSet (zeroSet c) :=
  MeasurableSet.iInter fun _ => measurableSet_nearSet _ _

theorem zeroSet_anti {c c' : ℝ≥0} (h : c ≤ c') : zeroSet c' ⊆ zeroSet c := by
  intro v hv
  refine mem_iInter.2 fun k => ?_
  obtain ⟨q, hq⟩ := mem_iUnion.1 (mem_iInter.1 hv k)
  exact mem_iUnion.2 ⟨q, h.trans hq.1, hq.2⟩

/-- For a continuous curve, small values at rational times `≥ c` are small values at real times `≥ c`. -/
theorem forall_exists_rat_iff {ψ : ℝ≥0 → ℂ} (hψ : Continuous ψ) (c : ℝ≥0) :
    (∀ k : ℕ, ∃ q : ℚ≥0, c ≤ (q : ℝ≥0) ∧ ‖ψ q‖ < 1 / ((k : ℝ) + 1)) ↔
      ∀ ε : ℝ, 0 < ε → ∃ t : ℝ≥0, c ≤ t ∧ ‖ψ t‖ < ε := by
  constructor
  · intro h ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨q, hq, hlt⟩ := h k
    exact ⟨q, hq, hlt.trans hk⟩
  · intro h k
    obtain ⟨t, ht, hlt⟩ := h _ (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))
    exact exists_rat_of_norm_lt hψ ht hlt

/-- **Small late values under dilation**: `c^{−1/2} η(c ·)` has arbitrarily small values at times `≥ 1` iff `η` has
arbitrarily small values at times `≥ c`. -/
theorem forall_exists_dilate_iff {η : ℝ≥0 → ℂ} {c : ℝ≥0} (hc : c ≠ 0) :
    (∀ ε : ℝ, 0 < ε → ∃ t : ℝ≥0, 1 ≤ t ∧ ‖(((√(c : ℝ))⁻¹ : ℝ) : ℂ) * η (c * t)‖ < ε) ↔
      ∀ ε : ℝ, 0 < ε → ∃ t : ℝ≥0, c ≤ t ∧ ‖η t‖ < ε := by
  have hc' : (0 : ℝ) < c := by
    have := pos_iff_ne_zero.2 hc
    exact_mod_cast this
  have hs : 0 < √(c : ℝ) := Real.sqrt_pos.2 hc'
  have hn : ∀ t : ℝ≥0, ‖(((√(c : ℝ))⁻¹ : ℝ) : ℂ) * η (c * t)‖ = ‖η (c * t)‖ / √(c : ℝ) := by
    intro t
    rw [norm_mul, Complex.norm_of_nonneg (by positivity), inv_mul_eq_div]
  constructor
  · intro h ε hε
    obtain ⟨t, ht, hlt⟩ := h (ε / √(c : ℝ)) (div_pos hε hs)
    refine ⟨c * t, ?_, ?_⟩
    · calc c = c * 1 := (mul_one c).symm
        _ ≤ c * t := mul_le_mul_of_nonneg_left ht zero_le
    · rw [hn, div_lt_div_iff_of_pos_right hs] at hlt
      exact hlt
  · intro h ε hε
    obtain ⟨t, ht, hlt⟩ := h (ε * √(c : ℝ)) (mul_pos hε hs)
    have hc0 : (0 : ℝ≥0) < c := pos_iff_ne_zero.2 hc
    have hct : c * (t / c) = t := by rw [mul_comm, div_mul_cancel₀ t hc]
    refine ⟨t / c, (le_div_iff₀ hc0).2 (by rwa [one_mul]), ?_⟩
    rw [hn, hct, div_lt_iff₀ hs]
    exact hlt

/-! ### No return to the seed -/

section Seed

variable {nL nR : ℕ} {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **A transient seed trace does not return to `0`** (every `κ > 0`): for an integrated `SLE_κ(ρ)` evolution with all
its marks at the seed and admissible side partial sums, if almost surely every continuous generating trace on
`[0, ∞)` tends to `∞`, then almost surely no such trace takes the value `0` at a positive time. -/
theorem ae_trace_ne_zero_of_seed (hκ : 0 < κ)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR (fun _ => 0) (fun _ => 0))
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ)
    (htr : ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → ∀ t : ℝ≥0, 0 < t → η t ≠ 0 := by
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
        Tendsto (fun t => ‖ηs t‖) atTop atTop := by
    filter_upwards [IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hκ hF hadm hE,
      htr, hE.2.2.2.2] with ω ⟨hζω, _, ηs, hηs⟩ htrω hp
    have hwc : Continuous fun t => W t ω := by
      have h := hp.2.2.2.1
      rw [hζω] at h
      exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
    exact ⟨hζω, hwc, hp.1, ηs, hηs, htrω ηs hηs⟩
  -- the probability of `Z_c` does not depend on `c > 0`
  have hsc : ∀ c : ℝ≥0, c ≠ 0 → P (X ⁻¹' zeroSet c) = P (X ⁻¹' zeroSet 1) := by
    intro c hc
    set Xc := ratProc (fun ω => ζ ω / c) (dilProc c W) with hXc
    have hXcm : Measurable Xc := measurable_ratProc (hE.dilate_zero hc).2.1
    have heq : X ⁻¹' zeroSet c =ᵐ[P] Xc ⁻¹' zeroSet 1 := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [hgood] with ω ⟨hζω, hwc, hw0, ηs, hηs, _⟩
      have hηc : Continuous ηs :=
        continuousOn_univ.1 (hηs.2.1.mono fun s _ => show (s : ℝ≥0∞) ≤ ⊤ from le_top)
      have hdil := hηs.dilate hc
      rw [ENNReal.top_div_of_ne_top ENNReal.coe_ne_top] at hdil
      have hdc : Continuous (dilPath c fun t => W t ω) :=
        continuous_const.mul (hwc.comp (continuous_const.mul continuous_id))
      have hd0 : dilPath c (fun t => W t ω) 0 = 0 := by simp [dilPath, hw0]
      have hXcω : Xc ω = fun q : ℚ≥0 => dilPath c (fun t => W t ω) q := by
        rw [hXc, ratProc_of_eq_top (ζ := fun ω => ζ ω / c) (W := dilProc c W) (ω := ω) (show ζ ω / c = ⊤ by
          rw [hζω]; exact ENNReal.top_div_of_ne_top ENNReal.coe_ne_top)]
        rfl
      have hXω : X ω = fun q : ℚ≥0 => W q ω := by rw [hX, ratProc_of_eq_top hζω]
      have hηdc : Continuous fun s : ℝ≥0 => (((√(c : ℝ))⁻¹ : ℝ) : ℂ) * ηs (c * s) :=
        continuousOn_univ.1 (hdil.2.1.mono fun s _ => show (s : ℝ≥0∞) ≤ ⊤ from le_top)
      have e1 : X ω ∈ zeroSet c ↔ ∀ k : ℕ, ∃ q : ℚ≥0, c ≤ (q : ℝ≥0) ∧ ‖ηs q‖ < 1 / ((k : ℝ) + 1) := by
        rw [hXω]
        simp only [zeroSet, mem_iInter]
        exact forall_congr' fun k => mem_nearSet_iff hwc hw0 hηs
      have e2 : Xc ω ∈ zeroSet 1 ↔ ∀ k : ℕ, ∃ q : ℚ≥0, 1 ≤ (q : ℝ≥0) ∧
          ‖(((√(c : ℝ))⁻¹ : ℝ) : ℂ) * ηs (c * q)‖ < 1 / ((k : ℝ) + 1) := by
        rw [hXcω]
        simp only [zeroSet, mem_iInter]
        exact forall_congr' fun k => mem_nearSet_iff hdc hd0 hdil
      show X ω ∈ zeroSet c ↔ Xc ω ∈ zeroSet 1
      rw [e1, e2, forall_exists_rat_iff hηc, forall_exists_rat_iff hηdc, forall_exists_dilate_iff hc]
    rw [measure_congr heq, ← Measure.map_apply hXcm (measurableSet_zeroSet 1), hlaw c hc,
      Measure.map_apply hXm (measurableSet_zeroSet 1)]
  -- `P(Z_1) = 0`: the events `Z_{N+1}` decrease to a null event (transience)
  have hanti : Antitone fun N : ℕ => X ⁻¹' zeroSet ((N : ℝ≥0) + 1) := fun n m hnm =>
    preimage_mono (zeroSet_anti (by exact_mod_cast Nat.add_le_add_right hnm 1))
  have hlim := tendsto_measure_iInter_atTop (μ := P)
    (fun N : ℕ => (hXm (measurableSet_zeroSet ((N : ℝ≥0) + 1))).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have h0 : P (⋂ N : ℕ, X ⁻¹' zeroSet ((N : ℝ≥0) + 1)) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hgood] with ω ⟨hζω, hwc, hw0, ηs, hηs, htrω⟩ hmem
    obtain ⟨T, hT⟩ := eventually_atTop.1 (htrω.eventually_ge_atTop 1)
    obtain ⟨N, hN⟩ := exists_nat_ge T
    have h1 := mem_iInter.1 hmem N
    rw [mem_preimage, hX, ratProc_of_eq_top hζω] at h1
    obtain ⟨q, hq, hlt⟩ := (mem_nearSet_iff hwc hw0 hηs).1 (mem_iInter.1 h1 0)
    have hTq : T ≤ (q : ℝ≥0) := hN.trans ((le_add_of_nonneg_right zero_le).trans hq)
    have h2 := hT _ hTq
    norm_num at hlt
    linarith
  have hconst : ∀ N : ℕ, P (X ⁻¹' zeroSet ((N : ℝ≥0) + 1)) = P (X ⁻¹' zeroSet 1) :=
    fun N => hsc _ (by positivity)
  have h1 : P (X ⁻¹' zeroSet 1) = 0 := by
    have e : (⇑P ∘ fun N : ℕ => X ⁻¹' zeroSet ((N : ℝ≥0) + 1)) = fun _ => P (X ⁻¹' zeroSet 1) :=
      funext hconst
    rw [h0, e] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  -- conclusion
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, X ω ∉ zeroSet (1 / ((n : ℝ≥0) + 1)) := by
    rw [ae_all_iff]
    intro n
    have hz : P (X ⁻¹' zeroSet (1 / ((n : ℝ≥0) + 1))) = 0 := by rw [hsc _ (by positivity), h1]
    exact measure_eq_zero_iff_ae_notMem.1 hz
  filter_upwards [hgood, hall] with ω ⟨hζω, hwc, hw0, ηs, hηs, _⟩ hω η hη t ht hzero
  have hηc : Continuous ηs :=
    continuousOn_univ.1 (hηs.2.1.mono fun s _ => show (s : ℝ≥0∞) ≤ ⊤ from le_top)
  have hηt : η t = ηs t := hη.eq_of_le hηs hwc.continuousOn hw0 le_top
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht
  apply hω n
  rw [hX, ratProc_of_eq_top hζω]
  refine mem_iInter.2 fun k => (mem_nearSet_iff hwc hw0 hηs).2 ?_
  refine exists_rat_of_norm_lt hηc hn.le ?_
  rw [← hηt, hzero, norm_zero]
  positivity

end Seed

end InteractingSLE.Sec5.CfLineRegQ
