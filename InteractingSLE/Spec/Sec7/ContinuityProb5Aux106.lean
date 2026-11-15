/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb5TailCode
import InteractingSLE.Spec.Sec7.ContinuityProb4Aux106

/-!
# §7.3: transience on a final infinite band (Aux. lemmas 102, 106 and 113 when a side total is at most `−2`)

Packet PROVE-SEC7-C5. Specification §7.3, Aux. lemma 106 (`source/spec/p337-384.md` L392, p. 354): "If `a ≤ 0` or
`b ≤ 0`, Aux. lemma 102 gives finite total angular clock. The alternating bands `U ≤ 2/3` and `U ≥ 1/3` have only
finitely many switches on that clock […]. On the final infinite band, deleting the opposite mark has finite energy,
bounded by a constant times `∫ D^{-2} dt`. Apply the bounded-energy comparison from each adapted band starting time with
an additional integer angular-clock cutoff, and take the countable union. This transfers the one-force transience
assertion without conditioning on a non-stopping last switch." The same argument is the case `s_L ≤ −2` or `s_R ≤ −2`
of Aux. lemma 113 (p. 370).

* **`ae_tendsto_of_eventualBand`**: for an evolution of a separated ordered word whose reduced words (one side
  deleted) have the full trace event at every separated ordered start, with a continuous trace on `[0, ζ]`, almost
  surely on `{ζ = ∞}`: if the total angular clock `∫₀^∞ D^{-2}` is finite and the driver eventually stays at distance
  more than `D/4` from the nearest mark of one side, every continuous generating trace on `[0, ∞)` tends to infinity.
  Proof: restart at an integer time `N` after the last band switch (`ae_bandTail_rational`) with a clock cutoff above
  the remaining discrete clock (`sum_inv_sq_le_integral`): the band never ends, so the shifted driver has a transient
  trace (whole-tail Girsanov); join it with the trace on `[0, N]` (`IsGeneratingTraceIcc.join`) and use uniqueness of
  generating traces.
* Named inputs: `Aux102BandStatement` (Aux. lemma 102 with the finitely many switches: finite angular clock and a
  final band, for `s ≤ −2` or `q ≤ −2`), `Aux106PositiveStatement` (Aux. lemma 106's transience when `a, b > 0`:
  Aux. lemma 100 and the stationary Jacobi path-law transfer (J12)–(J14)).
* **`aux106TransienceStatement_of_inputs`**: PROVE-SEC7-C4's `Aux106TransienceStatement` from these and the
  one-force inputs of the `κ < 4` induction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace Band

variable {nL nR : ℕ}

/-! ### Discrete and continuous angular clocks -/

/-- `Σ_{j < n} D(j + 1)^{-2} ≤ ∫₀ⁿ D^{-2}` for a nondecreasing positive continuous `D`. -/
theorem sum_inv_sq_le_integral {D : ℝ≥0 → ℝ} (hD0 : 0 < D 0) (hmono : Monotone D) (hc : Continuous D)
    (n : ℕ) : ∑ j ∈ Finset.range n, (D (j + 1 : ℕ))⁻¹ ^ 2 ≤ ∫ s in (0 : ℝ)..(n : ℝ), (D s.toNNReal)⁻¹ ^ 2 := by
  have hpos : ∀ t, 0 < D t := fun t => hD0.trans_le (hmono zero_le)
  set c : ℕ → ℝ := fun j => (D (j + 1 : ℕ))⁻¹ ^ 2 with hcdef
  have hc0 : ∀ j, 0 ≤ c j := fun j => sq_nonneg _
  rw [← integral_floor_step_nat hc0 n]
  refine intervalIntegral.integral_mono_on (Nat.cast_nonneg n) (intervalIntegrable_floor_step hc0 n) ?_ ?_
  · refine ContinuousOn.intervalIntegrable ?_
    refine (((hc.comp continuous_real_toNNReal).continuousOn).inv₀ fun s _ => (hpos _).ne').pow 2
  · intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hle : D s.toNNReal ≤ D ((⌊s⌋₊ + 1 : ℕ) : ℝ≥0) := by
      refine hmono ?_
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0, NNReal.coe_natCast]
      push_cast
      exact (Nat.lt_floor_add_one s).le
    simp only [hcdef]
    rw [inv_pow, inv_pow]
    exact inv_anti₀ (pow_pos (hpos _) 2) (pow_le_pow_left₀ (hpos _).le hle 2)

/-! ### Transience on a final infinite band -/

section Assembly

open Sec2 Sec2.Assembly Sec2.Restart RandRestart

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {i₀ : Fin nL} {j₀ : Fin nR}

theorem crossGap_shiftMarks (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (w : ℝ≥0 → ℝ) (σ t : ℝ≥0) :
    crossGap (shiftMarks vL w σ) (shiftMarks vR w σ) i₀ j₀ t = crossGap vL vR i₀ j₀ (σ + t) := by
  simp only [crossGap, shiftMarks]; ring

/-- The discrete clock of the chain restarted at an integer time `N ≥ 1` is bounded by the angular clock. -/
theorem discClock_shift_le {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {w : ℝ≥0 → ℝ}
    (hD0 : 0 < crossGap vL vR i₀ j₀ 0) (hmono : Monotone (crossGap vL vR i₀ j₀))
    (hc : Continuous (crossGap vL vR i₀ j₀)) {M : ℝ}
    (hM : ∀ t : ℝ≥0, ∫ s in (0 : ℝ)..t, (crossGap vL vR i₀ j₀ s.toNNReal)⁻¹ ^ 2 ≤ M) {N : ℕ} (hN : 1 ≤ N)
    (t : ℝ≥0) : discClock (shiftMarks vL w N) (shiftMarks vR w N) i₀ j₀ t ≤ M := by
  set n := ⌊(t : ℝ)⌋₊ + 1 with hn
  have hsub : discClock (shiftMarks vL w N) (shiftMarks vR w N) i₀ j₀ t ≤
      ∑ j ∈ Finset.range (N + n), (crossGap vL vR i₀ j₀ (j + 1 : ℕ))⁻¹ ^ 2 := by
    simp only [discClock, crossGap_shiftMarks]
    have e : ∀ k ∈ Finset.range n, (crossGap vL vR i₀ j₀ ((N : ℝ≥0) + (k : ℝ≥0)))⁻¹ ^ 2 =
        (crossGap vL vR i₀ j₀ (((k + (N - 1)) + 1 : ℕ) : ℝ≥0))⁻¹ ^ 2 := fun k _ => by
      congr 3
      push_cast
      rw [add_assoc, tsub_add_cancel_of_le (by exact_mod_cast hN : (1 : ℝ≥0) ≤ N), add_comm]
    rw [Finset.sum_congr rfl e]
    have hinj : ∀ a ∈ Finset.range n, ∀ b ∈ Finset.range n, a + (N - 1) = b + (N - 1) → a = b :=
      fun a _ b _ h => by omega
    rw [← Finset.sum_image (f := fun j => (crossGap vL vR i₀ j₀ ((j + 1 : ℕ) : ℝ≥0))⁻¹ ^ 2) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hj
    rw [Finset.mem_range] at hk ⊢
    omega
  refine hsub.trans ((sum_inv_sq_le_integral hD0 hmono hc (N + n)).trans ?_)
  have := hM ((N + n : ℕ) : ℝ≥0)
  simpa using this

/-- **Transience on a final infinite band.** For an evolution of a separated ordered word whose reduced words have
the full trace event at every separated ordered start, with a continuous trace on `[0, ζ]` almost surely: almost
surely on `{ζ = ∞}`, if the total angular clock `∫₀^∞ D^{-2}` is finite and the driver eventually stays at distance
more than `D/4` from the nearest right mark (or from the nearest left mark), every continuous generating trace on
`[0, ∞)` tends to infinity. -/
theorem ae_tendsto_of_eventualBand [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hsep : ∀ i j, xL i < xR j)
    (hredR : ∀ s : (Fin nL → ℝ) × (Fin nR → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS κ ρL (0 : Fin nR → ℝ) (fullTraceSet (nL := nL) (nR := nR)))
    (hredL : ∀ s : (Fin nL → ℝ) × (Fin nR → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS κ (0 : Fin nL → ℝ) ρR (fullTraceSet (nL := nL) (nR := nR)))
    (hi₀ : ∀ i, i₀ ≤ i) (hj₀ : ∀ j, j₀ ≤ j)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    (hband : ∀ᵐ ω ∂P, ζ ω = ⊤ →
      (∃ M : ℝ, ∀ t : ℝ≥0, ∫ s in (0 : ℝ)..t, (VR j₀ s.toNNReal ω - VL i₀ s.toNNReal ω)⁻¹ ^ 2 ≤ M) ∧
      ((∃ T : ℝ≥0, ∀ t, T ≤ t → VR j₀ t ω - VL i₀ t ω < 4 * (VR j₀ t ω - W t ω)) ∨
        (∃ T : ℝ≥0, ∀ t, T ≤ t → VR j₀ t ω - VL i₀ t ω < 4 * (W t ω - VL i₀ t ω)))) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ → ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  have hbt := ae_bandTail_rational (i₀ := i₀) (j₀ := j₀) hκ hE hredR hredL hi₀ hj₀
  filter_upwards [hbt, htr, hband, hE.2.2.2.2] with ω hbω htrω hbandω hp hζ η hη
  obtain ⟨⟨M, hM⟩, hside⟩ := hbandω hζ
  have hF := hp.isForcePath
  rw [hζ] at hp
  have hwc : Continuous fun t => W t ω := by
    have := hp.isForcePath.continuousOn_w
    simpa using this
  have hcD : Continuous (crossGap (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀) := by
    have h1 := hp.isForcePath.continuousOn_vR j₀
    have h2 := hp.isForcePath.continuousOn_vL i₀
    simp only [ENNReal.coe_lt_top, ofPred_true, continuousOn_univ] at h1 h2
    exact h1.sub h2
  have hmono : Monotone (crossGap (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀) := fun s t hst =>
    hp.isForcePath.crossGap_le i₀ j₀ hst ENNReal.coe_lt_top
  have hD0 : 0 < crossGap (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀ 0 := by
    simp only [crossGap, hp.isForcePath.vL_zero, hp.isForcePath.vR_zero]
    exact sub_pos.2 (hsep i₀ j₀)
  -- the trace on `[0, ∞)` given by finite-time continuity
  obtain ⟨η₁, hη₁⟩ := htrω
  rw [hζ] at hη₁
  have hw0 : W 0 ω = 0 := hp.1
  have hwcon : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ⊤} := hwc.continuousOn
  -- the restart time and the clock cutoff
  obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, (∀ t, T ≤ t → VR j₀ t ω - VL i₀ t ω < 4 * (VR j₀ t ω - W t ω)) ∨
      (∀ t, T ≤ t → VR j₀ t ω - VL i₀ t ω < 4 * (W t ω - VL i₀ t ω)) := by
    rcases hside with ⟨T, h⟩ | ⟨T, h⟩
    · exact ⟨T, Or.inl h⟩
    · exact ⟨T, Or.inr h⟩
  set N : ℕ := ⌈(T : ℝ)⌉₊ + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hTN : T ≤ (N : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast, hNdef]
    push_cast
    linarith [Nat.le_ceil (T : ℝ)]
  set m : ℕ := ⌈M⌉₊ + 1 with hmdef
  have hMm : M < m := by rw [hmdef]; push_cast; linarith [Nat.le_ceil M]
  have hclock : ∀ t : ℝ≥0, discClock (shiftMarks (fun i t => VL i t ω) (fun t => W t ω) N)
      (shiftMarks (fun j t => VR j t ω) (fun t => W t ω) N) i₀ j₀ t < m := fun t =>
    (discClock_shift_le hD0 hmono hcD hM hN1 t).trans_lt hMm
  have hq : Real.toNNReal ((N : ℚ) : ℝ) = (N : ℝ≥0) := by
    rw [Rat.cast_natCast, Real.toNNReal_natCast]
  obtain ⟨hR, hL⟩ := hbω (N : ℚ) m (Or.inr hsep) (by rw [hq, hζ]; exact ENNReal.coe_lt_top)
  rw [hq, hζ, ENNReal.top_sub_coe] at hR hL
  -- the band from `N` never ends: the shifted driver has a transient trace
  have hev : TraceEvent (shiftNN (fun t => W t ω) N) ⊤ := by
    rcases hT with hTR | hTL
    · convert hR using 1
      symm
      refine le_antisymm le_top (le_min (le_hitTime fun s _ _ hs => ?_) le_rfl)
      rcases hs with hs | hs
      · have h := hTR ((N : ℝ≥0) + s) (hTN.trans le_self_add)
        simp only [crossGap, shiftMarks] at hs
        unfold shiftNN at hs
        linarith
      · exact (not_le.2 (hclock s)) hs
    · convert hL using 1
      symm
      refine le_antisymm le_top (le_min (le_hitTime fun s _ _ hs => ?_) le_rfl)
      rcases hs with hs | hs
      · have h := hTL ((N : ℝ≥0) + s) (hTN.trans le_self_add)
        simp only [crossGap, shiftMarks] at hs
        unfold shiftNN at hs
        linarith
      · exact (not_le.2 (hclock s)) hs
  obtain ⟨η₂, hη₂, hη₂t⟩ := hev
  -- join with the trace on `[0, N]`
  have hIcc := IsGeneratingTrace.isGeneratingTraceIcc hη₁ hwcon hw0 (σ := (N : ℝ≥0)) ENNReal.coe_lt_top
  have hwcon' : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < (N : ℝ≥0) + ⊤} := by
    rw [add_top]; exact hwcon
  obtain ⟨hJ, hJt⟩ := IsGeneratingTraceIcc.join hwcon' hw0 hIcc hη₂
  rw [add_top] at hJ
  have hJt' := hJt rfl (hη₂t rfl)
  refine hJt'.congr fun t => ?_
  rw [IsGeneratingTrace.eq_of_le hη hJ hwcon hw0 le_top]

end Assembly

end Band

/-! ### Aux. lemma 106: the reduction of its transience -/

/-- **Named input: Aux. lemma 102 with the finitely many band switches** (Specification p. 348, Aux. lemma 102:
"If `s ≤ −2` or `q ≤ −2`, then the total angular clock `∫ D_t^{-2} dt` until the continuation threshold […] is finite
almost surely"; p. 354, Aux. lemma 106: "The alternating bands `U ≤ 2/3` and `U ≥ 1/3` have only finitely many switches
on that clock: Brownian motion and the finite-variation error have finite terminal limits, and the drift is bounded on
the middle band"; the same in Aux. lemma 113, p. 370). For `κ > 0` and an evolution of a separated ordered word with
at least one mark on each side whose left or right total weight is at most `−2`: almost surely on `{ζ = ∞}`, the total
angular clock of the nearest-group cross-gap `D = V^{R,0} − V^{L,0}` is finite, and eventually the driver stays at
distance more than `D/4` from the nearest right mark (`U < 3/4`) or from the nearest left mark (`U > 1/4`). -/
def Aux102BandStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ {nL nR : ℕ} (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin (nR + 1) → ℝ), IsOrderedForceWord xL xR → (∀ i j, xL i < xR j) →
    ((∑ i, ρL i) ≤ -2 ∨ (∑ j, ρR j) ≤ -2) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
      (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ζ ω = ⊤ →
        (∃ M : ℝ, ∀ t : ℝ≥0, ∫ s in (0 : ℝ)..t, (VR 0 s.toNNReal ω - VL 0 s.toNNReal ω)⁻¹ ^ 2 ≤ M) ∧
        ((∃ T : ℝ≥0, ∀ t, T ≤ t → VR 0 t ω - VL 0 t ω < 4 * (VR 0 t ω - W t ω)) ∨
          (∃ T : ℝ≥0, ∀ t, T ≤ t → VR 0 t ω - VL 0 t ω < 4 * (W t ω - VL 0 t ω)))

/-- **Named input: Aux. lemma 106's transience when `a, b > 0`** (Specification pp. 354–355, from "Suppose now that
`a, b > 0`": the clock change (J12), Aux. lemma 100 (positive-time absolute continuity of the Jacobi entrance), the
stationary two-sided Jacobi path-law transfer (J14) and [Yua22] Corollary 1.3). For `0 < κ < 4`, under the two-seed
premise, for every evolution of a word with one mark on each side, not both at the seed, and both weights `> −2`:
almost surely, if the lifetime is infinite, every continuous generating trace on `[0, ∞)` tends to infinity. -/
def Aux106PositiveStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
    (∀ (xL xR ρL ρR : Fin 1 → ℝ), (∀ i, xL i = 0) → (∀ i, xR i = 0) → (∀ i, -2 < ρL i) →
      (∀ i, -2 < ρR i) → LP.IsCompleteForceWord.{u} κ xL xR ρL ρR) →
    ∀ (xL xR ρL ρR : Fin 1 → ℝ), IsOrderedForceWord xL xR → (xL 0 < 0 ∨ 0 < xR 0) → -2 < ρL 0 → -2 < ρR 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ζ ω = ⊤ →
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop

/-- **`Sec7.Aux106TransienceStatement` from Aux. lemma 102 with its band switches, the positive case, Theorem 2.2's
existence and the one-force inputs of the `κ < 4` induction.** The case `a ≤ 0` or `b ≤ 0` is proved here
(`ae_tendsto_of_eventualBand`: final infinite band, whole-tail Girsanov, the one-force words, join). -/
theorem aux106TransienceStatement_of_inputs (hex : ExistsEvolutionStatement)
    (h1 : SeedOneForceTraceStatement.{u}) (h99 : Aux99Statement.{u}) (h102 : Aux102BandStatement.{u})
    (hpos : Aux106PositiveStatement.{u}) : Aux106TransienceStatement.{u} := by
  intro κ hκ hκ4 h2 xL xR ρL ρR hF hside Ω mΩ P _ 𝓕 W VL VR B ζ hE
  by_cases hneg : ρL 0 ≤ -2 ∨ ρR 0 ≤ -2
  · have hsep : ∀ i j, xL i < xR j := by
      intro i j
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      rcases hside with h | h
      · exact h.trans_le (hF.2.2.2 0)
      · exact (hF.2.1 0).trans_lt h
    have hD : LP.DistinctCompleteBelow.{u} κ 2 := distinctCompleteBelow_two h1 h99 hκ hκ4
    have htr := ae_isGeneratingTrace_lifetime hκ hex hD hE hF (by norm_num) (by norm_num) (Or.inl hsep)
    have hsum : (∑ i, ρL i) ≤ -2 ∨ (∑ j, ρR j) ≤ -2 := by
      simpa only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] using hneg
    have hband := h102 κ hκ (nL := 0) (nR := 0) xL xR ρL ρR hF hsep hsum P 𝓕 W VL VR B ζ hE
    exact Band.ae_tendsto_of_eventualBand (i₀ := 0) (j₀ := 0) hκ hE hsep
      (ae_mem_lawSetS_zero_right hκ hex hD ρL (by norm_num))
      (ae_mem_lawSetS_zero_left hκ hex hD ρR (by norm_num)) (fun i => Fin.zero_le i) (fun j => Fin.zero_le j)
      htr hband
  · rw [not_or, not_le, not_le] at hneg
    exact hpos κ hκ hκ4 h2 xL xR ρL ρR hF hside hneg.1 hneg.2 P 𝓕 W VL VR B ζ hE

end Sec7

end InteractingSLE
