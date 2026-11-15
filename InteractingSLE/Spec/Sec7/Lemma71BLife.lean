/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71BLocal
import InteractingSLE.Spec.Sec7.Lemma71BBound
import InteractingSLE.Spec.Supplement.LPAssembly
import BrownianMotion.StochasticIntegral.DoobLp

/-!
# Lemma 7.1, terminal capacity: the localized martingale part of the stopped two-seed driver

Packet PROVE-LEMMA71B. Specification, proof of Lemma 7.1 (`source/spec/p193-240.md` L604, p. 225: "Its terminal
capacity cannot be finite. Otherwise the globally defined admissible two-seed driving process would have a bounded
driver on that finite interval").

For the two-seed word `(0⁻; 0⁺)` with weights `(ρᴸ; ρᴿ)` and a driver `W` killed at `T` whose coupling means are local
martingales before `min (swallowTime z) T`, consider the stopped drivers `W⁽ⁿ⁾ = stopDrv W T G (n + 1)` and the
localizing times `τ_{K,n} = locTime W⁽ⁿ⁾ V⁽ⁿ⁾ K n` (`V⁽ⁿ⁾` the geometric seed images of `W⁽ⁿ⁾`). This file proves:

* `locTime_lt_exitAbove`: `τ_{K,n}` comes strictly before the exit time of `W⁽ⁿ⁾`;
* `martingale_stoppedProcess_sMart`, `martingale_stoppedProcess_sMart_sq`: Theorem 2.4's martingale part `M⁽ⁿ⁾`
  of `W⁽ⁿ⁾` stopped at `τ_{K,n}` and `(M⁽ⁿ⁾)² − κ t` stopped at `τ_{K,n}` are martingales
  (`Lemma71BMart`, `Lemma71BLocal` and PROVE-SEC2-MART's quadratic-variation identification);
* `integral_sq_stoppedProcess_sMart_le`: `E[(M⁽ⁿ⁾_{τ ∧ K})²] ≤ κ K`, uniformly in `n`;
* **`measureReal_le_sMart`** (Doob's maximal inequality): `P(sup_{t ≤ K} |M⁽ⁿ⁾_{t ∧ τ}| ≥ λ) ≤ (1 + κ K)/(2 λ)`,
  uniformly in `n`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma71B

open MartChar MartChar.RealFlow Coupling

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Notation -/

/-- The stopped driver at level `n + 1`. -/
abbrev sDrv (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0∞) (G : Set Ω) (n : ℕ) : ℝ≥0 → Ω → ℝ :=
  stopDrv W T G ((n : ℝ) + 1)

/-- Its geometric seed images `(Vᴸ, Vᴿ)`. -/
abbrev sV (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0∞) (G : Set Ω) (n : ℕ) : Fin 1 ⊕ Fin 1 → ℝ≥0 → Ω → ℝ :=
  jointV (geomL (sDrv W T G n) LP.twoSeedXL) (geomR (sDrv W T G n) LP.twoSeedXR)

/-- The localizing time `τ_{K,n}`. -/
abbrev sTau (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0∞) (G : Set Ω) (K n : ℕ) : Ω → WithTop ℝ≥0 :=
  locTime (sDrv W T G n) (sV W T G n) K n

/-- The martingale part `M⁽ⁿ⁾ = W⁽ⁿ⁾ + ½ (ρᴸ Vᴸ + ρᴿ Vᴿ)` of Theorem 2.4. -/
abbrev sMart (rL rR : ℝ) (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0∞) (G : Set Ω) (n : ℕ) : ℝ≥0 → Ω → ℝ :=
  martProc (jointρ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)) (sDrv W T G n) (sV W T G n)

/-! ### The stopped two-seed driver -/

section Stopped

variable {T : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {G : Set Ω}

/-- The geometric image of the right seed at time `0`. -/
theorem geomR_twoSeed_zero' {W' : ℝ≥0 → Ω → ℝ} {ω : Ω} (hW' : Continuous fun s => W' s ω)
    (hW0 : W' 0 ω = 0) (i : Fin 1) : geomR W' LP.twoSeedXR i 0 ω = 0 := by
  have hc : Continuous (Bessel.realPath W' ω) := hW'.comp continuous_real_toNNReal
  have h0 : Bessel.realPath W' ω 0 = 0 := by simp [Bessel.realPath, hW0]
  simp only [geomR, LP.twoSeedXR, NNReal.coe_zero]
  exact rightImg_zero hc h0 le_rfl

/-- The geometric image of the left seed at time `0`. -/
theorem geomL_twoSeed_zero' {W' : ℝ≥0 → Ω → ℝ} {ω : Ω} (hW' : Continuous fun s => W' s ω)
    (hW0 : W' 0 ω = 0) (i : Fin 1) : geomL W' LP.twoSeedXL i 0 ω = 0 := by
  have hc : Continuous (Bessel.realPath (fun t ω => -W' t ω) ω) := by
    show Continuous fun s : ℝ => -W' s.toNNReal ω
    exact (hW'.comp continuous_real_toNNReal).neg
  have h0 : Bessel.realPath (fun t ω => -W' t ω) ω 0 = 0 := by simp [Bessel.realPath, hW0]
  simp only [geomL, LP.twoSeedXL, NNReal.coe_zero, neg_zero]
  rw [rightImg_zero hc h0 le_rfl, neg_zero]

theorem jointV_twoSeed_zero (j : Fin 1 ⊕ Fin 1) : jointV LP.twoSeedXL LP.twoSeedXR j = 0 := by
  cases j <;> rfl

variable (hW0 : ∀ ω, W 0 ω = 0) (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω})
  (hunb : ∀ ω, ω ∈ G → T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|)
include hW0 hc hunb

theorem continuous_sDrv (n : ℕ) (ω : Ω) : Continuous fun s => sDrv W T G n s ω :=
  continuous_stopDrv (hW0 ω) (hc ω) (hunb ω)

omit hc in
theorem sDrv_zero (n : ℕ) (ω : Ω) : sDrv W T G n 0 ω = 0 :=
  stopDrv_zero (hW0 ω) (hunb ω)

theorem continuous_sV (n : ℕ) (j : Fin 1 ⊕ Fin 1) (ω : Ω) : Continuous fun t => sV W T G n j t ω := by
  have hWc := continuous_sDrv hW0 hc hunb (G := G) n
  cases j with
  | inl i => exact (isForcePath_geomL hWc LP.twoSeedXL ω i).1
  | inr i => exact (isForcePath_geomR hWc LP.twoSeedXR ω i).1

theorem sV_zero (n : ℕ) (j : Fin 1 ⊕ Fin 1) (ω : Ω) : sV W T G n j 0 ω = 0 := by
  have hWc := continuous_sDrv hW0 hc hunb (G := G) n
  cases j with
  | inl i => exact geomL_twoSeed_zero' (hWc ω) (sDrv_zero hW0 hunb n ω) i
  | inr i => exact geomR_twoSeed_zero' (hWc ω) (sDrv_zero hW0 hunb n ω) i

/-- **The localizing time comes before the exit time** (on `G`): at the exit time `|W| ≥ n + 1`, so `|W|` passes
`n + 1/2`, and the localizing quantity `|W| + |Vᴸ| + |Vᴿ|` reaches `n`, strictly earlier. -/
theorem locTime_lt_exitAbove (K n : ℕ) {ω : Ω} (hω : ω ∈ G) :
    sTau W T G K n ω < exitAbove W T G ((n : ℝ) + 1) ω := by
  rcases eq_or_ne (exitAbove W T G ((n : ℝ) + 1) ω) ⊤ with htop | hne
  · rw [htop]
    exact lt_of_le_of_lt (locTime_le K n ω) (WithTop.coe_lt_top _)
  obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 hne
  have huT := lt_of_exitAbove_eq hω hu.symm
  -- at the exit time `|W u| ≥ n + 1`
  have hWu : (n : ℝ) + 1 ≤ |W u ω| := by
    have h := hu.symm
    rw [exitAbove_of_mem hω] at h
    have := le_of_hitBelow_eq (f := fun s => -|W s ω|) (hc ω).abs.neg h
    linarith
  have hsu : ∀ s ≤ u, sDrv W T G n s ω = W s ω := fun s hs =>
    stopDrv_eq_of_le (hW0 ω) (hunb ω) (by rw [← hu]; exact WithTop.coe_le_coe.2 hs)
  -- `|W⁽ⁿ⁾|` passes `n + 1/2` before `u`
  have hcont : ContinuousOn (fun s => |sDrv W T G n s ω|) (Icc 0 u) :=
    (continuous_abs.comp (continuous_sDrv hW0 hc hunb n ω)).continuousOn
  have hmid : (n : ℝ) + 1 / 2 ∈ Icc (|sDrv W T G n 0 ω|) (|sDrv W T G n u ω|) := by
    rw [sDrv_zero hW0 hunb n ω, abs_zero, hsu u le_rfl]
    constructor <;> [positivity; linarith]
  obtain ⟨s, hs, hseq⟩ := intermediate_value_Icc zero_le hcont hmid
  have hsltu : s < u := by
    refine lt_of_le_of_ne hs.2 fun h => ?_
    have h' : |sDrv W T G n u ω| = (n : ℝ) + 1 / 2 := by rw [← h]; exact hseq
    rw [hsu u le_rfl] at h'
    linarith
  -- the localizing quantity reaches `n` by time `s`
  have hexit : MathFin.exitTime (absSum (sDrv W T G n) (sV W T G n)) n ω ≤ (s : WithTop ℝ≥0) := by
    rw [MathFin.exitTime_le_iff (continuous_absSum (continuous_sDrv hW0 hc hunb n)
      (continuous_sV hW0 hc hunb n))]
    refine ⟨s, ⟨zero_le, le_rfl⟩, ?_⟩
    have h1 : |sDrv W T G n s ω| ≤ absSum (sDrv W T G n) (sV W T G n) s ω := by
      simp only [absSum]
      linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => abs_nonneg (sV W T G n j s ω)]
    have h2 : 0 ≤ absSum (sDrv W T G n) (sV W T G n) s ω :=
      (abs_nonneg _).trans h1
    rw [abs_of_nonneg h2]
    have : (n : ℝ) ≤ |sDrv W T G n s ω| := by simp only at hseq; rw [hseq]; linarith
    linarith
  calc sTau W T G K n ω ≤ MathFin.exitTime (absSum (sDrv W T G n) (sV W T G n)) n ω := min_le_right _ _
    _ ≤ s := hexit
    _ < u := WithTop.coe_lt_coe.2 hsltu
    _ = exitAbove W T G ((n : ℝ) + 1) ω := hu

/-- Up to the localizing time, `|W⁽ⁿ⁾| ≤ n` and `|V⁽ⁿ⁾| ≤ n`. -/
theorem abs_le_of_le_sTau {K n : ℕ} {ω : Ω} {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) ≤ sTau W T G K n ω) :
    |sDrv W T G n t ω| ≤ n ∧ ∀ j, |sV W T G n j t ω| ≤ n := by
  have hV0 : ∀ j ω, sV W T G n j 0 ω = jointV LP.twoSeedXL LP.twoSeedXR j := fun j ω => by
    rw [jointV_twoSeed_zero]
    exact sV_zero hW0 hc hunb n j ω
  have h := abs_le_of_le_locTime (W := sDrv W T G n) (V := sV W T G n) (w₀ := 0)
    (x := jointV LP.twoSeedXL LP.twoSeedXR)
    (sDrv_zero hW0 hunb n) hV0 (continuous_sDrv hW0 hc hunb n) (continuous_sV hW0 hc hunb n) ht
  simp only [abs_zero, add_zero, jointV_twoSeed_zero, Finset.sum_const_zero] at h
  exact h

end Stopped

/-! ### The martingale part of the stopped driver -/

section Mart

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous]
  {κ rL rR : ℝ} {T : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {G : Set Ω}

/-- The martingale part `M = W + ½ (ρᴸ Vᴸ + ρᴿ Vᴿ)` of a two-seed state started at `0`. -/
theorem sMart_eq (hW0 : ∀ ω, W 0 ω = 0)
    (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω})
    (hunb : ∀ ω, ω ∈ G → T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    sMart rL rR W T G n t ω = sDrv W T G n t ω +
      (1 / 2) * (rL * sV W T G n (Sum.inl 0) t ω + rR * sV W T G n (Sum.inr 0) t ω) := by
  simp only [sMart, martProc, martValue, sDrv_zero hW0 hunb n ω, Fintype.sum_sum_type,
    Fin.sum_univ_one, jointρ, Sum.elim_inl, Sum.elim_inr]
  rw [sV_zero hW0 hc hunb n (Sum.inl 0) ω, sV_zero hW0 hc hunb n (Sum.inr 0) ω]
  ring

/-- **The martingale part is bounded up to the localizing time.** -/
theorem abs_stoppedProcess_sMart_le (hW0 : ∀ ω, W 0 ω = 0)
    (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω})
    (hunb : ∀ ω, ω ∈ G → T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|)
    (K n : ℕ) (t : ℝ≥0) (ω : Ω) :
    |stoppedProcess (sMart rL rR W T G n) (sTau W T G K n) t ω| ≤ n + (|rL| + |rR|) / 2 * n := by
  have hle : (((min (t : WithTop ℝ≥0) (sTau W T G K n ω)).untopA : ℝ≥0) : WithTop ℝ≥0) ≤
      sTau W T G K n ω := by
    rw [coe_untopA_of_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))]
    exact min_le_right _ _
  obtain ⟨hW, hV⟩ := abs_le_of_le_sTau hW0 hc hunb hle
  simp only [stoppedProcess]
  rw [sMart_eq hW0 hc hunb]
  have h1 := hV (Sum.inl 0)
  have h2 := hV (Sum.inr 0)
  have hL : |rL * sV W T G n (Sum.inl 0) ((min (t : WithTop ℝ≥0) (sTau W T G K n ω)).untopA) ω| ≤
      |rL| * n := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hR : |rR * sV W T G n (Sum.inr 0) ((min (t : WithTop ℝ≥0) (sTau W T G K n ω)).untopA) ω| ≤
      |rR| * n := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  calc _ ≤ |sDrv W T G n ((min (t : WithTop ℝ≥0) (sTau W T G K n ω)).untopA) ω| +
        |(1 / 2) * (rL * sV W T G n (Sum.inl 0) ((min (t : WithTop ℝ≥0) (sTau W T G K n ω)).untopA) ω +
          rR * sV W T G n (Sum.inr 0) ((min (t : WithTop ℝ≥0) (sTau W T G K n ω)).untopA) ω)| :=
        abs_add_le _ _
    _ ≤ n + (|rL| + |rR|) / 2 * n := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        have := abs_add_le (rL * sV W T G n (Sum.inl 0)
          ((min (t : WithTop ℝ≥0) (sTau W T G K n ω)).untopA) ω)
          (rR * sV W T G n (Sum.inr 0) ((min (t : WithTop ℝ≥0) (sTau W T G K n ω)).untopA) ω)
        nlinarith

variable (hκ : 0 < κ) (hm : HasMartingaleMeansBefore κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓖 W T)
  (hW0 : ∀ ω, W 0 ω = 0) (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω})
  (hWa : AdaptedBefore 𝓖 T W) (hG : MeasurableSet[𝓖 0] G) (hGP : P Gᶜ = 0)
  (hunb : ∀ ω, ω ∈ G → T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|)
include hκ hm hW0 hc hWa hG hGP hunb

/-- **Theorem 2.4's localization for the stopped driver**: the martingale part `M⁽ⁿ⁾` stopped at `τ_{K,n}` and
`(M⁽ⁿ⁾)² − κ t` stopped at `τ_{K,n}` are martingales. -/
theorem martingale_sMart (K n : ℕ) :
    Martingale (stoppedProcess (sMart rL rR W T G n) (sTau W T G K n)) 𝓖 P ∧
      Martingale (stoppedProcess (fun t ω => sMart rL rR W T G n t ω ^ 2 - κ * t) (sTau W T G K n))
        𝓖 P := by
  have hWc := continuous_sDrv hW0 hc hunb (G := G) n
  have hWa' : StronglyAdapted 𝓖 (sDrv W T G n) := stronglyAdapted_stopDrv hWa hG hc _
  have hVLa := fun i => stronglyAdapted_geomL hWa' hWc LP.twoSeedXL i
  have hVRa := fun i => stronglyAdapted_geomR hWa' hWc LP.twoSeedXR i
  have hVa : ∀ j, StronglyAdapted 𝓖 (sV W T G n j) := fun j => by
    cases j with
    | inl i => exact hVLa i
    | inr i => exact hVRa i
  have hpath : ∀ ω j, IsForcePath (fun t => sDrv W T G n t ω) (fun t => sV W T G n j t ω) :=
    fun ω j => by
      cases j with
      | inl i => exact isForcePath_geomL hWc LP.twoSeedXL ω i
      | inr i => exact isForcePath_geomR hWc LP.twoSeedXR ω i
  have hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓖 P
      (fun ω => min (QuantumZipper.swallowTime (wpath (sDrv W T G n) ω) z : WithTop ℝ≥0)
        (exitAbove W T G ((n : ℝ) + 1) ω))
      (coupProc κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (sDrv W T G n)
        (geomL (sDrv W T G n) LP.twoSeedXL) (geomR (sDrv W T G n) LP.twoSeedXR) z) :=
    fun z hz => isLocalMartingaleBefore_coupProc_stopDrv hm hW0 hc hWa hG hunb _ hz
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    simpa only [compl_def] using hGP
  have hτθ : ∀ᵐ ω ∂P, sTau W T G K n ω < exitAbove W T G ((n : ℝ) + 1) ω := by
    filter_upwards [hGae] with ω hω using locTime_lt_exitAbove hW0 hc hunb K n hω
  obtain ⟨hN, hQ⟩ := martingale_driftProc_quadProc_of_before (xL := LP.twoSeedXL) (xR := LP.twoSeedXR)
    hκ (sDrv_zero hW0 hunb n)
    (fun i ω => geomL_twoSeed_zero' (hWc ω) (sDrv_zero hW0 hunb n ω) i)
    (fun i ω => geomR_twoSeed_zero' (hWc ω) (sDrv_zero hW0 hunb n ω) i) hWc
    (fun i ω => (isForcePath_geomL hWc LP.twoSeedXL ω i).1)
    (fun i ω => (isForcePath_geomR hWc LP.twoSeedXR ω i).1) hWa' hVLa hVRa
    (fun ω t i => geomL_le (hWc ω) LP.twoSeedXL i t) (fun ω t i => le_geomR (hWc ω) LP.twoSeedXR i t)
    hmart K n hτθ
  have hτ : IsStoppingTime 𝓖 (sTau W T G K n) :=
    isStoppingTime_locTime hWc (continuous_sV hW0 hc hunb n) hWa' hVa K n
  exact ⟨martingale_stoppedProcess_martProc (locTime_le K n) hN,
    martingale_stoppedProcess_martProc_sq_sub hτ (locTime_le K n)
      (fun ω t ht => abs_le_of_le_sTau hW0 hc hunb ht) hWc hWa' hVa hpath hN hQ⟩

/-- **The second moment of the stopped martingale part**: `E[(M⁽ⁿ⁾_{τ ∧ K})²] ≤ κ K`, uniformly in `n`. -/
theorem integral_sq_stoppedProcess_sMart_le (K n : ℕ) :
    ∫ ω, stoppedProcess (sMart rL rR W T G n) (sTau W T G K n) K ω ^ 2 ∂P ≤ κ * K := by
  obtain ⟨-, hM2⟩ := martingale_sMart hκ hm hW0 hc hWa hG hGP hunb K n
  set X := stoppedProcess (fun t ω => sMart rL rR W T G n t ω ^ 2 - κ * t) (sTau W T G K n) with hX
  have h0 : ∀ ω, X 0 ω = 0 := fun ω => by
    rw [hX, stoppedProcess_eq_of_le (by simp)]
    simp only [sMart, martProc, martValue, sub_self, mul_zero, Finset.sum_const_zero, NNReal.coe_zero]
    ring
  have hint : ∫ ω, X K ω ∂P = 0 := by
    have := hM2.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ K) MeasurableSet.univ
    simp only [Measure.restrict_univ] at this
    rw [← this]
    simp only [h0, integral_zero]
  have hle : ∀ ω, stoppedProcess (sMart rL rR W T G n) (sTau W T G K n) K ω ^ 2 ≤ X K ω + κ * K := by
    intro ω
    have hr : (((min ((K : ℝ≥0) : WithTop ℝ≥0) (sTau W T G K n ω)).untopA : ℝ≥0) : ℝ) ≤ K := by
      have h := untopA_le_of_le (τ := fun ω => min ((K : ℝ≥0) : WithTop ℝ≥0) (sTau W T G K n ω))
        (T := (K : ℝ≥0)) (fun ω => min_le_left _ _) ω
      exact_mod_cast h
    simp only [hX, stoppedProcess]
    nlinarith
  calc ∫ ω, stoppedProcess (sMart rL rR W T G n) (sTau W T G K n) K ω ^ 2 ∂P
      ≤ ∫ ω, (X K ω + κ * K) ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
          ((hM2.integrable K).add (integrable_const _)) (Eventually.of_forall hle)
    _ = κ * K := by
        rw [integral_add (hM2.integrable K) (integrable_const _), hint, integral_const]
        simp

end Mart

/-! ### Doob's inequality, the pathwise driver bound, and exhaustion -/

section Doob

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous]
  {κ rL rR : ℝ} {T : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {G : Set Ω}

/-- **Doob's maximal inequality for the stopped martingale part**:
`P(sup_{t ≤ K} |M⁽ⁿ⁾_{t ∧ τ}| ≥ c) ≤ (1 + κ K)/(2 c)`, uniformly in `n`. -/
theorem measureReal_le_sMart (hκ : 0 < κ)
    (hm : HasMartingaleMeansBefore κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓖 W T)
    (hW0 : ∀ ω, W 0 ω = 0) (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω})
    (hWa : AdaptedBefore 𝓖 T W) (hG : MeasurableSet[𝓖 0] G) (hGP : P Gᶜ = 0)
    (hunb : ∀ ω, ω ∈ G → T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|)
    (K n : ℕ) {c : ℝ} (hcpos : 0 < c) :
    P.real {ω | c ≤ ⨆ i : Set.Iic (K : ℝ≥0),
      ‖stoppedProcess (sMart rL rR W T G n) (sTau W T G K n) i ω‖} ≤ (1 + κ * K) / (2 * c) := by
  obtain ⟨hM, -⟩ := martingale_sMart hκ hm hW0 hc hWa hG hGP hunb K n
  set X := stoppedProcess (sMart rL rR W T G n) (sTau W T G K n) with hX
  have hXc : ∀ ω, Continuous fun t => X t ω := fun ω =>
    continuous_stoppedProcess (fun ω => continuous_martProc (continuous_sDrv hW0 hc hunb n)
      (continuous_sV hW0 hc hunb n) ω) (locTime_le K n) ω
  have hdoob := ProbabilityTheory.maximal_ineq_norm hM c (K : ℝ≥0) fun ω => (hXc ω).isRightContinuous
  set A := {ω | c ≤ ⨆ i : Set.Iic (K : ℝ≥0), ‖X i ω‖} with hA
  set C : ℝ := n + (|rL| + |rR|) / 2 * n with hC
  have hb : ∀ ω, |X K ω| ≤ C := fun ω => abs_stoppedProcess_sMart_le hW0 hc hunb K n K ω
  have hXm : AEStronglyMeasurable (X K) P := ((hM.1 K).mono (𝓖.le K)).aestronglyMeasurable
  have hX2 : Integrable (fun ω => X K ω ^ 2) P := by
    refine Integrable.of_bound (hXm.pow 2) (C ^ 2) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb ω) 2
  have hsq : Integrable (fun ω => (1 + X K ω ^ 2) / 2) P :=
    ((integrable_const 1).add hX2).div_const 2
  have h1 : ∫ ω in A, ‖X K ω‖ ∂P ≤ ∫ ω, ‖X K ω‖ ∂P :=
    setIntegral_le_integral (hM.integrable K).norm (Eventually.of_forall fun ω => norm_nonneg _)
  have h2 : ∫ ω, ‖X K ω‖ ∂P ≤ ∫ ω, (1 + X K ω ^ 2) / 2 ∂P := by
    refine integral_mono (hM.integrable K).norm hsq fun ω => ?_
    simp only [Real.norm_eq_abs]
    nlinarith [sq_abs (X K ω), abs_nonneg (X K ω), sq_nonneg (|X K ω| - 1)]
  have h3 : ∫ ω, (1 + X K ω ^ 2) / 2 ∂P = (1 + ∫ ω, X K ω ^ 2 ∂P) / 2 := by
    rw [integral_div, integral_add (integrable_const 1) hX2, integral_const]
    simp
  have h4 := integral_sq_stoppedProcess_sMart_le hκ hm hW0 hc hWa hG hGP hunb K n
  rw [smul_eq_mul] at hdoob
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **The pathwise bound**: if the stopped martingale part stays below `c` on `[0, K]`, then up to the localizing
time `|W| ≤ twoSeedBound ρᴸ ρᴿ K c` (`abs_le_twoSeedBound`). -/
theorem abs_le_of_not_le_iSup (hL : -2 < rL) (hR : -2 < rR) (hW0 : ∀ ω, W 0 ω = 0)
    (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω})
    (hunb : ∀ ω, ω ∈ G → T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|)
    (K n : ℕ) {c : ℝ} {ω : Ω} (hω : ω ∈ G)
    (hlt : ¬ c ≤ ⨆ i : Set.Iic (K : ℝ≥0), ‖stoppedProcess (sMart rL rR W T G n) (sTau W T G K n) i ω‖)
    {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) ≤ sTau W T G K n ω) : |W t ω| ≤ twoSeedBound rL rR K c := by
  set X := stoppedProcess (sMart rL rR W T G n) (sTau W T G K n) with hX
  set τ := sTau W T G K n with hτ
  have hτK : τ ω ≤ ((K : ℝ≥0) : WithTop ℝ≥0) := locTime_le K n ω
  have hbdd : BddAbove (range fun i : Set.Iic (K : ℝ≥0) => ‖X i ω‖) :=
    ⟨n + (|rL| + |rR|) / 2 * n, by
      rintro _ ⟨i, rfl⟩
      exact abs_stoppedProcess_sMart_le hW0 hc hunb K n i ω⟩
  rw [not_le] at hlt
  -- the martingale part is below `c` up to `τ`
  have hMle : ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ τ ω → |sMart rL rR W T G n s ω| ≤ c := by
    intro s hs
    have hsK : s ≤ (K : ℝ≥0) := WithTop.coe_le_coe.1 (hs.trans hτK)
    have h := le_ciSup hbdd ⟨s, hsK⟩
    rw [hX, stoppedProcess_eq_of_le hs] at h
    exact h.trans hlt.le
  -- the path
  set w : ℝ → ℝ := fun r => sDrv W T G n r.toNNReal ω with hw
  have hwc : Continuous w := (continuous_sDrv hW0 hc hunb n ω).comp continuous_real_toNNReal
  have hw0 : w 0 = 0 := by simp only [hw, Real.toNNReal_zero, sDrv_zero hW0 hunb n ω]
  have hτne : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hτK
  set S : ℝ := ((τ ω).untopA : ℝ) with hS
  have hSK : S ≤ K := by
    have := untopA_le_of_le (τ := τ) (T := (K : ℝ≥0)) (fun ω => locTime_le K n ω) ω
    exact_mod_cast this
  have hpath : ∀ r ∈ Icc (0 : ℝ) S,
      |w r - rL / 2 * rightImg (fun s => -w s) 0 r + rR / 2 * rightImg w 0 r| ≤ c := by
    intro r hr
    have hrτ : ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω := by
      rw [← coe_untopA_of_ne_top hτne]
      exact WithTop.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)
    have h := hMle _ hrτ
    rw [sMart_eq hW0 hc hunb] at h
    have hr0 : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr.1
    have hL' : sV W T G n (Sum.inl 0) r.toNNReal ω = -rightImg (fun s => -w s) 0 r := by
      simp only [sV, jointV, Sum.elim_inl, geomL, LP.twoSeedXL, neg_zero, hr0]
      rfl
    have hR' : sV W T G n (Sum.inr 0) r.toNNReal ω = rightImg w 0 r := by
      simp only [sV, jointV, Sum.elim_inr, geomR, LP.twoSeedXR, hr0]
      rfl
    rw [hL', hR'] at h
    have hwr : w r = sDrv W T G n r.toNNReal ω := rfl
    rw [hwr]
    convert h using 2
    ring
  have htS : (t : ℝ) ∈ Icc (0 : ℝ) S := by
    refine ⟨t.coe_nonneg, ?_⟩
    have : t ≤ (τ ω).untopA := by
      rw [← coe_untopA_of_ne_top hτne] at ht
      exact WithTop.coe_le_coe.1 ht
    exact_mod_cast this
  have hbound := abs_le_twoSeedBound hwc hw0 hL hR hSK hpath htS
  have hagree : sDrv W T G n t ω = W t ω :=
    stopDrv_eq_of_le (hW0 ω) (hunb ω) (ht.trans (locTime_lt_exitAbove hW0 hc hunb K n hω).le)
  simp only [hw, Real.toNNReal_coe, hagree] at hbound
  exact hbound

/-- **The localizing times exhaust `[0, T)`** (on `G`, below `K`): for `t < T` and `t < K`, eventually in `n`,
`t ≤ τ_{K,n}`. Up to `t` the stopped drivers agree with `W`, which is bounded on `[0, t]`, and their seed images
are bounded by `max |W| + 1 + 2√t`, so the localizing quantity stays below `n` for `n` large. -/
theorem eventually_le_sTau (hW0 : ∀ ω, W 0 ω = 0)
    (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω})
    (hunb : ∀ ω, ω ∈ G → T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|)
    {K : ℕ} {ω : Ω} (hω : ω ∈ G) {t : ℝ≥0} (htT : (t : ℝ≥0∞) < T ω) (htK : t ≤ K) :
    ∀ᶠ n : ℕ in atTop, (t : WithTop ℝ≥0) ≤ sTau W T G K n ω := by
  obtain ⟨C₁, hC₁⟩ := exists_lt_exitAbove hω (hc ω) htT
  have hsub : Icc (0 : ℝ≥0) t ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) < T ω} := fun s hs =>
    lt_of_le_of_lt (by exact_mod_cast hs.2) htT
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn ((hc ω).mono hsub)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, zero_le⟩)
  set A : ℝ := B + 2 * (B + capConst t) with hA
  filter_upwards [eventually_gt_atTop ⌈max C₁ A⌉₊] with n hn
  have hn' : max C₁ A < n := by
    have := Nat.lt_of_ceil_lt hn
    exact_mod_cast this
  have hnC : C₁ < (n : ℝ) + 1 := by linarith [le_max_left C₁ A]
  have hnA : A < n := lt_of_le_of_lt (le_max_right _ _) hn'
  have hte : (t : WithTop ℝ≥0) < exitAbove W T G ((n : ℝ) + 1) ω := hC₁ _ hnC
  have hagree : ∀ s ≤ t, sDrv W T G n s ω = W s ω := fun s hs =>
    stopDrv_eq_of_le (hW0 ω) (hunb ω) ((WithTop.coe_le_coe.2 hs).trans hte.le)
  -- the localizing quantity is below `A` on `[0, t]`
  set w : ℝ → ℝ := fun r => sDrv W T G n r.toNNReal ω with hw
  have hwc : Continuous w := (continuous_sDrv hW0 hc hunb n ω).comp continuous_real_toNNReal
  have hw0 : w 0 = 0 := by simp only [hw, Real.toNNReal_zero, sDrv_zero hW0 hunb n ω]
  have hwB : ∀ r ∈ Icc (0 : ℝ) t, |w r| ≤ B := fun r hr => by
    have hrt : r.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hr.2
    simp only [hw, hagree _ hrt]
    have := hB r.toNNReal ⟨zero_le, hrt⟩
    rwa [Real.norm_eq_abs] at this
  have habs : ∀ s ∈ Icc (0 : ℝ≥0) t, absSum (sDrv W T G n) (sV W T G n) s ω ≤ A := by
    intro s hs
    have hs' : (s : ℝ) ∈ Icc (0 : ℝ) t := ⟨s.coe_nonneg, by exact_mod_cast hs.2⟩
    have hR := rightImg_mem_of_le (w := w) hwc hw0 hs' le_rfl hB0
      fun u hu => (le_abs_self _).trans (hwB u hu)
    have hL := rightImg_mem_of_le (w := fun r => -w r) hwc.neg (by simp [hw0]) hs' le_rfl hB0
      fun u hu => (neg_le_abs _).trans (hwB u hu)
    have hVR : |sV W T G n (Sum.inr 0) s ω| ≤ B + capConst t := by
      have : sV W T G n (Sum.inr 0) s ω = rightImg w 0 s := by
        simp only [sV, jointV, Sum.elim_inr, geomR, LP.twoSeedXR]; rfl
      rw [this, abs_of_nonneg hR.1]
      exact hR.2.2
    have hVL : |sV W T G n (Sum.inl 0) s ω| ≤ B + capConst t := by
      have : sV W T G n (Sum.inl 0) s ω = -rightImg (fun r => -w r) 0 s := by
        simp only [sV, jointV, Sum.elim_inl, geomL, LP.twoSeedXL, neg_zero]; rfl
      rw [this, abs_neg, abs_of_nonneg hL.1]
      exact hL.2.2
    have hW : |sDrv W T G n s ω| ≤ B := by
      have := hwB s hs'
      simp only [hw, Real.toNNReal_coe] at this
      exact this
    simp only [absSum, Fintype.sum_sum_type, Fin.sum_univ_one]
    linarith
  -- hence the exit time of the localizing quantity is after `t`
  have hexit : (t : WithTop ℝ≥0) < MathFin.exitTime (absSum (sDrv W T G n) (sV W T G n)) n ω := by
    by_contra hle
    rw [not_lt, MathFin.exitTime_le_iff (continuous_absSum (continuous_sDrv hW0 hc hunb n)
      (continuous_sV hW0 hc hunb n))] at hle
    obtain ⟨s, hs, hns⟩ := hle
    have h0 : 0 ≤ absSum (sDrv W T G n) (sV W T G n) s ω := by
      simp only [absSum]
      positivity
    rw [abs_of_nonneg h0] at hns
    linarith [habs s hs]
  exact le_min (WithTop.coe_le_coe.2 htK) hexit.le

end Doob

end InteractingSLE.Sec7.Lemma71B
