/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LP4Swallow
import InteractingSLE.Spec.Supplement.LP2
import InteractingSLE.Spec.Supplement.LP4ZeroOne
import InteractingSLE.Spec.Supplement.Lemma716
import InteractingSLE.Spec.Supplement.GB7aCmpPath

/-!
# Lemma G8's finite swallow: every positive point is swallowed, for every `κ > 0`

Packet PROVE-RLC-J, item (b) of `planning/handoffs/PROVE-RLC-G.md` ("What remains"). Source: supplement §7.7, proof of
Lemma G8 (`source/spec/p481-528.md` L466–L470, pp. 499–500): "The right gap of `α` has accessible Jacobi endpoint
because `r < c`. At a finite positive-separation right collision, the geometric seed-force coordinate identity and
simplicity give a new positive real trace contact […] Thus the probability of a positive real contact is positive.
Exact scaling implies a positive probability of reaching `(x, ∞)` for every fixed `x > 0`. Let `τ_x` be the first
swallowing of `x`. On the finite branch its landing point is a real `q ≥ x` […] Lemma 7.16 excludes `q = x`, so
`q > x`."

The existing route (Proposition LP4's right swallow, `LP.LP4S.lp4RightSwallowStatement`) is stated for `κ > 4`
because its single input, Lemma LP2 (`LP.LP2.lp2`), is: LP2's Lyapunov exponent needs `4 < κ`. Everything else in that
route (the ratio restart, the windows, the bounded-energy deletion of the separated left drift) holds for every
`κ > 0`. This file:

1. **Lemma LP2 for every `κ > 0`** (`lp2_of_pos`): a new Lyapunov observable for LP2's probabilistic machinery
   (`LP.LP2.measure_alive_le`, valid for `κ > 0`). With `X = g_t(x) − W_t`, `D = g_t(x) − V_t`, `R = X − D`, take
   `F = D^λ + θ X^{λ−2} (X − D)²` (LP2's `lyap` with `a = 0`, `e = λ`). Since `dD = (2/X − 2/R) dt`, the first term
   has drift `−2λ D^λ/(XR) ≤ −2λ X^{λ−2} u^λ` (`u = D/X`), for every `κ`; the second has LP2's drift
   `θ X^{λ−2} P(R/X)`, `P(1) = λ (ρ − c + κλ/2) < 0` for `0 < λ < 2(c − ρ)/κ`, `c = κ/2 − 2`
   (`drift_eq_zeroExp`, `exists_lyapParams_zeroExp`).
2. **The right swallow for every `κ > 0`** (`exists_swallowed_twoSeed`): LP4S's steps 1–4 with `lp2_of_pos`.
3. **Every fixed point is swallowed** (`ae_swallowed_twoSeed`): exact scaling of the two-seed path law
   (`LP.ZeroOne.map_dilPath_map_killedPath`) makes `P(x swallowed)` independent of `x` (`measure_swalSet_eq`), hence
   positive; continuity from above gives positive probability to "every positive integer is swallowed", a dilation
   invariant event, which the dilation zero–one law (Aux. lemma 128, `LP.ZeroOne.aux128DriverStatement`) makes almost
   sure.
4. **The landing point** (`ae_swallow_landing`, `0 < κ < 4`): at the swallowing time `σ` of `x` (`RealSwallowAt`) the
   force gap `V^R − W` vanishes (it lies below the passive gap, which tends to `0`), so the tip is a real point
   `q ≥ x` (`IsLoewnerTraceLT.exists_tip_real_of_collision_right`), and `q ≠ x` by Lemma 7.16 (`Lemma716.ae_trace_ne`).

Hypotheses: two-seed word (marks at `0⁻`, `0⁺`), `r_L > −2`, `−2 < r_R < κ/2 − 2` (for G8's reference path `α`:
`r_L = 1 + d`, `r_R = r`). No Theorem 1.2/1.3 input is used (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.RLCJ

open QuantumZipper Sec7.Dilation LP

/-! ### Lemma LP2 for every `κ > 0`: the Lyapunov parameters -/

section Lyapunov

open LP.LP2

variable {κ ρ e θ : ℝ}

/-- **The drift of `F = D^e + θ X^{e−2} (X − D)²`** (LP2's `lyap` with `a = 0`) along `v = (2/X, 2/R)`: the first term
contributes `−2e D^e/(X R)` for every `κ`; the second is LP2's `θ X^{e−2} P(R/X)`. -/
theorem drift_eq_zeroExp {X D : ℝ} (hX : 0 < X) (hD : 0 < D) (hR : 0 < X - D) :
    lyapX 0 e θ X D * (2 / X + ρ / 2 * (2 / (X - D))) + lyapD 0 e θ X D * (2 / X - 2 / (X - D)) +
        κ / 2 * lyapXX 0 e θ X D =
      -(2 * e) * D ^ e / (X * (X - D)) +
        θ * X ^ (0 + e - 2) *
          ((2 * (0 + e - 2) + κ * (0 + e - 2) * (0 + e - 2 - 1) / 2) * ((X - D) / X) ^ 2 +
            (0 + e - 2) * (ρ + 2 * κ) * ((X - D) / X) + (2 * ρ + 4 + κ)) := by
  have hX0 := hX.ne'
  have hD0 := hD.ne'
  have hR0 := hR.ne'
  simp only [lyapX, lyapD, lyapXX, Real.rpow_sub_one hX0, Real.rpow_sub_one hD0, Real.rpow_zero, zero_mul,
    zero_add, one_mul]
  generalize D ^ e = De
  generalize X ^ (e - 2) = Xp
  field_simp
  ring

/-- **The Lyapunov parameters for every `κ > 0`** (`ρ < κ/2 − 2`): with `a = 0` and `0 < e < 1`, the observable
`obs κ ρ 0 e θ` satisfies the drift, lower and nonnegativity bounds of `LP.LP2.measure_alive_le`. -/
theorem exists_lyapParams_zeroExp (hκ : 0 < κ) (hρc : ρ < κ / 2 - 2) :
    ∃ e θ γ m : ℝ, 0 < e ∧ e < 1 ∧ 0 < θ ∧ 0 < γ ∧ 0 < m ∧
      (∀ p ∈ region κ ρ, 0 < gapX κ ρ p - gapD p →
        Ito.itoGen (obs κ ρ 0 e θ) p (2 / gapX κ ρ p, 2 / (gapX κ ρ p - gapD p)) ≤
          -γ * gapX κ ρ p ^ (0 + e - 2)) ∧
      (∀ p ∈ region κ ρ, gapD p ≤ gapX κ ρ p → m * gapX κ ρ p ^ (0 + e) ≤ obs κ ρ 0 e θ p) ∧
      (∀ p ∈ region κ ρ, 0 ≤ obs κ ρ 0 e θ p) := by
  -- the exponent `0 < e < min 1 (2 (c − ρ)/κ)`
  have hcρ : 0 < κ / 2 - 2 - ρ := by linarith
  set e := min (1 / 2) ((κ / 2 - 2 - ρ) / κ) with he
  have he0 : 0 < e := lt_min (by norm_num) (by positivity)
  have he1 : e < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have he2 : e ≤ (κ / 2 - 2 - ρ) / κ := min_le_right _ _
  have hκe : κ * e ≤ κ / 2 - 2 - ρ := by rw [mul_comm]; exact (le_div_iff₀ hκ).1 he2
  have hABC : (2 * (0 + e - 2) + κ * (0 + e - 2) * (0 + e - 2 - 1) / 2) + (0 + e - 2) * (ρ + 2 * κ) +
      (2 * ρ + 4 + κ) < 0 := by
    have h : (2 * (0 + e - 2) + κ * (0 + e - 2) * (0 + e - 2 - 1) / 2) + (0 + e - 2) * (ρ + 2 * κ) +
        (2 * ρ + 4 + κ) = e * (ρ - (κ / 2 - 2) + κ * e / 2) := by ring
    rw [h]
    exact mul_neg_of_pos_of_neg he0 (by nlinarith)
  obtain ⟨θ, γ, m, hθ, hγ, hm, hbd⟩ := exists_drift_consts (e := e) (show 0 < 2 * e by positivity) hABC
  refine ⟨e, θ, γ, m, he0, he1, hθ, hγ, hm, fun p hp hR => ?_, fun p hp hDX => ?_, fun p hp => ?_⟩
  · have hX : 0 < gapX κ ρ p := hp.1
    have hD : 0 < gapD p := hp.2
    rw [itoGen_obs hκ.le hp]
    dsimp only
    rw [drift_eq_zeroExp hX hD hR]
    have hu : 0 < gapD p / gapX κ ρ p := div_pos hD hX
    have hu1 : gapD p / gapX κ ρ p ≤ 1 := (div_le_one hX).2 (by linarith)
    have hRX : (gapX κ ρ p - gapD p) / gapX κ ρ p = 1 - gapD p / gapX κ ρ p := by
      field_simp
    rw [hRX]
    have h1 := (hbd _ hu hu1).1
    have hXp : 0 < gapX κ ρ p ^ (0 + e - 2) := Real.rpow_pos_of_pos hX _
    have h2 := mul_le_mul_of_nonneg_left h1 hXp.le
    -- the first term: `D^e/(X R) ≥ D^e/X² = X^{e−2} u^e`
    have hDe : 0 < gapD p ^ e := Real.rpow_pos_of_pos hD _
    have hfirst : gapX κ ρ p ^ (0 + e - 2) * (gapD p / gapX κ ρ p) ^ e ≤
        gapD p ^ e / (gapX κ ρ p * (gapX κ ρ p - gapD p)) := by
      have heq := rpow_mul_rpow_div_sq (a := 0) (e := e) hX hD
      rw [Real.rpow_zero, one_mul] at heq
      rw [← heq]
      apply div_le_div_of_nonneg_left hDe.le (mul_pos hX hR)
      nlinarith
    have h3 : -(2 * e) * gapD p ^ e / (gapX κ ρ p * (gapX κ ρ p - gapD p)) ≤
        -(2 * e) * (gapX κ ρ p ^ (0 + e - 2) * (gapD p / gapX κ ρ p) ^ e) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonpos_left hfirst (by linarith)
    nlinarith
  · have hX : 0 < gapX κ ρ p := hp.1
    have hD : 0 < gapD p := hp.2
    have hu : 0 < gapD p / gapX κ ρ p := div_pos hD hX
    have hu1 : gapD p / gapX κ ρ p ≤ 1 := (div_le_one hX).2 hDX
    have h1 := (hbd _ hu hu1).2
    rw [obs, lyap_eq hX hD, rpow_sub_two_mul_sq hX, mul_comm m]
    exact mul_le_mul_of_nonneg_left h1 (Real.rpow_pos_of_pos hX _).le
  · have hX : 0 < gapX κ ρ p := hp.1
    have hD : 0 < gapD p := hp.2
    rw [obs, lyap]
    have h1 : 0 ≤ gapX κ ρ p ^ (0 : ℝ) := (Real.rpow_pos_of_pos hX _).le
    have h2 : 0 ≤ gapD p ^ e := (Real.rpow_pos_of_pos hD _).le
    have h3 : 0 ≤ gapX κ ρ p ^ (0 + e - 2) := (Real.rpow_pos_of_pos hX _).le
    positivity


/-- **Lemma LP2 for every `κ > 0`** (finite swallowing of a passive point by the single-right-seed evolution,
`−2 < ρ < κ/2 − 2`): `LP.LP2.lp2`'s proof with the parameters `exists_lyapParams_zeroExp`. -/
theorem lp2_of_pos {κ ρ : ℝ} (hκ0 : 0 < κ) (hρ : -2 < ρ) (hρc : ρ < κ / 2 - 2) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {xL ρL : Fin 0 → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 1 → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL (fun _ => 0) ρL (fun _ => ρ) P 𝓕 W VL VR B ζ) {x : ℝ}
    (hx : 0 < x) :
    ∀ᵐ ω ∂P, ∃ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω ∧ ¬ LP.LP3.Alive (fun t => W t.toNNReal ω) x T := by
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  obtain ⟨G, hG, hGc, hgood⟩ := exists_measurableSet_subset_of_ae (ae_isGood hκ0 hρ hE)
  obtain ⟨e, θ, γ, m, hl0, hl1, -, hγ, hm, hdrift, hlow, hnn⟩ := exists_lyapParams_zeroExp hκ0 hρc
  set l := (0 : ℝ) + e with hldef
  have hl0' : 0 < l := by rw [hldef, zero_add]; exact hl0
  set A : Set Ω := {ω | ω ∈ G ∧ ∀ T : ℝ≥0, LP.LP3.Alive (fun t => W t.toNNReal ω) x T} with hAdef
  suffices hA : P A = 0 by
    have hGae : ∀ᵐ ω ∂P, ω ∈ G :=
      (measure_eq_zero_iff_ae_notMem.1 hGc).mono fun ω h => by simpa using h
    have hAae : ∀ᵐ ω ∂P, ω ∉ A := measure_eq_zero_iff_ae_notMem.1 hA
    filter_upwards [hGae, hAae] with ω hωG hωA
    have hnot : ¬ ∀ T : ℝ≥0, LP.LP3.Alive (fun t => W t.toNNReal ω) x T := fun h => hωA ⟨hωG, h⟩
    push Not at hnot
    obtain ⟨T, hT⟩ := hnot
    exact ⟨T, by rw [(hgood ω hωG).1]; exact ENNReal.coe_lt_top, hT⟩
  have hxl : 0 < x ^ l := Real.rpow_pos_of_pos hx l
  have hδ : ∀ δ : ℝ, 0 < δ → P A ≤ ENNReal.ofReal δ := by
    intro δ hδ
    set K := x ^ l * (1 + 2 / (m * δ)) with hK
    have hK0 : 0 < K := by positivity
    set M := K ^ (1 / l) with hMdef
    have hM0 : 0 < M := Real.rpow_pos_of_pos hK0 _
    have hMl : M ^ l = K := by
      rw [hMdef, ← Real.rpow_mul hK0.le, one_div_mul_cancel hl0'.ne', Real.rpow_one]
    have hxM : x < M := by
      have hlt : x ^ l < M ^ l := by
        rw [hMl, hK]
        have : 0 < 2 / (m * δ) := by positivity
        nlinarith
      exact (Real.rpow_lt_rpow_iff hx.le hM0.le hl0').1 hlt
    have hMp : 0 < γ * M ^ (l - 2) := mul_pos hγ (Real.rpow_pos_of_pos hM0 _)
    set T : ℝ≥0 := (2 * x ^ l / (γ * M ^ (l - 2) * δ)).toNNReal with hTdef
    have hT : (T : ℝ) = 2 * x ^ l / (γ * M ^ (l - 2) * δ) :=
      Real.coe_toNNReal _ (by positivity)
    have hTpos : 0 < (T : ℝ) := by rw [hT]; positivity
    have hb := measure_alive_le hκ0 hE hG hGc hgood hx hl0' (by linarith) hγ hm hdrift hlow hnn hxM hTpos
    have he1 : x ^ l / (γ * M ^ (l - 2)) / T = δ / 2 := by
      rw [hT]; field_simp
    have he2 : x ^ l / (m * M ^ l) ≤ δ / 2 := by
      have h : x ^ l / (m * M ^ l) = δ / (m * δ + 2) := by
        rw [hMl, hK]; field_simp
      rw [h]
      exact div_le_div_of_nonneg_left hδ.le (by norm_num) (by nlinarith)
    calc P A ≤ ENNReal.ofReal (x ^ l / (γ * M ^ (l - 2)) / T) +
          ENNReal.ofReal (x ^ l / (m * M ^ l)) := hb
      _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := by
          rw [he1]; exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal he2)
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  rw [zero_add]
  have := hδ ε hε
  rwa [ENNReal.ofReal_coe_nnreal] at this


end Lyapunov

/-! ### The right swallow for every `κ > 0` (LP4S's steps with `lp2_of_pos`) -/

section RightSwallow

open Sec2 Sec2.Assembly Sec7.RandRestart LP.LP4S

variable {κ : ℝ}

/-- **Step 1 for every `κ > 0`** (`LP.LP4S.codeLaw_allSet_zero_ne_zero` with `lp2_of_pos`): the word `SLE_κ(0; ρ)` from
`(−1, 1)` swallows a point beyond its right mark with positive canonical probability. -/
theorem codeLaw_allSet_zero_ne_zero_of_pos (hκ : 0 < κ) {ρ : ℝ} (hρ : -2 < ρ) (hρc : ρ < κ / 2 - 2) :
    codeLaw κ (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => ρ) allSet ((fun _ => -1), fun _ => 1) ≠ 0 := by
  have h0 : (-2 : ℝ) < (fun _ : Fin 1 => (0 : ℝ)) 0 := by norm_num
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ Zhan.isOrderedForceWord_zero (ρL := fun _ => (0 : ℝ))
      (ρR := fun _ => ρ)
  have hD := hE.compEmb (OrderEmbedding.ofIsEmpty : Fin 0 ↪o Fin 1)
    (RelEmbedding.refl (· ≤ ·) : Fin 1 ↪o Fin 1) (fun _ _ => rfl) (fun i hi => absurd ⟨i, rfl⟩ hi)
  have hLP2 : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < (q : ℝ) → ∃ T' : ℝ≥0, ¬ LP3.Alive (fun s : ℝ => W s.toNNReal ω) q T' := by
    rw [ae_all_iff]
    intro q
    by_cases hq : (0 : ℝ) < q
    · filter_upwards [lp2_of_pos hκ hρ hρc hD hq] with ω hω _
      obtain ⟨T', -, hT'⟩ := hω
      exact ⟨T', hT'⟩
    · exact ae_of_all _ fun ω h => absurd h hq
  obtain ⟨A, T, -, hA0, hlaw, hgood⟩ := exists_ratio_restart hκ h0 hρ hE one_pos measurableSet_allSet
    (fun _ _ _ => Iff.rfl) (fun s w w' τ h hw => swalAll_congr s w w' τ h hw)
    (K := codeLaw κ (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => ρ) allSet ((fun _ => -1), fun _ => 1))
    (fun L hL => codeLaw_allSet_ray hκ h0 hρ zero_le_one hL)
  have hsub : A ≤ᵐ[P] (A ∩ {ω | SwalAll (wordAt W VL VR T ω) (fun t => W (T ω + t) ω - W (T ω) ω)
      (ζ ω - T ω)} : Set Ω) := by
    filter_upwards [hLP2] with ω hω hωA
    obtain ⟨-, hζω, hp, -⟩ := hgood ω hωA
    refine ⟨hωA, ?_⟩
    show SwalAll (wordAt W VL VR T ω) (fun t => W (T ω + t) ω - W (T ω) ω) (ζ ω - T ω)
    rw [hζω, ENNReal.top_sub_coe]
    exact swalAll_of_forall_swallowed hp (T ω) hω
  intro hK
  rw [hK, zero_mul] at hlaw
  exact hA0 (le_antisymm ((measure_mono_ae hsub).trans hlaw.le) zero_le)

/-- **Step 2 for every `κ > 0`** (`LP.LP4S.exists_codeLaw_winSet_ne_zero`): for some `n`, the word `SLE_κ(0; ρ)` from
`(−1, r)`, `r = 1/(2(n + 1))`, swallows a point beyond its right mark by time `1/4` while the driver stays above
`−1/2`, with positive canonical probability. -/
theorem exists_codeLaw_winSet_ne_zero_of_pos (hκ : 0 < κ) {ρ : ℝ} (hρ : -2 < ρ) (hρc : ρ < κ / 2 - 2) :
    ∃ n : ℕ, codeLaw κ (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => ρ) (winSet (1 / 2) (1 / 4))
      ((fun _ => -1), fun _ => 1 / (2 * ((n : ℝ) + 1))) ≠ 0 := by
  have h0 : (-2 : ℝ) < (fun _ : Fin 1 => (0 : ℝ)) 0 := by norm_num
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE, hζ⟩ := exists_twoForce hκ (ρL := fun _ => (0 : ℝ)) h0
    (ρR := fun _ => ρ) hρ one_pos zero_le_one
  have hsep : ∀ i j, (fun _ : Fin 1 => (-1 : ℝ)) i < (fun _ : Fin 1 => (1 : ℝ)) j := fun _ _ => by norm_num
  have hall : P {ω | SwalAll ((fun _ : Fin 1 => (-1 : ℝ)), fun _ : Fin 1 => (1 : ℝ)) (fun t => W t ω) (ζ ω)} ≠ 0 := by
    rw [measure_allSet_eq_codeLaw hκ hsep hE]
    have h := codeLaw_allSet_zero_ne_zero_of_pos hκ hρ hρc
    simpa using h
  have hcover : {ω | SwalAll ((fun _ : Fin 1 => (-1 : ℝ)), fun _ : Fin 1 => (1 : ℝ)) (fun t => W t ω) (ζ ω)} ≤ᵐ[P]
      ⋃ n : ℕ, {ω | SwalWin ((n : ℝ) + 1) (((n : ℝ) + 1) ^ 2)
        ((fun _ : Fin 1 => (-1 : ℝ)), fun _ : Fin 1 => (1 : ℝ)) (fun t => W t ω) (ζ ω)} := by
    filter_upwards [hζ, hE.2.2.2.2] with ω hζω hp h
    rw [hζω] at hp
    obtain ⟨hwc, hw0⟩ := Sec7.IsIntegratedSLEPath.continuous_w_of_top hp
    have h' : SwalAll ((fun _ : Fin 1 => (-1 : ℝ)), fun _ : Fin 1 => (1 : ℝ)) (fun t => W t ω) ⊤ := by
      rw [← hζω]; exact h
    rw [swalAll_top_iff hwc hw0, rAll_iff_exists_rWin hwc] at h'
    obtain ⟨M, N, hMN⟩ := h'
    obtain ⟨n, hn⟩ := exists_nat_ge (max M N)
    refine mem_iUnion.2 ⟨n, ?_⟩
    show SwalWin ((n : ℝ) + 1) (((n : ℝ) + 1) ^ 2) ((fun _ : Fin 1 => (-1 : ℝ)), fun _ : Fin 1 => (1 : ℝ))
      (fun t => W t ω) (ζ ω)
    rw [hζω, swalWin_top_iff hwc hw0]
    refine hMN.mono (by linarith [le_max_left M N]) ?_
    have h1 : N ≤ (n : ℝ) + 1 := by linarith [le_max_right M N]
    nlinarith
  have hpos : ∃ n : ℕ, P {ω | SwalWin ((n : ℝ) + 1) (((n : ℝ) + 1) ^ 2)
      ((fun _ : Fin 1 => (-1 : ℝ)), fun _ : Fin 1 => (1 : ℝ)) (fun t => W t ω) (ζ ω)} ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hall (measure_mono_null_ae hcover (measure_iUnion_null hcon))
  obtain ⟨n, hn⟩ := hpos
  refine ⟨n, ?_⟩
  set m : ℝ := (n : ℝ) + 1 with hm
  have hm0 : 0 < m := by positivity
  have hL : 0 < 2 * m := by positivity
  have ha : 0 < 1 / (2 * m) := by positivity
  have hstart : (((fun _ => -1), fun _ => 1 / (2 * m)) : (Fin 1 → ℝ) × (Fin 1 → ℝ)) =
      ((fun _ => -(1 / (2 * m) * (2 * m))), fun _ => 1 / (2 * m) * 1) := by
    refine Prod.ext (funext fun _ => ?_) (funext fun _ => ?_)
    · show (-1 : ℝ) = -(1 / (2 * m) * (2 * m)); field_simp
    · show 1 / (2 * m) = 1 / (2 * m) * 1; ring
  rw [hstart, codeLaw_winSet_scale hκ h0 hρ hL zero_le_one ha]
  have hM : (1 / 2 : ℝ) / (1 / (2 * m)) = m := by field_simp
  have hN : (1 / 4 : ℝ) / (1 / (2 * m)) ^ 2 = m ^ 2 := by field_simp; ring
  rw [hM, hN, codeLaw_winSet_zero hκ hL zero_le_one ρ m (m ^ 2) (fun i => i.elim0) (fun i => i.elim0),
    ← codeLaw_winSet_zero hκ one_pos zero_le_one ρ m (m ^ 2) (fun i => i.elim0) (fun i => i.elim0),
    ← measure_winSet_eq_codeLaw hκ hsep hE]
  exact hn

/-- **The right swallow for every `κ > 0`** (LP4's right swallowing, `LP.LP4S.lp4RightSwallowStatement`, without
`κ > 4`): for every two-seed evolution with `r_L > −2` and `−2 < r_R < κ/2 − 2`, with positive probability some real
point `x > 0` is swallowed at a finite time. -/
theorem exists_swallowed_twoSeed (hκ : 0 < κ) {rL rR : ℝ} (hL : -2 < rL) (hR : -2 < rR) (hRc : rR < κ / 2 - 2)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) :
    ∃ᵐ ω ∂P, ∃ x : ℝ, 0 < x ∧ ∃ T : ℝ≥0, ZhanGT4.IsSwallowedBy (fun s : ℝ => W s.toNNReal ω) x T := by
  obtain ⟨n, hn⟩ := exists_codeLaw_winSet_ne_zero_of_pos hκ hR hRc
  set r : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hr
  have hr0 : 0 < r := by positivity
  have h0 : (-2 : ℝ) < (fun _ : Fin 1 => (0 : ℝ)) 0 := by norm_num
  have hL' : (-2 : ℝ) < (fun _ : Fin 1 => rL) 0 := hL
  have hR' : (-2 : ℝ) < (fun _ : Fin 1 => rR) 0 := hR
  have hK : codeLaw κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) allSet ((fun _ => -1), fun _ => r) ≠ 0 := by
    obtain ⟨Ω₁, m₁, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, hE₁, hζ₁⟩ :=
      exists_twoForce hκ (ρL := fun _ => (0 : ℝ)) h0 (ρR := fun _ => rR) hR one_pos hr0.le
    have hF : IsOrderedForceWord (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => r) :=
      ⟨antitone_const, fun _ => by norm_num, monotone_const, fun _ => hr0.le⟩
    refine codeLaw_allSet_ne_zero_of_compare hκ hF (show (-1 : ℝ) < r by linarith) hR' (M := 1 / 2)
      (N := 1 / 4) (δ := 1 / 4) (by norm_num) (by norm_num) (by norm_num) hE₁ hζ₁ ?_
    rw [measure_winSet_eq_codeLaw hκ (fun _ _ => show (-1 : ℝ) < r by linarith) hE₁]
    exact hn
  obtain ⟨A, T, -, hA0, hlaw, hgood⟩ := exists_ratio_restart hκ hL' hR' hE hr0 measurableSet_allSet
    (fun _ _ _ => Iff.rfl) (fun s w w' τ h hw => swalAll_congr s w w' τ h hw)
    (K := codeLaw κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) allSet ((fun _ => -1), fun _ => r))
    (fun L hL => codeLaw_allSet_ray hκ hL' hR' hr0.le hL)
  rw [frequently_ae_iff]
  have hsub : A ∩ {ω | SwalAll (wordAt W VL VR T ω) (fun t => W (T ω + t) ω - W (T ω) ω) (ζ ω - T ω)} ⊆
      {ω | ∃ x : ℝ, 0 < x ∧ ∃ T : ℝ≥0, ZhanGT4.IsSwallowedBy (fun s : ℝ => W s.toNNReal ω) x T} := by
    rintro ω ⟨hωA, hω⟩
    obtain ⟨-, hζω, hp, -⟩ := hgood ω hωA
    have hω' : SwalAll (wordAt W VL VR T ω) (fun t => W (T ω + t) ω - W (T ω) ω) ⊤ := by
      rw [← ENNReal.top_sub_coe (r := T ω), ← hζω]; exact hω
    exact exists_swallowed_of_swalAll hp (T ω) hω'
  intro h0'
  have := measure_mono_null hsub h0'
  rw [hlaw] at this
  exact mul_ne_zero hK hA0 this

end RightSwallow

/-! ### Every fixed positive point is swallowed: scaling and the zero–one law -/

/-- The paths under which the point `x > 0` is swallowed by an integer time. -/
def swalSet (x : ℝ) (hx : 0 < x) : Set (ℝ≥0 → ℝ) := ⋃ n : ℕ, (LP3.aliveSet 1 x hx (n : ℝ≥0))ᶜ

theorem measurableSet_swalSet (x : ℝ) (hx : 0 < x) : MeasurableSet (swalSet x hx) :=
  MeasurableSet.iUnion fun _ => (LP3.measurableSet_aliveSet _ _ _ _).compl

theorem mem_swalSet_iff {x : ℝ} {hx : 0 < x} {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) :
    w ∈ swalSet x hx ↔ ∃ T : ℝ≥0, ZhanGT4.IsSwallowedBy (fun s : ℝ => w s.toNNReal) x T := by
  constructor
  · intro h
    simp only [swalSet, mem_iUnion, mem_compl_iff] at h
    obtain ⟨n, hn⟩ := h
    rw [LP3.mem_aliveSet_iff hw hw0, LP4HB.pathDrive_one] at hn
    exact ⟨n, hn⟩
  · rintro ⟨T, hT⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (T : ℝ)
    simp only [swalSet, mem_iUnion, mem_compl_iff]
    refine ⟨n, ?_⟩
    rw [LP3.mem_aliveSet_iff hw hw0, LP4HB.pathDrive_one]
    exact LP4HB.isSwallowedBy_mono T.coe_nonneg (by exact_mod_cast hn) hT

/-- **Swallowing is monotone in the point**: if `y` is swallowed by `T`, so is every `x ∈ (0, y]`. -/
theorem isSwallowedBy_of_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {x y T : ℝ} (hT : 0 ≤ T)
    (hx : 0 < x) (hxy : x ≤ y) (h : ZhanGT4.IsSwallowedBy W y T) : ZhanGT4.IsSwallowedBy W x T := by
  rintro ⟨u, hu⟩
  rcases hxy.lt_or_eq with hlt | heq
  · exact h (QuantumZipper.RS.exists_isForwardSol_of_lt hW hT (by rw [hW0]; exact hx) hlt hu)
  · exact h ⟨u, heq ▸ hu⟩

/-- Scaling: `dilPath c w` swallows `x` iff `w` swallows `√c x`. -/
theorem dilPath_mem_swalSet_iff {c : ℝ≥0} (hc : c ≠ 0) {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    {x : ℝ} (hx : 0 < x) (hx' : 0 < √(c : ℝ) * x) :
    dilPath c w ∈ swalSet x hx ↔ w ∈ swalSet (√(c : ℝ) * x) hx' := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast pos_iff_ne_zero.2 hc
  have hsc : 0 < √(c : ℝ) := Real.sqrt_pos.2 hc0
  have hdc := continuous_dilPath (c := c) w hw
  have hd0 : dilPath c w 0 = 0 := dilPath_zero hw0
  rw [mem_swalSet_iff hdc hd0, mem_swalSet_iff hw hw0]
  constructor
  · rintro ⟨T, hT⟩
    have hci : c⁻¹ ≠ 0 := inv_ne_zero hc
    have h := LP4HB.isSwallowedBy_dilPath_of hci hT
    have hdd : ∀ s : ℝ≥0, dilPath c⁻¹ (dilPath c w) s = w s := fun s => by
      simp only [dilPath]
      have e1 : c * (c⁻¹ * s) = s := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
      rw [e1, NNReal.coe_inv, Real.sqrt_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ hsc.ne', one_mul]
    simp only [hdd] at h
    have hx1 : x / √((c⁻¹ : ℝ≥0) : ℝ) = √(c : ℝ) * x := by
      rw [NNReal.coe_inv, Real.sqrt_inv]; field_simp
    rw [hx1] at h
    refine ⟨(T / (c⁻¹ : ℝ≥0) : ℝ).toNNReal, ?_⟩
    rw [Real.coe_toNNReal _ (div_nonneg T.coe_nonneg (by positivity))]
    exact h
  · rintro ⟨T, hT⟩
    have h := LP4HB.isSwallowedBy_dilPath_of hc hT
    have hx1 : √(c : ℝ) * x / √(c : ℝ) = x := by field_simp
    rw [hx1] at h
    refine ⟨(T / c : ℝ).toNNReal, ?_⟩
    rw [Real.coe_toNNReal _ (div_nonneg T.coe_nonneg hc0.le)]
    exact h

theorem swalSet_congr {x x' : ℝ} (e : x = x') (hx : 0 < x) (hx' : 0 < x') : swalSet x hx = swalSet x' hx' := by
  subst e; rfl

section Law

variable {κ rL rR : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem killedPath_eq_of_top {ω : Ω} (hζ : ζ ω = ⊤) : ZeroOne.killedPath W ζ ω = fun t => W t ω := by
  funext t
  simp [ZeroOne.killedPath, Sec7.killedProc, hζ]

/-- **Exact scaling**: the probability that a fixed point `x > 0` is swallowed does not depend on `x`. -/
theorem measure_swalSet_eq (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR) [IsProbabilityMeasure P]
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    P (ZeroOne.killedPath W ζ ⁻¹' swalSet x hx) = P (ZeroOne.killedPath W ζ ⁻¹' swalSet y hy) := by
  set c : ℝ≥0 := ((y / x) ^ 2).toNNReal with hcdef
  have hc' : (c : ℝ) = (y / x) ^ 2 := Real.coe_toNNReal _ (by positivity)
  have hc : c ≠ 0 := by
    intro h0
    have : ((y / x) ^ 2 : ℝ) = 0 := by rw [← hc', h0]; rfl
    exact (pow_pos (div_pos hy hx) 2).ne' this
  have hsq : √(c : ℝ) * x = y := by
    rw [hc', Real.sqrt_sq (div_pos hy hx).le]; field_simp
  have hx' : 0 < √(c : ℝ) * x := by rw [hsq]; exact hy
  have hK := ZeroOne.measurable_killedPath hE.2.1
  have hlaw := ZeroOne.map_dilPath_map_killedPath hκ hL hR hE hc
  have hgood := ae_good hκ hL hR hE
  have hae : (ZeroOne.killedPath W ζ ⁻¹' (dilPath c ⁻¹' swalSet x hx) : Set Ω) =ᵐ[P]
      (ZeroOne.killedPath W ζ ⁻¹' swalSet (√(c : ℝ) * x) hx' : Set Ω) := by
    refine eventuallyEqSet_iff.2 ?_
    filter_upwards [hgood] with ω ⟨hζ, hw, hw0⟩
    simp only [mem_preimage, killedPath_eq_of_top hζ]
    exact dilPath_mem_swalSet_iff hc hw hw0 hx hx'
  calc P (ZeroOne.killedPath W ζ ⁻¹' swalSet x hx)
      = P.map (ZeroOne.killedPath W ζ) (swalSet x hx) :=
        (Measure.map_apply hK (measurableSet_swalSet x hx)).symm
    _ = (P.map (ZeroOne.killedPath W ζ)).map (dilPath c) (swalSet x hx) := by rw [hlaw]
    _ = P.map (ZeroOne.killedPath W ζ) (dilPath c ⁻¹' swalSet x hx) :=
        Measure.map_apply ZeroOne.measurable_dilPath (measurableSet_swalSet x hx)
    _ = P (ZeroOne.killedPath W ζ ⁻¹' (dilPath c ⁻¹' swalSet x hx)) :=
        Measure.map_apply hK (ZeroOne.measurable_dilPath (measurableSet_swalSet x hx))
    _ = P (ZeroOne.killedPath W ζ ⁻¹' swalSet (√(c : ℝ) * x) hx') := measure_congr hae
    _ = P (ZeroOne.killedPath W ζ ⁻¹' swalSet y hy) := by rw [swalSet_congr hsq hx' hy]

/-- The paths under which every positive integer point is swallowed. -/
def allSwalSet : Set (ℝ≥0 → ℝ) := ⋂ k : ℕ, swalSet ((k : ℝ) + 1) (by positivity)

theorem measurableSet_allSwalSet : MeasurableSet allSwalSet :=
  MeasurableSet.iInter fun _ => measurableSet_swalSet _ _

theorem mem_allSwalSet_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) :
    w ∈ allSwalSet ↔ ∀ x : ℝ, 0 < x → ∃ T : ℝ≥0, ZhanGT4.IsSwallowedBy (fun s : ℝ => w s.toNNReal) x T := by
  have hWc : Continuous fun s : ℝ => w s.toNNReal := hw.comp continuous_real_toNNReal
  have hW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simp [hw0]
  simp only [allSwalSet, mem_iInter]
  constructor
  · intro h x hx
    obtain ⟨k, hk⟩ := exists_nat_ge x
    obtain ⟨T, hT⟩ := (mem_swalSet_iff hw hw0).1 (h k)
    exact ⟨T, isSwallowedBy_of_le hWc hW0 T.coe_nonneg hx (by linarith) hT⟩
  · intro h k
    exact (mem_swalSet_iff hw hw0).2 (h _ (by positivity))

theorem dilPath_mem_allSwalSet_iff {c : ℝ≥0} (hc : c ≠ 0) {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) :
    dilPath c w ∈ allSwalSet ↔ w ∈ allSwalSet := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast pos_iff_ne_zero.2 hc
  have hsc : 0 < √(c : ℝ) := Real.sqrt_pos.2 hc0
  have hdc := continuous_dilPath (c := c) w hw
  have hd0 : dilPath c w 0 = 0 := dilPath_zero hw0
  rw [mem_allSwalSet_iff hdc hd0, mem_allSwalSet_iff hw hw0]
  constructor
  · intro h x hx
    have h1 := h (x / √(c : ℝ)) (div_pos hx hsc)
    have h2 := (mem_swalSet_iff hdc hd0 (hx := div_pos hx hsc)).2 h1
    rw [dilPath_mem_swalSet_iff hc hw hw0 (div_pos hx hsc) (by rw [mul_div_cancel₀ _ hsc.ne']; exact hx),
      swalSet_congr (mul_div_cancel₀ _ hsc.ne') _ hx] at h2
    exact (mem_swalSet_iff hw hw0).1 h2
  · intro h x hx
    have hx' : 0 < √(c : ℝ) * x := mul_pos hsc hx
    exact (mem_swalSet_iff hdc hd0 (hx := hx)).1
      ((dilPath_mem_swalSet_iff hc hw hw0 hx hx').2 ((mem_swalSet_iff hw hw0).2 (h _ hx')))

/-- **Every fixed positive point is swallowed** by the two-seed evolution with a hitting right weight, almost surely
(`κ > 0`, `r_L > −2`, `−2 < r_R < κ/2 − 2`): the right swallow of positive probability
(`exists_swallowed_twoSeed`), exact scaling (`measure_swalSet_eq`) and the dilation zero–one law (Aux. lemma 128). -/
theorem ae_swallowed_twoSeed (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR) (hRc : rR < κ / 2 - 2)
    [IsProbabilityMeasure P]
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ x : ℝ, 0 < x → ∃ T : ℝ≥0, ZhanGT4.IsSwallowedBy (fun s : ℝ => W s.toNNReal ω) x T := by
  have hgood := ae_good hκ hL hR hE
  set K := ZeroOne.killedPath W ζ with hKdef
  have hKm : Measurable K := ZeroOne.measurable_killedPath hE.2.1
  have hone : (0 : ℝ) < 1 := one_pos
  -- the probability `p` of swallowing `1` is positive
  have hp : P (K ⁻¹' swalSet 1 hone) ≠ 0 := by
    have hcover : {ω | ∃ x : ℝ, 0 < x ∧ ∃ T : ℝ≥0, ZhanGT4.IsSwallowedBy (fun s : ℝ => W s.toNNReal ω) x T}
        ≤ᵐ[P] ⋃ n : ℕ, K ⁻¹' swalSet (1 / ((n : ℝ) + 1)) (by positivity) := by
      filter_upwards [hgood] with ω ⟨hζ, hw, hw0⟩ ⟨x, hx, T, hT⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
      have hWc : Continuous fun s : ℝ => W s.toNNReal ω := hw.comp continuous_real_toNNReal
      have hW0 : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by simp [hw0]
      refine mem_iUnion.2 ⟨n, ?_⟩
      show K ω ∈ swalSet (1 / ((n : ℝ) + 1)) (by positivity)
      rw [hKdef, killedPath_eq_of_top hζ, mem_swalSet_iff hw hw0]
      exact ⟨T, isSwallowedBy_of_le hWc hW0 T.coe_nonneg (by positivity) hn.le hT⟩
    intro h0
    have hall : ∀ n : ℕ, P (K ⁻¹' swalSet (1 / ((n : ℝ) + 1)) (by positivity)) = 0 := fun n => by
      rw [measure_swalSet_eq hκ hL hR hE _ hone]; exact h0
    have := measure_mono_null_ae hcover (measure_iUnion_null hall)
    exact (exists_swallowed_twoSeed hκ hL hR hRc hE) (measure_eq_zero_iff_ae_notMem.1 this)
  -- the event "every positive integer is swallowed" has positive probability
  obtain ⟨G, hG, hGc, hGgood⟩ := LP.LP2.exists_measurableSet_subset_of_ae hgood
  set A : ℕ → Set Ω := fun k => G ∩ K ⁻¹' swalSet ((k : ℝ) + 1) (by positivity) with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k => hG.inter (hKm (measurableSet_swalSet _ _))
  have hAanti : Antitone A := by
    intro k l hkl ω ⟨hωG, hω⟩
    refine ⟨hωG, ?_⟩
    obtain ⟨hζ, hw, hw0⟩ := hGgood ω hωG
    have hWc : Continuous fun s : ℝ => W s.toNNReal ω := hw.comp continuous_real_toNNReal
    have hW0 : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by simp [hw0]
    simp only [mem_preimage, hKdef, killedPath_eq_of_top hζ] at hω ⊢
    obtain ⟨T, hT⟩ := (mem_swalSet_iff hw hw0).1 hω
    exact (mem_swalSet_iff hw hw0).2 ⟨T, isSwallowedBy_of_le hWc hW0 T.coe_nonneg (by positivity)
      (by have : (k : ℝ) ≤ l := by exact_mod_cast hkl
          linarith) hT⟩
  have hAk : ∀ k, P (A k) = P (K ⁻¹' swalSet 1 hone) := fun k => by
    show P (G ∩ K ⁻¹' swalSet ((k : ℝ) + 1) (by positivity)) = _
    rw [Set.inter_comm, measure_inter_conull hGc]
    exact measure_swalSet_eq hκ hL hR hE _ hone
  have hInter : P (⋂ k, A k) = P (K ⁻¹' swalSet 1 hone) := by
    have h := tendsto_measure_iInter_atTop (fun k => (hAm k).nullMeasurableSet) hAanti ⟨0, measure_ne_top P _⟩
    rw [show (⇑P ∘ A) = fun _ => P (K ⁻¹' swalSet 1 hone) from funext hAk] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hGpos : P {ω | (fun t => W t ω) ∈ allSwalSet} ≠ 0 := by
    intro h0
    refine hp (le_antisymm ?_ zero_le)
    rw [← hInter, ← h0]
    refine measure_mono fun ω hω => ?_
    have hω' := mem_iInter.1 hω
    obtain ⟨hζ, hw, hw0⟩ := hGgood ω (hω' 0).1
    show (fun t => W t ω) ∈ allSwalSet
    refine mem_iInter.2 fun k => ?_
    have := (hω' k).2
    simpa only [mem_preimage, hKdef, killedPath_eq_of_top hζ] using this
  -- the zero–one law
  rcases ZeroOne.aux128DriverStatement κ hκ rL rR hL hR allSwalSet measurableSet_allSwalSet
    (fun c hc w hw hw0 => dilPath_mem_allSwalSet_iff hc hw hw0) P 𝓕 W VL VR B ζ hE with h | h
  · filter_upwards [h, hgood] with ω hω ⟨_, hw, hw0⟩
    exact (mem_allSwalSet_iff hw hw0).1 hω
  · exact absurd (measure_eq_zero_iff_ae_notMem.2 h) hGpos


/-- **The landing point of the first swallow of `x`** (G8's proof, p. 500: "Let `τ_x` be the first swallowing of `x`.
On the finite branch its landing point is a real `q ≥ x` […] Lemma 7.16 excludes `q = x`, so `q > x`"). For the
two-seed evolution with `0 < κ < 4`, `r_L > −2`, `−2 < r_R < κ/2 − 2` and a generating trace, almost surely `x > 0`
is swallowed at a finite time `σ` (`RealSwallowAt`: alive on `[0, s]` for `s < σ`, not on `[0, σ]`), and the trace at
`σ` is a real point `q > x` beyond which every real point is still alive at `σ`. -/
theorem ae_swallow_landing (hκ : 0 < κ) (hκ4 : κ < 4) (hL : -2 < rL) (hR : -2 < rR) (hRc : rR < κ / 2 - 2)
    [IsProbabilityMeasure P]
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {x : ℝ} (hx : 0 < x) :
    ∀ᵐ ω ∂P, ∃ σ : ℝ≥0, (σ : ℝ≥0∞) < ζ ω ∧ RealSwallowAt (fun s : ℝ => W s.toNNReal ω) x σ ∧
      ∃ q : ℝ, x < q ∧ η ω σ = q ∧
        ∀ y : ℝ, q < y → ∃ v, IsForwardSol (fun s : ℝ => W s.toNNReal ω) (y : ℂ) σ v := by
  have hne := Lemma716.ae_trace_ne (ρL := fun _ => rL) (ρR := fun _ => rR) hκ hκ4 hE hη hL hR hRc hx.ne'
  filter_upwards [ae_swallowed_twoSeed hκ hL hR hRc hE, ae_good hκ hL hR hE, hη, hE.2.2.2.2, hne]
    with ω hsw ⟨hζ, hw, hw0⟩ hηω hp hneω
  rw [hζ] at hp hηω
  set Wr : ℝ → ℝ := fun s => W s.toNNReal ω with hWr
  have hWc : Continuous Wr := hw.comp continuous_real_toNNReal
  have hW0 : Wr 0 = 0 := by simp [hWr, hw0]
  obtain ⟨T, hT⟩ := hsw x hx
  obtain ⟨σ, ⟨hσ0, -⟩, hσ⟩ := exists_realSwallowAt hWc hW0 hx T.coe_nonneg hT
  set σN : ℝ≥0 := σ.toNNReal with hσN
  have hσσ : (σN : ℝ) = σ := Real.coe_toNNReal _ hσ0.le
  obtain ⟨hWc', hW0', hVc, hV0, hWV, hVeq, hVint, hnull⟩ := LP4S.rightMark_props hp 0 rfl
  -- the force gap vanishes at `σ`
  set g : ℝ → ℝ := fun s => VR 0 s.toNNReal ω - W s.toNNReal ω with hg
  have hgc : Continuous g := hVc.sub hWc
  have hXlim : Tendsto (fun s => (fwdMap Wr s x).re) (𝓝[<] σ) (𝓝 0) := by
    have h := (Complex.continuous_re.tendsto _).comp (tendsto_fwdMap_of_realSwallowAt hWc hW0 hx hσ)
    rw [Complex.zero_re] at h
    exact h
  have hgle : ∀ᶠ s in 𝓝[<] σ, 0 ≤ g s ∧ g s ≤ (fwdMap Wr s x).re := by
    filter_upwards [Ioo_mem_nhdsLT hσ0] with s hs
    obtain ⟨v, hv⟩ := hσ.2.1 s ⟨hs.1.le, hs.2⟩
    have hb := (LP4S.rightGap_bounds hWc' hW0' hVc hV0 hWV hVeq hVint hnull hx hs.1.le hv s
      ⟨hs.1.le, le_rfl⟩).1
    rw [fwdMap_eq_of_isForwardSol hWc hv ⟨hs.1.le, le_rfl⟩]
    exact ⟨sub_nonneg.2 (hWV s), by simp only [hg]; linarith⟩
  have hgσ : g σ = 0 := by
    have hlim : Tendsto g (𝓝[<] σ) (𝓝 (g σ)) := hgc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_antisymm (le_of_tendsto_of_tendsto hlim hXlim (hgle.mono fun s hs => hs.2))
      (ge_of_tendsto hlim (hgle.mono fun s hs => hs.1))
  -- the tip at `σ`
  have hfp := IsIntegratedSLEPath.isForcePath hp
  set T₂ : ℝ≥0 := σN + 1 with hT₂
  have hσT₂ : σ < T₂ := by rw [hT₂, NNReal.coe_add, hσσ]; simp
  have hUw : ∀ s : ℝ, 0 ≤ s → s < T₂ → Wr s = W s.toNNReal ω := fun _ _ _ => rfl
  have hηR : IsLoewnerTraceLT Wr T₂ (fun s : ℝ => η ω s.toNNReal) :=
    GB7a.isLoewnerTraceLT_of_agree hηω le_top hUw
  obtain ⟨hc, hue, hi, hn⟩ := GB7a.centredPkg hfp.continuousOn_w (hfp.continuousOn_vR 0)
    (fun t ht => hfp.integrable_gapR ht 0) (fun t ht => hfp.vR_eq ht 0) (hfp.volume_collisionR 0) le_top hUw
    hσ0.le hσT₂
  have hnn : ∀ s ∈ Icc (0 : ℝ) σ, 0 ≤ VR 0 s.toNNReal ω - W s.toNNReal ω := fun s _ => sub_nonneg.2 (hWV s)
  obtain ⟨q, hq, -, hqal⟩ := hηR.exists_tip_real_of_collision_right hWc hW0 hσ0.le hσT₂ hc hnn hue hi hn hgσ
  have hqx : x ≤ q := by
    by_contra hlt
    push Not at hlt
    exact hσ.2.2 (hqal x hlt)
  have hηq : η ω σN = q := by simpa [hσN] using hq
  have hxq : x ≠ q := fun h => hneω σN (by rw [hζ]; exact le_top) (by rw [hηq, h])
  refine ⟨σN, by rw [hζ]; exact ENNReal.coe_lt_top, by rw [hσσ]; exact hσ, q, lt_of_le_of_ne hqx hxq, hηq,
    fun y hy => by rw [hσσ]; exact hqal y hy⟩

end Law

end InteractingSLE.RLCJ
