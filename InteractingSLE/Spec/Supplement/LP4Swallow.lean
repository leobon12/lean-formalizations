/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LP4SwallowRatio
import InteractingSLE.Spec.Supplement.LP4SwallowCompare
import InteractingSLE.Spec.Supplement.LP2

/-!
# LP4's last input: the two-seed evolution swallows a positive point with positive probability

Packet PROVE-LP18. Specification p. 482, first paragraph of the proof of Proposition LP4 (right side): "After the first
`D = 1` level, wait for a right-seed collision using accessibility of the right Jacobi endpoint. The left force is then
separated from the driver by `D > 0`. Map out, center, and divide by `D`. In these coordinates insert a passive point
`ε > 0`. Lemma LP2 and scaling imply that its swallowing time and the driver oscillation up to that time are
respectively `ε²` and `ε` times finite random variables. Thus, for sufficiently small deterministic `ε`, it is swallowed
before the buffered stop … with positive probability. The separated left drift can be deleted through this stop by the
bounded-energy change in LP1. Equivalence transfers that positive probability to the actual two-seed future. The inverse
real boundary map sends this passive point to a physical real point strictly beyond the previous right swallowed
extreme. Hence the new right extreme is positive."

**`lp4RightSwallowStatement`** proves LP17's named input `LP4RightSwallowStatement`, and with it
`lp4Statement_of_collar`: LP4 (`LP4Statement`) from Zhan's stopping collar alone.

The route, which needs neither the Jacobi endpoint nor an inverse boundary map:

1. **LP2 at the ratio restart** (`codeLaw_allSet_zero_ne_zero`). For the word `SLE_κ(0; ρ)` (a zero-weight left seed),
   deleting the left mark gives LP2's single right seed, so every positive point is swallowed. Restart at the first
   time `T ≥ 1` with `R = L` (`exists_ratio_restart`; `L = W − V^L`, `R = V^R − W`): a physical point `x > 0` alive at
   `T` has a restarted image beyond the restarted right mark (`exists_restart_not_alive`), which the future swallows.
   The restarted word is `L_T (−1, 1)`, so the canonical probability that the word `(−1, 1)` swallows a point beyond
   its right mark is positive.
2. **The window** (`exists_codeLaw_winSet_ne_zero`). On one evolution of `(−1, 1)` the windowed events
   "swallowed by `t < (n+1)²`, the driver above `−(n + 1)` until then" exhaust that event, so one of them has positive
   probability. Scaling by `1/(2(n + 1))` and moving the zero-weight left mark (it does not act on the driver) give:
   the word `(−1, r)`, `r = 1/(2(n + 1))`, swallows a point beyond its right mark by time `1/4` while the driver stays
   above `−1/2`, so the left gap stays above `1/2`, with positive probability.
3. **Deleting the left drift** (`codeLaw_allSet_ne_zero_of_compare`): the target weight `r_L` on the separated left mark
   is a bounded-energy Girsanov change through that stop, so the target word `SLE_κ(r_L; r_R)` from `(−1, r)` swallows a
   point beyond its right mark with positive canonical probability.
4. **The ratio restart of the actual evolution** at the first time `T ≥ 1` with `R = r L`: the restarted word is
   `L_T (−1, r)`, its canonical probability is the same along the ray (`codeLaw_allSet_ray`), so with positive
   probability the future swallows a point `y` beyond the restarted right mark, and the physical point
   `y − (V^R_T − W_T) > 0` is swallowed (`exists_swallowed_of_swalAll`, the bound `g_t(x) − V^R_t ≤ x`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.LP.LP4S

open QuantumZipper Sec2 Sec2.Assembly Sec7.RandRestart Sec7.Dilation

/-! ### Restarted drivers and physical points -/

theorem alive_restart_iff {w : ℝ≥0 → ℝ} {T : ℝ≥0} {y S : ℝ} :
    LP3.Alive (fun s : ℝ => (fun t : ℝ≥0 => w (T + t) - w T) s.toNNReal) y S ↔
      LP3.Alive (fun r : ℝ => (fun s : ℝ => w s.toNNReal) ((T : ℝ) + r) - (fun s : ℝ => w s.toNNReal) T) y S := by
  have h : ∀ r ∈ Icc (0 : ℝ) S, (fun s : ℝ => (fun t : ℝ≥0 => w (T + t) - w T) s.toNNReal) r =
      (fun r : ℝ => (fun s : ℝ => w s.toNNReal) ((T : ℝ) + r) - (fun s : ℝ => w s.toNNReal) T) r := by
    intro r hr
    simp only [Real.toNNReal_coe]
    rw [Real.toNNReal_add T.coe_nonneg hr.1, Real.toNNReal_coe]
  constructor
  · rintro ⟨u, hu⟩; exact ⟨u, _root_.QuantumZipper.isForwardSol_congr_drive h hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, _root_.QuantumZipper.isForwardSol_congr_drive (fun r hr => (h r hr).symm) hu⟩

section Path

variable {κ : ℝ} {ρL ρR : Fin 1 → ℝ} {w : ℝ≥0 → ℝ} {vL vR : Fin 1 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}

/-- **From the restarted event to a physical point**: if the driver of a two-seed path restarted at `T` swallows a
point beyond the restarted right mark, then some physical point `x > 0` is swallowed at a finite time. -/
theorem exists_swallowed_of_swalAll
    (hp : IsIntegratedSLEPath κ (fun _ => 0) (fun _ => 0) ρL ρR w vL vR b ⊤) (T : ℝ≥0)
    (h : SwalAll ((fun i => vL i T - w T), fun j => vR j T - w T) (fun t => w (T + t) - w T) ⊤) :
    ∃ x : ℝ, 0 < x ∧ ∃ T' : ℝ≥0, ZhanGT4.IsSwallowedBy (fun s : ℝ => w s.toNNReal) x T' := by
  obtain ⟨hWc, hW0, hVc, hV0, hWV, hVeq, hVint, hnull⟩ := rightMark_props hp 0 rfl
  have hwc : Continuous w := (Sec7.IsIntegratedSLEPath.continuous_w_of_top hp).1
  have hw'c : Continuous fun t => w (T + t) - w T :=
    (hwc.comp (continuous_const.add continuous_id)).sub continuous_const
  have hw'0 : (fun t => w (T + t) - w T) 0 = 0 := by simp
  rw [swalAll_top_iff hw'c hw'0] at h
  obtain ⟨y, -, hry, t, hd⟩ := h
  rw [alive_restart_iff] at hd
  obtain ⟨x, hx, hdx⟩ := exists_not_alive_of_restart hWc hW0 hVc hV0 hWV hVeq hVint hnull T.coe_nonneg
    t.coe_nonneg (by simpa using hry) hd
  refine ⟨x, hx, T + t, ?_⟩
  show ¬ LP3.Alive _ x ((T + t : ℝ≥0) : ℝ)
  rw [NNReal.coe_add]
  exact hdx

/-- **From physical points to the restarted event**: if every positive rational point is swallowed at a finite time,
then the driver of a two-seed path restarted at `T` swallows a point beyond the restarted right mark. -/
theorem swalAll_of_forall_swallowed
    (hp : IsIntegratedSLEPath κ (fun _ => 0) (fun _ => 0) ρL ρR w vL vR b ⊤) (T : ℝ≥0)
    (hall : ∀ q : ℚ, 0 < (q : ℝ) → ∃ T' : ℝ≥0, ¬ LP3.Alive (fun s : ℝ => w s.toNNReal) q T') :
    SwalAll ((fun i => vL i T - w T), fun j => vR j T - w T) (fun t => w (T + t) - w T) ⊤ := by
  obtain ⟨hWc, hW0, hVc, hV0, hWV, hVeq, hVint, hnull⟩ := rightMark_props hp 0 rfl
  have hwc : Continuous w := (Sec7.IsIntegratedSLEPath.continuous_w_of_top hp).1
  have hw'c : Continuous fun t => w (T + t) - w T :=
    (hwc.comp (continuous_const.add continuous_id)).sub continuous_const
  have hw'0 : (fun t => w (T + t) - w T) 0 = 0 := by simp
  rw [swalAll_top_iff hw'c hw'0]
  -- a rational point alive at `T`
  obtain ⟨u₀, -, hmax⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_isMaxOn
    (nonempty_Icc.2 zero_le) hwc.continuousOn
  obtain ⟨q, hq⟩ := exists_rat_gt (max (w u₀ + 1) 1)
  have hq0 : (0 : ℝ) < q := by linarith [le_max_right (w u₀ + 1) 1]
  have hal : LP3.Alive (fun s : ℝ => w s.toNNReal) q T :=
    LP3.alive_of_forall_add_le hWc T.coe_nonneg one_pos fun s hs => by
      have hsI : s.toNNReal ∈ Icc (0 : ℝ≥0) T :=
        ⟨zero_le, by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]; exact hs.2⟩
      have h1 := hmax hsI
      simp only [mem_ofPred_eq] at h1
      linarith [le_max_left (w u₀ + 1) 1]
  obtain ⟨T', hT'⟩ := hall q hq0
  have hTT' : (T : ℝ) ≤ T' := by
    by_contra hlt
    push Not at hlt
    exact hT' (hal.mono T'.coe_nonneg hlt.le)
  obtain ⟨y, hy, hyd⟩ := exists_restart_not_alive hWc hW0 hVc hV0 hWV hVeq hVint hnull hq0 T.coe_nonneg hTT'
    hal hT'
  have hy' : vR 0 T - w T < y := by simpa using hy
  have hWVT : w T ≤ vR 0 T := by simpa using hWV T
  refine ⟨y, by linarith, hy', (T' - T : ℝ).toNNReal, ?_⟩
  rw [alive_restart_iff, Real.coe_toNNReal _ (sub_nonneg.2 hTT')]
  exact hyd

end Path

/-! ### Canonical probabilities along rays -/

section Ray

variable {κ : ℝ}

/-- An evolution of a separated one-mark-per-side word `(−L, R)` with weights `> −2`, with infinite lifetime. -/
theorem exists_twoForce (hκ : 0 < κ) {ρL ρR : Fin 1 → ℝ} (hρL : -2 < ρL 0) (hρR : -2 < ρR 0) {L R : ℝ}
    (hL : 0 < L) (hR : 0 ≤ R) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ (fun _ => -L) (fun _ => R) ρL ρR P 𝓕 W VL VR B ζ ∧ ∀ᵐ ω ∂P, ζ ω = ⊤ := by
  have hF : IsOrderedForceWord (fun _ : Fin 1 => -L) (fun _ : Fin 1 => R) :=
    ⟨antitone_const, fun _ => by linarith, monotone_const, fun _ => hR⟩
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hF (ρL := ρL) (ρR := ρR)
  exact ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE, Sec2.Assembly2.ae_lifetime_eq_top_twoSeed hκ hE hρL hρR⟩

theorem sqrt_inv_sq_toNNReal {a : ℝ} (ha : 0 < a) :
    (√(((a⁻¹ ^ 2).toNNReal : ℝ≥0) : ℝ))⁻¹ = a ∧ √(((a⁻¹ ^ 2).toNNReal : ℝ≥0) : ℝ) = a⁻¹ ∧
      (((a⁻¹ ^ 2).toNNReal : ℝ≥0) : ℝ) = a⁻¹ ^ 2 := by
  have h2 : (((a⁻¹ ^ 2).toNNReal : ℝ≥0) : ℝ) = a⁻¹ ^ 2 := Real.coe_toNNReal _ (by positivity)
  have hs : √(((a⁻¹ ^ 2).toNNReal : ℝ≥0) : ℝ) = a⁻¹ := by
    rw [h2, Real.sqrt_sq (by positivity)]
  exact ⟨by rw [hs, inv_inv], hs, h2⟩

/-- **The windowed canonical probability under scaling** of the word `(−L, R)` by `a > 0`. -/
theorem codeLaw_winSet_scale (hκ : 0 < κ) {ρL ρR : Fin 1 → ℝ} (hρL : -2 < ρL 0) (hρR : -2 < ρR 0) {L R a : ℝ}
    (hL : 0 < L) (hR : 0 ≤ R) (ha : 0 < a) (M N : ℝ) :
    codeLaw κ ρL ρR (winSet M N) ((fun _ => -(a * L)), fun _ => a * R) =
      codeLaw κ ρL ρR (winSet (M / a) (N / a ^ 2)) ((fun _ => -L), fun _ => R) := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE, hζ⟩ := exists_twoForce hκ hρL hρR hL hR
  set c : ℝ≥0 := (a⁻¹ ^ 2).toNNReal with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact (Real.toNNReal_pos.2 (by positivity)).ne'
  obtain ⟨e1, e2, e3⟩ := sqrt_inv_sq_toNNReal ha
  have h := codeLaw_winSet_dilate hκ (fun _ _ => by linarith) hE hζ hc0 M N
  rw [e1, e2, e3] at h
  have hs1 : ((fun i : Fin 1 => a * (fun _ : Fin 1 => -L) i), fun j : Fin 1 => a * (fun _ : Fin 1 => R) j) =
      (((fun _ => -(a * L)), fun _ => a * R) : (Fin 1 → ℝ) × (Fin 1 → ℝ)) := by
    refine Prod.ext (funext fun _ => ?_) rfl
    show a * -L = -(a * L)
    ring
  have hM : a⁻¹ * M = M / a := by ring
  have hN : a⁻¹ ^ 2 * N = N / a ^ 2 := by field_simp
  rw [hs1, hM, hN] at h
  exact h

/-- **The swallowing canonical probability is constant along rays.** -/
theorem codeLaw_allSet_ray (hκ : 0 < κ) {ρL ρR : Fin 1 → ℝ} (hρL : -2 < ρL 0) (hρR : -2 < ρR 0) {r : ℝ}
    (hr : 0 ≤ r) {L : ℝ} (hL : 0 < L) :
    codeLaw κ ρL ρR allSet ((fun _ => -L), fun _ => r * L) =
      codeLaw κ ρL ρR allSet ((fun _ => -1), fun _ => r) := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE, hζ⟩ := exists_twoForce hκ hρL hρR one_pos hr
  set c : ℝ≥0 := (L⁻¹ ^ 2).toNNReal with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact (Real.toNNReal_pos.2 (by positivity)).ne'
  obtain ⟨e1, -, -⟩ := sqrt_inv_sq_toNNReal hL
  have h := codeLaw_allSet_dilate hκ (fun _ _ => by linarith) hE hζ hc0
  rw [e1] at h
  have hs1 : ((fun i : Fin 1 => L * (fun _ : Fin 1 => (-1 : ℝ)) i), fun j : Fin 1 => L * (fun _ : Fin 1 => r) j) =
      (((fun _ => -L), fun _ => r * L) : (Fin 1 → ℝ) × (Fin 1 → ℝ)) := by
    refine Prod.ext (funext fun _ => ?_) (funext fun _ => ?_)
    · show L * -1 = -L
      ring
    · show L * r = r * L
      ring
  rw [hs1] at h
  exact h

end Ray

/-! ### Steps 1–3: the canonical probabilities -/

section Steps

variable {κ : ℝ}

/-- **Step 1** (LP2 at the ratio restart): the word `SLE_κ(0; ρ)` from `(−1, 1)` swallows a point beyond its right mark
with positive canonical probability (`κ > 4`, `−2 < ρ < κ/2 − 2`). -/
theorem codeLaw_allSet_zero_ne_zero (hκ4 : 4 < κ) {ρ : ℝ} (hρ : -2 < ρ) (hρc : ρ < κ / 2 - 2) :
    codeLaw κ (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => ρ) allSet ((fun _ => -1), fun _ => 1) ≠ 0 := by
  have hκ : 0 < κ := by linarith
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
    · filter_upwards [LP2.lp2 hκ4 hρ hρc hD hq] with ω hω _
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

/-- **Step 2** (the window): for some `n`, the word `SLE_κ(0; ρ)` from `(−1, r)`, `r = 1/(2(n + 1))`, swallows a point
beyond its right mark by time `1/4` while the driver stays above `−1/2`, with positive canonical probability. -/
theorem exists_codeLaw_winSet_ne_zero (hκ4 : 4 < κ) {ρ : ℝ} (hρ : -2 < ρ) (hρc : ρ < κ / 2 - 2) :
    ∃ n : ℕ, codeLaw κ (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => ρ) (winSet (1 / 2) (1 / 4))
      ((fun _ => -1), fun _ => 1 / (2 * ((n : ℝ) + 1))) ≠ 0 := by
  have hκ : 0 < κ := by linarith
  have h0 : (-2 : ℝ) < (fun _ : Fin 1 => (0 : ℝ)) 0 := by norm_num
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE, hζ⟩ := exists_twoForce hκ (ρL := fun _ => (0 : ℝ)) h0 (ρR := fun _ => ρ) hρ one_pos
    zero_le_one
  have hsep : ∀ i j, (fun _ : Fin 1 => (-1 : ℝ)) i < (fun _ : Fin 1 => (1 : ℝ)) j := fun _ _ => by norm_num
  have hall : P {ω | SwalAll ((fun _ : Fin 1 => (-1 : ℝ)), fun _ : Fin 1 => (1 : ℝ)) (fun t => W t ω) (ζ ω)} ≠ 0 := by
    rw [measure_allSet_eq_codeLaw hκ hsep hE]
    have h := codeLaw_allSet_zero_ne_zero hκ4 hρ hρc
    simpa using h
  have hcover : {ω | SwalAll ((fun _ : Fin 1 => (-1 : ℝ)), fun _ : Fin 1 => (1 : ℝ)) (fun t => W t ω) (ζ ω)} ≤ᵐ[P]
      ⋃ n : ℕ, {ω | SwalWin ((n : ℝ) + 1) (((n : ℝ) + 1) ^ 2) ((fun _ : Fin 1 => (-1 : ℝ)), fun _ : Fin 1 => (1 : ℝ)) (fun t => W t ω) (ζ ω)} := by
    filter_upwards [hζ, hE.2.2.2.2] with ω hζω hp h
    rw [hζω] at hp
    obtain ⟨hwc, hw0⟩ := Sec7.IsIntegratedSLEPath.continuous_w_of_top hp
    have h' : SwalAll ((fun _ : Fin 1 => (-1 : ℝ)), fun _ : Fin 1 => (1 : ℝ)) (fun t => W t ω) ⊤ := by rw [← hζω]; exact h
    rw [swalAll_top_iff hwc hw0, rAll_iff_exists_rWin hwc] at h'
    obtain ⟨M, N, hMN⟩ := h'
    obtain ⟨n, hn⟩ := exists_nat_ge (max M N)
    refine mem_iUnion.2 ⟨n, ?_⟩
    show SwalWin ((n : ℝ) + 1) (((n : ℝ) + 1) ^ 2) ((fun _ : Fin 1 => (-1 : ℝ)), fun _ : Fin 1 => (1 : ℝ)) (fun t => W t ω) (ζ ω)
    rw [hζω, swalWin_top_iff hwc hw0]
    refine hMN.mono (by linarith [le_max_left M N]) ?_
    have h1 : N ≤ (n : ℝ) + 1 := by linarith [le_max_right M N]
    nlinarith
  have hpos : ∃ n : ℕ, P {ω | SwalWin ((n : ℝ) + 1) (((n : ℝ) + 1) ^ 2) ((fun _ : Fin 1 => (-1 : ℝ)), fun _ : Fin 1 => (1 : ℝ))
      (fun t => W t ω) (ζ ω)} ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hall (measure_mono_null_ae hcover (measure_iUnion_null hcon))
  obtain ⟨n, hn⟩ := hpos
  refine ⟨n, ?_⟩
  set m : ℝ := (n : ℝ) + 1 with hm
  have hm0 : 0 < m := by positivity
  have hL : 0 < 2 * m := by positivity
  have ha : 0 < 1 / (2 * m) := by positivity
  -- scale `(−1, r)` to `(−2m, 1)`
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

end Steps

/-! ### The theorem -/

/-- **LP4's right swallowing** (specification p. 482, the right half of the first paragraph of the proof of
Proposition LP4): for every two-seed evolution with `κ > 4` and `−2 < r_L, r_R < κ/2 − 2`, with positive probability
some real point `x > 0` is swallowed at a finite time. This is LP17's named input `LP4RightSwallowStatement`. -/
theorem lp4RightSwallowStatement : LP4RightSwallowStatement.{u} := by
  intro κ hκ4 rL rR hL _ hR hRc Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hκ : 0 < κ := by linarith
  obtain ⟨n, hn⟩ := exists_codeLaw_winSet_ne_zero hκ4 hR hRc
  set r : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hr
  have hr0 : 0 < r := by positivity
  have h0 : (-2 : ℝ) < (fun _ : Fin 1 => (0 : ℝ)) 0 := by norm_num
  have hL' : (-2 : ℝ) < (fun _ : Fin 1 => rL) 0 := hL
  have hR' : (-2 : ℝ) < (fun _ : Fin 1 => rR) 0 := hR
  -- Step 3: the target word from `(−1, r)` swallows beyond its right mark with positive canonical probability
  have hK : codeLaw κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) allSet ((fun _ => -1), fun _ => r) ≠ 0 := by
    obtain ⟨Ω₁, m₁, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, hE₁, hζ₁⟩ :=
      exists_twoForce hκ (ρL := fun _ => (0 : ℝ)) h0 (ρR := fun _ => rR) hR one_pos hr0.le
    have hF : IsOrderedForceWord (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => r) :=
      ⟨antitone_const, fun _ => by norm_num, monotone_const, fun _ => hr0.le⟩
    refine codeLaw_allSet_ne_zero_of_compare hκ hF (show (-1 : ℝ) < r by linarith) hR' (M := 1 / 2)
      (N := 1 / 4) (δ := 1 / 4) (by norm_num) (by norm_num) (by norm_num) hE₁ hζ₁ ?_
    rw [measure_winSet_eq_codeLaw hκ (fun _ _ => show (-1 : ℝ) < r by linarith) hE₁]
    exact hn
  -- Step 4: the ratio restart of the actual evolution
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

end InteractingSLE.LP.LP4S

namespace InteractingSLE.LP

/-- **LP4's right swallowing**, the named input of LP17 (`LP4HalfBallStraddle.lean`), proved. -/
theorem lp4RightSwallowStatement : LP4RightSwallowStatement.{u} :=
  LP4S.lp4RightSwallowStatement

/-- **Proposition LP4** (`LP4Statement`) from Zhan's stopping collar (`κ > 4`) alone. -/
theorem lp4Statement_of_collar (hcol : ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ) :
    LP4Statement.{u} :=
  lp4Statement_of_rightSwallow hcol lp4RightSwallowStatement

/-- LP4's avoid step (`LP4AvoidStatement`) from Zhan's stopping collar alone. -/
theorem lp4AvoidStatement_of_collar (hcol : ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ) :
    LP4AvoidStatement.{u} :=
  lp4AvoidStatement_of_halfBall (lp4HalfBallStatement_of_rightSwallow hcol lp4RightSwallowStatement)

end InteractingSLE.LP
