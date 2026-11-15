/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHi3Gen

/-!
# The low-sector trial bound: a tight right cluster is swallowed or the evolution dies

Packet PROVE-TRIALS-HI3. Specification §7.3, Aux. lemmas 110–111 ("swallows an entire side at a finite continuous
endpoint"), in driver form. For an evolution whose right side has at least two marks with total `s ∈ (κ/2 − 4,
κ/2 − 2)`, started from a **tight** configuration (the right spread is a small fraction `ε₀` of the far right gap
`X₀`, and the left marks are at distance at least `K₀ X₀`):

  `P(ζ = ∞ and no two marks on the same side ever meet) ≤ 1/2`   (`measure_noMeet_le_half`).

Proof (no strip SLE, no field): the swallow Lyapunov function `F = α X^λ + β (Δ/X)^μ` of `TrialsHi3Gen`, with
`α = (K₁ X₀)^{−λ}`, `β = ε₁^{−μ}`, has generator `≤ −c X^{λ−2}` on the tight region `{X < K₁ X₀, Δ < ε₁ X}`
(`genT_le_of_region`; the left marks stay far because the cross gap is nondecreasing). Sample the localized Itô
martingale (`Clock.martingale_angLoc`) at the exit `ρ` of the region `{e < X < K₁X₀, e < Δ < ε₁X}` capped by `n`
(optional sampling for continuous martingales). The sampled value `Z_n` has `E Z_n ≤ F(0) ≤ 1/2` and dominates both
`F` at the exit (which is `≥ 1` at a bad exit) and `c (K₁X₀)^{λ−2}` times the elapsed time. On `{ζ = ∞, no meet}`
the far gap and the spread never vanish (either would make two right marks meet), so as `e → 0`, `n → ∞` either the
region is left through a bad face (`Z_n ≥ 1` eventually) or the elapsed time diverges (`Z_n → ∞`); Fatou's lemma
and Markov's inequality conclude.

## Main results

* `tightLev`, `tightExit`, `isStoppingTime_tightExit`;
* `tightMart`, `martingale_tightMart`, `continuous_tightMart`;
* **`measure_noMeet_le_half`**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace TrialsHi3

open Zhan Clock ZhanGT4

/-! ### The tight region and its exit time -/

section Exit

variable {nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The tight-region level** of `(W, V^{R,0}, V^{R,j₁})`: positive iff `e < X < K` and `e < Δ < ε₁ X`, where
`X = V^{R,j₁} − W` and `Δ = V^{R,j₁} − V^{R,0}`. -/
def tightLev (K ε₁ e : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  min (min (K - (p.2.2 - p.1)) ((p.2.2 - p.1) - e))
    (min (ε₁ * (p.2.2 - p.1) - (p.2.2 - p.2.1)) ((p.2.2 - p.2.1) - e))

theorem continuous_tightLev (K ε₁ e : ℝ) : Continuous (tightLev K ε₁ e) := by
  unfold tightLev; fun_prop

theorem tightLev_pos_iff {K ε₁ e : ℝ} {p : ℝ × ℝ × ℝ} :
    0 < tightLev K ε₁ e p ↔ (p.2.2 - p.1 < K ∧ e < p.2.2 - p.1) ∧
      (p.2.2 - p.2.1 < ε₁ * (p.2.2 - p.1) ∧ e < p.2.2 - p.2.1) := by
  simp only [tightLev, lt_min_iff, sub_pos]

theorem tightLev_nonneg_iff {K ε₁ e : ℝ} {p : ℝ × ℝ × ℝ} :
    0 ≤ tightLev K ε₁ e p ↔ (p.2.2 - p.1 ≤ K ∧ e ≤ p.2.2 - p.1) ∧
      (p.2.2 - p.2.1 ≤ ε₁ * (p.2.2 - p.1) ∧ e ≤ p.2.2 - p.2.1) := by
  simp only [tightLev, le_min_iff, sub_nonneg]

/-- The level process along the evolution. -/
def tightProc (K ε₁ e : ℝ) (W : ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (j₁ : Fin (nR + 1)) :
    ℝ≥0 → Ω → ℝ :=
  fun t ω => tightLev K ε₁ e (W t ω, VR 0 t ω, VR j₁ t ω)

/-- **The exit time from the tight region** (the first time before `ζ` with level `≤ 0`; `0` on `N`). -/
def tightExit (N : Set Ω) (ζ : Ω → ℝ≥0∞) (K ε₁ e : ℝ) (W : ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ)
    (j₁ : Fin (nR + 1)) (ω : Ω) : ℝ≥0∞ :=
  Sec7.zeroOn N (firstMeet zeroProc (tightProc K ε₁ e W VR j₁) ζ) ω

variable {N : Set Ω} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {K ε₁ e : ℝ}
  {j₁ : Fin (nR + 1)}

theorem continuousOn_tightProc {ω : Ω} (hW : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (h0 : ContinuousOn (fun t => VR 0 t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (h1 : ContinuousOn (fun t => VR j₁ t ω) {t | (t : ℝ≥0∞) < ζ ω}) :
    ContinuousOn (fun t => tightProc K ε₁ e W VR j₁ t ω - zeroProc t ω) {t | (t : ℝ≥0∞) < ζ ω} := by
  simp only [tightProc, zeroProc, sub_zero]
  exact (continuous_tightLev K ε₁ e).comp_continuousOn (hW.prodMk (h0.prodMk h1))

/-- **The tight exit is a stopping time.** -/
theorem isStoppingTime_tightExit {𝓖 : Filtration ℝ≥0 mΩ} (hW : AdaptedBefore 𝓖 ζ W)
    (h0 : AdaptedBefore 𝓖 ζ (VR 0)) (h1 : AdaptedBefore 𝓖 ζ (VR j₁)) (hN : ∀ t, MeasurableSet[𝓖 t] N)
    (hc : ∀ ω ∉ N, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ContinuousOn (fun t => VR 0 t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ContinuousOn (fun t => VR j₁ t ω) {t | (t : ℝ≥0∞) < ζ ω}) :
    IsStoppingTime 𝓖 fun ω => (tightExit N ζ K ε₁ e W VR j₁ ω : WithTop ℝ≥0) := by
  have hYa : AdaptedBefore 𝓖 ζ (tightProc K ε₁ e W VR j₁) :=
    adaptedBefore_of_eq (fun _ p => tightLev K ε₁ e p) (fun _ => (continuous_tightLev K ε₁ e).measurable)
      hW h0 h1 fun t ω => rfl
  have hZa : AdaptedBefore 𝓖 ζ (zeroProc (Ω := Ω)) :=
    adaptedBefore_of_eq (fun _ _ => 0) (fun _ => measurable_const) hW h0 h1 fun _ _ => rfl
  exact isStoppingTime_firstMeet_off hZa hYa hN fun ω hω =>
    continuousOn_tightProc (hc ω hω).1 (hc ω hω).2.1 (hc ω hω).2.2

/-- Before the tight exit the state is in the tight region. -/
theorem pos_of_lt_tightExit {ω : Ω} (hω : ω ∉ N) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < tightExit N ζ K ε₁ e W VR j₁ ω) :
    (t : ℝ≥0∞) < ζ ω ∧ 0 < tightLev K ε₁ e (W t ω, VR 0 t ω, VR j₁ t ω) := by
  rw [tightExit, Sec7.zeroOn_of_notMem hω] at ht
  have h := lt_of_lt_firstMeet ht
  exact ⟨h.1, by simpa [tightProc, zeroProc] using h.2⟩

theorem tightExit_le_lifetime {ω : Ω} (hω : ω ∉ N) : tightExit N ζ K ε₁ e W VR j₁ ω ≤ ζ ω := by
  rw [tightExit, Sec7.zeroOn_of_notMem hω]; exact firstMeet_le_lifetime

/-- If the level is positive on `[0, t]`, `t < ζ`, the exit is after `t`. -/
theorem lt_tightExit_of_forall {ω : Ω} (hω : ω ∉ N)
    (hc : ContinuousOn (fun t => tightProc K ε₁ e W VR j₁ t ω - zeroProc t ω) {t | (t : ℝ≥0∞) < ζ ω})
    {t : ℝ≥0} (htζ : (t : ℝ≥0∞) < ζ ω) (h : ∀ s ≤ t, 0 < tightLev K ε₁ e (W s ω, VR 0 s ω, VR j₁ s ω)) :
    (t : ℝ≥0∞) < tightExit N ζ K ε₁ e W VR j₁ ω := by
  rw [tightExit, Sec7.zeroOn_of_notMem hω]
  by_contra hle
  rw [not_lt] at hle
  obtain ⟨m, hm, -, hmle⟩ := exists_eq_firstMeet hc (hle.trans_lt htζ)
  have hmt : m ≤ t := by rw [hm] at hle; exact_mod_cast hle
  have := h m hmt
  simp only [tightProc, zeroProc] at hmle
  linarith

/-- At a finite exit before `ζ`, the level vanishes there and is positive before. -/
theorem tightLev_tightExit {ω : Ω} (hω : ω ∉ N)
    (hc : ContinuousOn (fun t => tightProc K ε₁ e W VR j₁ t ω - zeroProc t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hlt : tightExit N ζ K ε₁ e W VR j₁ ω < ζ ω) :
    ∃ m : ℝ≥0, tightExit N ζ K ε₁ e W VR j₁ ω = m ∧ (m : ℝ≥0∞) < ζ ω ∧
      tightLev K ε₁ e (W m ω, VR 0 m ω, VR j₁ m ω) ≤ 0 := by
  rw [tightExit, Sec7.zeroOn_of_notMem hω] at hlt ⊢
  obtain ⟨m, hm, hmζ, hmle⟩ := exists_eq_firstMeet hc hlt
  exact ⟨m, hm, hmζ, by simpa [tightProc, zeroProc] using hmle⟩

end Exit

/-! ### The localized martingale -/

section Mart

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

/-- **The localized Itô martingale of the swallow Lyapunov function** (no extra coordinate). -/
def tightMart (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin (nR + 1) → ℝ) (G : Set Ω) (T : ℕ → Ω → ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (a α β lam μ : ℝ) (n : ℕ) (t : ℝ≥0)
    (ω : Ω) : ℝ :=
  lyapT κ xL xR ρL ρR (Fin.last nR) a α β lam μ
      (coordA xL xR G VL VR (fun _ _ => 0) (min t (angLoc G T W VL VR B ζ n ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (angLoc G T W VL VR B ζ n ω)) ω) -
    ∫ s in (0 : ℝ)..(min t (angLoc G T W VL VR B ζ n ω) : ℝ≥0),
      Ito.itoGen (lyapT κ xL xR ρL ρR (Fin.last nR) a α β lam μ)
        (coordA xL xR G VL VR (fun _ _ => 0) s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
        (densA G W VL VR (fun _ _ => 0) s ω)

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T) (hx : 0 < xR 0 - xL 0)

include hE hGm hGc hgood hT hx in
theorem martingale_tightMart {a : ℝ} (ha : 0 < a) (α β lam μ : ℝ) (n : ℕ) :
    Martingale (tightMart κ xL xR ρL ρR G T W VL VR B ζ a α β lam μ n) (usualAugmentation 𝓕 P) P :=
  martingale_angLoc hE hGm hGc hgood hT hx
    ((contDiff_lyapT κ xL xR ρL ρR (Fin.last nR) ha α β lam μ).contDiffOn) n
    (I := fun _ _ => 0) (c := fun _ _ => 0) (KI := 0) (Kc := 0) (fun _ _ _ _ => by simp)
    (fun _ _ => intervalIntegrable_const) (fun _ _ => by simp) (fun _ _ _ _ => by simp)
    ⟨fun _ _ => 0, fun _ => measurable_const, fun _ _ _ _ => rfl⟩ (fun _ _ => continuousOn_const)

omit hE hGm hGc hT hx in
theorem tightMart_min (a α β lam μ : ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    tightMart κ xL xR ρL ρR G T W VL VR B ζ a α β lam μ n t ω =
      tightMart κ xL xR ρL ρR G T W VL VR B ζ a α β lam μ n (min t (angLoc G T W VL VR B ζ n ω)) ω := by
  simp only [tightMart, min_assoc, min_self]

omit hE hGm hGc hT hx in
theorem coord_eq_pathCoord {ω : Ω} (hω : ω ∈ G) (t : ℝ≥0) :
    (coordA xL xR G VL VR (fun _ _ => 0) t ω, Sec2.TwoSeed.brownG G B t ω) =
      pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 t := by
  simp only [coordA, Sec2.TwoSeed.brownG, hω, ↓reduceIte]; rfl

omit hE hGm hGc hT hx in
theorem densA_eq_angDens {ω : Ω} (hω : ω ∈ G) (s : ℝ) :
    densA G W VL VR (fun _ _ => 0) s ω =
      angDens (W s.toNNReal ω) (fun i => VL i s.toNNReal ω) (fun j => VR j s.toNNReal ω) 0 := by
  simp only [densA, hω, ↓reduceIte]

include hgood in
omit hE hGm hGc hT hx in
/-- The itô integrand is interval-integrable up to `σ_n` (the velocities are integrable, the derivatives of the
`C³` function are continuous along the path). -/
theorem intervalIntegrable_tightGen {a : ℝ} (ha : 0 < a) (α β lam μ : ℝ) (n : ℕ) {ω : Ω} (hω : ω ∈ G) :
    IntervalIntegrable (fun s : ℝ => Ito.itoGen (lyapT κ xL xR ρL ρR (Fin.last nR) a α β lam μ)
        (coordA xL xR G VL VR (fun _ _ => 0) s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
        (densA G W VL VR (fun _ _ => 0) s ω)) volume 0 (angLoc G T W VL VR B ζ n ω) := by
  have hω' := hgood ω hω
  have hF := hω'.1.isForcePath
  set σ := angLoc G T W VL VR B ζ n ω
  have hσζ : (σ : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime hω'
  have hΦ := contDiff_lyapT κ xL xR ρL ρR (Fin.last nR) ha α β lam μ
  have hpath : ContinuousOn (fun s : ℝ => pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0
      s.toNNReal) (uIcc 0 (σ : ℝ)) := by
    rw [uIcc_of_le σ.coe_nonneg]
    have hm := mapsTo_toNNReal (ζ := ζ ω) hσζ
    refine ContinuousOn.prodMk (ContinuousOn.prodMk ?_ (ContinuousOn.prodMk ?_ continuousOn_const)) ?_
    · exact continuousOn_pi.2 fun i =>
        (hF.continuousOn_vL i).comp continuous_real_toNNReal.continuousOn hm
    · exact continuousOn_pi.2 fun j =>
        (hF.continuousOn_vR j).comp continuous_real_toNNReal.continuousOn hm
    · exact (hω'.2.1.comp continuous_real_toNNReal).continuousOn
  have hPFc : Continuous (Ito.partialFst (lyapT κ xL xR ρL ρR (Fin.last nR) a α β lam μ)) :=
    (hΦ.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hF1 : ContDiff ℝ 2 (fderiv ℝ (lyapT κ xL xR ρL ρR (Fin.last nR) a α β lam μ)) :=
    hΦ.fderiv_right (by norm_num)
  have hPSSc : Continuous (Ito.partialSndSnd (lyapT κ xL xR ρL ρR (Fin.last nR) a α β lam μ)) :=
    ((hF1.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
  have hlam : IntervalIntegrable (fun s : ℝ => angDens (W s.toNNReal ω) (fun i => VL i s.toNNReal ω)
      (fun j => VR j s.toNNReal ω) (0 : ℝ)) volume 0 σ :=
    intervalIntegrable_scoord (fun i => hF.intervalIntegrable_forceL hσζ i)
      (fun j => hF.intervalIntegrable_forceR hσζ j) intervalIntegrable_const
  have h := (Ito.intervalIntegrable_clm_apply (hPFc.comp_continuousOn hpath) hlam).add
    ((hPSSc.comp_continuousOn hpath).intervalIntegrable.const_mul (1 / 2))
  refine h.congr fun s _ => ?_
  simp only [Function.comp_apply, coord_eq_pathCoord hω, densA_eq_angDens hω, Ito.itoGen]

include hgood in
omit hE hGm hGc hT hx in
/-- **The martingale is continuous in time.** -/
theorem continuous_tightMart {a : ℝ} (ha : 0 < a) (α β lam μ : ℝ) (n : ℕ) (ω : Ω) :
    Continuous fun t => tightMart κ xL xR ρL ρR G T W VL VR B ζ a α β lam μ n t ω := by
  by_cases hω : ω ∈ G
  · have hω' := hgood ω hω
    have hF := hω'.1.isForcePath
    set σ := angLoc G T W VL VR B ζ n ω with hσdef
    have hσζ : (σ : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime hω'
    have hgi := intervalIntegrable_tightGen hgood ha α β lam μ n hω (κ := κ) (xL := xL) (xR := xR)
      (ρL := ρL) (ρR := ρR) (T := T) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ)
    have hinner : Continuous fun t : ℝ≥0 => ((min t σ : ℝ≥0) : ℝ) :=
      NNReal.continuous_coe.comp (continuous_id.min continuous_const)
    have hmaps : ∀ t : ℝ≥0, ((min t σ : ℝ≥0) : ℝ) ∈ Icc 0 (σ : ℝ) := fun t =>
      ⟨(min t σ).coe_nonneg, by exact_mod_cast min_le_right t σ⟩
    have hpath : ContinuousOn (fun s : ℝ => pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0
        s.toNNReal) (Icc 0 (σ : ℝ)) := by
      have hm := mapsTo_toNNReal (ζ := ζ ω) hσζ
      refine ContinuousOn.prodMk (ContinuousOn.prodMk ?_ (ContinuousOn.prodMk ?_ continuousOn_const)) ?_
      · exact continuousOn_pi.2 fun i =>
          (hF.continuousOn_vL i).comp continuous_real_toNNReal.continuousOn hm
      · exact continuousOn_pi.2 fun j =>
          (hF.continuousOn_vR j).comp continuous_real_toNNReal.continuousOn hm
      · exact (hω'.2.1.comp continuous_real_toNNReal).continuousOn
    have hA : ContinuousOn (fun s : ℝ => lyapT κ xL xR ρL ρR (Fin.last nR) a α β lam μ
        (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 s.toNNReal)) (Icc 0 (σ : ℝ)) :=
      (contDiff_lyapT κ xL xR ρL ρR (Fin.last nR) ha α β lam μ).continuous.comp_continuousOn hpath
    have hI : ContinuousOn (fun x : ℝ => ∫ s in (0 : ℝ)..x, Ito.itoGen (lyapT κ xL xR ρL ρR (Fin.last nR) a α β lam μ)
        (coordA xL xR G VL VR (fun _ _ => 0) s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
        (densA G W VL VR (fun _ _ => 0) s ω)) (Icc 0 (σ : ℝ)) := by
      have h := intervalIntegral.continuousOn_primitive_interval ((intervalIntegrable_iff').1 hgi)
      rwa [uIcc_of_le σ.coe_nonneg] at h
    have hcomp := (hA.sub hI).comp_continuous hinner hmaps
    refine hcomp.congr fun t => ?_
    simp only [tightMart, Function.comp_apply, Pi.sub_apply, Real.toNNReal_coe, ← hσdef, coord_eq_pathCoord hω]
  · have h0 : angLoc G T W VL VR B ζ n ω = 0 := angLoc_of_not_mem hω n
    simp only [tightMart, h0, min_zero]
    exact continuous_const

include hgood in
omit hE hGm hGc hT hx in
/-- **The martingale along a good path**, with the explicit generator where the far gap and spread exceed the
cutoff level (before `r`). -/
theorem tightMart_eq {a : ℝ} (hκ : 0 ≤ κ) (ha : 0 < a) (α β lam μ : ℝ) (n : ℕ) {ω : Ω} (hω : ω ∈ G)
    (r : ℝ≥0) (hr : r ≤ angLoc G T W VL VR B ζ n ω)
    (hreg : ∀ s : ℝ, s ∈ Ico 0 (r : ℝ) → a < VR (Fin.last nR) s.toNNReal ω - W s.toNNReal ω ∧
      a < VR (Fin.last nR) s.toNNReal ω - VR 0 s.toNNReal ω) :
    tightMart κ xL xR ρL ρR G T W VL VR B ζ a α β lam μ n r ω =
      lyapT κ xL xR ρL ρR (Fin.last nR) a α β lam μ
          (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 r) -
        ∫ s in (0 : ℝ)..(r : ℝ), genT κ ρL ρR (Fin.last nR) α β lam μ (W · ω) (fun i t => VL i t ω)
          (fun j t => VR j t ω) s := by
  have hω' := hgood ω hω
  have hp := hω'.1
  have hσζ : (angLoc G T W VL VR B ζ n ω : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime hω'
  have hrζ : (r : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hr) hσζ
  simp only [tightMart, min_eq_left hr, coord_eq_pathCoord hω]
  congr 1
  refine intervalIntegral.integral_congr_ae ((Measure.ae_ne volume (r : ℝ)).mono fun s hsr hs => ?_)
  rw [uIoc_of_le r.coe_nonneg] at hs
  have hs' : s ∈ Ico 0 (r : ℝ) := ⟨hs.1.le, lt_of_le_of_ne hs.2 hsr⟩
  have hsζ := Sec2.toNNReal_lt_of_mem_Icc hrζ (Ico_subset_Icc_self hs')
  simp only [densA_eq_angDens hω]
  refine (itoGen_lyapT_pathCoord hp hκ ha (Fin.last nR) α β lam μ 0 0 hsζ (hreg s hs').1
    (hreg s hs').2).trans ?_
  simp only [genT, Real.toNNReal_coe]

include hgood in
omit hE hGm hGc hT hx in
/-- **The pathwise lower bound.** If before `r ≤ σ_n` the state stays in the tight region
`{e < X < K, e < Δ < ε₁ X}` (`e ≥ 2a`), and the start has `K (1 + 1/η) ≤ x^{R,0} − x^{L,0}`, then
`lyapT(r) + α λ (θ/2) K^{λ−2} r ≤ M_r`. -/
theorem le_tightMart {a : ℝ} (hκ : 0 ≤ κ) (ha : 0 < a) {α β lam μ ε₁ η θ K e : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hlam : 0 < lam) (hlam2 : lam ≤ 2) (hμ : 0 < μ) (hε₁ : ε₁ < 1) (hη : 0 < η) (hθ : 0 ≤ θ) (hae : a < e)
    (hK : 0 < K) (hstart : K * (1 + 1 / η) ≤ xR 0 - xL 0)
    (h1 : ((∑ j, ρR j) - (κ / 2 - 2)) + κ * lam / 2 + (∑ j, |ρR j|) * (ε₁ / (1 - ε₁)) +
      (∑ i, |ρL i|) * η ≤ -(θ / 2))
    (h2 : (κ / 2 - 4 - ∑ j, ρR j) + κ * μ / 2 + (∑ j, |ρR j|) * (ε₁ / (1 - ε₁)) + (∑ i, |ρL i|) * η ≤ 0)
    (n : ℕ) {ω : Ω} (hω : ω ∈ G) (r : ℝ≥0) (hr : r ≤ angLoc G T W VL VR B ζ n ω)
    (hreg : ∀ s : ℝ≥0, s < r → 0 < tightLev K ε₁ e (W s ω, VR 0 s ω, VR (Fin.last nR) s ω)) :
    lyapT κ xL xR ρL ρR (Fin.last nR) a α β lam μ
        (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 r) +
      α * lam * (θ / 2) * K ^ (lam - 2) * r ≤ tightMart κ xL xR ρL ρR G T W VL VR B ζ a α β lam μ n r ω := by
  have hω' := hgood ω hω
  have hp := hω'.1
  have hf := hp.isForcePath
  have hσζ : (angLoc G T W VL VR B ζ n ω : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime hω'
  have hrζ : (r : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hr) hσζ
  -- the region at real times `s ∈ [0, r)`
  have hregR : ∀ s : ℝ, s ∈ Ico 0 (r : ℝ) → 0 < tightLev K ε₁ e
      (W s.toNNReal ω, VR 0 s.toNNReal ω, VR (Fin.last nR) s.toNNReal ω) := fun s hs =>
    hreg _ ((Real.toNNReal_lt_iff_lt_coe hs.1).2 hs.2)
  have hsζ : ∀ s : ℝ, s ∈ Ico 0 (r : ℝ) → (s.toNNReal : ℝ≥0∞) < ζ ω := fun s hs =>
    Sec2.toNNReal_lt_of_mem_Icc hrζ (Ico_subset_Icc_self hs)
  have hcut : ∀ s : ℝ, s ∈ Ico 0 (r : ℝ) → a < VR (Fin.last nR) s.toNNReal ω - W s.toNNReal ω ∧
      a < VR (Fin.last nR) s.toNNReal ω - VR 0 s.toNNReal ω := fun s hs => by
    obtain ⟨⟨-, h2⟩, -, h4⟩ := tightLev_pos_iff.1 (hregR s hs)
    exact ⟨hae.trans h2, hae.trans h4⟩
  -- the generator bound on `[0, r)`
  set C₁ := α * lam * (θ / 2) * K ^ (lam - 2) with hC₁
  have hgen : ∀ s : ℝ, s ∈ Ico 0 (r : ℝ) →
      genT κ ρL ρR (Fin.last nR) α β lam μ (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s ≤ -C₁ := by
    intro s hs
    obtain ⟨⟨hXK, hXe⟩, hΔε, hΔe⟩ := tightLev_pos_iff.1 (hregR s hs)
    simp only at hXK hXe hΔε hΔe
    set t := s.toNNReal
    have hX : 0 < VR (Fin.last nR) t ω - W t ω := (ha.trans hae).trans hXe
    have hD := le_gap_of_lt hω' (hsζ s hs)
    have hR0X : VR 0 t ω - W t ω ≤ VR (Fin.last nR) t ω - W t ω := by
      have := hf.monotone_vR (hsζ s hs) (Fin.zero_le (Fin.last nR)); simp only at this; linarith
    have hL0 : K / η ≤ W t ω - VL 0 t ω := by
      have e1 : K * (1 + 1 / η) = K + K / η := by ring
      linarith
    have hL0p : 0 < W t ω - VL 0 t ω := (div_pos hK hη).trans_le hL0
    have hXη : VR (Fin.last nR) t ω - W t ω ≤ η * (W t ω - VL 0 t ω) := by
      have : K ≤ η * (W t ω - VL 0 t ω) := by
        rw [div_le_iff₀ hη] at hL0; linarith
      linarith
    have hb := genT_le_of_region hp (hsζ s hs) hα hβ hlam hμ hε₁ hX ((ha.trans hae).trans hΔe) hΔε.le hL0p
      hXη h1 h2
    have e : genT κ ρL ρR (Fin.last nR) α β lam μ (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
        (s.toNNReal : ℝ) = genT κ ρL ρR (Fin.last nR) α β lam μ (W · ω) (fun i t => VL i t ω)
          (fun j t => VR j t ω) s := by simp only [genT, Real.toNNReal_coe]
    rw [e] at hb
    have hpow : K ^ (lam - 2) ≤ (VR (Fin.last nR) t ω - W t ω) ^ (lam - 2) :=
      Real.rpow_le_rpow_of_nonpos hX hXK.le (by linarith)
    have hc : 0 ≤ α * lam * (θ / 2) := by positivity
    have := mul_le_mul_of_nonneg_left hpow hc
    simp only [hC₁]
    linarith
  -- integrate
  have hreg' := tightMart_eq hgood hκ ha α β lam μ n hω r hr hcut (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR)
  rw [hreg']
  have hgi := intervalIntegrable_tightGen hgood ha α β lam μ n hω (κ := κ) (xL := xL) (xR := xR)
    (ρL := ρL) (ρR := ρR) (T := T) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ)
  have hgir : IntervalIntegrable (fun s : ℝ => genT κ ρL ρR (Fin.last nR) α β lam μ (W · ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) s) volume 0 r := by
    have h1 := hgi.mono_set (by
      rw [uIcc_of_le r.coe_nonneg, uIcc_of_le (angLoc G T W VL VR B ζ n ω).coe_nonneg]
      exact Icc_subset_Icc_right (by exact_mod_cast hr))
    refine h1.congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 ((Measure.ae_ne volume (r : ℝ)).mono fun s hsr hs => ?_)
    rw [uIoc_of_le r.coe_nonneg] at hs
    have hs' : s ∈ Ico 0 (r : ℝ) := ⟨hs.1.le, lt_of_le_of_ne hs.2 hsr⟩
    simp only [coord_eq_pathCoord hω, densA_eq_angDens hω]
    refine (itoGen_lyapT_pathCoord hp hκ ha (Fin.last nR) α β lam μ 0 0 (hsζ s hs') (hcut s hs').1
      (hcut s hs').2).trans ?_
    simp only [genT, Real.toNNReal_coe]
  have hint : ∫ s in (0 : ℝ)..(r : ℝ), genT κ ρL ρR (Fin.last nR) α β lam μ (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) s ≤ ∫ _s in (0 : ℝ)..(r : ℝ), -C₁ := by
    refine intervalIntegral.integral_mono_ae_restrict r.coe_nonneg hgir intervalIntegrable_const ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 ((Measure.ae_ne volume (r : ℝ)).mono fun s hsr hs => ?_)
    exact hgen s ⟨hs.1, lt_of_le_of_ne hs.2 hsr⟩
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
  linarith

end Mart

/-! ### The constants -/

section Const

/-- **The exponents and the region parameters.** For `κ > 0`, a right total `s ∈ (κ/2 − 4, κ/2 − 2)` and weight
masses `AR, AL ≥ 0` there are `λ ∈ (0, 1]`, `μ > 0`, `ε₁ ∈ (0, 1/2]`, `η > 0` with both bracket conditions of
`genT_le_of_region` (with `θ = κ/2 − 2 − s`). -/
theorem exists_tight_consts {κ s AR AL : ℝ} (hκ : 0 < κ) (hs1 : κ / 2 - 4 < s) (hs2 : s < κ / 2 - 2)
    (hAR : 0 ≤ AR) (hAL : 0 ≤ AL) :
    ∃ lam μ ε₁ η : ℝ, 0 < lam ∧ lam ≤ 1 ∧ 0 < μ ∧ 0 < ε₁ ∧ ε₁ ≤ 1 / 2 ∧ 0 < η ∧
      (s - (κ / 2 - 2)) + κ * lam / 2 + AR * (ε₁ / (1 - ε₁)) + AL * η ≤ -((κ / 2 - 2 - s) / 2) ∧
      (κ / 2 - 4 - s) + κ * μ / 2 + AR * (ε₁ / (1 - ε₁)) + AL * η ≤ 0 := by
  set θ₁ := κ / 2 - 2 - s with hθ₁
  set θ₂ := s - (κ / 2 - 4) with hθ₂
  have h₁ : 0 < θ₁ := by rw [hθ₁]; linarith
  have h₂ : 0 < θ₂ := by rw [hθ₂]; linarith
  set θm := min θ₁ θ₂ with hθm
  have hm : 0 < θm := lt_min h₁ h₂
  have hm1 : θm ≤ θ₁ := min_le_left _ _
  have hm2 : θm ≤ θ₂ := min_le_right _ _
  refine ⟨min (θ₁ / (2 * κ)) 1, θ₂ / (2 * κ), min (1 / 2) (θm / (16 * (AR + 1))), θm / (8 * (AL + 1)),
    lt_min (by positivity) one_pos, min_le_right _ _, by positivity, lt_min (by norm_num) (by positivity),
    min_le_left _ _, by positivity, ?_, ?_⟩
  all_goals
    have hl : κ * min (θ₁ / (2 * κ)) 1 / 2 ≤ θ₁ / 4 := by
      have : min (θ₁ / (2 * κ)) 1 ≤ θ₁ / (2 * κ) := min_le_left _ _
      have e : κ * (θ₁ / (2 * κ)) / 2 = θ₁ / 4 := by field_simp; ring
      nlinarith
    have hmu : κ * (θ₂ / (2 * κ)) / 2 = θ₂ / 4 := by field_simp; ring
    set ε₁ := min (1 / 2) (θm / (16 * (AR + 1))) with hε₁
    have hε₁0 : 0 < ε₁ := lt_min (by norm_num) (by positivity)
    have hε₁h : ε₁ ≤ 1 / 2 := min_le_left _ _
    have hε₁m : ε₁ ≤ θm / (16 * (AR + 1)) := min_le_right _ _
    have hq : ε₁ / (1 - ε₁) ≤ 2 * ε₁ := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have he1 : AR * (ε₁ / (1 - ε₁)) ≤ θm / 8 := by
      have h1 : AR * (ε₁ / (1 - ε₁)) ≤ AR * (2 * ε₁) := mul_le_mul_of_nonneg_left hq hAR
      have h2 : AR * (2 * ε₁) ≤ (AR + 1) * (2 * (θm / (16 * (AR + 1)))) := by
        have := mul_le_mul_of_nonneg_left hε₁m (by linarith : (0 : ℝ) ≤ 2 * (AR + 1))
        nlinarith
      have e : (AR + 1) * (2 * (θm / (16 * (AR + 1)))) = θm / 8 := by field_simp; ring
      linarith
    have he2 : AL * (θm / (8 * (AL + 1))) ≤ θm / 8 := by
      rw [show AL * (θm / (8 * (AL + 1))) = θm / 8 * (AL / (AL + 1)) by field_simp]
      have : AL / (AL + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith
  · linarith
  · linarith

end Const

/-! ### Values of the Lyapunov function -/

section Values

theorem cutPow_nonneg {a : ℝ} (ha : 0 < a) (p x : ℝ) : 0 ≤ cutPow a p x := by
  unfold cutPow
  rcases le_or_gt x (a / 2) with hx | hx
  · have : 2 * x / a - 1 ≤ 0 := by rw [sub_nonpos, div_le_one ha]; linarith
    rw [Real.smoothTransition.zero_of_nonpos this, zero_mul]
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.rpow_nonneg (by linarith) _)

theorem cutPow_le {a p x : ℝ} (hx : 0 ≤ x) : cutPow a p x ≤ x ^ p := by
  unfold cutPow
  have h0 := Real.rpow_nonneg hx p
  calc Real.smoothTransition (2 * x / a - 1) * x ^ p ≤ 1 * x ^ p :=
        mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _) h0
    _ = x ^ p := one_mul _

theorem cutPow_eq {a p x : ℝ} (ha : 0 < a) (hx : a < x) : cutPow a p x = x ^ p :=
  (cutPow_eventuallyEq ha p hx).self_of_nhds

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ}
  {ρR : Fin (nR + 1) → ℝ}

theorem lyapT_nonneg {a α β lam μ : ℝ} (ha : 0 < a) (hα : 0 ≤ α) (hβ : 0 ≤ β) (j₁ : Fin (nR + 1))
    (p : SCoord nL (nR + 1) × ℝ) : 0 ≤ lyapT κ xL xR ρL ρR j₁ a α β lam μ p := by
  unfold lyapT
  have := cutPow_nonneg ha lam (farX κ xL xR ρL ρR j₁ p)
  have := cutPow_nonneg ha μ (sprD j₁ p)
  have := cutPow_nonneg ha (-μ) (farX κ xL xR ρL ρR j₁ p)
  positivity

/-- The value at the start `((x^L, x^R, 0), 0)`. -/
theorem lyapT_angInit_le {a α β lam μ : ℝ} (ha : 0 < a) (hα : 0 ≤ α) (hβ : 0 ≤ β) (j₁ : Fin (nR + 1))
    (hX : 0 < xR j₁) (hΔ : 0 ≤ xR j₁ - xR 0) :
    lyapT κ xL xR ρL ρR j₁ a α β lam μ (angInit xL xR) ≤
      α * xR j₁ ^ lam + β * ((xR j₁ - xR 0) ^ μ * xR j₁ ^ (-μ)) := by
  have hfx : farX κ xL xR ρL ρR j₁ (angInit xL xR) = xR j₁ := by
    simp [farX, drv, driftLin, angInit]
  have hsd : sprD j₁ (angInit xL xR) = xR j₁ - xR 0 := rfl
  unfold lyapT
  rw [hfx, hsd]
  have h1 := cutPow_le (a := a) (p := lam) hX.le
  have h2 := cutPow_le (a := a) (p := μ) hΔ
  have h3 := cutPow_le (a := a) (p := -μ) hX.le
  have h4 := mul_le_mul h2 h3 (cutPow_nonneg ha _ _) (Real.rpow_nonneg hΔ _)
  have h5 := mul_le_mul_of_nonneg_left h1 hα
  have h6 := mul_le_mul_of_nonneg_left h4 hβ
  linarith

/-- **At a bad face the Lyapunov function is at least `1`**: `X ≥ K` or `Δ ≥ ε₁ X`, with `α = K^{−λ}`,
`β = ε₁^{−μ}`. -/
theorem one_le_lyapT {a lam μ K ε₁ : ℝ} (ha : 0 < a) (hlam : 0 < lam) (hμ : 0 < μ) (hK : 0 < K) (hε₁ : 0 < ε₁)
    (j₁ : Fin (nR + 1)) {p : SCoord nL (nR + 1) × ℝ} (hX : a < farX κ xL xR ρL ρR j₁ p) (hD : a < sprD j₁ p)
    (hbad : K ≤ farX κ xL xR ρL ρR j₁ p ∨ ε₁ * farX κ xL xR ρL ρR j₁ p ≤ sprD j₁ p) :
    1 ≤ lyapT κ xL xR ρL ρR j₁ a (K ^ (-lam)) (ε₁ ^ (-μ)) lam μ p := by
  set X := farX κ xL xR ρL ρR j₁ p with hXdef
  set Δ := sprD j₁ p with hΔdef
  have hX0 : 0 < X := ha.trans hX
  have hD0 : 0 < Δ := ha.trans hD
  unfold lyapT
  rw [← hXdef, ← hΔdef, cutPow_eq ha hX, cutPow_eq ha hD, cutPow_eq ha hX]
  have hA : 0 ≤ K ^ (-lam) * X ^ lam := by positivity
  have hB : 0 ≤ ε₁ ^ (-μ) * (Δ ^ μ * X ^ (-μ)) := by positivity
  rcases hbad with h | h
  · have h1 : K ^ lam ≤ X ^ lam := Real.rpow_le_rpow hK.le h hlam.le
    have h2 : K ^ (-lam) * K ^ lam = 1 := by
      rw [Real.rpow_neg hK.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hK _).ne']
    have h3 : K ^ (-lam) * K ^ lam ≤ K ^ (-lam) * X ^ lam :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hK.le _)
    linarith
  · have h1 : (ε₁ * X) ^ μ ≤ Δ ^ μ := Real.rpow_le_rpow (by positivity) h hμ.le
    have h2 : ε₁ ^ (-μ) * ((ε₁ * X) ^ μ * X ^ (-μ)) = 1 := by
      rw [Real.mul_rpow hε₁.le hX0.le, Real.rpow_neg hε₁.le, Real.rpow_neg hX0.le]
      have := (Real.rpow_pos_of_pos hε₁ μ).ne'
      have := (Real.rpow_pos_of_pos hX0 μ).ne'
      field_simp
    have h3 : ε₁ ^ (-μ) * ((ε₁ * X) ^ μ * X ^ (-μ)) ≤ ε₁ ^ (-μ) * (Δ ^ μ * X ^ (-μ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hX0.le _))
        (Real.rpow_nonneg hε₁.le _)
    linarith

end Values

/-! ### The main estimate -/

section Main

/-- The value of `min x n` for `x : WithTop ℝ≥0`. -/
theorem exists_min_coe (x : WithTop ℝ≥0) (n : ℝ≥0) :
    ∃ r : ℝ≥0, min x (n : WithTop ℝ≥0) = r ∧ r ≤ n ∧ (∀ s : ℝ≥0, s < r → (s : WithTop ℝ≥0) < x) ∧
      ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < x → t ≤ n → t ≤ r := by
  induction x using WithTop.recTopCoe with
  | top => exact ⟨n, min_eq_right le_top, le_rfl, fun s _ => WithTop.coe_lt_top s, fun _ _ h => h⟩
  | coe y =>
    refine ⟨min y n, by push_cast; rfl, min_le_right _ _, fun s hs => ?_, fun t ht htn => ?_⟩
    · exact_mod_cast hs.trans_le (min_le_left _ _)
    · exact le_min (by exact_mod_cast ht.le) htn

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}

/-- **A tight right cluster with total in `(κ/2 − 4, κ/2 − 2)` is swallowed or the evolution dies, with probability
at least `1/2`.** For `κ > 0`, a right side with at least two marks (`0 < nR`) and total in `(κ/2 − 4, κ/2 − 2)`,
there are `ε₀, K₀ > 0` such that from every separated ordered start with `x^{R,0} > 0`, right spread
`x^{R,last} − x^{R,0} ≤ ε₀ x^{R,last}` and cross gap `x^{R,0} − x^{L,0} ≥ K₀ x^{R,last}`, every evolution has
`P(ζ = ∞, no two marks on the same side ever meet) ≤ 1/2`. -/
theorem measure_noMeet_le_half (hκ : 0 < κ) (hnR : 0 < nR) (hs1 : κ / 2 - 4 < ∑ j, ρR j)
    (hs2 : ∑ j, ρR j < κ / 2 - 2) :
    ∃ ε₀ K₀ : ℝ, 0 < ε₀ ∧ 0 < K₀ ∧ ∀ (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ),
      IsOrderedForceWord xL xR → (∀ i j, xL i < xR j) → 0 < xR 0 →
      xR (Fin.last nR) - xR 0 ≤ ε₀ * xR (Fin.last nR) → K₀ * xR (Fin.last nR) ≤ xR 0 - xL 0 →
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
        {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
        {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞},
        IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
        P {ω | ζ ω = ⊤ ∧ ∀ t, ¬ SameSideMeet (fun i t => VL i t ω) (fun j t => VR j t ω) t} ≤
          ENNReal.ofReal (1 / 2) := by
  obtain ⟨lam, μ, ε₁, η, hlam, hlam1, hμ, hε₁, hε₁h, hη, h1, h2⟩ := exists_tight_consts hκ hs1 hs2
    (AR := ∑ j, |ρR j|) (AL := ∑ i, |ρL i|)
    (Finset.sum_nonneg fun j _ => abs_nonneg (ρR j)) (Finset.sum_nonneg fun i _ => abs_nonneg (ρL i))
  set θ := κ / 2 - 2 - ∑ j, ρR j with hθ
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  set K₁ : ℝ := (4 : ℝ) ^ (1 / lam) with hK₁
  have hK₁pos : 0 < K₁ := by positivity
  have hK₁lam : K₁ ^ lam = 4 := by
    rw [hK₁, ← Real.rpow_mul (by norm_num), one_div_mul_cancel hlam.ne', Real.rpow_one]
  set q : ℝ := (1 / 4 : ℝ) ^ (1 / μ) with hq
  have hqpos : 0 < q := by positivity
  have hqμ : q ^ μ = 1 / 4 := by
    rw [hq, ← Real.rpow_mul (by norm_num), one_div_mul_cancel hμ.ne', Real.rpow_one]
  refine ⟨ε₁ * q, K₁ * (1 + 1 / η), by positivity, by positivity, ?_⟩
  intro xL xR hF hsep hxR0 hΔ₀ hD₀ Ω mΩ P _ 𝓕 W VL VR B ζ hE
  set S := {ω | ζ ω = ⊤ ∧ ∀ t, ¬ SameSideMeet (fun i t => VL i t ω) (fun j t => VR j t ω) t} with hSdef
  by_cases hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · have hnt := ae_ne_top_of_thresholdCondition hE hthr
    calc P S ≤ P {ω | ¬ ζ ω ≠ ⊤} := measure_mono fun ω hω => not_not.2 hω.1
      _ = 0 := ae_iff.1 hnt
      _ ≤ _ := bot_le
  obtain ⟨T, G, hT, hGm, hGc, hgood⟩ := exists_setup hκ hE hthr
  have hP := hE.1.isProbabilityMeasure'
  have hEa := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hx : 0 < xR 0 - xL 0 := sub_pos.2 (hsep 0 0)
  set j₁ := Fin.last nR with hj₁
  have hj₁0 : (0 : Fin (nR + 1)) ≠ j₁ := by
    intro h
    have := congrArg Fin.val h
    simp [hj₁] at this
    omega
  set X₀ := xR j₁ with hX₀
  have hx0 : xR 0 ≤ X₀ := hF.2.2.1 (Fin.zero_le _)
  have hX₀pos : 0 < X₀ := hxR0.trans_le hx0
  set K := K₁ * X₀ with hK
  have hKpos : 0 < K := mul_pos hK₁pos hX₀pos
  set α := K ^ (-lam) with hα
  set β := ε₁ ^ (-μ) with hβ
  have hα0 : 0 ≤ α := Real.rpow_nonneg hKpos.le _
  have hβ0 : 0 ≤ β := Real.rpow_nonneg hε₁.le _
  set e : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with he
  have hepos : ∀ m, 0 < e m := fun m => Nat.one_div_pos_of_nat
  set a : ℕ → ℝ := fun m => e m / 2 with ha
  have hapos : ∀ m, 0 < a m := fun m => half_pos (hepos m)
  have hae : ∀ m, a m < e m := fun m => half_lt_self (hepos m)
  set C₁ := α * lam * (θ / 2) * K ^ (lam - 2) with hC₁
  have hC₁pos : 0 < C₁ := by
    have : 0 < α := Real.rpow_pos_of_pos hKpos _
    have : 0 < K ^ (lam - 2) := Real.rpow_pos_of_pos hKpos _
    positivity
  have hstart : K * (1 + 1 / η) ≤ xR 0 - xL 0 := by
    have e1 : K * (1 + 1 / η) = K₁ * (1 + 1 / η) * X₀ := by rw [hK]; ring
    rw [e1]; exact hD₀
  -- the exit times, sampling times and martingales
  set τ : ℕ → Ω → ℝ≥0∞ := fun m => tightExit Gᶜ ζ K ε₁ (e m) W VR j₁ with hτdef
  have hτ : ∀ m, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (τ m ω : WithTop ℝ≥0) := fun m =>
    isStoppingTime_tightExit hEa.2.1 (hEa.2.2.2.1 0) (hEa.2.2.2.1 j₁)
      (fun t => (measurableSet_good_usual hGm hGc t).compl) (fun ω hω => by
        have hF' := (hgood ω (not_not.1 hω)).1.isForcePath
        exact ⟨hF'.continuousOn_w, hF'.continuousOn_vR 0, hF'.continuousOn_vR j₁⟩)
  set ρ : ℕ → Ω → WithTop ℝ≥0 := fun m ω => min (τ m ω : WithTop ℝ≥0) ((m : ℝ≥0) : WithTop ℝ≥0) with hρdef
  have hρ : ∀ m, IsStoppingTime (usualAugmentation 𝓕 P) (ρ m) := fun m => (hτ m).min_const (m : ℝ≥0)
  have hρle : ∀ m ω, ρ m ω ≤ ((m : ℝ≥0) : WithTop ℝ≥0) := fun m ω => min_le_right _ _
  set M : ℕ → ℝ≥0 → Ω → ℝ := fun m => tightMart κ xL xR ρL ρR G T W VL VR B ζ (a m) α β lam μ m with hMdef
  have hM : ∀ m, Martingale (M m) (usualAugmentation 𝓕 P) P := fun m =>
    martingale_tightMart hE hGm hGc hgood hT hx (hapos m) α β lam μ m
  have hMrc : ∀ m ω t, ContinuousWithinAt (M m · ω) (Ici t) t := fun m ω t =>
    (continuous_tightMart hgood (hapos m) α β lam μ m ω).continuousWithinAt
  set Z : ℕ → Ω → ℝ := fun m => stoppedValue (M m) (ρ m) with hZdef
  have hZi : ∀ m, Integrable (Z m) P := fun m =>
    (tendsto_lintegral_stoppedValue_dyadicUpperTime (hM m).supermartingale (hMrc m) (hρ m) (hρle m)).2.1
  have hos : ∀ m, ∫ ω, M m 0 ω ∂P = ∫ ω, Z m ω ∂P := fun m => by
    have h := setIntegral_stoppedValue_eq_of_rightContinuous (hM m) (hMrc m)
      (isStoppingTime_const (usualAugmentation 𝓕 P) 0) (hρ m) (fun ω => bot_le)
      (T := m) (hρle m) MeasurableSet.univ
    simpa only [setIntegral_univ, stoppedValue_const] using h
  -- the initial value
  have hM0 : ∀ m ω, M m 0 ω = lyapT κ xL xR ρL ρR j₁ (a m) α β lam μ (angInit xL xR) := by
    intro m ω
    have h0 : min (0 : ℝ≥0) (angLoc G T W VL VR B ζ m ω) = 0 := min_eq_left bot_le
    simp only [hMdef, tightMart, h0, NNReal.coe_zero, intervalIntegral.integral_same, sub_zero]
    congr 1
    by_cases hω : ω ∈ G
    · have hω' := hgood ω hω
      have hF' := hω'.1.isForcePath
      simp only [coordA, Sec2.TwoSeed.brownG, hω, ↓reduceIte, angInit, hω'.2.2.1, hF'.vL_zero, hF'.vR_zero]
    · simp only [coordA, Sec2.TwoSeed.brownG, hω, ↓reduceIte, angInit]
  have hstartV : ∀ m, lyapT κ xL xR ρL ρR j₁ (a m) α β lam μ (angInit xL xR) ≤ 1 / 2 := by
    intro m
    refine (lyapT_angInit_le (hapos m) hα0 hβ0 j₁ hX₀pos (sub_nonneg.2 hx0)).trans ?_
    have hA : α * X₀ ^ lam = 1 / 4 := by
      rw [hα, hK, Real.mul_rpow hK₁pos.le hX₀pos.le, Real.rpow_neg hK₁pos.le, Real.rpow_neg hX₀pos.le,
        hK₁lam]
      have := (Real.rpow_pos_of_pos hX₀pos lam).ne'
      field_simp
    have hΔ0 : 0 ≤ xR j₁ - xR 0 := sub_nonneg.2 hx0
    have hB1 : (xR j₁ - xR 0) ^ μ ≤ (ε₁ * q * X₀) ^ μ := Real.rpow_le_rpow hΔ0 hΔ₀ hμ.le
    have hB2 : β * ((ε₁ * q * X₀) ^ μ * X₀ ^ (-μ)) = 1 / 4 := by
      rw [hβ, Real.mul_rpow (by positivity) hX₀pos.le, Real.mul_rpow hε₁.le hqpos.le, hqμ,
        Real.rpow_neg hε₁.le, Real.rpow_neg hX₀pos.le]
      have := (Real.rpow_pos_of_pos hX₀pos μ).ne'
      have := (Real.rpow_pos_of_pos hε₁ μ).ne'
      field_simp
    have hB3 : β * ((xR j₁ - xR 0) ^ μ * X₀ ^ (-μ)) ≤ β * ((ε₁ * q * X₀) ^ μ * X₀ ^ (-μ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB1 (Real.rpow_nonneg hX₀pos.le _)) hβ0
    linarith
  -- the pathwise lower bound
  have hlow : ∀ m, ∀ ω ∈ G, ∀ r : ℝ≥0, ρ m ω = r → (∀ s : ℝ≥0, s < r → (s : WithTop ℝ≥0) < τ m ω) →
      lyapT κ xL xR ρL ρR j₁ (a m) α β lam μ (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0
          (min r (angLoc G T W VL VR B ζ m ω))) + C₁ * (min r (angLoc G T W VL VR B ζ m ω) : ℝ≥0) ≤ Z m ω := by
    intro m ω hω r hr hrτ
    have hZ : Z m ω = M m r ω := by simp only [hZdef, stoppedValue, hr, WithTop.untopD_coe]
    rw [hZ, hMdef]
    simp only
    rw [tightMart_min]
    refine le_tightMart hgood hκ.le (hapos m) hα0 hβ0 hlam (by linarith) hμ (by linarith) hη hθ0.le (hae m)
      hKpos hstart h1 h2 m hω _ (min_le_right _ _) fun s hs => ?_
    have hs' : (s : WithTop ℝ≥0) < τ m ω := hrτ s (hs.trans_le (min_le_left _ _))
    exact (pos_of_lt_tightExit (N := Gᶜ) (not_not.2 hω) hs').2
  -- on `{ζ = ∞, no meet}` the sampled values are eventually at least `1`
  have hev : ∀ ω ∈ G, ζ ω = ⊤ → (∀ t, ¬ SameSideMeet (fun i t => VL i t ω) (fun j t => VR j t ω) t) →
      ∀ᶠ m in atTop, 1 ≤ Z m ω := by
    intro ω hω hζ hnm
    have hω' := hgood ω hω
    have hp := hω'.1
    have hf := hp.isForcePath
    have hωN : ω ∉ Gᶜ := not_not.2 hω
    have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω := fun t => by rw [hζ]; exact ENNReal.coe_lt_top
    set Xf : ℝ≥0 → ℝ := fun t => VR j₁ t ω - W t ω with hXf
    set Df : ℝ≥0 → ℝ := fun t => VR j₁ t ω - VR 0 t ω with hDf
    have hDpos : ∀ t, 0 < Df t := by
      intro t
      have h0 := hf.monotone_vR (hlt t) (Fin.zero_le j₁)
      simp only at h0
      rcases h0.lt_or_eq with h | h
      · simp only [hDf]; linarith
      · exact absurd (Or.inr ⟨0, j₁, hj₁0, h⟩) (hnm t)
    have hDX : ∀ t, Df t ≤ Xf t := fun t => by
      have := hf.w_le_vR (hlt t) 0
      simp only [hDf, hXf]; linarith
    have huniv : ∀ {g : ℝ≥0 → ℝ}, ContinuousOn g {t | (t : ℝ≥0∞) < ζ ω} → Continuous g := fun hg =>
      continuousOn_univ.1 (hg.mono fun t _ => hlt t)
    have hDc : Continuous Df := (huniv (hf.continuousOn_vR j₁)).sub (huniv (hf.continuousOn_vR 0))
    have hlevc : ∀ m, ContinuousOn (fun t => tightProc K ε₁ (e m) W VR j₁ t ω - zeroProc t ω)
        {t | (t : ℝ≥0∞) < ζ ω} := fun m =>
      continuousOn_tightProc hf.continuousOn_w (hf.continuousOn_vR 0) (hf.continuousOn_vR j₁)
    have hδ : ∀ t₁ : ℝ≥0, ∃ δ > 0, ∀ s ≤ t₁, δ ≤ Df s := fun t₁ => by
      obtain ⟨δ, hδ, h⟩ := exists_pos_le_of_continuousOn_Icc hDc.continuousOn (t := t₁) fun s _ => hDpos s
      exact ⟨δ, hδ, fun s hs => h s ⟨bot_le, hs⟩⟩
    have hev_e : ∀ δ > 0, ∀ᶠ m : ℕ in atTop, e m < δ := fun δ hδ =>
      (tendsto_one_div_add_atTop_nhds_zero_nat).eventually (gt_mem_nhds hδ)
    have hev_n : ∀ t₁ : ℝ≥0, ∀ᶠ m : ℕ in atTop, t₁ ≤ (m : ℝ≥0) := fun t₁ => by
      filter_upwards [eventually_ge_atTop ⌈(t₁ : ℝ)⌉₊] with m hm
      have : (t₁ : ℝ) ≤ m := (Nat.le_ceil _).trans (by exact_mod_cast hm)
      exact_mod_cast this
    have hev_σ : ∀ t₁ : ℝ≥0, ∀ᶠ m : ℕ in atTop, t₁ ≤ angLoc G T W VL VR B ζ m ω := fun t₁ => by
      obtain ⟨n₀, hn₀⟩ := exists_forall_le_angLoc hω' hgood hω (hT.2.1 ω) (hlt t₁)
      exact eventually_atTop.2 ⟨n₀, hn₀⟩
    by_cases hbad : ∃ t₀, ¬ (Xf t₀ < K ∧ Df t₀ < ε₁ * Xf t₀)
    · obtain ⟨t₀, ht₀⟩ := hbad
      obtain ⟨δ, hδ, hδle⟩ := hδ t₀
      filter_upwards [hev_e δ hδ, hev_n t₀, hev_σ t₀] with m hm1 hm2 hm3
      have hlev0 : tightLev K ε₁ (e m) (W t₀ ω, VR 0 t₀ ω, VR j₁ t₀ ω) ≤ 0 := by
        by_contra hc
        obtain ⟨⟨h1', -⟩, h3', -⟩ := tightLev_pos_iff.1 (not_le.1 hc)
        exact ht₀ ⟨h1', h3'⟩
      have hτle : τ m ω ≤ t₀ := by
        simp only [hτdef, tightExit, Sec7.zeroOn_of_notMem hωN]
        exact firstMeet_le_of (hlt t₀) (by simpa [tightProc, zeroProc] using hlev0)
      obtain ⟨m₁, hm₁, -, hlevm₁⟩ := tightLev_tightExit hωN (hlevc m) (hτle.trans_lt (hlt t₀))
      have hτm : τ m ω = m₁ := hm₁
      have hm₁t₀ : m₁ ≤ t₀ := by rw [hτm] at hτle; exact_mod_cast hτle
      have hX₁ : e m < Xf m₁ := lt_of_lt_of_le hm1 ((hδle m₁ hm₁t₀).trans (hDX m₁))
      have hD₁ : e m < Df m₁ := lt_of_lt_of_le hm1 (hδle m₁ hm₁t₀)
      have hbad₁ : K ≤ Xf m₁ ∨ ε₁ * Xf m₁ ≤ Df m₁ := by
        by_contra hc
        push Not at hc
        have : 0 < tightLev K ε₁ (e m) (W m₁ ω, VR 0 m₁ ω, VR j₁ m₁ ω) :=
          tightLev_pos_iff.2 ⟨⟨hc.1, hX₁⟩, hc.2, hD₁⟩
        linarith
      have hρm : ρ m ω = m₁ := by
        simp only [hρdef]
        rw [show (τ m ω : WithTop ℝ≥0) = (m₁ : WithTop ℝ≥0) from hτm]
        exact min_eq_left (by exact_mod_cast hm₁t₀.trans hm2)
      have hrτ : ∀ s : ℝ≥0, s < m₁ → (s : WithTop ℝ≥0) < τ m ω := fun s hs => by
        rw [show (τ m ω : WithTop ℝ≥0) = (m₁ : WithTop ℝ≥0) from hτm]; exact_mod_cast hs
      have hb := hlow m ω hω m₁ hρm hrτ
      rw [min_eq_left (hm₁t₀.trans hm3)] at hb
      have hone : 1 ≤ lyapT κ xL xR ρL ρR j₁ (a m) α β lam μ
          (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 m₁) := by
        refine one_le_lyapT (hapos m) hlam hμ hKpos hε₁ j₁ ?_ ?_ ?_
        · rw [farX_pathCoord hp j₁ 0 (hlt m₁)]; exact (hae m).trans hX₁
        · rw [sprD_pathCoord]; exact (hae m).trans hD₁
        · rw [farX_pathCoord hp j₁ 0 (hlt m₁), sprD_pathCoord]; exact hbad₁
      have : 0 ≤ C₁ * (m₁ : ℝ) := mul_nonneg hC₁pos.le m₁.coe_nonneg
      linarith
    · push Not at hbad
      set t₁ : ℝ≥0 := (1 / C₁).toNNReal with ht₁
      obtain ⟨δ, hδ, hδle⟩ := hδ t₁
      filter_upwards [hev_e δ hδ, hev_n t₁, hev_σ t₁] with m hm1 hm2 hm3
      have hpos : ∀ s ≤ t₁, 0 < tightLev K ε₁ (e m) (W s ω, VR 0 s ω, VR j₁ s ω) := fun s hs =>
        tightLev_pos_iff.2 ⟨⟨(hbad s).1, lt_of_lt_of_le hm1 ((hδle s hs).trans (hDX s))⟩, (hbad s).2,
          lt_of_lt_of_le hm1 (hδle s hs)⟩
      have ht₁τ : (t₁ : ℝ≥0∞) < τ m ω := lt_tightExit_of_forall hωN (hlevc m) (hlt t₁) hpos
      obtain ⟨r, hr, -, hrτ, hrge⟩ := exists_min_coe (τ m ω : WithTop ℝ≥0) (m : ℝ≥0)
      have ht₁r : t₁ ≤ r := hrge t₁ ht₁τ hm2
      have hb := hlow m ω hω r hr hrτ
      have hmin : (t₁ : ℝ) ≤ (min r (angLoc G T W VL VR B ζ m ω) : ℝ≥0) := by
        exact_mod_cast le_min ht₁r hm3
      have hL0 := lyapT_nonneg (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) (lam := lam) (μ := μ)
        (hapos m) hα0 hβ0 j₁
        (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 (min r (angLoc G T W VL VR B ζ m ω)))
      have ht₁v : (t₁ : ℝ) = 1 / C₁ := Real.coe_toNNReal _ (by positivity)
      have hC : C₁ * (t₁ : ℝ) = 1 := by rw [ht₁v]; field_simp
      have := mul_le_mul_of_nonneg_left hmin hC₁pos.le
      linarith
  -- Fatou and Markov
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := (measure_eq_zero_iff_ae_notMem.1 hGc).mono fun ω h => not_not.1 h
  have hZnn : ∀ m, 0 ≤ᵐ[P] Z m := fun m => by
    filter_upwards [hGae] with ω hω
    obtain ⟨r, hr, -, hrτ, -⟩ := exists_min_coe (τ m ω : WithTop ℝ≥0) (m : ℝ≥0)
    have hb := hlow m ω hω r hr hrτ
    have hL0 := lyapT_nonneg (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) (lam := lam) (μ := μ)
      (hapos m) hα0 hβ0 j₁
      (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 (min r (angLoc G T W VL VR B ζ m ω)))
    have : 0 ≤ C₁ * ((min r (angLoc G T W VL VR B ζ m ω) : ℝ≥0) : ℝ) := mul_nonneg hC₁pos.le (NNReal.coe_nonneg _)
    show 0 ≤ Z m ω
    linarith
  have hEZ : ∀ m, ∫ ω, Z m ω ∂P ≤ 1 / 2 := fun m => by
    rw [← hos m]
    simp only [hM0, integral_const, probReal_univ, one_smul]
    exact hstartV m
  set f : ℕ → Ω → ℝ≥0∞ := fun m ω => ENNReal.ofReal (Z m ω) with hfdef
  have hfm : ∀ m, AEMeasurable (f m) P := fun m => (hZi m).aemeasurable.ennreal_ofReal
  set g : ℕ → Ω → ℝ≥0∞ := fun m => (hfm m).mk (f m) with hgdef
  have hgm : ∀ m, Measurable (g m) := fun m => (hfm m).measurable_mk
  have hfg : ∀ᵐ ω ∂P, ∀ m, f m ω = g m ω := ae_all_iff.2 fun m => (hfm m).ae_eq_mk
  have hlim : Measurable fun ω => liminf (fun m => g m ω) atTop := Measurable.liminf hgm
  have hsub : ∀ᵐ ω ∂P, ω ∈ S → 1 ≤ liminf (fun m => g m ω) atTop := by
    filter_upwards [hfg, hGae] with ω hfgω hωG hωS
    refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [hev ω hωG hωS.1 hωS.2] with m hm
    rw [← hfgω m, hfdef]
    simpa using ENNReal.ofReal_le_ofReal hm
  have hS : P S ≤ P {ω | 1 ≤ liminf (fun m => g m ω) atTop} := measure_mono_ae (hsub.mono fun ω h hω => h hω)
  have hmk := mul_meas_ge_le_lintegral₀ (μ := P) hlim.aemeasurable 1
  rw [one_mul] at hmk
  have hfat := lintegral_liminf_le' (μ := P) (u := atTop) fun m => (hgm m).aemeasurable
  have hgint : ∀ m, ∫⁻ ω, g m ω ∂P ≤ ENNReal.ofReal (1 / 2) := fun m => by
    rw [← lintegral_congr_ae (hfm m).ae_eq_mk, hfdef]
    simp only
    rw [← ofReal_integral_eq_lintegral_ofReal (hZi m) (hZnn m)]
    exact ENNReal.ofReal_le_ofReal (hEZ m)
  have hliminf : liminf (fun m => ∫⁻ ω, g m ω ∂P) atTop ≤ ENNReal.ofReal (1 / 2) :=
    Filter.liminf_le_of_frequently_le' (Frequently.of_forall hgint)
  exact hS.trans (hmk.trans (hfat.trans hliminf))

end Main

end TrialsHi3

end Sec7

end InteractingSLE
