/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.SLE.All
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution

/-!
# κ > 4 boundary geometry: the exact statements of Part A, and the source collar

Packet PROVE-ZHAN-GT4-A. Source: Astra, *Follow-up proofs and dependency audit*, Part A
(`source/external/AstraIG1/ig1_followup_proofs.txt` L129–L960, ruling R38). This file fixes the exact Lean form
of the three geometric outputs of Part A that other packets consume, and proves the deterministic consequence of
the source collar (A.0) used in A.4 ("the source-collar lemma gives `a < 0 < b`").

## The statements

* `StoppingCollarStatement κ` — **(G7)** (A.4, L833–L838; the LP4 input, specification p. 483, [Zha10, Corollary
  6.1]): for ordinary chordal `SLE_κ` and every positive finite stopping time `T`, almost surely
  (G5) `f_T((c, d)) ⊂ ℍ` (`HasInteriorInverseBoundary`) and every real point strictly between the swallowed real
  extremes has a relative upper-half-plane neighbourhood inside `K_T` (`HasRealCollar`).
* `FirstSwallowCrosscutStatement κ` — **A.3** (L648–L655): at the first swallowing time `T_x` of a deterministic
  `x ≠ 0`, `∂(ℍ \ K_{T_x}) ∩ ℍ` is a simple crosscut with real endpoints on opposite sides of `0`; for `κ ≥ 8` the
  endpoint on the side of `x` is `x`, for `4 < κ < 8` it lies strictly farther from `0` than `x`.
* `SeparatedTwoForceStatement κ` — **A.5** (L841–L846): for the two-force law `SLE_κ(ρ_L; ρ_R)` with marks
  `p_L < 0 < p_R` and `ρ_L, ρ_R ≥ κ/2 − 2`, the terminal hull is bounded by two simple proper crosscuts from `∞`
  to points of `(p_L, 0)` and `(0, p_R)`, and it has positive distance from every compact subset of
  `(−∞, p_L] ∪ [p_R, ∞)`.

## Conventions

The driver of ordinary `SLE_κ` is QuantumZipper's `drive κ B ω = √κ B` and the hulls are `fwdHull`; the
centered maps are `fwdMap W T z = g_T(z) − W_T` and `fwdMapInv W T w = g_T⁻¹(W_T + w)`. A real point `x` is
**swallowed by time `T`** when its centered real flow has no solution on `[0, T]` (`IsSwallowedBy`); these are
the real points of the closed hull, the source's `K̄_T ∩ ℝ = [a, b]`. "Strictly between the swallowed real
extremes" is "strictly between two swallowed real points", which avoids `sInf`/`sSup` junk. The open inverse
interval `(c − W_T, d − W_T)` (centered) is the complement of the closure of the centered images of the real
points alive at `T` (`exteriorCoords`): `g_T` maps the exterior rays `(−∞, a)`, `(b, ∞)` increasingly onto
`(−∞, c)`, `(d, ∞)`.

## Proved here

* `isSwallowedBy_of_halfBall`: if `K_T` contains `ℍ ∩ B(0, ε)`, every real `x` with `|x| < ε` is swallowed by
  `T` (a real point alive at `T` keeps a neighbourhood of nearby points of `ℍ` unswallowed,
  `not_mem_fwdHull_of_isForwardSol`).
* `ae_forall_exists_isSwallowedBy_neg_pos`: for ordinary `SLE_κ`, `κ > 4`, almost surely at every `t > 0`
  there are swallowed real points on both sides of `0` (with A.0 = [RS05, Lemma 7.3],
  `ae_forall_sleHull_halfBall_of_four_lt`): the source's `a(t) < 0 < b(t)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open QuantumZipper

/-! ### Deterministic notions -/

/-- **The real point `x` is swallowed by time `T`** under the driver `W`: the centered real flow from `x` has no
solution on `[0, T]` (it has met the driver at some time `≤ T`; for `x = 0` it starts on the driver). -/
def IsSwallowedBy (W : ℝ → ℝ) (x T : ℝ) : Prop :=
  ¬ ∃ v, IsForwardSol W (x : ℂ) T v

/-- **The real collar** (G7, second part): every real point `y` strictly between two real points swallowed by
time `T` has a relative upper-half-plane neighbourhood inside the hull `K_T`. -/
def HasRealCollar (W : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ x y z : ℝ, IsSwallowedBy W x T → IsSwallowedBy W z T → x < y → y < z →
    ∃ ε > (0 : ℝ), ∀ w ∈ H, ‖w - y‖ < ε → w ∈ fwdHull W T

/-- **The exterior inverse coordinates** at time `T`: the closure of the centered images `g_T(x) − W_T` of the
real points `x` alive at `T`. Its complement is the open inverse interval `(c − W_T, d − W_T)` of the hull. -/
def exteriorCoords (W : ℝ → ℝ) (T : ℝ) : Set ℝ :=
  closure {r : ℝ | ∃ x : ℝ, (∃ v, IsForwardSol W (x : ℂ) T v) ∧ (fwdMap W T x).re = r}

/-- **The inverse boundary is interior on the open inverse interval** ((G5), `f_T((c, d)) ⊂ ℍ`): at every
real `u` off the exterior coordinates, the centered inverse map `g_T⁻¹(W_T + ·)` has a boundary value, and it
lies in `ℍ`. -/
def HasInteriorInverseBoundary (W : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ u : ℝ, u ∉ exteriorCoords W T →
    ∃ p ∈ H, Tendsto (fwdMapInv W T) (𝓝[H] (u : ℂ)) (𝓝 p)

/-- **A simple crosscut of `ℍ` with real endpoints**, parametrized by `[0, 1]`: continuous and injective on
`[0, 1]`, with its open part in `ℍ` and real endpoints `γ 0`, `γ 1`. -/
def IsRealCrosscut (γ : ℝ → ℂ) : Prop :=
  ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Icc 0 1) ∧ γ '' Ioo 0 1 ⊆ H ∧ (γ 0).im = 0 ∧ (γ 1).im = 0

/-- **A simple proper crosscut of `ℍ` from a real point to `∞`**, parametrized by `[0, ∞)`: continuous and
injective, `γ 0` real, `γ (0, ∞) ⊆ ℍ`, and `|γ s| → ∞`. -/
def IsProperCrosscut (γ : ℝ → ℂ) : Prop :=
  ContinuousOn γ (Ici 0) ∧ InjOn γ (Ici 0) ∧ γ '' Ioi 0 ⊆ H ∧ (γ 0).im = 0 ∧
    Tendsto (fun s => ‖γ s‖) atTop atTop

/-! ### The named statements of Part A -/

/-- **(G7): the inverse boundary and the real collar at a stopping time** (Part A.4, L833–L838; the LP4 input,
specification p. 483: "[Zha10, Corollary 6.1] … every real point strictly between the swallowed real extremes has
a relative upper-half-plane neighborhood inside the swallowed hull"). For ordinary chordal `SLE_κ` driven by a
Brownian motion `B` of a filtration `𝓕` and every positive finite `𝓕`-stopping time `T`, almost surely
`f_T((c(T), d(T))) ⊂ ℍ` and every `x ∈ (a(T), b(T))` has a relative upper-half-plane neighbourhood in `K_T`. -/
def StoppingCollarStatement (κ : ℝ) : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓕 B P →
    ∀ T : Ω → ℝ≥0, IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0)) → (∀ ω, 0 < T ω) →
      ∀ᵐ ω ∂P, HasInteriorInverseBoundary (drive κ B ω) (T ω) ∧
        HasRealCollar (drive κ B ω) (T ω)

/-- **A.3: the first swallowing of a fixed real point** (L648–L655). For ordinary chordal `SLE_κ` and a
deterministic `x ≠ 0`, almost surely `x` is swallowed at a finite time `σ = T_x`, and `∂(ℍ \ K_σ) ∩ ℍ` is the open
part of a simple crosscut `γ` with real endpoints `γ 0 < 0 < γ 1`. If `κ ≥ 8`, the endpoint on the side of `x` is
`x`; if `4 < κ < 8`, it lies strictly farther from `0` than `x`. -/
def FirstSwallowCrosscutStatement (κ : ℝ) : Prop :=
  4 < κ → ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    ∀ x : ℝ, x ≠ 0 → ∀ᵐ ω ∂P, ∃ σ : ℝ, RealSwallowAt (drive κ B ω) x σ ∧
      ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re < 0 ∧ 0 < (γ 1).re ∧
        frontier (H \ fwdHull (drive κ B ω) σ) ∩ H = γ '' Ioo 0 1 ∧
        (x < 0 → (8 ≤ κ → (γ 0).re = x) ∧ (κ < 8 → (γ 0).re < x)) ∧
        (0 < x → (8 ≤ κ → (γ 1).re = x) ∧ (κ < 8 → x < (γ 1).re))

/-- The terminal hull of a driver `w` on `[0, ζ)`: the union of its hulls `K_t`, `t < ζ`. -/
def terminalHull (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Set ℂ :=
  ⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < ζ), fwdHull (fun s : ℝ => w s.toNNReal) t

/-- **A.5: the separated two-force boundary input** (L841–L846, L898–L901). For `κ > 4`, marks `p_L < 0 < p_R`
and weights `ρ_L, ρ_R ≥ κ/2 − 2` (the source's `ρ = C(κ − 4)`, `C ≥ 1/2`), almost surely the integrated
`SLE_κ(ρ_L; ρ_R)` evolution lives forever, the frontier in `ℍ` of the complement of its terminal hull is the union of
two simple proper crosscuts from `∞` to a point of `(p_L, 0)` and to a point of `(0, p_R)`, and the terminal hull
has positive distance from every compact subset of `(−∞, p_L] ∪ [p_R, ∞)`. (The source warns not to strengthen the
last assertion to a uniform distance from the whole unbounded rays.) -/
def SeparatedTwoForceStatement (κ : ℝ) : Prop :=
  4 < κ → ∀ (pL pR ρL ρR : ℝ), pL < 0 → 0 < pR → κ / 2 - 2 ≤ ρL → κ / 2 - 2 ≤ ρR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ ![pL] ![pR] ![ρL] ![ρR] P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ζ ω = ⊤ ∧
          (∃ γL γR : ℝ → ℂ, IsProperCrosscut γL ∧ IsProperCrosscut γR ∧
            pL < (γL 0).re ∧ (γL 0).re < 0 ∧ 0 < (γR 0).re ∧ (γR 0).re < pR ∧
            frontier (H \ terminalHull (fun t => W t ω) (ζ ω)) ∩ H = γL '' Ioi 0 ∪ γR '' Ioi 0) ∧
          ∀ C : Set ℝ, IsCompact C → C ⊆ Iic pL ∪ Ici pR →
            ∃ δ > (0 : ℝ), ∀ z ∈ terminalHull (fun t => W t ω) (ζ ω), ∀ x ∈ C, δ ≤ ‖z - x‖

/-! ### The source collar gives swallowed real points on both sides (A.0, A.4) -/

/-- **A real point inside a half-ball of the hull is swallowed.** If `K_T ⊇ ℍ ∩ B(0, ε)`, then every real `x`
with `|x| < ε` is swallowed by time `T`: a real point alive on `[0, T]` keeps the points of `ℍ` near it outside
`K_T` (`not_mem_fwdHull_of_isForwardSol`). -/
theorem isSwallowedBy_of_halfBall {W : ℝ → ℝ} (hW : Continuous W) {T ε : ℝ} (hT : 0 ≤ T)
    (hK : ∀ z ∈ H, ‖z‖ < ε → z ∈ fwdHull W T) {x : ℝ} (hx : |x| < ε) : IsSwallowedBy W x T := by
  rintro ⟨u, hu⟩
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hT hu
  set E := Real.exp (2 / δ ^ 2 * T) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- a point `x + i s` with `s` small
  set s := min ((ε - |x|) / 2) (δ / (2 * E)) with hs
  have hs0 : 0 < s := lt_min (by linarith) (by positivity)
  set z : ℂ := (x : ℂ) + (s : ℂ) * I with hz
  have hzim : 0 < z.im := by simp [hz, hs0]
  have hzx : ‖z - (x : ℂ)‖ = s := by
    rw [hz, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs0]
  have hzn : ‖z‖ < ε := by
    calc ‖z‖ ≤ ‖(x : ℂ)‖ + ‖z - (x : ℂ)‖ := norm_le_norm_add_norm_sub' z x
      _ = |x| + s := by rw [hzx, Complex.norm_real, Real.norm_eq_abs]
      _ < ε := by have := min_le_left ((ε - |x|) / 2) (δ / (2 * E)); linarith
  have hzp : ‖z - (x : ℂ)‖ * E < δ := by
    rw [hzx]
    have h1 : s ≤ δ / (2 * E) := min_le_right _ _
    calc s * E ≤ δ / (2 * E) * E := mul_le_mul_of_nonneg_right h1 hE0.le
      _ = δ / 2 := by field_simp
      _ < δ := by linarith
  exact not_mem_fwdHull_of_isForwardSol hW hu hδ hlow hzim hzp (hK z hzim hzn)

/-- **Swallowed real points on both sides of the source** (A.4: "The source-collar lemma gives `a < 0 < b`").
For ordinary chordal `SLE_κ`, `κ > 4`, almost surely at every time `t > 0` some negative and some positive real point
are swallowed by time `t`. From A.0 = [RS05, Lemma 7.3] (`ae_forall_sleHull_halfBall_of_four_lt`) and
`isSwallowedBy_of_halfBall`. -/
theorem ae_forall_exists_isSwallowedBy_neg_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 4 < κ) :
    ∀ᵐ ω ∂P, ∀ t > (0 : ℝ), ∃ x < (0 : ℝ), ∃ y > (0 : ℝ),
      IsSwallowedBy (drive κ B ω) x t ∧ IsSwallowedBy (drive κ B ω) y t := by
  filter_upwards [ae_forall_sleHull_halfBall_of_four_lt hB hκ, hB.cont] with ω hω hc t ht
  obtain ⟨ε, hε, hK⟩ := hω t ht
  have hW : Continuous (drive κ B ω) := drive_continuous hc
  have hx : |-(ε / 2)| < ε := by rw [abs_neg, abs_of_pos (half_pos hε)]; linarith
  have hy : |ε / 2| < ε := by rw [abs_of_pos (half_pos hε)]; linarith
  exact ⟨-(ε / 2), by linarith, ε / 2, half_pos hε,
    isSwallowedBy_of_halfBall hW ht.le hK hx, isSwallowedBy_of_halfBall hW ht.le hK hy⟩

end InteractingSLE.ZhanGT4
