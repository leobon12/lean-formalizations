import QuantumZipper.Proofs.Zipper.B2Markov
import QuantumZipper.Proofs.LQG.PalmNorm
import QuantumZipper.Proofs.Loewner.RevMapExtension
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Complex.RealDeriv

/-!
# E1 (definitions and the change of variables `y = F x`)

`blueprint/E_BRANCH_BLUEPRINT.md` §2 and §4, node E1 (Palm-zip field clause); split and exact
statements in `handoff/E1-PLAN.md`. Paper: Sheffield, *Conformal weldings of random surfaces*,
arXiv:1012.4797, Theorem 4.5 (p. 51) and Lemma 5.6 (pp. 66–68); the route (Palm formula plus
coordinate change, no Itô calculus) is the blueprint's.

## Definitions (blueprint §2, "zipped-coordinate data")

For a driver `V`, a time `t`, a normalizer `ϖ` and a real point `x`:
* `IsLive V t x` : `t < τ_x = realHitTime V x` (`x` not swallowed by time `t`);
  `liveNeg V t = {x < 0 | IsLive V t x}`;
* `Fder V t x = exp ∫₀ᵗ 2/(realRevMap V s x)² ds` (`F'(x)`, `F = realRevMap V t`);
* `varpiT V t ϖ = ϖ.map (revMap V t)` (`ϖ_t`);
* `rhoT κ V t ϖ x = e^{−γ q_t/2} F'(x) ρ_{ϖ_t}(F x)` with `ρ_{ϖ_t} = rhoNorm γ 𝔥₀ ϖ_t`
  (`PalmNorm`); since `e^{γ 𝔥₀(y)/2} = |y|` this is the blueprint's
  `|F x| F'(x) exp(−(γ/2)(∫𝔥₀ dϖ_t + q_t) − (γ²/4) k_t(F x) + (γ²/8) kk_t)`;
* `targetField κ V t ϖ x Y = addConst (N_{ϖ_t}(ofFun (𝔥₀ + (γ/2)(neumannH (F x) · − k_t)) + Y)) (−q_t)`;
* `mReg`, `nuPalm`: `m = evalReg h⁰ ϖ` (AUDIT7 Z2) and `ν = qBoundaryMeasure γ (addConst h⁰ (−m))`;
* `hFix κ v t Y = coordChange (𝔥₀ + Y) (revMap v t) Q`, `mFix κ v t ϖ Y = evalReg (𝔥₀ + Y) ϖ_t + q_t`
  (what `h⁰` and `m` are when `Y_t = 𝔥₀ + Y` and the driver is the fixed path `v`).

## Results

* `not_isLive_zero`: `0` is never live (`realHitTime v 0 = 0` when `v 0 = 0`);
  `Icc_inter_isLive_eq`: on `[−δ,0]` the live points are those of `liveNeg`.
* `isRealRevSol_of_isCRevSol`, `isOpen_setOf_isLive`, `isOpen_liveNeg`: the live set is open
  (complex solutions from nearby real points are real; own elementary argument).
* `hasDerivWithinAt_realRevMap`, `injOn_realRevMap`: on a set of live points, `F = realRevMap v t`
  is injective with derivative `Fder v t` (from A2-ext, `RevMapExtension`).
* **`lintegral_image_realRevMap`** (E1-CV): for measurable `s` of live points and `g ≥ 0`,
  `∫⁻_{F s} g = ∫⁻_s F' · (g ∘ F)` (mathlib `lintegral_image_eq_lintegral_abs_deriv_mul`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open B2 PalmNorm

/-! ## 1. Definitions -/

/-- `x` is not swallowed by the reverse flow of `V` by time `t`. -/
def IsLive (V : ℝ → ℝ) (t x : ℝ) : Prop := ENNReal.ofReal t < realHitTime V x

/-- The live negative half-line `{x < 0 | t < τ_x}`. -/
def liveNeg (V : ℝ → ℝ) (t : ℝ) : Set ℝ := {x | x < 0 ∧ IsLive V t x}

/-- `F'(x) = exp ∫₀ᵗ 2/(realRevMap V s x)² ds`. -/
def Fder (V : ℝ → ℝ) (t x : ℝ) : ℝ :=
  Real.exp (∫ s in (0 : ℝ)..t, 2 / (realRevMap V s x) ^ 2)

/-- `ϖ_t = ϖ.map (revMap V t)`. -/
def varpiT (V : ℝ → ℝ) (t : ℝ) (ϖ : Measure ℂ) : Measure ℂ := ϖ.map (revMap V t)

/-- The Palm-zip density `ρ_t(x;V) = e^{−γ q_t/2} F'(x) ρ_{ϖ_t}(F x)`. -/
def rhoT (κ : ℝ) (V : ℝ → ℝ) (t : ℝ) (ϖ : Measure ℂ) (x : ℝ) : ℝ :=
  Real.exp (-(Real.sqrt κ / 2 * qt κ V t ϖ)) * Fder V t x *
    rhoNorm (Real.sqrt κ) (h0rev κ) (varpiT V t ϖ) (realRevMap V t x)

/-- The field on the right side of E1, for a given free field sample `Y`. -/
def targetField (κ : ℝ) (V : ℝ → ℝ) (t : ℝ) (ϖ : Measure ℂ) (x : ℝ) (Y : FieldSample) :
    FieldSample :=
  addConst (normAt (varpiT V t ϖ)
    (ofFun (shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V t ϖ) (realRevMap V t x)) + Y))
    (-(qt κ V t ϖ))

/-- Fixed-driver version of `h⁰`: `coordChange (𝔥₀ + Y) (revMap v t) Q`. -/
def hFix (κ : ℝ) (v : ℝ → ℝ) (t : ℝ) (Y : FieldSample) : FieldSample :=
  coordChange (ofFun (h0rev κ) + Y) (revMap v t) (Qc (Real.sqrt κ))

/-- Fixed-driver version of `m`: `evalReg (𝔥₀ + Y) ϖ_t + q_t`. -/
def mFix (κ : ℝ) (v : ℝ → ℝ) (t : ℝ) (ϖ : Measure ℂ) (Y : FieldSample) : ℝ :=
  evalReg (ofFun (h0rev κ) + Y) (varpiT v t ϖ) + qt κ v t ϖ

variable {Ω : Type*}

/-- `m = evalReg h⁰ ϖ` (AUDIT7 Z2). -/
def mReg (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ) (ω : Ω) : ℝ :=
  evalReg (h0f κ T B X ω) ϖ

/-- `ν = qBoundaryMeasure γ (addConst h⁰ (−m))`. -/
def nuPalm (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ) (ω : Ω) :
    Measure ℝ :=
  qBoundaryMeasure (Real.sqrt κ) (addConst (h0f κ T B X ω) (-(mReg κ T B X ϖ ω)))

/-- Hypotheses on the normalizer `ϖ` (blueprint §2: any admissible probability measure with
compact support in `ℍ`; Frostman for RC1). Both the arc of §2 and `foldedCircle (3 * I) 1`
(AUDIT8) satisfy them. -/
structure IsNormalizer (ϖ : Measure ℂ) : Prop where
  prob : IsProbabilityMeasure ϖ
  adm : IsAdmissibleH ϖ
  cpt : ∃ K : Set ℂ, IsCompact K ∧ K ⊆ H ∧ ϖ Kᶜ = 0
  frost : ∃ α C : ℝ, 0 < α ∧ IsFrostman ϖ α C

/-! ## 2. Live points -/

variable {v : ℝ → ℝ} {t : ℝ}

/-- `0` is never live: there is no real reverse solution started at `v 0 = 0`. -/
theorem not_isLive_zero (hv0 : v 0 = 0) (t : ℝ) : ¬ IsLive v t 0 := by
  have h : realHitTime v 0 = 0 := by
    refine le_antisymm (iSup_le fun T => iSup_le fun hT => iSup_le fun ⟨u, hu⟩ => ?_) bot_le
    exfalso
    have h0 := hu.2 0 ⟨le_rfl, hT⟩
    rw [intervalIntegral.integral_same, hv0] at h0
    exact h0.1 (by rw [h0.2]; ring)
  simp [IsLive, h]

theorem exists_isRealRevSol_of_isLive {x : ℝ} (h : IsLive v t x) : ∃ u, IsRealRevSol v x t u :=
  RealLine.exists_isRealRevSol_of_lt_realHitTime h

theorem Icc_inter_isLive_eq (hv0 : v 0 = 0) (δ : ℝ) :
    Icc (-δ) 0 ∩ {x | IsLive v t x} = Icc (-δ) 0 ∩ liveNeg v t := by
  ext x
  refine ⟨fun ⟨hx, hl⟩ => ⟨hx, lt_of_le_of_ne hx.2 fun h => ?_, hl⟩,
    fun ⟨hx, hl⟩ => ⟨hx, hl.2⟩⟩
  subst h
  exact not_isLive_zero hv0 t hl

/-- A complex reverse solution from a real point is real (conjugation symmetry and uniqueness),
so it gives a real reverse solution. -/
theorem isRealRevSol_of_isCRevSol {y T : ℝ} {u : ℝ → ℂ}
    (hu : RevMapExtension.IsCRevSol v (y : ℂ) T u) :
    IsRealRevSol v y T (fun s => (u s).re) := by
  have hc := RevMapExtension.isCRevSol_conj hu
  rw [Complex.conj_ofReal] at hc
  have hreal : ∀ s ∈ Icc (0 : ℝ) T, u s = ((u s).re : ℂ) := fun s hs => by
    have h1 : (starRingEnd ℂ) (u s) = u s := (RevMapExtension.isCRevSol_unique hc hu hs)
    exact (Complex.conj_eq_iff_re.1 h1).symm
  refine ⟨Complex.continuous_re.comp_continuousOn hu.1, fun s hs => ⟨fun h0 => ?_, ?_⟩⟩
  · exact (hu.2 s hs).1 (by rw [hreal s hs]; exact_mod_cast h0)
  · have heq := congrArg Complex.re (hu.2 s hs).2
    have hint : (∫ r in (0 : ℝ)..s, 2 / u r) = ((∫ r in (0 : ℝ)..s, 2 / (u r).re : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs.1] at hr
      have hr' : r ∈ Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans hs.2⟩
      conv_lhs => rw [hreal r hr']
      push_cast; rfl
    rw [hint] at heq
    simpa using heq

/-- The set of live points is open. -/
theorem isOpen_setOf_isLive (hv : Continuous v) : IsOpen {x | IsLive v t x} := by
  rw [Metric.isOpen_iff]
  intro x hx
  obtain ⟨T', h1⟩ := lt_iSup_iff.1 (show ENNReal.ofReal t < realHitTime v x from hx)
  obtain ⟨hT', h2⟩ := lt_iSup_iff.1 h1
  obtain ⟨⟨w, hw⟩, h3⟩ := lt_iSup_iff.1 h2
  obtain ⟨c, -, ρ, hρ, hball⟩ := RevMapExtension.exists_ball_isCRevSol hv hT' hw
  refine ⟨ρ, hρ, fun y hy => ?_⟩
  have hy' : (y : ℂ) ∈ Metric.ball (x : ℂ) ρ := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, ← Real.dist_eq]
    exact hy
  obtain ⟨u, hu, -⟩ := hball y hy'
  exact lt_of_lt_of_le h3 (RealLine.ofReal_le_realHitTime hT' (isRealRevSol_of_isCRevSol hu))

theorem isOpen_liveNeg (hv : Continuous v) (t : ℝ) : IsOpen (liveNeg v t) :=
  isOpen_Iio.inter (isOpen_setOf_isLive (t := t) hv)

/-! ## 3. The change of variables `y = F x` (E1-CV) -/

theorem Fder_pos (V : ℝ → ℝ) (t x : ℝ) : 0 < Fder V t x := Real.exp_pos _

/-- On a set of live points, `realRevMap v t` has derivative `Fder v t` (within the set). -/
theorem hasDerivWithinAt_realRevMap (hv : Continuous v) (ht : 0 ≤ t) {s : Set ℝ}
    (hs : ∀ x ∈ s, IsLive v t x) {x : ℝ} (hx : x ∈ s) :
    HasDerivWithinAt (realRevMap v t) (Fder v t x) s x := by
  obtain ⟨U, hUo, hsU, -, hd, -, -, hR, hD, -⟩ :=
    RevMapExtension.exists_revMapExt_extension hv ht s hs
  have hda : HasDerivAt (RevMapExtension.revMapExt v t)
      (deriv (RevMapExtension.revMapExt v t) x) (x : ℂ) :=
    ((hd _ (hsU x hx)).differentiableAt (hUo.mem_nhds (hsU x hx))).hasDerivAt
  have hre := hda.real_of_complex
  rw [hD x hx, Complex.ofReal_re] at hre
  refine hre.hasDerivWithinAt.congr_of_mem (fun y hy => ?_) hx
  rw [hR y hy, Complex.ofReal_re]

/-- `realRevMap v t` is injective on live points. -/
theorem injOn_realRevMap (hv : Continuous v) (ht : 0 ≤ t) {s : Set ℝ}
    (hs : ∀ x ∈ s, IsLive v t x) : InjOn (realRevMap v t) s :=
  ((RealLine.strictMonoOn_realRevMap hv ht).mono fun x hx =>
    exists_isRealRevSol_of_isLive (hs x hx)).injOn

/-- **E1-CV.** Change of variables `y = F x`, `F = realRevMap v t`, on a measurable set of live
points. -/
theorem lintegral_image_realRevMap (hv : Continuous v) (ht : 0 ≤ t) {s : Set ℝ}
    (hsm : MeasurableSet s) (hs : ∀ x ∈ s, IsLive v t x) (g : ℝ → ℝ≥0∞) :
    ∫⁻ y in realRevMap v t '' s, g y =
      ∫⁻ x in s, ENNReal.ofReal (Fder v t x) * g (realRevMap v t x) := by
  rw [lintegral_image_eq_lintegral_abs_deriv_mul hsm
    (fun x hx => hasDerivWithinAt_realRevMap hv ht hs hx) (injOn_realRevMap hv ht hs)]
  simp_rw [abs_of_pos (Fder_pos v t _)]

end E1
end QuantumZipper
