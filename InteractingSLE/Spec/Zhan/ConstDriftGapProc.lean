/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.ConstDriftGapScale
import InteractingSLE.Spec.Zhan.AvoidMart
import InteractingSLE.Spec.Zhan.StripNoncollisionGen
import InteractingSLE.Spec.Sec2.AddMarksFlow

/-!
# The upper-gap diffusion as an adapted process; finite quadratic variation of `φ(X)`

Packet PROVE-ZHAN-A6. For a Brownian motion `B` with every path continuous and `B 0 = 0`, the upper gap (3.15)

  `X_t = q − √κ B_t + Λ_t`,  `Λ_t = ∫₀ᵗ (tanh(X_u/2) − σ) du`,

is realized for every `ω` by the adapted tamed flow `Sec2.markFlow` (`upGapDrift`, `upGapProc`). Its exponential
`λ̃ = e^Λ` is a positive state solving `λ̃' = Ψ(λ̃, B)`, `Ψ(λ̃, b) = λ̃ (tanh(x/2) − σ)`, `x = q − √κ b + log λ̃`
(`upGapState_eq_integral`). For a nonnegative `C³` function `φ` with `φ'(tanh(x/2) − σ) + (κ/2)φ'' ≤ 0` the
observable `Φ = φ(x)` of the state has nonpositive Itô drift and `∂_b Φ = −√κ φ'(x)` (`itoGen_upGapObs`,
`partialSnd_upGapObs`), so PROVE-ZHAN-B's `ae_bddAbove_integral_sq_partialSnd` gives, almost surely,
`∫₀^∞ κ φ'(X)² < ∞` (`ae_bdd_integral_sq_upGapProc`).

Uniqueness (`eqOn_upGapProc`): every continuous solution of (3.15) on `[0, T]` is `upGapProc` there
(`OneForce.eqOn_lipSol`, Grönwall for the `½`-Lipschitz `tanh(·/2)`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

/-! ### The observable of the state `(λ̃, b)` -/

section Obs

variable {κ σ q : ℝ}

/-- The upper gap read from the state `(λ̃, b)`: `x = q − √κ b + log λ̃`. -/
def upGapCoord (κ q : ℝ) (p : ℝ × ℝ) : ℝ := q - Real.sqrt κ * p.2 + Real.log p.1

/-- The state region `λ̃ > 0`. -/
def upGapRegion : Set (ℝ × ℝ) := {p | 0 < p.1}

/-- The field `Ψ(λ̃, b) = λ̃ (tanh(x/2) − σ)`. -/
def upGapField (κ σ q : ℝ) (p : ℝ × ℝ) : ℝ := p.1 * (Real.tanh (upGapCoord κ q p / 2) - σ)

theorem isOpen_upGapRegion : IsOpen upGapRegion := isOpen_lt continuous_const continuous_fst

theorem compl_upGapRegion_nonempty : upGapRegionᶜ.Nonempty := ⟨(0, 0), by simp [upGapRegion]⟩

theorem contDiffOn_upGapCoord (κ q : ℝ) : ContDiffOn ℝ (⊤ : ℕ∞) (upGapCoord κ q) upGapRegion := by
  unfold upGapCoord
  refine (contDiffOn_const.sub (contDiffOn_const.mul contDiffOn_snd)).add ?_
  exact contDiffOn_fst.log fun p hp => (show 0 < p.1 from hp).ne'

theorem contDiffAt_upGapCoord {p : ℝ × ℝ} (hp : p ∈ upGapRegion) {n : ℕ∞} :
    ContDiffAt ℝ n (upGapCoord κ q) p :=
  ((contDiffOn_upGapCoord κ q).contDiffAt (isOpen_upGapRegion.mem_nhds hp)).of_le
    (by exact_mod_cast le_top)

theorem continuous_tanh_half : Continuous fun x : ℝ => Real.tanh (x / 2) :=
  lipschitzWith_tanh_half.continuous

theorem continuousOn_upGapField (κ σ q : ℝ) : ContinuousOn (upGapField κ σ q) upGapRegion := by
  unfold upGapField
  refine continuousOn_fst.mul (ContinuousOn.sub ?_ continuousOn_const)
  exact continuous_tanh_half.comp_continuousOn (contDiffOn_upGapCoord κ q).continuousOn

theorem hasDerivAt_upGapCoord_snd (p : ℝ × ℝ) :
    HasDerivAt (fun y : ℝ => upGapCoord κ q (p.1, y)) (-Real.sqrt κ) p.2 := by
  have h := (((hasDerivAt_id p.2).const_mul (Real.sqrt κ)).const_sub q).add_const (Real.log p.1)
  simpa [upGapCoord] using h

theorem partialSnd_upGapCoord {p : ℝ × ℝ} (hp : p ∈ upGapRegion) :
    Ito.partialSnd (upGapCoord κ q) p = -Real.sqrt κ :=
  Ito.partialSnd_eq_of_hasDerivAt ((contDiffAt_upGapCoord hp (n := 1)).differentiableAt one_ne_zero)
    (hasDerivAt_upGapCoord_snd p)

theorem itoGen_upGapCoord {p : ℝ × ℝ} (hp : p ∈ upGapRegion) (v : ℝ) :
    Ito.itoGen (upGapCoord κ q) p v = v / p.1 := by
  have hp0 : 0 < p.1 := hp
  have hfst : Ito.partialFst (upGapCoord κ q) p v = v / p.1 := by
    refine Ito.partialFst_eq_of_hasDerivAt ((contDiffAt_upGapCoord hp (n := 1)).differentiableAt one_ne_zero)
      ?_
    have h1 : HasDerivAt (fun t : ℝ => p.1 + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p.1
    have h2 := (h1.log (by simpa using hp0.ne')).const_add (q - Real.sqrt κ * p.2)
    simpa [upGapCoord] using h2
  have hss : Ito.partialSndSnd (upGapCoord κ q) p = 0 :=
    Ito.partialSndSnd_eq_of_hasDerivAt (contDiffAt_upGapCoord hp) (g := fun _ => -Real.sqrt κ)
      (Eventually.of_forall fun y => partialSnd_upGapCoord (show (p.1, y) ∈ upGapRegion from hp0))
      (hasDerivAt_const _ _)
  rw [Ito.itoGen, hfst, hss]
  ring

variable {φ φ' φ'' : ℝ → ℝ}

/-- **The generator of `Φ = φ(x)` along the field**: `φ'(x)(tanh(x/2) − σ) + (κ/2) φ''(x)`. -/
theorem itoGen_upGapObs (hκ : 0 ≤ κ) (hφ : ContDiff ℝ 2 φ) (h1 : ∀ x, HasDerivAt φ (φ' x) x)
    (h2 : ∀ x, HasDerivAt φ' (φ'' x) x) {p : ℝ × ℝ} (hp : p ∈ upGapRegion) :
    Ito.itoGen (fun r => φ (upGapCoord κ q r)) p (upGapField κ σ q p) =
      φ' (upGapCoord κ q p) * (Real.tanh (upGapCoord κ q p / 2) - σ) +
        κ / 2 * φ'' (upGapCoord κ q p) := by
  have hp0 : 0 < p.1 := hp
  rw [itoGen_comp_of_hasDerivAt hφ.contDiffAt (contDiffAt_upGapCoord hp) (Eventually.of_forall h1) (h2 _),
    itoGen_upGapCoord hp, partialSnd_upGapCoord hp, upGapField]
  rw [neg_sq, Real.sq_sqrt hκ]
  field_simp

/-- `∂_b Φ = −√κ φ'(x)`. -/
theorem partialSnd_upGapObs (h1 : ∀ x, HasDerivAt φ (φ' x) x) {p : ℝ × ℝ} (hp : p ∈ upGapRegion) :
    Ito.partialSnd (fun r => φ (upGapCoord κ q r)) p = -Real.sqrt κ * φ' (upGapCoord κ q p) := by
  rw [partialSnd_comp_of_hasDerivAt ((contDiffAt_upGapCoord hp (n := 1)).differentiableAt one_ne_zero) (h1 _),
    partialSnd_upGapCoord hp]
  ring

end Obs

/-! ### The adapted upper gap -/

section Process

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {κ σ q : ℝ} {B : ℝ≥0 → Ω → ℝ}

/-- The drift integral `Λ_t = ∫₀ᵗ (tanh(X/2) − σ)` of the upper gap `X = q − √κ B + Λ` (the adapted tamed flow
`Sec2.markFlow`). -/
def upGapDrift (κ σ q : ℝ) (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  Sec2.markFlow (fun x => Real.tanh (x / 2) - σ) 0 (fun _ => ⊤) (fun t ω => Real.sqrt κ * B t ω - q)

/-- The upper gap `X_t = q − √κ B_t + Λ_t`. -/
def upGapProc (κ σ q : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  q - Real.sqrt κ * B t ω + upGapDrift κ σ q B t ω

/-- The positive state `λ̃ = e^Λ`. -/
def upGapState (κ σ q : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := Real.exp (upGapDrift κ σ q B t ω)

theorem lipschitzWith_upGapDrift_field (σ : ℝ) :
    LipschitzWith (1 / 2 + 0) fun x : ℝ => Real.tanh (x / 2) - σ :=
  lipschitzWith_tanh_half.sub (LipschitzWith.const σ)

theorem abs_upGapDrift_field_le (σ x : ℝ) : |Real.tanh (x / 2) - σ| ≤ 1 + |σ| := by
  refine (abs_sub _ _).trans ?_
  have := Real.abs_tanh_lt_one (x / 2)
  linarith

/-- The path facts for one `ω` with a continuous Brownian path. -/
theorem upGapDrift_facts {ω : Ω} (hBc : Continuous (B · ω)) :
    Continuous (fun t => upGapDrift κ σ q B t ω) ∧
      ∀ t : ℝ≥0, upGapDrift κ σ q B t ω =
        ∫ s in (0 : ℝ)..t, (Real.tanh (upGapProc κ σ q B s.toNNReal ω / 2) - σ) := by
  have hW : ContinuousOn (fun s => Real.sqrt κ * B s ω - q) {s : ℝ≥0 | (s : ℝ≥0∞) < ⊤} :=
    ((continuous_const.mul hBc).sub continuous_const).continuousOn
  obtain ⟨hc, heq⟩ := Sec2.markFlow_eq_of_continuousOn (y := 0) (ζ := fun _ : Ω => (⊤ : ℝ≥0∞))
    (W := fun t ω => Real.sqrt κ * B t ω - q) (lipschitzWith_upGapDrift_field σ)
    (abs_upGapDrift_field_le σ) hW
  refine ⟨?_, fun t => ?_⟩
  · rw [← continuousOn_univ]
    exact hc.mono fun s _ => ENNReal.coe_lt_top
  · have h := heq t ENNReal.coe_lt_top
    rw [zero_add] at h
    change Sec2.markFlow _ _ _ _ t ω = _
    rw [h]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [upGapProc, upGapDrift]
    congr 3
    ring

theorem upGapDrift_zero (ω : Ω) : upGapDrift κ σ q B 0 ω = 0 := Sec2.markFlow_zero _ _ _ _ ω

theorem continuous_upGapProc {ω : Ω} (hBc : Continuous (B · ω)) :
    Continuous fun t => upGapProc κ σ q B t ω :=
  (continuous_const.sub (continuous_const.mul hBc)).add (upGapDrift_facts hBc).1

/-- Each `upGapDrift … t` is `𝓖_t`-measurable. -/
theorem measurable_upGapDrift {𝓖 : Filtration ℝ≥0 mΩ} (hB : ∀ t, Measurable[𝓖 t] (B t)) (t : ℝ≥0) :
    Measurable[𝓖 t] (upGapDrift κ σ q B t) := by
  refine Sec2.measurable_markFlow (lipschitzWith_upGapDrift_field σ).continuous.measurable
    (fun s A hA => ?_) t
  have h : {ω | ((s : ℝ≥0∞) < (⊤ : ℝ≥0∞)) ∧ Real.sqrt κ * B s ω - q ∈ A} =
      (fun ω => Real.sqrt κ * B s ω - q) ⁻¹' A := by
    ext ω; simp
  rw [h]
  exact (((hB s).const_mul _).sub_const q) hA

/-- **The state equation** `λ̃_t = 1 + ∫₀ᵗ Ψ(λ̃_s, B_s) ds`. -/
theorem upGapState_eq_integral {ω : Ω} (hBc : Continuous (B · ω)) (t : ℝ≥0) :
    upGapState κ σ q B t ω =
      1 + ∫ s in (0 : ℝ)..t, upGapField κ σ q (Zhan.pathX (upGapState κ σ q B) B s.toNNReal ω) := by
  obtain ⟨hc, heq⟩ := upGapDrift_facts (κ := κ) (σ := σ) (q := q) hBc
  set g : ℝ → ℝ := fun r => Real.tanh (upGapProc κ σ q B r.toNNReal ω / 2) - σ with hg
  have hgc : Continuous g :=
    (continuous_tanh_half.comp ((continuous_upGapProc hBc).comp continuous_real_toNNReal)).sub
      continuous_const
  set H : ℝ → ℝ := fun r => ∫ s in (0 : ℝ)..r, g s with hH
  have hHd : ∀ r, HasDerivAt H (g r) r := fun r => (hgc.integral_hasStrictDerivAt 0 r).hasDerivAt
  have hHeq : ∀ r : ℝ, 0 ≤ r → upGapDrift κ σ q B r.toNNReal ω = H r := fun r hr => by
    rw [heq, Real.coe_toNNReal r hr]
  have hint : IntervalIntegrable (fun r => Real.exp (H r) * g r) volume 0 t :=
    ((Real.continuous_exp.comp (continuous_iff_continuousAt.2 fun r => (hHd r).continuousAt)).mul
      hgc).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun r => Real.exp (H r)) (f' := fun r => Real.exp (H r) * g r)
    (fun r _ => (hHd r).exp) hint
  have hH0 : H 0 = 0 := intervalIntegral.integral_same
  rw [hH0, Real.exp_zero] at hFTC
  have hcongr : ∫ s in (0 : ℝ)..t, upGapField κ σ q (Zhan.pathX (upGapState κ σ q B) B s.toNNReal ω) =
      ∫ s in (0 : ℝ)..t, Real.exp (H s) * g s := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le t.coe_nonneg] at hr
    simp only [upGapField, upGapCoord, Zhan.pathX, upGapState, Real.log_exp, hg, upGapProc]
    rw [hHeq r hr.1]
  rw [hcongr, hFTC, upGapState, ← hHeq t t.coe_nonneg, Real.toNNReal_coe]
  ring

theorem upGapCoord_pathX (t : ℝ≥0) (ω : Ω) :
    upGapCoord κ q (Zhan.pathX (upGapState κ σ q B) B t ω) = upGapProc κ σ q B t ω := by
  simp only [upGapCoord, Zhan.pathX, upGapState, Real.log_exp, upGapProc]

theorem pathX_upGapState_mem (t : ℝ≥0) (ω : Ω) : Zhan.pathX (upGapState κ σ q B) B t ω ∈ upGapRegion :=
  Real.exp_pos _

end Process

/-! ### Finite quadratic variation of `φ(X)`; uniqueness -/

section QV

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {κ σ q : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {φ φ' φ'' : ℝ → ℝ}

/-- **`∫₀^∞ κ φ'(X)² < ∞` almost surely** for a nonnegative `C³` function `φ` with
`φ'(tanh(x/2) − σ) + (κ/2) φ'' ≤ 0` (PROVE-ZHAN-B's `ae_bddAbove_integral_sq_partialSnd` for `φ(q − √κ b + log λ̃)`
along the state `λ̃ = e^Λ`). -/
theorem ae_bdd_integral_sq_upGapProc [IsProbabilityMeasure P] (hB : IsFilteredBrownianReal 𝓖 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) (hκ : 0 ≤ κ) (q : ℝ)
    (hφ : ContDiff ℝ 3 φ) (hφ0 : ∀ x, 0 ≤ φ x) (h1 : ∀ x, HasDerivAt φ (φ' x) x)
    (h2 : ∀ x, HasDerivAt φ' (φ'' x) x)
    (hL : ∀ x, φ' x * (Real.tanh (x / 2) - σ) + κ / 2 * φ'' x ≤ 0) :
    ∀ᵐ ω ∂P, ∃ S : ℝ, ∀ t : ℝ≥0,
      ∫ s in (0 : ℝ)..t, κ * φ' (upGapProc κ σ q B s.toNNReal ω) ^ 2 ≤ S := by
  have key := ae_bddAbove_integral_sq_partialSnd (𝓖 := 𝓖) (P := P) (E := ℝ) (B := B)
    (U := upGapRegion) (Φ := fun r => φ (upGapCoord κ q r)) (Ψ := upGapField κ σ q)
    (Λ := upGapState κ σ q B) (G := univ) (p₀ := 1)
    hB hBc isOpen_upGapRegion compl_upGapRegion_nonempty
    (hφ.comp_contDiffOn ((contDiffOn_upGapCoord κ q).of_le
      (WithTop.coe_le_coe.2 (le_top : (3 : ℕ∞) ≤ ⊤))))
    (fun _ _ => hφ0 _) (continuousOn_upGapField κ σ q)
    (fun ω _ t => by
      rw [itoGen_upGapObs hκ (hφ.of_le (by norm_num)) h1 h2 (pathX_upGapState_mem t ω)]
      exact hL _)
    (fun t => Real.measurable_exp.comp (measurable_upGapDrift hB.2.1 t))
    (fun ω => Real.continuous_exp.comp (upGapDrift_facts (κ := κ) (σ := σ) (q := q) (hBc ω)).1)
    MeasurableSet.univ (by simp)
    (fun ω => by simp [upGapState, upGapDrift_zero])
    hB0
    (fun ω _ t => upGapState_eq_integral (hBc ω) t)
    (fun ω _ t => pathX_upGapState_mem t ω)
  filter_upwards [key] with ω hω
  obtain ⟨S, hS⟩ := hω
  refine ⟨S, fun t => le_trans (le_of_eq ?_) (hS t)⟩
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [partialSnd_upGapObs h1 (pathX_upGapState_mem _ ω), upGapCoord_pathX, mul_pow, neg_sq, Real.sq_sqrt hκ]

/-- **Uniqueness**: every continuous solution of (3.15) on `[0, T]` is the upper gap `upGapProc` there. -/
theorem eqOn_upGapProc {ω : Ω} (hBc : Continuous (B · ω)) {T : ℝ} (hT : 0 ≤ T) {X : ℝ → ℝ}
    (hXc : ContinuousOn X (Icc 0 T))
    (hX : ∀ t ∈ Icc 0 T, X t = q - (Real.sqrt κ * B t.toNNReal ω + σ * t) +
      ∫ r in (0 : ℝ)..t, Real.tanh (X r / 2)) :
    ∀ t ∈ Icc 0 T, X t = upGapProc κ σ q B t.toNNReal ω := by
  set w : ℝ → ℝ := fun r => -(Real.sqrt κ * B r.toNNReal ω + σ * r) with hw
  have hwc : Continuous w :=
    ((continuous_const.mul (hBc.comp continuous_real_toNNReal)).add
      (continuous_const.mul continuous_id)).neg
  have hLD : OneForce.LipData (fun x => Real.tanh (x / 2)) w :=
    ⟨⟨_, lipschitzWith_tanh_half⟩, ⟨1, fun x => (Real.abs_tanh_lt_one _).le⟩, hwc⟩
  set Y : ℝ → ℝ := fun r => upGapProc κ σ q B r.toNNReal ω with hYdef
  have hYcont : Continuous Y := (continuous_upGapProc hBc).comp continuous_real_toNNReal
  have hY : ∀ t ∈ Icc (0 : ℝ) T, Y t = q + w t + ∫ r in (0 : ℝ)..t, (fun x => Real.tanh (x / 2)) (Y r) := by
    intro t ht
    have h := (upGapDrift_facts (κ := κ) (σ := σ) (q := q) hBc).2 t.toNNReal
    rw [Real.coe_toNNReal t ht.1] at h
    have hint : IntervalIntegrable (fun r : ℝ => Real.tanh (upGapProc κ σ q B r.toNNReal ω / 2)) volume 0 t :=
      (continuous_tanh_half.comp hYcont).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul] at h
    simp only [hYdef, hw, upGapProc, h]
    ring
  have h1 := OneForce.eqOn_lipSol hLD hT hXc (fun s hs => by rw [hX s hs]; simp only [hw]; ring)
  have h2 := OneForce.eqOn_lipSol hLD hT hYcont.continuousOn hY
  intro t ht
  rw [← h1 ht, h2 ht]

end QV

end Zhan

end InteractingSLE
