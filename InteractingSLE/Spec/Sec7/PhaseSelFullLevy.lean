/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseSelFull
import InteractingSLE.Spec.Coupling.WholeField5Germ
import InteractingSLE.Spec.Sec2.OneForceLaw

/-!
# §7.4, Aux. lemma 122 before a stopping lifetime, part 2: the driving Brownian motion continued after the lifetime

Packet PROVE-STRIPSYS5 (specification §7.4, Aux. lemma 122; the continuation of a stopped Brownian motion by an
independent one, `planning/handoffs/PROVE-STRIPSYS4.md` §5 item 1).

If the explicit coupling means are local martingales only before swallowing **and before a stopping lifetime `T`**,
the driver's martingale part `M = W − W₀ + ½ ∑ ρ (V − V₀)` stopped at the localizing times `lifeLoc n` is a bounded
martingale with square compensator `κ (t ∧ lifeLoc n)` (`PhaseSelFull.martingale_martProc_lifeLoc`). Then:

* `martingale_exp_lifeLoc`: `exp(a M^{τₙ}/√κ − a² (t ∧ τₙ)/2)` is a martingale (MathFin's slow-clock exponential
  martingale, `LevyExpMartingale.martingale_exp`);
* `exists_brownian_continuation`: on `Ω × Ω₀`, with an independent Brownian motion on `Ω₀`, the process equal to
  `M/√κ` up to `T` and continued by the independent increments afterwards is a Brownian motion of the product
  filtration (`WholeField.isTCExpMartingale_annClock`,
  `WholeField.IsTCExpMartingale.isFilteredBrownianReal_complNoise`).

The coordinates are continuous on all of `ℝ≥0` (so `M` has a value at `T`); the coupling hypothesis is used only
before `T`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace PhaseSelFull

open MartChar

section Clock

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]
  {W : ℝ≥0 → Ω → ℝ} {V : ι → ℝ≥0 → Ω → ℝ} {T : Ω → WithTop ℝ≥0}

theorem locTime_mono (hWc : ∀ ω, Continuous fun t => W t ω) (hVc : ∀ j ω, Continuous fun t => V j t ω)
    {n m : ℕ} (hnm : n ≤ m) (ω : Ω) : locTime W V n n ω ≤ locTime W V m m ω :=
  min_le_min (WithTop.coe_le_coe.2 (by exact_mod_cast hnm))
    (MathFin.exitTime_mono (continuous_absSum hWc hVc) hnm ω)

/-- The localizing times `lifeLoc n` increase with `n`. -/
theorem lifeLoc_mono (hWc : ∀ ω, Continuous fun t => W t ω) (hVc : ∀ j ω, Continuous fun t => V j t ω)
    (ω : Ω) : Monotone fun n => lifeLoc W V T n ω := by
  intro n m hnm
  by_cases h : ω ∈ initEvent W V n
  · have h' : ω ∈ initEvent W V m := by
      have h1 : absSum W V 0 ω < n := h
      show absSum W V 0 ω < m
      exact h1.trans_le (by exact_mod_cast hnm)
    simp only [lifeLoc_of_mem h, lifeLoc_of_mem h']
    exact min_le_min (locTime_mono hWc hVc hnm ω) le_rfl
  · simp only [lifeLoc_of_notMem h]
    exact (WithTop.coe_le_coe.2 bot_le).trans
      (show (((⊥ : ℝ≥0)) : WithTop ℝ≥0) ≤ _ from by rw [WithTop.coe_bot]; exact bot_le)

/-- **Every time up to `T` is eventually below `lifeLoc n`.** -/
theorem eventually_le_lifeLoc (hWc : ∀ ω, Continuous fun t => W t ω)
    (hVc : ∀ j ω, Continuous fun t => V j t ω) {ω : Ω} {u : ℝ≥0} (hu : (u : WithTop ℝ≥0) ≤ T ω) :
    ∀ᶠ n in atTop, (u : WithTop ℝ≥0) ≤ lifeLoc W V T n ω := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (absSum W V 0 ω)
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge (u : ℝ)
  have hex := (WithTop.tendsto_nhds_top_iff _).1 (MathFin.exitTime_tendsto_top (continuous_absSum hWc hVc) ω) u
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop N₁, hex] with n hn0 hn1 hn2
  have hmem : ω ∈ initEvent W V n := by
    show absSum W V 0 ω < n
    exact hN₀.trans_le (by exact_mod_cast hn0)
  rw [lifeLoc_of_mem hmem]
  refine le_min (le_min ?_ hn2.le) hu
  exact WithTop.coe_le_coe.2 (by
    have : (u : ℝ) ≤ n := hN₁.trans (by exact_mod_cast hn1)
    exact_mod_cast this)

/-- `lifeLoc n` as an element of `ℝ≥0` (it is at most `n`). -/
def lifeLocN (W : ℝ≥0 → Ω → ℝ) (V : ι → ℝ≥0 → Ω → ℝ) (T : Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  (lifeLoc W V T n ω).untopA

theorem coe_lifeLocN (W : ℝ≥0 → Ω → ℝ) (V : ι → ℝ≥0 → Ω → ℝ) (T : Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) :
    ((lifeLocN W V T n ω : ℝ≥0) : WithTop ℝ≥0) = lifeLoc W V T n ω :=
  coe_untopA_of_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top (lifeLoc_le_n W V T n ω))

theorem stoppedProcess_lifeLoc (X : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    stoppedProcess X (lifeLoc W V T n) t ω = X (min t (lifeLocN W V T n ω)) ω := by
  simp only [stoppedProcess, ← coe_lifeLocN W V T n ω, ← WithTop.coe_min]
  rfl

/-- **The annealed clock is the identity up to `T`.** -/
theorem annClock_lifeLocN_eq (hWc : ∀ ω, Continuous fun t => W t ω)
    (hVc : ∀ j ω, Continuous fun t => V j t ω) {ω : Ω} {u : ℝ≥0} (hu : (u : WithTop ℝ≥0) ≤ T ω) :
    WholeField.annClock (lifeLocN W V T) u ω = u := by
  refine le_antisymm (WholeField.annClock_le _ u ω) ?_
  obtain ⟨n, hn⟩ := (eventually_le_lifeLoc hWc hVc hu).exists
  refine le_ciSup_of_le (WholeField.bddAbove_min _ u ω) n (le_of_eq (min_eq_left ?_).symm)
  rw [← coe_lifeLocN] at hn
  exact WithTop.coe_le_coe.1 hn

end Clock

section Levy

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {ι : Type*} [Fintype ι] {ρ : ι → ℝ} {W : ℝ≥0 → Ω → ℝ} {V : ι → ℝ≥0 → Ω → ℝ} {T : Ω → WithTop ℝ≥0}

/-- **The stopped martingale part is bounded**: `|M_{t ∧ lifeLoc n}| ≤ 2n + n ∑ |ρ|`. -/
theorem abs_martProc_lifeLocN_le (hWc : ∀ ω, Continuous fun t => W t ω)
    (hVc : ∀ j ω, Continuous fun t => V j t ω) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    |martProc ρ W V (min t (lifeLocN W V T n ω)) ω| ≤ 2 * n + (∑ j, |ρ j|) * n := by
  have hR : 0 ≤ ∑ j, |ρ j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases h : ω ∈ initEvent W V n
  · set θ := min t (lifeLocN W V T n ω) with hθ
    have hθτ : (θ : WithTop ℝ≥0) ≤ lifeLoc W V T n ω := by
      rw [← coe_lifeLocN]; exact WithTop.coe_le_coe.2 (min_le_right _ _)
    have h0τ : ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ lifeLoc W V T n ω := by
      rw [← coe_lifeLocN]; exact WithTop.coe_le_coe.2 bot_le
    have hb := abs_le_of_le_lifeLoc hWc hVc h hθτ
    have hb0 := abs_le_of_le_lifeLoc hWc hVc h h0τ
    simp only [martProc, martValue]
    have hs : |∑ j, ρ j * (V j θ ω - V j 0 ω)| ≤ (∑ j, |ρ j|) * (2 * n) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := abs_sub (V j θ ω) (V j 0 ω)
      linarith [hb.2 j, hb0.2 j]
    have hw := abs_sub (W θ ω) (W 0 ω)
    calc |W θ ω - W 0 ω + 1 / 2 * ∑ j, ρ j * (V j θ ω - V j 0 ω)|
        ≤ |W θ ω - W 0 ω| + |1 / 2 * ∑ j, ρ j * (V j θ ω - V j 0 ω)| := abs_add_le _ _
      _ ≤ 2 * n + (∑ j, |ρ j|) * n := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        nlinarith [hb.1, hb0.1]
  · have h0 : lifeLocN W V T n ω = 0 := by
      simp only [lifeLocN, lifeLoc_of_notMem h]; rfl
    rw [h0, min_eq_right (zero_le : (0 : ℝ≥0) ≤ t)]
    simp only [martProc, martValue, sub_self, mul_zero, Finset.sum_const_zero, add_zero, abs_zero]
    positivity

/-- **The stopped exponential martingale.** If `M^{τₙ}` and `(M² − κ t)^{τₙ}` are martingales (`τₙ = lifeLoc n`),
then `exp(a M_{t∧τₙ}/√κ − a² (t ∧ τₙ)/2)` is a martingale (MathFin's slow-clock exponential martingale). -/
theorem martingale_exp_lifeLoc [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hVc : ∀ j ω, Continuous fun t => V j t ω) {n : ℕ}
    (hM : Martingale (stoppedProcess (martProc ρ W V) (lifeLoc W V T n)) 𝓕 P)
    (hM2 : Martingale (stoppedProcess (fun t ω => martProc ρ W V t ω ^ 2 - κ * t) (lifeLoc W V T n)) 𝓕 P)
    (a : ℝ) :
    Martingale (fun t ω => Real.exp (a * (martProc ρ W V (min t (lifeLocN W V T n ω)) ω / Real.sqrt κ) -
      a ^ 2 * ((min t (lifeLocN W V T n ω) : ℝ≥0) : ℝ) / 2)) 𝓕 P := by
  set S := lifeLocN W V T n with hS
  set M : ℝ≥0 → Ω → ℝ := fun t ω => martProc ρ W V (min t (S ω)) ω / Real.sqrt κ with hMdef
  set A : ℝ≥0 → Ω → ℝ := fun t ω => ((min t (S ω) : ℝ≥0) : ℝ) with hAdef
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hA : MathFin.LevyQuadraticSums.IsSlowClock A := by
    refine ⟨fun ω => by simp [hAdef], fun p q hpq ω => ?_, fun p q hpq ω => ?_⟩
    · have : min p (S ω) ≤ min q (S ω) := min_le_min hpq le_rfl
      simp only [hAdef, sub_nonneg]; exact_mod_cast this
    · simp only [hAdef]
      rcases le_total p (S ω) with h1 | h1 <;> rcases le_total q (S ω) with h2 | h2
      · rw [min_eq_left h1, min_eq_left h2]
      · rw [min_eq_left h1, min_eq_right h2]
        have : (S ω : ℝ) ≤ q := by exact_mod_cast h2
        linarith
      · rw [min_eq_right h1, min_eq_left h2]
        have : (p : ℝ) ≤ q := by exact_mod_cast hpq
        have : (q : ℝ) ≤ S ω := by exact_mod_cast h2
        linarith
      · rw [min_eq_right h1, min_eq_right h2, sub_self, sub_nonneg]; exact_mod_cast hpq
  have hMe : M = (Real.sqrt κ)⁻¹ • stoppedProcess (martProc ρ W V) (lifeLoc W V T n) := by
    funext t ω
    simp only [hMdef, Pi.smul_apply, smul_eq_mul, stoppedProcess_lifeLoc, hS]
    rw [div_eq_inv_mul]
  have hM' : Martingale M 𝓕 P := by rw [hMe]; exact hM.smul _
  have hM2e : (fun t ω => M t ω ^ 2 - A t ω) =
      κ⁻¹ • stoppedProcess (fun t ω => martProc ρ W V t ω ^ 2 - κ * t) (lifeLoc W V T n) := by
    funext t ω
    simp only [hMdef, hAdef, Pi.smul_apply, smul_eq_mul, stoppedProcess_lifeLoc, hS]
    rw [div_pow, Real.sq_sqrt hκ.le]
    field_simp
  have hM2' : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P := by rw [hM2e]; exact hM2.smul _
  have hK : ∀ t ω, |M t ω| ≤ (2 * n + (∑ j, |ρ j|) * n) / Real.sqrt κ := fun t ω => by
    simp only [hMdef]
    rw [abs_div, abs_of_pos hsk]
    exact div_le_div_of_nonneg_right (abs_martProc_lifeLocN_le hWc hVc n t ω) hsk.le
  have hcont : ∀ ω, Continuous fun t => M t ω := fun ω =>
    ((continuous_martProc hWc hVc ω).comp (continuous_id.min continuous_const)).div_const _
  exact MathFin.LevyExpMartingale.martingale_exp hA hM' hM2' hK hcont a

end Levy

section Continuation

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

theorem iSupFiltration_const (𝓕 : Filtration ℝ≥0 mΩ) : WholeField.iSupFiltration (fun _ : ℕ => 𝓕) = 𝓕 := by
  ext u s
  rw [WholeField.iSupFiltration_apply, iSup_const]

/-- **The driving Brownian motion continued after the lifetime** (Aux. lemma 122 with a stopping lifetime). Let the
coordinates be continuous adapted processes on all of `ℝ≥0` with the deterministic properties of force images, and
let every explicit coupling mean be a local martingale before swallowing and before the stopping time `T`. Then on
`Ω × Ω₀` (with an independent Brownian motion on `Ω₀`) there is a Brownian motion `B` of the product filtration, with
every path continuous, equal to the driver's martingale part `M/√κ` at every time `t ≤ T`. The initial word is
random. -/
theorem exists_brownian_continuation [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓕 W) (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i))
    (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i)) (hordL : ∀ ω t i, VL i t ω ≤ W t ω)
    (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime 𝓕 T)
    (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
      (coupProc κ ρL ρR W VL VR z)) :
    ∃ (Ω₀ : Type) (m₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 m₀) (B : ℝ≥0 → Ω × Ω₀ → ℝ),
      IsFilteredBrownianReal (WholeField.prodFiltration 𝓕 𝓦) B (P.prod P₀) ∧
        (∀ p, Continuous fun t => B t p) ∧
        ∀ (p : Ω × Ω₀) (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ T p.1 →
          B t p = martProc (jointρ ρL ρR) W (jointV VL VR) t p.1 / Real.sqrt κ := by
  set V := jointV VL VR with hV
  set ρ := jointρ ρL ρR with hρ
  have hVLc : ∀ i ω, Continuous fun t => VL i t ω := fun i ω => (hpathL ω i).1
  have hVRc : ∀ i ω, Continuous fun t => VR i t ω := fun i ω => (hpathR ω i).1
  have hVc : ∀ j ω, Continuous fun t => V j t ω := fun j ω => by
    cases j with
    | inl i => exact hVLc i ω
    | inr i => exact hVRc i ω
  have hVa : ∀ j, StronglyAdapted 𝓕 (V j) := fun j => by
    cases j with
    | inl i => exact hVLa i
    | inr i => exact hVRa i
  set S : ℕ → Ω → ℝ≥0 := lifeLocN W V T with hS
  set Bv : ℝ≥0 → Ω → ℝ := fun t ω => martProc ρ W V t ω / Real.sqrt κ with hBv
  have hSmono : ∀ ω, Monotone fun m => S m ω := fun ω m m' hmm' => by
    have h := lifeLoc_mono (T := T) hWc hVc ω hmm'
    simp only at h
    rw [← coe_lifeLocN, ← coe_lifeLocN] at h
    exact WithTop.coe_le_coe.1 h
  have hSm : ∀ (m : ℕ) (u : ℝ≥0), Measurable[𝓕 u] fun ω => min u (S m ω) := by
    intro m u
    have hσ := isStoppingTime_lifeLoc hWc hVc hWa hVa hT m
    refine measurable_of_Iic (mδ := 𝓕 u) fun x => ?_
    by_cases hx : u ≤ x
    · have : (fun ω => min u (S m ω)) ⁻¹' Iic x = univ := by
        ext ω; simp only [mem_preimage, mem_Iic, mem_univ, iff_true]; exact (min_le_left _ _).trans hx
      rw [this]; exact @MeasurableSet.univ _ (𝓕 u)
    · push Not at hx
      have : (fun ω => min u (S m ω)) ⁻¹' Iic x = {ω | lifeLoc W V T m ω ≤ x} := by
        ext ω
        simp only [mem_preimage, mem_Iic, min_le_iff, mem_ofPred_eq, hS, ← coe_lifeLocN W V T m ω,
          WithTop.coe_le_coe]
        exact ⟨fun h => h.resolve_left (not_le.2 hx), Or.inr⟩
      rw [this]
      exact 𝓕.mono hx.le _ (hσ x)
  have hBvc : ∀ ω, Continuous fun t => Bv t ω := fun ω => (continuous_martProc hWc hVc ω).div_const _
  have hBv0 : ∀ ω, Bv 0 ω = 0 := fun ω => by simp [hBv, martProc, martValue]
  have hexp : ∀ (m : ℕ) (a : ℝ), Martingale (fun t ω => Real.exp (a * Bv (min t (S m ω)) ω -
      a ^ 2 * ((min t (S m ω) : ℝ≥0) : ℝ) / 2)) ((fun _ : ℕ => 𝓕) m) P := by
    intro m a
    have hMM := martingale_martProc_lifeLoc hκ hW0 hWc hWa hVLa hVRa hordL hordR hpathL hpathR hT hmart m
    exact martingale_exp_lifeLoc hκ hWc hVc hMM.1 hMM.2 a
  have hTC := WholeField.isTCExpMartingale_annClock (𝒢 := fun _ : ℕ => 𝓕) (fun _ => monotone_const)
    hSmono hSm hBvc hBv0 hexp
  rw [iSupFiltration_const] at hTC
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓦, β, hβ, hβc, hβ0⟩ := OneForce.exists_filteredBrownian
  obtain ⟨hB, hBc⟩ := WholeField.IsTCExpMartingale.isFilteredBrownianReal_complNoise hTC
    (LocalTime.isFilteredPreBrownian_of_isFilteredBrownianReal hβ) hβc hβ0
  refine ⟨Ω₀, m₀, P₀, hP₀, 𝓦, _, hB, hBc, fun p t ht => ?_⟩
  have hc : WholeField.annClock S t p.1 = t := annClock_lifeLocN_eq hWc hVc ht
  rw [WholeField.complNoise_of_eq hc]
  simp only [hc, hBv]

end Continuation

end PhaseSelFull

end Sec7

end InteractingSLE
