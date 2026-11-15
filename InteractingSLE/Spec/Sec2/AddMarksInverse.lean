/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.GirsanovCut
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# The reverse change of measure: `dP/dQ` as a function of the paths

Packet PROVE-SEC2-GIR2. Specification, proof of Theorem 2.2 (`source/spec/p001-048.md` L488):
"One can also reverse this procedure … If there were multiple possibilities for the joint laws of
the `W_t`, `B_t`, and `V_t^{i,q}` in the multiple-force-point case, then this would produce multiple
possibilities for the joint laws in the single-force-point case". The transfer of uniqueness needs
the density `dP/dQ` of the original measure with respect to the changed one as a functional of the
paths observed under `Q`. Here, for a Girsanov measure `Q = Z_T · P` with drift `θ` and the
`Q`-Brownian motion `B̃ = B + ∫ θ`:

* `riemannSum_girsanovProcess`, `riemannSum_drift_eq_integral`, `tendsto_riemannSum_drift`: the
  Riemann sums of `θ` against `B̃` are those against `B` plus `∫ θ_n θ → ∫ θ²`;
* `stochIntegral_girsanovProcess_ae_eq`: **the `Q`-Itô integral against `B̃`** is
  `∫ θ dB̃ = ∫ θ dB + ∫ θ²`, `Q`-almost surely;
* `girsanovMeasure_neg_eq`: **inverse Girsanov**: `P` is the Girsanov measure of `Q` for the drift
  `−θ` and the Brownian motion `B̃`, i.e. `dP/dQ = exp(∫ θ dB̃ − ½ ∫ θ²)`, and
  `girsanovProcess_neg`: the reverse change gives back `B`;
* `map_prod_eq_of_tendstoInMeasure`: if `X₁`, `X₂` have the same law and `I_k` is the limit in
  probability of the same functionals `R_n(X_k)`, then `(X₁, I₁)` and `(X₂, I₂)` have the same law;
* `map_eq_of_girsanov`: **transfer of laws through the reverse change**: if the laws of `X₁`, `X₂`
  under two Girsanov measures `Q₁`, `Q₂` agree, and the Riemann sums of the drifts against the
  `Q_k`-Brownian motions and the quadratic integrals are the same functionals of `X_k`, then the laws
  of `X₁`, `X₂` under the original measures agree.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B θ : ℝ≥0 → Ω → ℝ}

/-! ### Riemann sums against `B̃ = B + ∫ θ` -/

/-- The Riemann sums against `B + ∫ θ` split into those against `B` and against the drift. -/
theorem riemannSum_girsanovProcess (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    riemannSum (girsanovProcess B θ) θ n t ω
      = riemannSum B θ n t ω + riemannSum (drift θ) θ n t ω := by
  unfold riemannSum girsanovProcess
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The Riemann sums of the drift part** are the integrals `∫₀ᵗ θ_n θ` of the left-point step
function `θ_n` against `θ` (for `t ≤ n`, so that the cells cover `[0, t]`). -/
theorem riemannSum_drift_eq_integral (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) {n : ℕ} {t : ℝ≥0} (htn : t ≤ n) (ω : Ω) :
    riemannSum (drift θ) θ n t ω
      = ∫ u in (0 : ℝ)..(t : ℝ), stepFun θ n u ω * θ u.toNNReal ω := by
  set h : ℝ → ℝ := fun u => θ u.toNNReal ω with hh
  set a : ℕ → ℝ := fun k => ((min (grid n k) t : ℝ≥0) : ℝ) with ha
  have hC : 0 ≤ C := (abs_nonneg _).trans (hθb 0 ω)
  have hint_h : ∀ x y : ℝ, IntervalIntegrable h volume x y := intervalIntegrable_time hθ hθb ω
  have hint_f : ∀ x y : ℝ, IntervalIntegrable (fun u => stepFun θ n u ω * h u) volume x y :=
    fun x y => (intervalIntegrable_const (c := C * C)).mono_fun'
      ((measurable_stepFun_time θ n ω).mul (measurable_time_of_progressive hθ ω)).aestronglyMeasurable
      (ae_of_all _ fun u => by
        show ‖stepFun θ n u ω * h u‖ ≤ C * C
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (abs_stepFun_le hθb n u ω) (hθb _ ω) (abs_nonneg _) hC)
  have ha0 : a 0 = 0 := by simp [ha, grid_zero]
  have haN : a (cells n) = t := by
    simp only [ha, grid_cells]
    rw [min_eq_right htn]
  rw [← haN, ← ha0, ← intervalIntegral.sum_integral_adjacent_intervals fun k _ => hint_f _ _]
  unfold riemannSum
  refine Finset.sum_congr rfl fun k _ => ?_
  have hmono : a k ≤ a (k + 1) := by
    simp only [ha, NNReal.coe_le_coe]
    exact min_le_min (grid_mono n (Nat.le_succ k)) le_rfl
  have hcongr : ∫ u in a k..a (k + 1), stepFun θ n u ω * h u
      = ∫ u in a k..a (k + 1), θ (grid n k) ω * h u := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_real (a (k + 1))] with u hune hu
    rw [uIoc_of_le hmono] at hu
    have hlt : u < a (k + 1) := lt_of_le_of_ne hu.2 hune
    have h1 : ((grid n k : ℝ≥0) : ℝ) < u := by
      by_cases hkt : grid n k ≤ t
      · have : a k = ((grid n k : ℝ≥0) : ℝ) := by simp only [ha]; rw [min_eq_left hkt]
        rw [← this]; exact hu.1
      · push Not at hkt
        have e1 : a k = t := by simp only [ha]; rw [min_eq_right hkt.le]
        have e2 : a (k + 1) = t := by
          simp only [ha]; rw [min_eq_right (hkt.le.trans (grid_mono n (Nat.le_succ k)))]
        exact absurd (hu.1.trans hlt) (by rw [e1, e2]; exact lt_irrefl _)
    have h2 : u < ((grid n (k + 1) : ℝ≥0) : ℝ) :=
      hlt.trans_le (by simp only [ha, NNReal.coe_le_coe]; exact min_le_left _ _)
    simp only [stepFun, stepIdx_eq_of_mem h1 h2]
  rw [hcongr, intervalIntegral.integral_const_mul]
  congr 1
  unfold drift
  rw [intervalIntegral.integral_interval_sub_left (hint_h _ _) (hint_h _ _)]

/-- **The drift Riemann sums converge to `∫ θ²`** at every `ω` along which `θ` is left-continuous at
almost every time. -/
theorem tendsto_riemannSum_drift (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) {ω : Ω}
    (hω : ∀ᵐ u ∂(volume : Measure ℝ),
      ContinuousWithinAt (fun s => θ s ω) (Set.Iic u.toNNReal) u.toNNReal) (t : ℝ≥0) :
    Tendsto (fun n => riemannSum (drift θ) θ n t ω) atTop (𝓝 (quadInt θ t ω)) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hθb 0 ω)
  have hlim : Tendsto (fun n => ∫ u in (0 : ℝ)..(t : ℝ), stepFun θ n u ω * θ u.toNNReal ω) atTop
      (𝓝 (quadInt θ t ω)) := by
    unfold quadInt
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C * C)
      (Eventually.of_forall fun n => ((measurable_stepFun_time θ n ω).mul
        (measurable_time_of_progressive hθ ω)).aestronglyMeasurable)
      (Eventually.of_forall fun n => ae_of_all _ fun u _ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (abs_stepFun_le hθb n u ω) (hθb _ ω) (abs_nonneg _) hC)
      intervalIntegrable_const (hω.mono fun u hu _ => ?_)
    rw [sq]
    exact (tendsto_stepFun hu).mul tendsto_const_nhds
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈(t : ℝ)⌉₊] with n hn
  have htn : t ≤ (n : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
  exact (riemannSum_drift_eq_integral hθ hθb htn ω).symm

/-- Convergence in measure passes to an absolutely continuous finite measure. -/
theorem tendstoInMeasure_of_absolutelyContinuous {Q : Measure Ω} [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (hQP : Q ≪ P) {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) Q) (h : TendstoInMeasure P f atTop g) :
    TendstoInMeasure Q f atTop g := by
  rw [exists_seq_tendstoInMeasure_atTop_iff hf]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ := (h.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  exact ⟨ns', hns', hQP.ae_le hae⟩

/-- **The Itô integral against the changed Brownian motion.** Under the Girsanov measure
`Q = Z_T · P` (drift `θ`, vanishing after `T`), the `Q`-Itô integral of `θ` against the `Q`-Brownian
motion `B̃ = B + ∫ θ` is `∫ θ dB + ∫ θ²`, `Q`-almost surely: the Riemann sums against `B̃` are those
against `B` plus `∫ θ_n θ`; the first converge in `P`-probability, hence in `Q`-probability, the second
converge pathwise to `∫ θ²`. -/
theorem stochIntegral_girsanovProcess_ae_eq [IsProbabilityMeasure P]
    (hBF : IsFilteredBrownianReal 𝓕 B P) (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) {T : ℝ≥0}
    (hθT : ∀ t ω, T ≤ t → θ t ω = 0) (t : ℝ≥0) :
    stochIntegral (girsanovMeasure P 𝓕 B θ T) 𝓕 (girsanovProcess B θ) θ t
      =ᵐ[girsanovMeasure P 𝓕 B θ T] fun ω => stochIntegral P 𝓕 B θ t ω + quadInt θ t ω := by
  have hPB := isFilteredPreBrownian_of_isFilteredBrownianReal hBF
  have hQeq := isEquivProbMeasure_girsanovMeasure (B := B) hθ.stronglyAdapted hθb hθreg T
  have := hQeq.isProb
  have hBQ := isFilteredBrownianReal_girsanov hBF hθ hθb hθreg hθT
  have hQB := isFilteredPreBrownian_of_isFilteredBrownianReal hBQ
  have hregQ : IsRiemannRegular (girsanovMeasure P 𝓕 B θ T) θ := hQeq.ac.ae_le hθreg
  have h1 := tendstoInMeasure_riemannSum hQB hθ.stronglyAdapted hθb hregQ t
  have hmeas : ∀ n, AEStronglyMeasurable (riemannSum (girsanovProcess B θ) θ n t)
      (girsanovMeasure P 𝓕 B θ T) := fun n =>
    ((stronglyMeasurable_riemannSum hQB hθ.stronglyAdapted n t).mono (𝓕.le t)).aestronglyMeasurable
  have h2 : TendstoInMeasure (girsanovMeasure P 𝓕 B θ T)
      (fun n => riemannSum (girsanovProcess B θ) θ n t) atTop
      (fun ω => stochIntegral P 𝓕 B θ t ω + quadInt θ t ω) := by
    rw [exists_seq_tendstoInMeasure_atTop_iff hmeas]
    intro ns hns
    obtain ⟨ns', hns', hae⟩ := ((tendstoInMeasure_riemannSum hPB hθ.stronglyAdapted hθb hθreg
      t).comp hns.tendsto_atTop).exists_seq_tendsto_ae
    refine ⟨ns', hns', hQeq.ac.ae_le ?_⟩
    filter_upwards [hae, hθreg] with ω hω hreg
    have hd := (tendsto_riemannSum_drift hθ hθb hreg t).comp (hns.comp hns').tendsto_atTop
    simp only [riemannSum_girsanovProcess]
    exact hω.add hd
  exact tendstoInMeasure_ae_unique h1 h2

theorem riemannSum_neg (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    riemannSum B (fun s ω => -θ s ω) n t ω = -riemannSum B θ n t ω := by
  unfold riemannSum
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The Itô integral is odd: `∫ (−θ) dB = −∫ θ dB` almost surely. -/
theorem stochIntegral_neg_ae_eq [IsProbabilityMeasure P] (hB : IsFilteredPreBrownian B 𝓕 P)
    (hθm : StronglyAdapted 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) (t : ℝ≥0) :
    stochIntegral P 𝓕 B (fun s ω => -θ s ω) t =ᵐ[P] fun ω => -stochIntegral P 𝓕 B θ t ω := by
  have hm' : StronglyAdapted 𝓕 (fun s ω => -θ s ω) := fun s => (hθm s).neg
  have hb' : ∀ s ω, |-θ s ω| ≤ C := fun s ω => by rw [abs_neg]; exact hθb s ω
  have hreg' : IsRiemannRegular P (fun s ω => -θ s ω) :=
    hθreg.mono fun ω hω => hω.mono fun u hu => hu.neg
  refine tendstoInMeasure_ae_unique (tendstoInMeasure_riemannSum hB hm' hb' hreg' t) ?_
  have h := tendstoInMeasure_riemannSum hB hθm hθb hθreg t
  intro ε hε
  have e : ∀ n, {ω | ε ≤ edist (riemannSum B (fun s ω => -θ s ω) n t ω)
      (-stochIntegral P 𝓕 B θ t ω)}
      = {ω | ε ≤ edist (riemannSum B θ n t ω) (stochIntegral P 𝓕 B θ t ω)} := fun n => by
    ext ω
    simp only [mem_ofPred_eq, riemannSum_neg, edist_neg_neg]
  simp only [e]
  exact h ε hε

theorem quadInt_neg : quadInt (fun s ω => -θ s ω) = quadInt θ := by
  funext t ω
  simp only [quadInt, neg_sq]

/-- The reverse change of the Brownian motion gives back `B`. -/
theorem girsanovProcess_neg : girsanovProcess (girsanovProcess B θ) (fun s ω => -θ s ω) = B := by
  funext t ω
  simp only [girsanovProcess, drift, intervalIntegral.integral_neg]
  ring

/-- **Inverse Girsanov: `dP/dQ = exp(∫ θ dB̃ − ½ ∫ θ²)`.** The original measure `P` is the Girsanov
measure of `Q = Z_T · P` for the reverse drift `−θ` and the `Q`-Brownian motion `B̃ = B + ∫ θ`
(Specification L488, "reverse this procedure"). -/
theorem girsanovMeasure_neg_eq [IsProbabilityMeasure P] (hBF : IsFilteredBrownianReal 𝓕 B P)
    (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) {T : ℝ≥0} (hθT : ∀ t ω, T ≤ t → θ t ω = 0) :
    girsanovMeasure (girsanovMeasure P 𝓕 B θ T) 𝓕 (girsanovProcess B θ) (fun s ω => -θ s ω) T
      = P := by
  have hPB := isFilteredPreBrownian_of_isFilteredBrownianReal hBF
  have hQeq := isEquivProbMeasure_girsanovMeasure (B := B) hθ.stronglyAdapted hθb hθreg T
  have := hQeq.isProb
  have hBQ := isFilteredBrownianReal_girsanov hBF hθ hθb hθreg hθT
  have hQB := isFilteredPreBrownian_of_isFilteredBrownianReal hBQ
  have hregQ : IsRiemannRegular (girsanovMeasure P 𝓕 B θ T) θ := hQeq.ac.ae_le hθreg
  have hI := stochIntegral_girsanovProcess_ae_eq hBF hθ hθb hθreg hθT T
  have hneg := stochIntegral_neg_ae_eq hQB hθ.stronglyAdapted hθb hregQ T
  have hdens : (fun ω => ENNReal.ofReal (doleansDensity (girsanovMeasure P 𝓕 B θ T) 𝓕
        (girsanovProcess B θ) (fun s ω => -θ s ω) T ω))
      =ᵐ[girsanovMeasure P 𝓕 B θ T] fun ω => ENNReal.ofReal (doleansDensity P 𝓕 B θ T ω)⁻¹ := by
    filter_upwards [hI, hneg] with ω h1 h2
    congr 1
    simp only [doleansDensity, quadInt_neg]
    rw [h2, h1, ← Real.exp_neg]
    congr 1
    ring
  have hZm : Measurable fun ω => doleansDensity P 𝓕 B θ T ω :=
    ((stronglyMeasurable_doleansDensity hθ hθb hθreg T).mono (𝓕.le T)).measurable
  have hZi : Measurable fun ω => (doleansDensity P 𝓕 B θ T ω)⁻¹ := hZm.inv
  rw [girsanovMeasure, withDensity_congr_ae hdens, girsanovMeasure,
    ← withDensity_mul _ hZm.ennreal_ofReal hZi.ennreal_ofReal]
  conv_rhs => rw [← withDensity_one (μ := P)]
  congr 1
  funext ω
  have hpos := doleansDensity_pos (P := P) (𝓕 := 𝓕) (B := B) (θ := θ) T ω
  simp only [Pi.mul_apply, Pi.one_apply]
  rw [← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one]

/-! ### Transfer of laws through the reverse change of measure -/

section Transfer

variable {E : Type*} [MeasurableSpace E]

/-- If `I` is the limit in probability of `R_n ∘ X`, and `R_{n_k}` converges to `J` on a set that `X`
charges fully, then `I = J ∘ X` almost surely. -/
theorem ae_eq_comp_of_tendstoInMeasure {Ω' : Type*} {m' : MeasurableSpace Ω'} {Q : Measure Ω'}
    [IsFiniteMeasure Q] {X : Ω' → E} (hX : Measurable X) {R : ℕ → E → ℝ}
    (hR : ∀ n, Measurable (R n)) {ns : ℕ → ℕ} (hns : StrictMono ns) {J : E → ℝ} {S : Set E}
    (hSJ : ∀ e ∈ S, Tendsto (fun k => R (ns k) e) atTop (𝓝 (J e)))
    (hXS : ∀ᵐ ω ∂Q, X ω ∈ S) {I : Ω' → ℝ}
    (hI : TendstoInMeasure Q (fun n ω => R n (X ω)) atTop I) : I =ᵐ[Q] fun ω => J (X ω) :=
  tendstoInMeasure_ae_unique (hI.comp hns.tendsto_atTop)
    (tendstoInMeasure_of_tendsto_ae (fun k => ((hR (ns k)).comp hX).aestronglyMeasurable)
      (hXS.mono fun _ hω => hSJ _ hω))

/-- **Limits in probability of the same functionals of equally distributed elements.** If `X₁`, `X₂`
have the same law and `I_k` is the limit in probability of `R_n(X_k)` for the same measurable
functionals `R_n`, then `(X₁, I₁)` and `(X₂, I₂)` have the same law: `I_k = J(X_k)` almost surely for
one measurable `J` (the `limsup` along a subsequence chosen for `X₁`). -/
theorem map_prod_eq_of_tendstoInMeasure {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁}
    {m₂ : MeasurableSpace Ω₂} {Q₁ : Measure Ω₁} {Q₂ : Measure Ω₂} [IsFiniteMeasure Q₁]
    [IsFiniteMeasure Q₂] {X₁ : Ω₁ → E} {X₂ : Ω₂ → E} (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hlaw : Q₁.map X₁ = Q₂.map X₂) {R : ℕ → E → ℝ} (hR : ∀ n, Measurable (R n))
    {I₁ : Ω₁ → ℝ} {I₂ : Ω₂ → ℝ}
    (h₁ : TendstoInMeasure Q₁ (fun n ω => R n (X₁ ω)) atTop I₁)
    (h₂ : TendstoInMeasure Q₂ (fun n ω => R n (X₂ ω)) atTop I₂) :
    Q₁.map (fun ω => (X₁ ω, I₁ ω)) = Q₂.map (fun ω => (X₂ ω, I₂ ω)) := by
  obtain ⟨ns, hns, hae₁⟩ := h₁.exists_seq_tendsto_ae
  set J : E → ℝ := fun e => limsup (fun k => R (ns k) e) atTop with hJ
  have hJm : Measurable J := Measurable.limsup fun k => hR (ns k)
  set S : Set E := {e | ∃ c, Tendsto (fun k => R (ns k) e) atTop (𝓝 c)} with hS
  have hSm : MeasurableSet S :=
    measurableSet_exists_tendsto fun k => hR (ns k)
  have hSJ : ∀ e ∈ S, Tendsto (fun k => R (ns k) e) atTop (𝓝 (J e)) := fun e ⟨c, hc⟩ => by
    have hJe : J e = c := hc.limsup_eq
    rw [hJe]
    exact hc
  have hS₁ : ∀ᵐ ω ∂Q₁, X₁ ω ∈ S := hae₁.mono fun ω hω => ⟨_, hω⟩
  have hS₂ : ∀ᵐ ω ∂Q₂, X₂ ω ∈ S := by
    have h := (ae_map_iff hX₁.aemeasurable hSm).2 hS₁
    rw [hlaw] at h
    exact (ae_map_iff hX₂.aemeasurable hSm).1 h
  have e₁ := ae_eq_comp_of_tendstoInMeasure hX₁ hR hns hSJ hS₁ h₁
  have e₂ := ae_eq_comp_of_tendstoInMeasure hX₂ hR hns hSJ hS₂ h₂
  have p₁ : (fun ω => (X₁ ω, I₁ ω)) =ᵐ[Q₁] (fun e => (e, J e)) ∘ X₁ :=
    e₁.mono fun ω h => by simp only [Function.comp_apply, h]
  have p₂ : (fun ω => (X₂ ω, I₂ ω)) =ᵐ[Q₂] (fun e => (e, J e)) ∘ X₂ :=
    e₂.mono fun ω h => by simp only [Function.comp_apply, h]
  have hpm : Measurable fun e => (e, J e) := measurable_id.prodMk hJm
  rw [Measure.map_congr p₁, Measure.map_congr p₂, ← Measure.map_map hpm hX₁,
    ← Measure.map_map hpm hX₂, hlaw]

variable {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}

/-- The reverse density as an explicit exponential: `P(X ∈ S) = ∫_{X ∈ S} exp(∫ θ dB̃ − ½ ∫ θ²) dQ`. -/
theorem measure_preimage_eq_lintegral_girsanov [IsProbabilityMeasure P]
    (hBF : IsFilteredBrownianReal 𝓕 B P) (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) {T : ℝ≥0}
    (hθT : ∀ t ω, T ≤ t → θ t ω = 0) {X : Ω → E} (hX : Measurable X) {S : Set E}
    (hS : MeasurableSet S) :
    P (X ⁻¹' S) = ∫⁻ ω, ((Prod.fst ⁻¹' S).indicator
      (fun p : E × ℝ => ENNReal.ofReal (Real.exp (p.2 - quadInt θ T ω / 2))))
        (X ω, stochIntegral (girsanovMeasure P 𝓕 B θ T) 𝓕 (girsanovProcess B θ) θ T ω)
        ∂(girsanovMeasure P 𝓕 B θ T) := by
  have hPB := isFilteredPreBrownian_of_isFilteredBrownianReal hBF
  have hQeq := isEquivProbMeasure_girsanovMeasure (B := B) hθ.stronglyAdapted hθb hθreg T
  have := hQeq.isProb
  have hBQ := isFilteredBrownianReal_girsanov hBF hθ hθb hθreg hθT
  have hQB := isFilteredPreBrownian_of_isFilteredBrownianReal hBQ
  have hregQ : IsRiemannRegular (girsanovMeasure P 𝓕 B θ T) θ := hQeq.ac.ae_le hθreg
  have hneg := stochIntegral_neg_ae_eq hQB hθ.stronglyAdapted hθb hregQ T
  conv_lhs => rw [← girsanovMeasure_neg_eq hBF hθ hθb hθreg hθT]
  rw [girsanovMeasure, withDensity_apply _ (hX hS), ← lintegral_indicator (hX hS)]
  refine lintegral_congr_ae ?_
  filter_upwards [hneg] with ω h
  by_cases hω : X ω ∈ S
  · rw [indicator_of_mem (show ω ∈ X ⁻¹' S from hω),
      indicator_of_mem (show (X ω, _) ∈ Prod.fst ⁻¹' S from hω)]
    simp only [doleansDensity, quadInt_neg, h, neg_neg]
  · rw [indicator_of_notMem (show ω ∉ X ⁻¹' S from hω),
      indicator_of_notMem (show (X ω, _) ∉ Prod.fst ⁻¹' S from hω)]

/-- **Transfer of laws through the reverse change of measure** (Specification L488: two different
laws in the multiple-force-point case would give, by the reverse change of measure, two different laws
in the reference case). For `k = 1, 2` let `Q_k = Z_T · P_k` be Girsanov measures (drifts `θ_k`
vanishing after `T`) and `X_k` random elements of the same measurable space. If the laws of `X₁` under
`Q₁` and `X₂` under `Q₂` agree, and the Riemann sums of `θ_k` against the `Q_k`-Brownian motion
`B_k + ∫ θ_k` and the quadratic integrals `∫₀ᵀ θ_k²` are the same measurable functionals `R_n`, `q` of
`X_k`, then the laws of `X₁` under `P₁` and `X₂` under `P₂` agree: `dP_k/dQ_k = exp(∫ θ_k dB̃_k − ½ ∫ θ_k²)`
is the same functional of `(X_k, lim R_n(X_k))`. -/
theorem map_eq_of_girsanov {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂] {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    {B₁ θ₁ : ℝ≥0 → Ω₁ → ℝ} {B₂ θ₂ : ℝ≥0 → Ω₂ → ℝ} (hB₁ : IsFilteredBrownianReal 𝓕₁ B₁ P₁)
    (hB₂ : IsFilteredBrownianReal 𝓕₂ B₂ P₂) (hθ₁ : IsStronglyProgressive 𝓕₁ θ₁)
    (hθ₂ : IsStronglyProgressive 𝓕₂ θ₂) {C₁ C₂ : ℝ} (hθb₁ : ∀ t ω, |θ₁ t ω| ≤ C₁)
    (hθb₂ : ∀ t ω, |θ₂ t ω| ≤ C₂) (hθreg₁ : IsRiemannRegular P₁ θ₁)
    (hθreg₂ : IsRiemannRegular P₂ θ₂) {T : ℝ≥0} (hθT₁ : ∀ t ω, T ≤ t → θ₁ t ω = 0)
    (hθT₂ : ∀ t ω, T ≤ t → θ₂ t ω = 0) {X₁ : Ω₁ → E} {X₂ : Ω₂ → E} (hX₁ : Measurable X₁)
    (hX₂ : Measurable X₂)
    (hlaw : (girsanovMeasure P₁ 𝓕₁ B₁ θ₁ T).map X₁ = (girsanovMeasure P₂ 𝓕₂ B₂ θ₂ T).map X₂)
    {R : ℕ → E → ℝ} (hR : ∀ n, Measurable (R n)) {q : E → ℝ} (hq : Measurable q)
    (hR₁ : ∀ n, riemannSum (girsanovProcess B₁ θ₁) θ₁ n T
      =ᵐ[girsanovMeasure P₁ 𝓕₁ B₁ θ₁ T] fun ω => R n (X₁ ω))
    (hR₂ : ∀ n, riemannSum (girsanovProcess B₂ θ₂) θ₂ n T
      =ᵐ[girsanovMeasure P₂ 𝓕₂ B₂ θ₂ T] fun ω => R n (X₂ ω))
    (hq₁ : quadInt θ₁ T =ᵐ[girsanovMeasure P₁ 𝓕₁ B₁ θ₁ T] fun ω => q (X₁ ω))
    (hq₂ : quadInt θ₂ T =ᵐ[girsanovMeasure P₂ 𝓕₂ B₂ θ₂ T] fun ω => q (X₂ ω)) :
    P₁.map X₁ = P₂.map X₂ := by
  have hPB₁ := isFilteredPreBrownian_of_isFilteredBrownianReal hB₁
  have hPB₂ := isFilteredPreBrownian_of_isFilteredBrownianReal hB₂
  have hQ₁ := isEquivProbMeasure_girsanovMeasure (B := B₁) hθ₁.stronglyAdapted hθb₁ hθreg₁ T
  have hQ₂ := isEquivProbMeasure_girsanovMeasure (B := B₂) hθ₂.stronglyAdapted hθb₂ hθreg₂ T
  have := hQ₁.isProb
  have := hQ₂.isProb
  have hQB₁ := isFilteredPreBrownian_of_isFilteredBrownianReal
    (isFilteredBrownianReal_girsanov hB₁ hθ₁ hθb₁ hθreg₁ hθT₁)
  have hQB₂ := isFilteredPreBrownian_of_isFilteredBrownianReal
    (isFilteredBrownianReal_girsanov hB₂ hθ₂ hθb₂ hθreg₂ hθT₂)
  have hT₁ : TendstoInMeasure (girsanovMeasure P₁ 𝓕₁ B₁ θ₁ T) (fun n ω => R n (X₁ ω)) atTop
      (stochIntegral (girsanovMeasure P₁ 𝓕₁ B₁ θ₁ T) 𝓕₁ (girsanovProcess B₁ θ₁) θ₁ T) :=
    (tendstoInMeasure_riemannSum hQB₁ hθ₁.stronglyAdapted hθb₁ (hQ₁.ac.ae_le hθreg₁) T).congr_left
      hR₁
  have hT₂ : TendstoInMeasure (girsanovMeasure P₂ 𝓕₂ B₂ θ₂ T) (fun n ω => R n (X₂ ω)) atTop
      (stochIntegral (girsanovMeasure P₂ 𝓕₂ B₂ θ₂ T) 𝓕₂ (girsanovProcess B₂ θ₂) θ₂ T) :=
    (tendstoInMeasure_riemannSum hQB₂ hθ₂.stronglyAdapted hθb₂ (hQ₂.ac.ae_le hθreg₂) T).congr_left
      hR₂
  have hpair := map_prod_eq_of_tendstoInMeasure hX₁ hX₂ hlaw hR hT₁ hT₂
  have hI₁ : Measurable (stochIntegral (girsanovMeasure P₁ 𝓕₁ B₁ θ₁ T) 𝓕₁ (girsanovProcess B₁ θ₁)
      θ₁ T) := ((isRiemannLimit_stochIntegral hQB₁ hθ₁.stronglyAdapted hθb₁ (hQ₁.ac.ae_le hθreg₁)
        T).1.mono (𝓕₁.le T)).measurable
  have hI₂ : Measurable (stochIntegral (girsanovMeasure P₂ 𝓕₂ B₂ θ₂ T) 𝓕₂ (girsanovProcess B₂ θ₂)
      θ₂ T) := ((isRiemannLimit_stochIntegral hQB₂ hθ₂.stronglyAdapted hθb₂ (hQ₂.ac.ae_le hθreg₂)
        T).1.mono (𝓕₂.le T)).measurable
  ext S hS
  rw [Measure.map_apply hX₁ hS, Measure.map_apply hX₂ hS,
    measure_preimage_eq_lintegral_girsanov hB₁ hθ₁ hθb₁ hθreg₁ hθT₁ hX₁ hS,
    measure_preimage_eq_lintegral_girsanov hB₂ hθ₂ hθb₂ hθreg₂ hθT₂ hX₂ hS]
  set G : E × ℝ → ℝ≥0∞ := (Prod.fst ⁻¹' S).indicator
    (fun p : E × ℝ => ENNReal.ofReal (Real.exp (p.2 - q p.1 / 2))) with hG
  have hGm : Measurable G :=
    (((measurable_snd.sub ((hq.comp measurable_fst).div_const 2)).exp).ennreal_ofReal).indicator
      (hS.preimage measurable_fst)
  have h₁ : ∫⁻ ω, ((Prod.fst ⁻¹' S).indicator
        (fun p : E × ℝ => ENNReal.ofReal (Real.exp (p.2 - quadInt θ₁ T ω / 2))))
        (X₁ ω, stochIntegral (girsanovMeasure P₁ 𝓕₁ B₁ θ₁ T) 𝓕₁ (girsanovProcess B₁ θ₁) θ₁ T ω)
        ∂(girsanovMeasure P₁ 𝓕₁ B₁ θ₁ T)
      = ∫⁻ p, G p ∂((girsanovMeasure P₁ 𝓕₁ B₁ θ₁ T).map fun ω => (X₁ ω,
          stochIntegral (girsanovMeasure P₁ 𝓕₁ B₁ θ₁ T) 𝓕₁ (girsanovProcess B₁ θ₁) θ₁ T ω)) := by
    rw [lintegral_map hGm (hX₁.prodMk hI₁)]
    refine lintegral_congr_ae ?_
    filter_upwards [hq₁] with ω hω
    simp only [hG, hω]
    by_cases h : X₁ ω ∈ S
    · rw [indicator_of_mem (show (X₁ ω, _) ∈ Prod.fst ⁻¹' S from h),
        indicator_of_mem (show (X₁ ω, _) ∈ Prod.fst ⁻¹' S from h)]
    · rw [indicator_of_notMem (show (X₁ ω, _) ∉ Prod.fst ⁻¹' S from h),
        indicator_of_notMem (show (X₁ ω, _) ∉ Prod.fst ⁻¹' S from h)]
  have h₂ : ∫⁻ ω, ((Prod.fst ⁻¹' S).indicator
        (fun p : E × ℝ => ENNReal.ofReal (Real.exp (p.2 - quadInt θ₂ T ω / 2))))
        (X₂ ω, stochIntegral (girsanovMeasure P₂ 𝓕₂ B₂ θ₂ T) 𝓕₂ (girsanovProcess B₂ θ₂) θ₂ T ω)
        ∂(girsanovMeasure P₂ 𝓕₂ B₂ θ₂ T)
      = ∫⁻ p, G p ∂((girsanovMeasure P₂ 𝓕₂ B₂ θ₂ T).map fun ω => (X₂ ω,
          stochIntegral (girsanovMeasure P₂ 𝓕₂ B₂ θ₂ T) 𝓕₂ (girsanovProcess B₂ θ₂) θ₂ T ω)) := by
    rw [lintegral_map hGm (hX₂.prodMk hI₂)]
    refine lintegral_congr_ae ?_
    filter_upwards [hq₂] with ω hω
    simp only [hG, hω]
    by_cases h : X₂ ω ∈ S
    · rw [indicator_of_mem (show (X₂ ω, _) ∈ Prod.fst ⁻¹' S from h),
        indicator_of_mem (show (X₂ ω, _) ∈ Prod.fst ⁻¹' S from h)]
    · rw [indicator_of_notMem (show (X₂ ω, _) ∉ Prod.fst ⁻¹' S from h),
        indicator_of_notMem (show (X₂ ω, _) ∉ Prod.fst ⁻¹' S from h)]
  rw [h₁, h₂, hpair]

end Transfer

end Girsanov

end InteractingSLE
