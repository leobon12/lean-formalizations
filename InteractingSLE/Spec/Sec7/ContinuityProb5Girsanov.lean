/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AddMarksInverse
import InteractingSLE.WangWu.EscapeRemote
import InteractingSLE.Spec.Sec2.AddMarksGirsanov

/-!
# Whole-tail Girsanov with bounded energy

Packet PROVE-SEC7-C5. Specification §7.3, Aux. lemma 101 (`source/spec/p337-384.md` L262–L264, p. 348): "Stop
additionally when the angular clock reaches `m`. The bounded-energy exponential and its reciprocal are uniformly
integrable and have strictly positive terminal values. Applying Girsanov to the integrated equations […] Hence the
two entire stopped driving laws are equivalent, also at an infinite terminal physical time"; Aux. lemma 106 (p. 354,
"On the final infinite band, deleting the opposite mark has finite energy"); Astra, *Formalization proofs*, L1561
("Bounded-energy adapted Girsanov gives equivalent measures on the entire stopped future: its exponential density and
reciprocal have positive integrable limits, by the deterministic energy bound").

For a Brownian motion `B` of a filtration `𝓕`, a bounded progressive drift `θ` that is left-continuous at almost
every time, and a deterministic energy bound `∫₀^∞ θ² ≤ K` (almost surely), the Doléans densities
`Z_n = exp(-∫₀ⁿ θ dB - ½ ∫₀ⁿ θ²)` at integer times are a martingale bounded in `L²` (`E Z_n² ≤ e^K`), hence uniformly
integrable, with an `L¹` and almost sure limit `Z_∞` (`tailDensity`); `E Z_n⁻¹ ≤ e^K` and Fatou make `Z_∞ > 0` almost
surely. Under `Q_∞ = Z_∞ · P` (`girsanovMeasureTail`):

* `Q_∞` is a probability measure equivalent to `P` (`isEquivProbMeasure_girsanovMeasureTail`);
* `Q_∞` agrees on `𝓕_d` with the Girsanov measure of every horizon `T ≥ d` (`girsanovMeasureTail_apply`);
* `B + ∫₀^· θ` is a Brownian motion of `𝓕` under `Q_∞` on the whole time line
  (`isFilteredBrownianReal_girsanovTail`), by the bounded-horizon theorem `isFilteredBrownianReal_girsanov` for the
  drifts cut at the integers.

The moment bounds use `(Z^θ)² = Z^{2θ} e^{∫θ²}` and `(Z^θ)⁻¹ = Z^{-θ} e^{∫θ²}` (homogeneity of the Itô integral,
`WangWu.Remote.stochIntegral_const_mul_ae_eq`) and `E Z^{cθ} = 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B θ : ℝ≥0 → Ω → ℝ}

/-! ### Moments of the Doléans density under a bounded energy -/

section Moments

variable [IsProbabilityMeasure P]

/-- `Z^{cθ} = exp(-c ∫θ dB - (c²/2) ∫θ²)` almost surely. -/
theorem doleansDensity_const_mul_ae_eq (hB : IsFilteredPreBrownian B 𝓕 P) (hθm : StronglyAdapted 𝓕 θ)
    {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) (c : ℝ) (t : ℝ≥0) :
    doleansDensity P 𝓕 B (fun s ω => c * θ s ω) t =ᵐ[P]
      fun ω => Real.exp (-(c * stochIntegral P 𝓕 B θ t ω) - c ^ 2 * quadInt θ t ω / 2) := by
  filter_upwards [WangWu.Remote.stochIntegral_const_mul_ae_eq hB hθm hθb hθreg c t] with ω hω
  have hq : quadInt (fun s ω => c * θ s ω) t ω = c ^ 2 * quadInt θ t ω := by
    simp only [quadInt, mul_pow]
    exact intervalIntegral.integral_const_mul _ _
  simp only [doleansDensity, hω, hq]

/-- **`E Z_t² ≤ e^K`** under the energy bound `∫₀ᵗ θ² ≤ K`. -/
theorem integral_sq_doleansDensity_le (hB : IsFilteredPreBrownian B 𝓕 P)
    (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) {K : ℝ} (t : ℝ≥0) (hK : ∀ᵐ ω ∂P, quadInt θ t ω ≤ K) :
    ∫ ω, doleansDensity P 𝓕 B θ t ω ^ 2 ∂P ≤ Real.exp K := by
  have hθm := hθ.stronglyAdapted
  have hm2 : StronglyAdapted 𝓕 (fun s ω => 2 * θ s ω) := fun s => (hθm s).const_mul 2
  have hb2 : ∀ s ω, |2 * θ s ω| ≤ 2 * C := fun s ω => by
    rw [abs_mul, abs_two]; exact mul_le_mul_of_nonneg_left (hθb s ω) zero_le_two
  have hreg2 : IsRiemannRegular P (fun s ω => 2 * θ s ω) :=
    hθreg.mono fun ω hω => hω.mono fun u hu => hu.const_mul 2
  have h2 := doleansDensity_const_mul_ae_eq hB hθm hθb hθreg 2 t
  have hle : (fun ω => doleansDensity P 𝓕 B θ t ω ^ 2) ≤ᵐ[P]
      fun ω => Real.exp K * doleansDensity P 𝓕 B (fun s ω => 2 * θ s ω) t ω := by
    filter_upwards [h2, hK] with ω hω hKω
    rw [hω, doleansDensity, ← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by push_cast; nlinarith)
  have hint2 : Integrable (doleansDensity P 𝓕 B (fun s ω => 2 * θ s ω) t) P :=
    (memLp_doleansDensity (B := B) hm2 hb2 hreg2 t).integrable one_le_two
  calc ∫ ω, doleansDensity P 𝓕 B θ t ω ^ 2 ∂P
      ≤ ∫ ω, Real.exp K * doleansDensity P 𝓕 B (fun s ω => 2 * θ s ω) t ω ∂P :=
        integral_mono_ae ((memLp_doleansDensity (B := B) hθm hθb hθreg t).integrable_sq)
          (hint2.const_mul _) hle
    _ = Real.exp K := by
        rw [integral_const_mul, integral_doleansDensity (B := B) hm2 hb2 hreg2 t, mul_one]

/-- **`E Z_t⁻¹ ≤ e^K`** under the energy bound `∫₀ᵗ θ² ≤ K` (as a lower integral). -/
theorem lintegral_inv_doleansDensity_le (hB : IsFilteredPreBrownian B 𝓕 P)
    (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) {K : ℝ} (t : ℝ≥0) (hK : ∀ᵐ ω ∂P, quadInt θ t ω ≤ K) :
    ∫⁻ ω, ENNReal.ofReal (doleansDensity P 𝓕 B θ t ω)⁻¹ ∂P ≤ ENNReal.ofReal (Real.exp K) := by
  have hθm := hθ.stronglyAdapted
  have hm1 : StronglyAdapted 𝓕 (fun s ω => (-1) * θ s ω) := fun s => (hθm s).const_mul (-1)
  have hb1 : ∀ s ω, |(-1) * θ s ω| ≤ C := fun s ω => by rw [neg_one_mul, abs_neg]; exact hθb s ω
  have hreg1 : IsRiemannRegular P (fun s ω => (-1) * θ s ω) :=
    hθreg.mono fun ω hω => hω.mono fun u hu => hu.const_mul (-1)
  have h1 := doleansDensity_const_mul_ae_eq hB hθm hθb hθreg (-1) t
  have hle : (fun ω => (doleansDensity P 𝓕 B θ t ω)⁻¹) ≤ᵐ[P]
      fun ω => Real.exp K * doleansDensity P 𝓕 B (fun s ω => (-1) * θ s ω) t ω := by
    filter_upwards [h1, hK] with ω hω hKω
    rw [hω, doleansDensity, ← Real.exp_neg, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  have hint1 : Integrable (doleansDensity P 𝓕 B (fun s ω => (-1) * θ s ω) t) P :=
    (memLp_doleansDensity (B := B) hm1 hb1 hreg1 t).integrable one_le_two
  have hI : Integrable (fun ω => Real.exp K * doleansDensity P 𝓕 B (fun s ω => (-1) * θ s ω) t ω) P :=
    hint1.const_mul _
  calc ∫⁻ ω, ENNReal.ofReal (doleansDensity P 𝓕 B θ t ω)⁻¹ ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp K * doleansDensity P 𝓕 B (fun s ω => (-1) * θ s ω) t ω) ∂P :=
        lintegral_mono_ae (hle.mono fun ω h => ENNReal.ofReal_le_ofReal h)
    _ = ENNReal.ofReal (∫ ω, Real.exp K * doleansDensity P 𝓕 B (fun s ω => (-1) * θ s ω) t ω ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hI
          (Eventually.of_forall fun ω => (mul_pos (Real.exp_pos K) (doleansDensity_pos t ω)).le)).symm
    _ = ENNReal.ofReal (Real.exp K) := by
        rw [integral_const_mul, integral_doleansDensity (B := B) hm1 hb1 hreg1 t, mul_one]

end Moments

/-! ### The terminal density and the whole-tail measure -/

/-- The filtration at integer times. -/
def natFiltration (𝓕 : Filtration ℝ≥0 mΩ) : Filtration ℕ mΩ where
  seq n := 𝓕 n
  mono' _ _ h := 𝓕.mono (by exact_mod_cast h)
  le' n := 𝓕.le n

theorem natFiltration_apply (𝓕 : Filtration ℝ≥0 mΩ) (n : ℕ) : natFiltration 𝓕 n = 𝓕 n := rfl

/-- The Doléans densities at integer times. -/
def densAt (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (B θ : ℝ≥0 → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  doleansDensity P 𝓕 B θ n

/-- **The terminal density** `Z_∞`: the limit of the densities at integer times. -/
def tailDensity (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (B θ : ℝ≥0 → Ω → ℝ) : Ω → ℝ :=
  (natFiltration 𝓕).limitProcess (densAt P 𝓕 B θ) P

/-- **The whole-tail Girsanov measure** `Q_∞ = Z_∞ · P`. -/
def girsanovMeasureTail (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (B θ : ℝ≥0 → Ω → ℝ) : Measure Ω :=
  P.withDensity fun ω => ENNReal.ofReal (tailDensity P 𝓕 B θ ω)

theorem measurable_tailDensity : Measurable (tailDensity P 𝓕 B θ) :=
  Filtration.stronglyMeasurable_limit_process'.measurable

section Tail

variable [IsProbabilityMeasure P] [hB : IsFilteredPreBrownian B 𝓕 P]

include hB

theorem martingale_densAt (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) : Martingale (densAt P 𝓕 B θ) (natFiltration 𝓕) P := by
  have hM := martingale_doleansDensity (B := B) hθ hθb hθreg
  exact ⟨fun n => hM.1 n, fun i j hij => hM.2 i j (by exact_mod_cast hij)⟩

theorem eLpNorm_one_densAt (hθm : StronglyAdapted 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) (n : ℕ) : eLpNorm (densAt P 𝓕 B θ n) 1 P = 1 := by
  have hint : Integrable (densAt P 𝓕 B θ n) P :=
    (memLp_doleansDensity (B := B) hθm hθb hθreg n).integrable one_le_two
  rw [eLpNorm_one_eq_lintegral_enorm]
  have e : (fun ω => ‖densAt P 𝓕 B θ n ω‖ₑ) = fun ω => ENNReal.ofReal (densAt P 𝓕 B θ n ω) :=
    funext fun ω => Real.enorm_eq_ofReal (doleansDensity_pos _ ω).le
  rw [e, ← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun ω => (doleansDensity_pos _ ω).le)]
  rw [show ∫ ω, densAt P 𝓕 B θ n ω ∂P = 1 from integral_doleansDensity (B := B) hθm hθb hθreg n,
    ENNReal.ofReal_one]

/-- **The densities at integer times are uniformly integrable** under a bounded energy. -/
theorem uniformIntegrable_densAt (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) {K : ℝ}
    (hK : ∀ᵐ ω ∂P, ∀ t, quadInt θ t ω ≤ K) : UniformIntegrable (densAt P 𝓕 B θ) 1 P := by
  have hθm := hθ.stronglyAdapted
  refine ⟨fun n => (memLp_doleansDensity (B := B) hθm hθb hθreg n).aestronglyMeasurable,
    MathFin.unifIntegrable_one_of_sq_integral_le
      (fun n => memLp_doleansDensity (B := B) hθm hθb hθreg n)
      (fun n => integral_sq_doleansDensity_le hB hθ hθb hθreg n (hK.mono fun ω h => h n)),
    1, fun n => ?_⟩
  rw [eLpNorm_one_densAt (B := B) hθm hθb hθreg n, ENNReal.coe_one]

theorem densAt_ae_eq_condExp (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) {K : ℝ} (hK : ∀ᵐ ω ∂P, ∀ t, quadInt θ t ω ≤ K) (n : ℕ) :
    densAt P 𝓕 B θ n =ᵐ[P] P[tailDensity P 𝓕 B θ | 𝓕 n] :=
  (martingale_densAt (B := B) hθ hθb hθreg).ae_eq_condExp_limitProcess
    (uniformIntegrable_densAt (B := B) hθ hθb hθreg hK) n

theorem ae_tendsto_densAt (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) {K : ℝ} (hK : ∀ᵐ ω ∂P, ∀ t, quadInt θ t ω ≤ K) :
    ∀ᵐ ω ∂P, Tendsto (fun n => densAt P 𝓕 B θ n ω) atTop (𝓝 (tailDensity P 𝓕 B θ ω)) :=
  (martingale_densAt (B := B) hθ hθb hθreg).submartingale.ae_tendsto_limitProcess_of_uniformIntegrable
    (uniformIntegrable_densAt (B := B) hθ hθb hθreg hK)

theorem integrable_tailDensity (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) {K : ℝ} (hK : ∀ᵐ ω ∂P, ∀ t, quadInt θ t ω ≤ K) :
    Integrable (tailDensity P 𝓕 B θ) P := by
  obtain ⟨-, -, R, hR⟩ := uniformIntegrable_densAt (B := B) hθ hθb hθreg hK
  exact (Filtration.memLp_limitProcess_of_eLpNorm_bdd
    (fun n => (memLp_doleansDensity (B := B) hθ.stronglyAdapted hθb hθreg n).aestronglyMeasurable)
    hR).integrable le_rfl

theorem ae_tailDensity_nonneg (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) {K : ℝ} (hK : ∀ᵐ ω ∂P, ∀ t, quadInt θ t ω ≤ K) :
    ∀ᵐ ω ∂P, 0 ≤ tailDensity P 𝓕 B θ ω := by
  filter_upwards [ae_tendsto_densAt (B := B) hθ hθb hθreg hK] with ω hω
  exact ge_of_tendsto hω (Eventually.of_forall fun n => (doleansDensity_pos _ ω).le)

/-- **`∫_A Z_∞ = ∫_A Z_d`** for `A ∈ 𝓕_d`. -/
theorem setIntegral_tailDensity (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) {K : ℝ} (hK : ∀ᵐ ω ∂P, ∀ t, quadInt θ t ω ≤ K) {d : ℝ≥0}
    {A : Set Ω} (hA : MeasurableSet[𝓕 d] A) :
    ∫ ω in A, tailDensity P 𝓕 B θ ω ∂P = ∫ ω in A, doleansDensity P 𝓕 B θ d ω ∂P := by
  set n := ⌈(d : ℝ)⌉₊ with hn
  have hdn : d ≤ (n : ℝ≥0) := by simpa using le_shift d 0
  have hAn : MeasurableSet[𝓕 n] A := 𝓕.mono hdn A hA
  rw [← setIntegral_condExp (𝓕.le n) (integrable_tailDensity (B := B) hθ hθb hθreg hK) hAn,
    setIntegral_congr_ae (𝓕.le n A hAn) ((densAt_ae_eq_condExp (B := B) hθ hθb hθreg hK n).mono
      fun ω h _ => h.symm)]
  exact setIntegral_doleansDensity_eq (B := B) hθ.stronglyAdapted hθb hθreg hdn hA

theorem integral_tailDensity (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) {K : ℝ} (hK : ∀ᵐ ω ∂P, ∀ t, quadInt θ t ω ≤ K) :
    ∫ ω, tailDensity P 𝓕 B θ ω ∂P = 1 := by
  have h := setIntegral_tailDensity (B := B) hθ hθb hθreg hK (d := 0) (A := univ) MeasurableSet.univ
  rw [setIntegral_univ, setIntegral_univ] at h
  rw [h, integral_doleansDensity (B := B) hθ.stronglyAdapted hθb hθreg 0]

/-- **The terminal density is almost surely positive** (Fatou on `Z_n⁻¹`, `E Z_n⁻¹ ≤ e^K`). -/
theorem ae_tailDensity_pos (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) {K : ℝ} (hK : ∀ᵐ ω ∂P, ∀ t, quadInt θ t ω ≤ K) :
    ∀ᵐ ω ∂P, 0 < tailDensity P 𝓕 B θ ω := by
  have hθm := hθ.stronglyAdapted
  set g : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (densAt P 𝓕 B θ n ω)⁻¹ with hg
  have hgm : ∀ n, Measurable (g n) := fun n =>
    ((stronglyMeasurable_doleansDensity (B := B) hθ hθb hθreg n).mono (𝓕.le n)).measurable.inv
      |>.ennreal_ofReal
  have hbound : ∀ n, ∫⁻ ω, g n ω ∂P ≤ ENNReal.ofReal (Real.exp K) := fun n =>
    lintegral_inv_doleansDensity_le hB hθ hθb hθreg n (hK.mono fun ω h => h n)
  have hfat : ∫⁻ ω, liminf (fun n => g n ω) atTop ∂P ≤ ENNReal.ofReal (Real.exp K) :=
    (lintegral_liminf_le' fun n => (hgm n).aemeasurable).trans (liminf_le_of_le (by isBoundedDefault)
      fun b hb => let ⟨n, hn⟩ := hb.exists; hn.trans (hbound n))
  have hlt := ae_lt_top' (Measurable.liminf hgm).aemeasurable (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfat)
  filter_upwards [hlt, ae_tendsto_densAt (B := B) hθ hθb hθreg hK, ae_tailDensity_nonneg (B := B) hθ hθb hθreg hK]
    with ω hω htd hnn
  rcases hnn.lt_or_eq with hpos | hzero
  · exact hpos
  · exfalso
    have h0 : Tendsto (fun n => densAt P 𝓕 B θ n ω) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hzero ▸ htd, Eventually.of_forall fun n => doleansDensity_pos _ ω⟩
    have hinf : Tendsto (fun n => g n ω) atTop (𝓝 ⊤) :=
      (ENNReal.tendsto_ofReal_atTop.comp (tendsto_inv_nhdsGT_zero.comp h0))
    rw [hinf.liminf_eq] at hω
    exact lt_irrefl _ hω

/-- **The whole-tail measure agrees on `𝓕_d` with the Girsanov measure of every horizon `T ≥ d`.** -/
theorem girsanovMeasureTail_apply (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) {K : ℝ}
    (hK : ∀ᵐ ω ∂P, ∀ t, quadInt θ t ω ≤ K) {d T : ℝ≥0} (hdT : d ≤ T) {A : Set Ω}
    (hA : MeasurableSet[𝓕 d] A) :
    girsanovMeasureTail P 𝓕 B θ A = girsanovMeasure P 𝓕 B θ T A := by
  rw [girsanovMeasure_apply_eq_ofReal_setIntegral hθ hθb hθreg hdT hA, girsanovMeasureTail,
    withDensity_apply _ (𝓕.le d A hA), ← ofReal_integral_eq_lintegral_ofReal
      (integrable_tailDensity (B := B) hθ hθb hθreg hK).integrableOn
      (ae_restrict_of_ae (ae_tailDensity_nonneg (B := B) hθ hθb hθreg hK)),
    setIntegral_tailDensity (B := B) hθ hθb hθreg hK hA]

/-- **`Q_∞` is a probability measure equivalent to `P`.** -/
theorem isEquivProbMeasure_girsanovMeasureTail (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) {K : ℝ}
    (hK : ∀ᵐ ω ∂P, ∀ t, quadInt θ t ω ≤ K) :
    MathFin.IsEquivProbMeasure P (girsanovMeasureTail P 𝓕 B θ) := by
  refine MathFin.isEquivProbMeasure_withDensity_of_isProbabilityMeasure P
    measurable_tailDensity.aemeasurable (ae_tailDensity_pos (B := B) hθ hθb hθreg hK) ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_tailDensity (B := B) hθ hθb hθreg hK)
      (ae_tailDensity_nonneg (B := B) hθ hθb hθreg hK), integral_tailDensity (B := B) hθ hθb hθreg hK, ENNReal.ofReal_one]

end Tail

/-! ### The drift cut at a time -/

/-- `θ` cut at the time `n`: `θ_t` for `t < n`, `0` afterwards. -/
def cutAt (θ : ℝ≥0 → Ω → ℝ) (n : ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ := if t < n then θ t ω else 0

theorem abs_cutAt_le {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C) (n t : ℝ≥0) (ω : Ω) :
    |cutAt θ n t ω| ≤ |C| := by
  unfold cutAt
  split_ifs
  · exact (hθb t ω).trans (le_abs_self C)
  · rw [abs_zero]; exact abs_nonneg C

theorem cutAt_of_le {n t : ℝ≥0} (h : n ≤ t) (ω : Ω) : cutAt θ n t ω = 0 := by
  simp only [cutAt, not_lt.2 h, ite_false]

theorem cutAt_of_lt {n t : ℝ≥0} (h : t < n) (ω : Ω) : cutAt θ n t ω = θ t ω := by
  simp only [cutAt, h, ite_true]

theorem isStronglyProgressive_cutAt (hθ : IsStronglyProgressive 𝓕 θ) (n : ℝ≥0) :
    IsStronglyProgressive 𝓕 (cutAt θ n) := fun i => by
  have hs : MeasurableSet[Subtype.instMeasurableSpace.prod (𝓕 i)]
      {p : Set.Iic i × Ω | (p.1 : ℝ≥0) < n} :=
    measurableSet_lt (measurable_subtype_coe.comp
      (@measurable_fst _ _ Subtype.instMeasurableSpace (𝓕 i))) measurable_const
  exact StronglyMeasurable.ite hs (hθ i) stronglyMeasurable_const

theorem isRiemannRegular_cutAt (hθreg : IsRiemannRegular P θ) (n : ℝ≥0) :
    IsRiemannRegular P (cutAt θ n) := by
  filter_upwards [hθreg] with ω hω
  filter_upwards [hω, ae_ne_real (n : ℝ)] with u hu hun
  rcases lt_trichotomy u.toNNReal n with h | h | h
  · refine hu.congr (fun s hs => cutAt_of_lt (lt_of_le_of_lt (mem_Iic.1 hs) h) ω) (cutAt_of_lt h ω)
  · have hn0 : n = 0 := by
      rcases le_or_gt u 0 with hu0 | hu0
      · rw [← h, Real.toNNReal_of_nonpos hu0]
      · exfalso
        apply hun
        rw [← h, Real.coe_toNNReal _ hu0.le]
    subst hn0
    have e : (fun s => cutAt θ 0 s ω) = fun _ => 0 := funext fun s => cutAt_of_le zero_le ω
    rw [e]
    exact continuousWithinAt_const
  · have hev : ∀ᶠ s in 𝓝[Iic u.toNNReal] u.toNNReal, n < s :=
      nhdsWithin_le_nhds (lt_mem_nhds h)
    refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_ (cutAt_of_le h.le ω)
    filter_upwards [hev] with s hs
    exact cutAt_of_le hs.le ω

theorem drift_cutAt {n t : ℝ≥0} (htn : t ≤ n) (ω : Ω) : drift (cutAt θ n) t ω = drift θ t ω := by
  unfold drift
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_ne_real (n : ℝ)] with u hun hu
  rw [uIoc_of_le t.coe_nonneg] at hu
  refine cutAt_of_lt ?_ ω
  have hu' : u < n := lt_of_le_of_ne (hu.2.trans (by exact_mod_cast htn)) hun
  rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hu.1.le]
  exact hu'

theorem girsanovProcess_cutAt {n t : ℝ≥0} (htn : t ≤ n) (ω : Ω) :
    girsanovProcess B (cutAt θ n) t ω = girsanovProcess B θ t ω := by
  simp only [girsanovProcess, drift_cutAt htn ω]

/-! ### Transfer of laws between measures that agree on a sub-σ-algebra -/

theorem map_eq_of_forall_eq {μ ν : Measure[mΩ] Ω} {d : ℝ≥0}
    (h : ∀ A, MeasurableSet[𝓕 d] A → μ A = ν A) {E : Type*} [MeasurableSpace E] {f : Ω → E}
    (hf : Measurable[𝓕 d] f) : μ.map f = ν.map f := by
  ext S hS
  rw [Measure.map_apply (hf.mono (𝓕.le d) le_rfl) hS, Measure.map_apply (hf.mono (𝓕.le d) le_rfl) hS]
  exact h _ (hf hS)

theorem indep_of_forall_eq {μ ν : Measure[mΩ] Ω} {d : ℝ≥0} {m₁ m₂ : MeasurableSpace Ω} (h₁ : m₁ ≤ 𝓕 d)
    (h₂ : m₂ ≤ 𝓕 d) (h : ∀ A, MeasurableSet[𝓕 d] A → μ A = ν A) (hind : Indep m₁ m₂ ν) :
    Indep m₁ m₂ μ := by
  rw [Indep_iff] at hind ⊢
  intro t1 t2 ht1 ht2
  rw [h _ ((h₁ _ ht1).inter (h₂ _ ht2)), h _ (h₁ _ ht1), h _ (h₂ _ ht2)]
  exact hind t1 t2 ht1 ht2

/-! ### Girsanov's theorem on the whole time line -/

/-- **Whole-tail Girsanov** (bounded drift, bounded energy). Let `B` be a Brownian motion of `𝓕`, `θ` a bounded
progressive process that is left-continuous at almost every time, and suppose `∫₀ᵗ θ² ≤ K` for all `t` almost surely.
Under `Q_∞ = Z_∞ · P` the process `B + ∫₀^· θ` is a Brownian motion of `𝓕` on the whole time line, and `Q_∞` is a
probability measure equivalent to `P`. -/
theorem isFilteredBrownianReal_girsanovTail (hBF : IsFilteredBrownianReal 𝓕 B P)
    (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) {K : ℝ} (hK : ∀ᵐ ω ∂P, ∀ t, quadInt θ t ω ≤ K) :
    MathFin.IsEquivProbMeasure P (girsanovMeasureTail P 𝓕 B θ) ∧
      IsFilteredBrownianReal 𝓕 (girsanovProcess B θ) (girsanovMeasureTail P 𝓕 B θ) := by
  have : IsProbabilityMeasure P := hBF.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hB := isFilteredPreBrownian_of_isFilteredBrownianReal hBF
  have hQ := isEquivProbMeasure_girsanovMeasureTail (B := B) hθ hθb hθreg hK
  set Q := girsanovMeasureTail P 𝓕 B θ with hQdef
  have hadapt := stronglyAdapted_girsanovProcess (B := B) (P := P) hθ
  -- the cut drifts and their Girsanov measures
  have hcut : ∀ n : ℝ≥0, IsFilteredBrownianReal 𝓕 (girsanovProcess B (cutAt θ n))
      (girsanovMeasure P 𝓕 B (cutAt θ n) n) := fun n =>
    isFilteredBrownianReal_girsanov hBF (isStronglyProgressive_cutAt hθ n) (abs_cutAt_le hθb n)
      (isRiemannRegular_cutAt hθreg n) fun t ω h => cutAt_of_le h ω
  have hagree : ∀ n : ℝ≥0, ∀ A, MeasurableSet[𝓕 n] A → Q A = girsanovMeasure P 𝓕 B (cutAt θ n) n A :=
    fun n A hA => by
      rw [hQdef, girsanovMeasureTail_apply (B := B) hθ hθb hθreg hK le_rfl hA]
      exact girsanovMeasure_apply_eq_of_eqOn hBF hθ (isStronglyProgressive_cutAt hθ n) hθb
        (abs_cutAt_le hθb n) hθreg (isRiemannRegular_cutAt hθreg n) le_rfl le_rfl hA
        (Eventually.of_forall fun ω _ t ht => (cutAt_of_lt ht ω).symm)
  refine ⟨hQ, ⟨⟨⟨fun I => ?_⟩, ?_⟩, hadapt.adapted, fun s t hst => ?_⟩⟩
  · -- the finite-dimensional laws
    set n : ℝ≥0 := I.sup id with hn
    have hIn : ∀ i ∈ I, i ≤ n := fun i hi => Finset.le_sup (f := id) hi
    have hf : Measurable[𝓕 n] fun ω => I.restrict (girsanovProcess B θ · ω) := by
      have hi : ∀ i : I, Measurable[𝓕 n] fun ω => girsanovProcess B θ i ω := fun i =>
        ((hadapt i).measurable).mono (𝓕.mono (hIn i i.2)) le_rfl
      let _ : MeasurableSpace Ω := 𝓕 n
      exact measurable_pi_iff.2 hi
    have heq : (fun ω => I.restrict (girsanovProcess B θ · ω))
        = fun ω => I.restrict (girsanovProcess B (cutAt θ n) · ω) := by
      funext ω i
      simp only [Finset.restrict]
      exact (girsanovProcess_cutAt (hIn i i.2) ω).symm
    have hlaw := ((hcut n).1.toIsPreBrownianReal.hasLaw I)
    refine ⟨(hf.mono (𝓕.le n) le_rfl).aemeasurable, ?_⟩
    rw [map_eq_of_forall_eq (hagree n) hf, heq]
    exact hlaw.map_eq
  · -- continuity
    filter_upwards [hQ.ac.ae_le hBF.1.cont] with ω hω
    exact hω.add (continuous_drift hθ hθb ω)
  · -- independent increments
    set n : ℝ≥0 := t with hn
    have hind := (hcut n).2.2 s t hst
    have e : (fun ω => girsanovProcess B (cutAt θ n) t ω - girsanovProcess B (cutAt θ n) s ω)
        = fun ω => girsanovProcess B θ t ω - girsanovProcess B θ s ω := by
      funext ω
      rw [girsanovProcess_cutAt le_rfl ω, girsanovProcess_cutAt hst ω]
    rw [e] at hind
    refine indep_of_forall_eq (d := n) ?_ (𝓕.mono hst) (hagree n) hind
    refine MeasurableSpace.comap_le_iff_le_map.2 fun S hS => ?_
    exact (((hadapt t).measurable).sub (((hadapt s).measurable).mono (𝓕.mono hst) le_rfl)) hS

end Girsanov

end InteractingSLE
