import QuantumZipper.Proofs.Thm18.G3RCore
import QuantumZipper.Proofs.Thm18.R18G3TCM5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 (R-c): the change of measure from `B` to `C` on the `R(x)`-side

Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71–72 and Remark 5.7 (D85 update 18:30).
With the densities `F_C`, `F_B` of `R18G3TCore` (both measurable for the outside field and the
Palm length), write `F_C = ρ_K F_B + (F_C − ρ_K F_B)` with the truncated ratio
`ρ_K = min(F_C / F_B, K)` (`0` where `F_B = 0`). The first part is a bounded outside-measurable
reweighting of scheme `B` (after the shift `Ψ`), controlled by the mixing body of `B`
(`abs_integral_weight_sub_le`); the second part is the truncation error `T_K`
(`rside_core`). If `F > 0` everywhere a.s. (the region-1 tail node), `T_K → 0` by dominated
convergence (`tendsto_g3T`). Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-- The truncated density ratio. -/
def g3ρ (γ : ℝ) (i : G3Idx) (K : ℝ≥0∞) (p : Ω₀ × ℝ) : ℝ≥0∞ :=
  if g3FB γ i p = 0 then 0 else min (g3FC γ i p / g3FB γ i p) K

/-- The truncation error on `E`. -/
def g3T (γ : ℝ) (i : G3Idx) (E : Set (Ω₀ × ℝ)) (K : ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ p, E.indicator 1 p * (g3FC γ i p - g3ρ γ i K p * g3FB γ i p) ∂g3Leb

theorem measurable_g3ρ (γ : ℝ) (i : G3Idx) (K : ℝ≥0∞) :
    Measurable[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] (g3ρ γ i K) :=
  Measurable.ite ((measurable_g3FB γ i) (measurableSet_singleton 0)) measurable_const
    (((measurable_g3FC γ i).div (measurable_g3FB γ i)).min measurable_const)

theorem g3ρ_le (γ : ℝ) (i : G3Idx) (K : ℝ≥0∞) (p : Ω₀ × ℝ) : g3ρ γ i K p ≤ K := by
  unfold g3ρ; split_ifs
  · exact bot_le
  · exact min_le_right _ _

theorem g3FB_ne_top (γ : ℝ) (i : G3Idx) (p : Ω₀ × ℝ) : g3FB γ i p ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (g3F_le_one _ _ _ _)

theorem g3FC_le_one (γ : ℝ) (i : G3Idx) (p : Ω₀ × ℝ) : g3FC γ i p ≤ 1 := by
  unfold g3FC
  calc (Ioi 0).indicator 1 p.2 * g3F γ i p.1 (p.2 - g3a γ (g3wProf γ) i p.1)
      ≤ 1 * 1 := mul_le_mul' (indicator_le_self' (fun _ _ => zero_le_one) _ |>.trans le_rfl)
        (g3F_le_one _ _ _ _)
    _ = 1 := one_mul 1

theorem g3ρ_mul_le (γ : ℝ) (i : G3Idx) (K : ℝ≥0∞) (p : Ω₀ × ℝ) :
    g3ρ γ i K p * g3FB γ i p ≤ g3FC γ i p := by
  unfold g3ρ; split_ifs with h
  · simp
  · calc min (g3FC γ i p / g3FB γ i p) K * g3FB γ i p
        ≤ g3FC γ i p / g3FB γ i p * g3FB γ i p := mul_le_mul_left (min_le_left _ _) _
      _ = g3FC γ i p := ENNReal.div_mul_cancel h (g3FB_ne_top γ i p)

theorem measurable_g3T_integrand (γ : ℝ) (i : G3Idx) {E : Set (Ω₀ × ℝ)} (hE : MeasurableSet E)
    (K : ℝ≥0∞) : Measurable fun p => E.indicator 1 p * (g3FC γ i p - g3ρ γ i K p * g3FB γ i p) :=
  (measurable_const.indicator hE).mul
    (((measurable_g3FC γ i).mono (outsideSigmaPalm_le_g3 i) le_rfl).sub
      (((measurable_g3ρ γ i K).mono (outsideSigmaPalm_le_g3 i) le_rfl).mul
        ((measurable_g3FB γ i).mono (outsideSigmaPalm_le_g3 i) le_rfl)))

/-- The truncation error is bounded by `Z_C P_C(E)`. -/
theorem g3T_le {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {E : Set (Ω₀ × ℝ)}
    (hE : MeasurableSet[sig₂ i] E) (K : ℝ≥0∞) :
    g3T γ i E K ≤ g3pZ γ (g3wProf γ) i * g3pPalmLaw γ (g3wProf γ) i E := by
  have hE0 : MeasurableSet E := sig_le_g3 i _ _ E hE
  have hind : Measurable[sig₂ i] (E.indicator (1 : Ω₀ × ℝ → ℝ≥0∞)) :=
    measurable_const.indicator hE
  rw [← lintegral_indicator_one hE0, lintegral_g3pC_FC hγ hγ2 i hind]
  exact lintegral_mono fun p => mul_le_mul' le_rfl tsub_le_self

/-- **The truncation error vanishes** when the conditional tail is positive. -/
theorem tendsto_g3T {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx)
    (hpos : ∀ᵐ ω ∂gffBase.P, ∀ v, 0 < g3F γ i ω v) {E : Set (Ω₀ × ℝ)}
    (hE : MeasurableSet[sig₂ i] E) :
    Tendsto (fun n : ℕ => g3T γ i E n) atTop (𝓝 0) := by
  have hE0 : MeasurableSet E := sig_le_g3 i _ _ E hE
  have hfin : ∫⁻ p, E.indicator 1 p * g3FC γ i p ∂g3Leb ≠ ⊤ := by
    have hind : Measurable[sig₂ i] (E.indicator (1 : Ω₀ × ℝ → ℝ≥0∞)) :=
      measurable_const.indicator hE
    rw [← lintegral_g3pC_FC hγ hγ2 i hind, lintegral_indicator_one hE0]
    exact ENNReal.mul_ne_top (g3pZ_pos_lt_top hγ hγ2 i).2.ne (measure_ne_top _ _)
  have h := tendsto_lintegral_of_dominated_convergence (μ := g3Leb) (f := fun _ => 0)
    (F := fun (n : ℕ) p => E.indicator 1 p * (g3FC γ i p - g3ρ γ i n p * g3FB γ i p))
    (fun p => E.indicator 1 p * g3FC γ i p) (fun n => measurable_g3T_integrand γ i hE0 n)
    (fun n => ae_of_all _ fun p => mul_le_mul' le_rfl tsub_le_self) hfin ?_
  · simpa only [lintegral_zero, g3T] using h
  have hpos' : ∀ᵐ p ∂g3Leb, ∀ v, 0 < g3F γ i p.1 v :=
    Measure.quasiMeasurePreserving_fst.ae hpos
  filter_upwards [hpos'] with p hp
  have hB : g3FB γ i p ≠ 0 := (hp _).ne'
  have hq : g3FC γ i p / g3FB γ i p ≠ ⊤ :=
    ENNReal.div_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top (g3FC_le_one γ i p)) hB
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hq
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  have hmin : min (g3FC γ i p / g3FB γ i p) (n : ℝ≥0∞) = g3FC γ i p / g3FB γ i p :=
    min_eq_left (hN.le.trans (by exact_mod_cast hn))
  simp only [g3ρ, hB, ite_false, hmin, ENNReal.div_mul_cancel hB (g3FB_ne_top γ i p), tsub_self,
    mul_zero]

/-- **Core estimate of the `R(x)`-side transfer** (per index). -/
theorem rside_core {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) (K : ℝ≥0)
    {A E G : Set (Ω₀ × ℝ)} (hA : MeasurableSet[sig₂ i] A) (hE : MeasurableSet[sig₂ i] E)
    (hAE : A ⊆ E) (hER : E ⊆ g3pR γ (g3wProf γ) i ⁻¹' reg2 i)
    (hG : MeasurableSet[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] G) {a e : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1)
    (H : ∀ G', MeasurableSet[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] G' →
      |(g3pPalmLaw γ (g3wCut γ i.η) i).real
          (g3Ψ γ i ⁻¹' A ∩ g3pR γ (g3wCut γ i.η) i ⁻¹' reg2 i ∩ G') -
        a * (g3pPalmLaw γ (g3wCut γ i.η) i).real
          (g3Ψ γ i ⁻¹' E ∩ g3pR γ (g3wCut γ i.η) i ⁻¹' reg2 i ∩ G')| ≤ e) :
    |(g3pZ γ (g3wProf γ) i).toReal * ((g3pPalmLaw γ (g3wProf γ) i).real (A ∩ G) -
        a * (g3pPalmLaw γ (g3wProf γ) i).real (E ∩ G))| ≤
      (g3pZ γ (g3wCut γ i.η) i).toReal * ((K : ℝ) * (2 * e)) + (g3T γ i E K).toReal := by
  set PB := g3pPalmLaw γ (g3wCut γ i.η) i
  set PC := g3pPalmLaw γ (g3wProf γ) i
  set RB := g3pR γ (g3wCut γ i.η) i ⁻¹' reg2 i with hRB
  set ρ := g3ρ γ i (K : ℝ≥0∞) with hρ
  set w : Ω₀ × ℝ → ℝ≥0∞ := fun p => G.indicator 1 (g3Ψ γ i p) * ρ (g3Ψ γ i p) with hw
  have hZB := g3pBZ_pos_lt_top hγ hγ2 i
  have hZC := g3pZ_pos_lt_top hγ hγ2 i
  have hGs : MeasurableSet[sig₂ i] G := outsidePalm_le_sig₂ i G hG
  have hwm : Measurable[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] w :=
    ((measurable_const.indicator hG).comp (measurable_g3Ψ_O γ i)).mul
      ((measurable_g3ρ γ i K).comp (measurable_g3Ψ_O γ i))
  have hwK : ∀ p, w p ≤ K := fun p => by
    simp only [hw]
    by_cases hp : g3Ψ γ i p ∈ G
    · rw [indicator_of_mem hp, Pi.one_apply, one_mul]; exact g3ρ_le γ i K _
    · rw [indicator_of_notMem hp, zero_mul]; exact bot_le
  have hRBm : MeasurableSet RB :=
    ((measurable_g3pR γ _ i).mono (sig_le_g3 i _ _) le_rfl) measurableSet_Ioo
  have hΨ0 : Measurable (g3Ψ γ i) :=
    measurable_shift_prod ((measurable_g3Dsh γ i).mono (outsideSigma2_le gffBase.gff _ _ _ _) le_rfl)
  have hO0 : outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂ ≤ (inferInstance : MeasurableSpace (Ω₀ × ℝ)) := outsideSigmaPalm_le_g3 i
  -- the key identity
  have key : ∀ S, MeasurableSet[sig₂ i] S → S ⊆ E →
      g3pZ γ (g3wProf γ) i * PC (S ∩ G) = g3pZ γ (g3wCut γ i.η) i *
        ∫⁻ p, (g3Ψ γ i ⁻¹' S ∩ RB).indicator w p ∂PB +
        ∫⁻ p, (S ∩ G).indicator 1 p * (g3FC γ i p - ρ p * g3FB γ i p) ∂g3Leb := by
    intro S hS hSE
    have hSG : MeasurableSet[sig₂ i] (S ∩ G) := hS.inter hGs
    have hind : Measurable[sig₂ i] ((S ∩ G).indicator (1 : Ω₀ × ℝ → ℝ≥0∞)) :=
      measurable_const.indicator hSG
    rw [← lintegral_indicator_one (sig_le_g3 i _ _ _ hSG), lintegral_g3pC_FC hγ hγ2 i hind]
    have hh : Measurable[sig₂ i] fun p => (S ∩ G).indicator 1 p * ρ p :=
      hind.mul ((measurable_g3ρ γ i K).mono (outsidePalm_le_sig₂ i) le_rfl)
    have hsupp : ∀ p, (S ∩ G).indicator 1 p * ρ p ≠ 0 → g3pR γ (g3wProf γ) i p ∈ reg2 i :=
      fun p hp => by
        by_contra hn
        apply hp
        have : p ∉ S ∩ G := fun h => hn (hER (hSE h.1))
        rw [indicator_of_notMem this, zero_mul]
    have eB := lintegral_g3pB_FB hγ hγ2 i hh hsupp
    have e1 : ∫⁻ p, (S ∩ G).indicator 1 (g3Ψ γ i p) * ρ (g3Ψ γ i p) * RB.indicator 1 p ∂PB =
        ∫⁻ p, (g3Ψ γ i ⁻¹' S ∩ RB).indicator w p ∂PB := by
      refine lintegral_congr fun p => ?_
      by_cases h1 : g3Ψ γ i p ∈ S <;> by_cases h2 : p ∈ RB <;> by_cases h3 : g3Ψ γ i p ∈ G <;>
        simp [indicator, h1, h2, h3, hw]
    have hsplit : ∀ p, (S ∩ G).indicator 1 p * g3FC γ i p =
        (S ∩ G).indicator 1 p * ρ p * g3FB γ i p +
          (S ∩ G).indicator 1 p * (g3FC γ i p - ρ p * g3FB γ i p) := fun p => by
      rw [mul_assoc, ← mul_add, add_tsub_cancel_of_le (g3ρ_mul_le γ i K p)]
    have hm1 : Measurable fun p => (S ∩ G).indicator 1 p * ρ p * g3FB γ i p :=
      (hh.mono (sig_le_g3 i _ _) le_rfl).mul ((measurable_g3FB γ i).mono hO0 le_rfl)
    rw [lintegral_congr hsplit, lintegral_add_left hm1, ← eB, ← e1]
  -- finiteness and comparisons
  have hTfin : g3T γ i E K ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hZC.2.ne (measure_ne_top _ _)) (g3T_le hγ hγ2 i hE K)
  have hRle : ∀ S S' : Set (Ω₀ × ℝ), S ⊆ S' →
      ∫⁻ p, S.indicator 1 p * (g3FC γ i p - ρ p * g3FB γ i p) ∂g3Leb ≤
        ∫⁻ p, S'.indicator 1 p * (g3FC γ i p - ρ p * g3FB γ i p) ∂g3Leb := fun S S' h =>
    lintegral_mono fun p => mul_le_mul' (indicator_le_indicator_of_subset h (fun _ => bot_le) p)
      le_rfl
  set rA := ∫⁻ p, (A ∩ G).indicator 1 p * (g3FC γ i p - ρ p * g3FB γ i p) ∂g3Leb
  set rE := ∫⁻ p, (E ∩ G).indicator 1 p * (g3FC γ i p - ρ p * g3FB γ i p) ∂g3Leb
  have hAE' : rA ≤ rE := hRle _ _ (inter_subset_inter_left _ hAE)
  have hET : rE ≤ g3T γ i E K := hRle _ _ inter_subset_left
  have hrE : rE ≠ ⊤ := ne_top_of_le_ne_top hTfin hET
  have hrA : rA ≠ ⊤ := ne_top_of_le_ne_top hrE hAE'
  -- real weights
  set wr : Ω₀ × ℝ → ℝ := fun p => (w p).toReal with hwr
  have hwlt : ∀ p, w p ≠ ⊤ := fun p => ne_top_of_le_ne_top ENNReal.coe_ne_top (hwK p)
  have hint : ∀ S : Set (Ω₀ × ℝ), MeasurableSet S →
      (∫⁻ p, S.indicator w p ∂PB).toReal = ∫ p, S.indicator wr p ∂PB := fun S hS => by
    rw [← integral_toReal ((hwm.mono hO0 le_rfl).indicator hS).aemeasurable
      (ae_of_all _ fun p => by
        by_cases hp : p ∈ S
        · rw [indicator_of_mem hp]; exact (hwlt p).lt_top
        · rw [indicator_of_notMem hp]; exact ENNReal.zero_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    by_cases hp : p ∈ S
    · simp [indicator_of_mem hp, hwr]
    · simp [indicator_of_notMem hp]
  have hlfin : ∀ S : Set (Ω₀ × ℝ), ∫⁻ p, S.indicator w p ∂PB ≠ ⊤ := fun S =>
    ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := K)) (by
      calc ∫⁻ p, S.indicator w p ∂PB ≤ ∫⁻ _, (K : ℝ≥0∞) ∂PB :=
            lintegral_mono fun p => (indicator_le_self' (fun _ _ => bot_le) p).trans (hwK p)
        _ = K := by rw [lintegral_const, measure_univ, mul_one])
  have hA' : MeasurableSet (g3Ψ γ i ⁻¹' A ∩ RB) := (hΨ0 (sig_le_g3 i _ _ _ hA)).inter hRBm
  have hE' : MeasurableSet (g3Ψ γ i ⁻¹' E ∩ RB) := (hΨ0 (sig_le_g3 i _ _ _ hE)).inter hRBm
  have kA := congrArg ENNReal.toReal (key A hA hAE)
  have kE := congrArg ENNReal.toReal (key E hE subset_rfl)
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.mul_ne_top hZB.2.ne (hlfin _)) hrA,
    ENNReal.toReal_mul, hint _ hA'] at kA
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.mul_ne_top hZB.2.ne (hlfin _)) hrE,
    ENNReal.toReal_mul, hint _ hE'] at kE
  simp only [← measureReal_def] at kA kE
  -- the weighted mixing bound for `B`
  have hwr0 : ∀ p, 0 ≤ wr p := fun p => ENNReal.toReal_nonneg
  have hwrK : ∀ p, wr p ≤ K := fun p =>
    ENNReal.toReal_le_of_le_ofReal K.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hwK p)
  have hwrm : Measurable[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] wr := hwm.ennreal_toReal
  have hwri : Integrable wr PB :=
    (integrable_const (K : ℝ)).mono' (hwrm.mono hO0 le_rfl).aestronglyMeasurable
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs, abs_of_nonneg (hwr0 p)]; exact hwrK p)
  have hW := abs_integral_weight_sub_le (𝒢 := outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂) (P := PB) hO0 hA' hE' ha0 ha1 H hwrm hwr0 hwri
    K.coe_nonneg
  have hz : ∫ p, (wr p - min (wr p) K) ∂PB = 0 := by
    simp only [min_eq_left (hwrK _), sub_self, integral_zero]
  rw [hz, mul_zero, add_zero] at hW
  -- combine
  set IA := ∫ p, (g3Ψ γ i ⁻¹' A ∩ RB).indicator wr p ∂PB
  set IE := ∫ p, (g3Ψ γ i ⁻¹' E ∩ RB).indicator wr p ∂PB
  have hrA0 : 0 ≤ rA.toReal := ENNReal.toReal_nonneg
  have hAE'' : rA.toReal ≤ rE.toReal := ENNReal.toReal_mono hrE hAE'
  have hET' : rE.toReal ≤ (g3T γ i E K).toReal := ENNReal.toReal_mono hTfin hET
  have hZB0 : 0 ≤ (g3pZ γ (g3wCut γ i.η) i).toReal := ENNReal.toReal_nonneg
  have heq : (g3pZ γ (g3wProf γ) i).toReal * (PC.real (A ∩ G) - a * PC.real (E ∩ G)) =
      (g3pZ γ (g3wCut γ i.η) i).toReal * (IA - a * IE) + (rA.toReal - a * rE.toReal) := by
    rw [mul_sub, kA, mul_left_comm, kE]; ring
  have hr : |rA.toReal - a * rE.toReal| ≤ (g3T γ i E K).toReal := by
    rw [abs_le]; constructor <;> nlinarith
  rw [heq]
  calc |(g3pZ γ (g3wCut γ i.η) i).toReal * (IA - a * IE) + (rA.toReal - a * rE.toReal)|
      ≤ |(g3pZ γ (g3wCut γ i.η) i).toReal * (IA - a * IE)| + |rA.toReal - a * rE.toReal| :=
        abs_add_le _ _
    _ ≤ (g3pZ γ (g3wCut γ i.η) i).toReal * ((K : ℝ) * (2 * e)) + (g3T γ i E K).toReal := by
        rw [abs_mul, abs_of_nonneg hZB0]
        exact add_le_add (mul_le_mul_of_nonneg_left hW hZB0) hr

end R18
end QuantumZipper
