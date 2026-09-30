import QuantumZipper.Proofs.Thm18.R18G3TCM6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 (R-a) closed: `G3TCMStmt` (Cameron–Martin step `A → B`)

Sheffield, arXiv:1012.4797, p. 72 and Remark 5.7 (adding a smooth function supported away from
the Palm regions changes the law only absolutely continuously); Berestycki–Powell,
arXiv:2004.04720, Lemma 3.12 (Cameron–Martin for the GFF). For each index,
`P_B(S_B ∩ G) − a P_B(M_B ∩ G) = κ (∫_{S_A} w − a ∫_{M_A} w)` with the outside weight
`w = 1_{G'} · cmTilt` (`g3pPalmLaw_cut_real`), and the mixing bound of scheme `A` over outside
events controls such weights after truncation at a level `K` chosen before the zoom level
(`abs_integral_weight_sub_le`, `tendsto_tail_cmTilt`). Own `ε`-bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-- The Cameron–Martin normalization ratio `Z_A / Z_B`. -/
def cmκ (γ : ℝ) (i : G3Idx) : ℝ := ((g3pZ γ (g3wCut γ i.η) i)⁻¹ * g3Z γ i).toReal

/-- The truncation tail of the tilt under the free Palm law. -/
def cmT (γ : ℝ) (i : G3Idx) (K : ℝ) : ℝ :=
  ∫ p, (cmTilt X₀ (g3wCut γ i.η) p.1 - min (cmTilt X₀ (g3wCut γ i.η) p.1) K) ∂(g3PalmLaw γ i)

theorem cmT_nonneg (γ : ℝ) (i : G3Idx) (K : ℝ) : 0 ≤ cmT γ i K :=
  integral_nonneg fun _ => sub_nonneg.2 (min_le_left _ _)

set_option maxHeartbeats 400000 in
/-- **Per-index transfer of the mixing bound.** -/
theorem bodyB_core {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx)
    {S M : Set (FieldSample × ℝ)} (hS : MeasurableSet S) (hM : MeasurableSet M)
    (hSl : IsLocS S) (hMl : IsLocS M) {a e K : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hK : 0 ≤ K)
    (H : ∀ G : Set (Ω₀ × ℝ), MeasurableSet[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3PalmLaw γ i).real ({p : Ω₀ × ℝ | (normField γ X₀ p.1, p.2) ∈ S} ∩ G) -
        a * (g3PalmLaw γ i).real ({p : Ω₀ × ℝ | (normField γ X₀ p.1, p.2) ∈ M} ∩ G)| ≤ e)
    {G : Set (Ω₀ × ℝ)} (hG : MeasurableSet[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] G) :
    |(g3pPalmLaw γ (g3wCut γ i.η) i).real
        ({p : Ω₀ × ℝ | (g3pField γ (g3wCut γ i.η) p.1, p.2) ∈ S} ∩ G) -
      a * (g3pPalmLaw γ (g3wCut γ i.η) i).real
        ({p : Ω₀ × ℝ | (g3pField γ (g3wCut γ i.η) p.1, p.2) ∈ M} ∩ G)| ≤
      cmκ γ i * (K * (2 * e) + 2 * cmT γ i K) := by
  have hZA := g3Z_pos_lt_top hγ hγ2 i
  have hZB := g3pBZ_pos_lt_top hγ hγ2 i
  have : IsProbabilityMeasure (g3PalmLaw γ i) := isProbabilityMeasure_g3 γ i
  obtain ⟨G', hG', hF⟩ := g3pPalmLaw_cut_real γ i hZA hZB hG
  rw [hF S hS hSl, hF M hM hMl]
  set D : Ω₀ × ℝ → ℝ := fun p => cmTilt X₀ (g3wCut γ i.η) p.1 with hD
  set w : Ω₀ × ℝ → ℝ := G'.indicator D with hw
  have hSA : MeasurableSet {p : Ω₀ × ℝ | (normField γ X₀ p.1, p.2) ∈ S} :=
    (((measurable_normField_g3 γ).comp measurable_fst).prodMk measurable_snd) hS
  have hMA : MeasurableSet {p : Ω₀ × ℝ | (normField γ X₀ p.1, p.2) ∈ M} :=
    (((measurable_normField_g3 γ).comp measurable_fst).prodMk measurable_snd) hM
  have e1 : ∀ B : Set (Ω₀ × ℝ), (B ∩ G').indicator D = B.indicator w := fun B => by
    rw [hw, indicator_indicator]
  rw [e1, e1]
  have hfstO : Measurable[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂,
      outsideSigma2 X₀ i.t₁ i.r₁ i.t₂ i.r₂] Prod.fst := by
    unfold outsideSigmaPalm; exact Measurable.of_comap_le le_sup_left
  have hDO : Measurable[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] D :=
    (measurable_cmTilt_g3wCut γ i).comp hfstO
  have hwO : Measurable[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] w := hDO.indicator hG'
  have hDpos : ∀ p, 0 < D p := fun p => cmTilt_pos _ _
  have hw0 : ∀ p, 0 ≤ w p := fun p => indicator_nonneg (fun p _ => (hDpos p).le) p
  have hDi : Integrable D (g3PalmLaw γ i) := integrable_cmTilt_g3PalmLaw γ i hZA hZB
  have hG'm : MeasurableSet G' := outsideSigmaPalm_le_g3 i _ hG'
  have hwi : Integrable w (g3PalmLaw γ i) := hDi.indicator hG'm
  have hmain := abs_integral_weight_sub_le (P := g3PalmLaw γ i) (outsideSigmaPalm_le_g3 i)
    hSA hMA ha0 ha1 H hwO hw0 hwi hK
  have hDm : Measurable D := measurable_cmTilt_fst _
  have htail : ∫ p, (w p - min (w p) K) ∂(g3PalmLaw γ i) ≤ cmT γ i K := by
    unfold cmT
    refine integral_mono_of_nonneg (ae_of_all _ fun p => sub_nonneg.2 (min_le_left _ _)) ?_
      (ae_of_all _ fun p => ?_)
    · refine hDi.mono' (hDm.sub (hDm.min measurable_const)).aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (min_le_left _ _))]
      have : 0 ≤ min (D p) K := le_min (hDpos p).le hK
      linarith
    · show w p - min (w p) K ≤ D p - min (D p) K
      by_cases hp : p ∈ G'
      · simp [hw, indicator, hp]
      · simp only [hw, indicator, hp, if_false]
        rw [min_eq_left hK, sub_self]
        exact sub_nonneg.2 (min_le_left _ _)
  have hκ : 0 ≤ cmκ γ i := ENNReal.toReal_nonneg
  unfold cmκ at hκ ⊢
  have hEq : ∀ k x y : ℝ, k * x - a * (k * y) = k * (x - a * y) := fun k x y => by ring
  rw [hEq, abs_mul, abs_of_nonneg hκ]
  refine mul_le_mul_of_nonneg_left (hmain.trans ?_) hκ
  linarith

/-! ## Independence of the zoom level -/

theorem g3pZ_cut_congr {γ : ℝ} {i i' : G3Idx} (h₁ : i.1.1 = i'.1.1) (h₂ : i.1.2.1 = i'.1.2.1) :
    g3pZ γ (g3wCut γ i.η) i = g3pZ γ (g3wCut γ i'.η) i' := by
  have hη : i.η = i'.η := h₂
  have hν₁ : g3pν₁ γ (g3wCut γ i'.η) i = g3pν₁ γ (g3wCut γ i'.η) i' := by
    funext ω; simp only [g3pν₁, G3Idx.t₁, G3Idx.r₁, G3Idx.δ, G3Idx.η, h₁, h₂]
  have hν₀ : g3pν₀ γ (g3wCut γ i'.η) i = g3pν₀ γ (g3wCut γ i'.η) i' := by
    funext ω; simp only [g3pν₀, G3Idx.t₁, G3Idx.r₁, G3Idx.t₂, G3Idx.r₂, G3Idx.δ, G3Idx.η, h₁, h₂]
  have hM : g3pMass γ (g3wCut γ i'.η) i = g3pMass γ (g3wCut γ i'.η) i' := by
    funext ω; simp only [g3pMass, G3Idx.δ, h₁, hν₁, hν₀]
  have h0 : g3pW0 γ (g3wCut γ i'.η) i = g3pW0 γ (g3wCut γ i'.η) i' := by
    funext p; unfold g3pW0; rw [hM]
  rw [hη]; unfold g3pZ; rw [h0]

theorem g3PalmLaw_congr' {γ : ℝ} {i i' : G3Idx} (h₁ : i.1.1 = i'.1.1) (h₂ : i.1.2.1 = i'.1.2.1) :
    g3PalmLaw γ i = g3PalmLaw γ i' :=
  g3PalmLaw_congr (g3W_congr (g3Z_congr (g3W0_congr h₁ h₂)) (g3W0_congr h₁ h₂))

theorem cmκ_congr {γ : ℝ} {i i' : G3Idx} (h₁ : i.1.1 = i'.1.1) (h₂ : i.1.2.1 = i'.1.2.1) :
    cmκ γ i = cmκ γ i' := by
  unfold cmκ; rw [g3pZ_cut_congr h₁ h₂, g3Z_congr (g3W0_congr (γ := γ) h₁ h₂)]

theorem cmT_congr {γ : ℝ} {i i' : G3Idx} (h₁ : i.1.1 = i'.1.1) (h₂ : i.1.2.1 = i'.1.2.1)
    (K : ℝ) : cmT γ i K = cmT γ i' K := by
  have hη : i.η = i'.η := h₂
  unfold cmT; rw [hη, g3PalmLaw_congr' h₁ h₂]

/-! ## The `ε`-bookkeeping -/

/-- Given the free bound `e` at a truncation level `K`, the cut-off bound is `≤ ε`. -/
theorem exists_K_e (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (i₀ : G3Idx) {ε : ℝ} (hε : 0 < ε) :
    ∃ K e : ℝ, 0 ≤ K ∧ 0 < e ∧ cmκ γ i₀ * (K * (2 * e) + 2 * cmT γ i₀ K) ≤ ε := by
  have hZA := g3Z_pos_lt_top hγ hγ2 i₀
  have hZB := g3pBZ_pos_lt_top hγ hγ2 i₀
  set κ := cmκ γ i₀ with hκdef
  have hκ : 0 ≤ κ := ENNReal.toReal_nonneg
  have hpos : 0 < ε / (4 * (κ + 1)) := by positivity
  obtain ⟨K, hK1, hK0⟩ := ((tendsto_tail_cmTilt γ i₀ hZA hZB).eventually
    (gt_mem_nhds hpos)).and (eventually_ge_atTop 0) |>.exists
  refine ⟨K, ε / (4 * (κ * K + 1)), hK0, by positivity, ?_⟩
  have hT : cmT γ i₀ K < ε / (4 * (κ + 1)) := hK1
  have hT0 := cmT_nonneg γ i₀ K
  have h1 : κ * K * (ε / (4 * (κ * K + 1))) ≤ ε / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hκ hK0]
  have h2 : κ * cmT γ i₀ K ≤ ε / 4 := by
    have h3 : cmT γ i₀ K * (4 * (κ + 1)) < ε := (lt_div_iff₀ (by positivity)).1 hT
    nlinarith
  nlinarith

/-! ## The statement -/

end R18
end QuantumZipper
