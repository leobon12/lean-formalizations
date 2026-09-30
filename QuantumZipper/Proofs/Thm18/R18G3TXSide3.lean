import QuantumZipper.Proofs.Thm18.R18G3TXSide
import QuantumZipper.Proofs.Thm18.G2FullMixLeb
import QuantumZipper.Proofs.Thm18.R18G3TFid2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (R-b): change of variables between the Palm laws of `B` and `C`

Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71. The Palm law of a profiled scheme is
`Z⁻¹ ∫ Leb{ℓ ∈ (0, M(ω)] : (ω, ℓ) ∈ S} dP(ω)` (`g3pPalmLaw_apply_eq_lebesgue`, as
`G2FullMixLeb.g3PalmLaw_apply_eq_lebesgue`). On the event that the Palm point lies in region 1,
the map `Φ(ω, ℓ) = (ω, ℓ − c_B(ω) + c_C(ω))` (a translation in `ℓ` for fixed `ω`) carries
scheme `B` to scheme `C` (`g3pX_transfer`), and `M_B − c_B = M_C − c_C = ν₁[−δ, t₁ + r₁)`.
Hence `Z_B P_B(Φ⁻¹ K ∩ {x_B ∈ region 1}) = Z_C P_C(K)` for `K ⊆ {x_C ∈ region 1}`
(`g3pPalm_cv`). Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- The open region-1 interval. -/
abbrev reg1 (i : G3Idx) : Set ℝ := Ioo (i.t₁ - i.r₁) (i.t₁ + i.r₁)

theorem g3pm_Icc_lt_top (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) (ω : Ω₀) (a b : ℝ) :
    (g3pν₁ γ g i ω + g3pν₀ γ g i ω) (Icc a b) < ⊤ := by
  have h₁ := bdryM_le_qBoundaryMeasure γ (restrictField (circIn i.t₁ i.r₁) (g3pField γ g ω))
    (Icc a b)
  have h₂ := bdryM_le_qBoundaryMeasure γ
    (restrictField (circOut i.t₁ i.r₁ i.t₂ i.r₂) (g3pField γ g ω)) (Icc a b)
  rw [Measure.add_apply]
  exact ENNReal.add_lt_top.2
    ⟨h₁.trans_lt (qBoundaryMeasure_Icc_lt_top γ _ _ _),
      h₂.trans_lt (qBoundaryMeasure_Icc_lt_top γ _ _ _)⟩

/-- **The Palm law as a Lebesgue mixture in the Palm length.** -/
theorem g3pPalmLaw_apply_eq_lebesgue (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx)
    (hZ : 0 < g3pZ γ g i ∧ g3pZ γ g i < ⊤) {S : Set (Ω₀ × ℝ)} (hS : MeasurableSet S) :
    g3pPalmLaw γ g i S = (g3pZ γ g i)⁻¹ * ∫⁻ ω, volume ({ℓ | (ω, ℓ) ∈ S} ∩
      Ioc 0 (g3pMass γ g i ω).toReal) ∂gffBase.P := by
  have hW0 : Measurable (g3pW0 γ g i) := (measurable_g3pW0 γ g i).mono (sig_le_g3 i _ _) le_rfl
  have hcoe : ∀ p, ((g3pW γ g i p : ℝ≥0) : ℝ≥0∞) = (g3pZ γ g i)⁻¹ * g3pW0 γ g i p := by
    intro p
    unfold g3pW; rw [if_pos hZ]
    exact ENNReal.coe_toNNReal (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hZ.1.ne')
      (g3pW0_ne_top γ g i p))
  rw [g3pPalmLaw, withDensity_apply _ hS, ← lintegral_indicator hS]
  have e1 : (S.indicator fun p => ((g3pW γ g i p : ℝ≥0) : ℝ≥0∞)) =
      fun p => (g3pZ γ g i)⁻¹ * S.indicator (g3pW0 γ g i) p := by
    funext p
    by_cases hp : p ∈ S
    · rw [indicator_of_mem hp, indicator_of_mem hp, hcoe]
    · rw [indicator_of_notMem hp, indicator_of_notMem hp, mul_zero]
  rw [e1, lintegral_const_mul _ (hW0.indicator hS),
    lintegral_prod _ (hW0.indicator hS).aemeasurable]
  congr 1
  refine lintegral_congr fun ω => ?_
  have hsec : MeasurableSet {ℓ : ℝ | (ω, ℓ) ∈ S} := measurable_prodMk_left hS
  rw [← lintegral_expMeasure_palmKernel_indicator hsec (M := g3pMass γ g i ω)
    (g3pm_Icc_lt_top γ g i ω _ _).ne]
  refine lintegral_congr fun ℓ => ?_
  by_cases hp : (ω, ℓ) ∈ S
  · rw [indicator_of_mem hp, indicator_of_mem (show ℓ ∈ {ℓ : ℝ | (ω, ℓ) ∈ S} from hp)]
    rfl
  · rw [indicator_of_notMem hp, indicator_of_notMem (show ℓ ∉ {ℓ : ℝ | (ω, ℓ) ∈ S} from hp)]

/-- The Palm length exceeds the mass `c` of `[B, 0]` when the Palm point is left of `B`. -/
theorem lt_of_lenLeft_mem {m : Measure ℝ} {A B ℓ c : ℝ} (hB : B < 0)
    (hc : m (Icc B 0) = ENNReal.ofReal c) (hx : lenLeft m ℓ ∈ Ioo A B) : c < ℓ := by
  set S : Set ℝ := {y | 0 < y ∧ ENNReal.ofReal ℓ ≤ m (Icc (-y) 0)} with hS
  have hs : -B < sInf S := by
    have := hx.2; unfold lenLeft at this; linarith
  have hbdd : BddBelow S := ⟨0, fun y hy => hy.1.le⟩
  by_contra h
  push Not at h
  have hmem : -B ∈ S := ⟨by linarith, by rw [neg_neg, hc]; exact ENNReal.ofReal_le_ofReal h⟩
  have := csInf_le hbdd hmem
  linarith

/-- The change of variables `Φ(ω, ℓ) = (ω, ℓ + c_C(ω) − c_B(ω))` from scheme `B` to scheme `C`. -/
def g3Φ (γ : ℝ) (i : G3Idx) (p : Ω₀ × ℝ) : Ω₀ × ℝ :=
  (p.1, p.2 + (g3pc γ (g3wProf γ) i p.1 - g3pc γ (g3wCut γ i.η) i p.1))

theorem measurable_g3pc_out (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) :
    Measurable[outsideSigma2 gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] (g3pc γ g i) :=
  ENNReal.measurable_toReal.comp ((Measure.measurable_coe measurableSet_Icc).comp
    ((measurable_bdryM γ).comp (measurable_g3pGap γ g i)))

theorem measurable_g3pc (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) : Measurable (g3pc γ g i) :=
  (measurable_g3pc_out γ g i).mono (outsideSigma2_le gffBase.gff _ _ _ _) le_rfl

theorem g3pν₀_le_m (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) (ω : Ω₀) (a b : ℝ) :
    g3pν₀ γ g i ω (Icc a b) ≠ ⊤ :=
  ne_top_of_le_ne_top (g3pm_Icc_lt_top γ g i ω a b).ne (by rw [Measure.add_apply]; exact le_add_self)

theorem measurable_g3Φ (γ : ℝ) (i : G3Idx) : Measurable (g3Φ γ i) :=
  measurable_fst.prodMk (measurable_snd.add (((measurable_g3pc γ _ i).comp measurable_fst).sub
    ((measurable_g3pc γ _ i).comp measurable_fst)))

/-- Almost surely both gap measures vanish on the closed region-1 interval, and the region-1
measure vanishes on `[t₁ + r₁, 0]`. -/
theorem ae_gap_null {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂gffBase.P, ∀ i : G3Idx,
      g3pν₀ γ (g3wCut γ i.η) i ω (Icc (i.t₁ - i.r₁) (i.t₁ + i.r₁)) = 0 ∧
      g3pν₀ γ (g3wProf γ) i ω (Icc (i.t₁ - i.r₁) (i.t₁ + i.r₁)) = 0 ∧
      g3pν₁ γ (g3wProf γ) i ω (Icc (i.t₁ + i.r₁) 0) = 0 := by
  filter_upwards [ae_g3pField_good hγ hγ2, ae_g3pBField_good hγ hγ2] with ω hC hB i
  exact ⟨g3pν₀_region_null_of hγ _ i ω (hB i.η i.hη).1 (hB i.η i.hη).2.1 (hB i.η i.hη).2.2.1,
    g3pν₀_region_null_of hγ _ i ω hC.1 hC.2.1 hC.2.2.1,
    g3pν₁_null_of hγ _ i ω hC.1 hC.2.1 hC.2.2.1⟩

theorem g3pMass_toReal_split {γ : ℝ} {g : ℂ → ℝ} {i : G3Idx} {ω : Ω₀}
    (h0 : g3pν₀ γ g i ω (Icc (i.t₁ - i.r₁) (i.t₁ + i.r₁)) = 0)
    (h1z : g3pν₁ γ g i ω (Icc (i.t₁ + i.r₁) 0) = 0) :
    (g3pMass γ g i ω).toReal =
      (g3pν₁ γ g i ω (Ico (-i.δ) (i.t₁ + i.r₁))).toReal + g3pc γ g i ω := by
  have hy : i.δ ∈ Ioo (-(i.t₁ + i.r₁)) (-(i.t₁ - i.r₁)) := by
    have := i.hη; have := i.hηδ
    constructor <;> · unfold G3Idx.t₁ G3Idx.r₁; linarith
  have hsp := g3pm_split h0 hy
  rw [Measure.add_apply _ _ (Icc (i.t₁ + i.r₁) 0), h1z, zero_add] at hsp
  have hfin := g3pm_Icc_lt_top γ g i ω (-i.δ) 0
  rw [hsp] at hfin
  rw [g3pMass, hsp, ENNReal.toReal_add (ENNReal.add_lt_top.1 hfin).1.ne
    (ENNReal.add_lt_top.1 hfin).2.ne, g3pc]

/-- **Sections of the change of variables.** -/
theorem section_g3Φ {γ : ℝ} {i : G3Idx} {ω : Ω₀}
    (h0B : g3pν₀ γ (g3wCut γ i.η) i ω (Icc (i.t₁ - i.r₁) (i.t₁ + i.r₁)) = 0)
    (h0C : g3pν₀ γ (g3wProf γ) i ω (Icc (i.t₁ - i.r₁) (i.t₁ + i.r₁)) = 0)
    (h1z : g3pν₁ γ (g3wProf γ) i ω (Icc (i.t₁ + i.r₁) 0) = 0)
    {K : Set (Ω₀ × ℝ)} (hKE : K ⊆ g3pX γ (g3wProf γ) i ⁻¹' reg1 i) :
    {ℓ | (ω, ℓ) ∈ g3Φ γ i ⁻¹' K ∩ g3pX γ (g3wCut γ i.η) i ⁻¹' reg1 i} ∩
        Ioc 0 (g3pMass γ (g3wCut γ i.η) i ω).toReal =
      (fun ℓ => ℓ + (g3pc γ (g3wProf γ) i ω - g3pc γ (g3wCut γ i.η) i ω)) ⁻¹'
        ({ℓ | (ω, ℓ) ∈ K} ∩ Ioc 0 (g3pMass γ (g3wProf γ) i ω).toReal) := by
  set cB := g3pc γ (g3wCut γ i.η) i ω
  set cC := g3pc γ (g3wProf γ) i ω
  have hB : i.t₁ + i.r₁ < 0 := by
    have := i.hη; unfold G3Idx.t₁ G3Idx.r₁; linarith
  have h1 := g3pν₁_cut_eq γ i ω
  have h1zB : g3pν₁ γ (g3wCut γ i.η) i ω (Icc (i.t₁ + i.r₁) 0) = 0 := by rw [h1]; exact h1z
  have finB := g3pν₀_le_m γ (g3wCut γ i.η) i ω (i.t₁ + i.r₁) 0
  have finC := g3pν₀_le_m γ (g3wProf γ) i ω (i.t₁ + i.r₁) 0
  have hmB : (g3pν₁ γ (g3wCut γ i.η) i ω + g3pν₀ γ (g3wCut γ i.η) i ω) (Icc (i.t₁ + i.r₁) 0) =
      ENNReal.ofReal cB := by
    rw [Measure.add_apply, h1zB, zero_add]; exact (ENNReal.ofReal_toReal finB).symm
  have hmC : (g3pν₁ γ (g3wProf γ) i ω + g3pν₀ γ (g3wProf γ) i ω) (Icc (i.t₁ + i.r₁) 0) =
      ENNReal.ofReal cC := by
    rw [Measure.add_apply, h1z, zero_add]; exact (ENNReal.ofReal_toReal finC).symm
  have hMB := g3pMass_toReal_split h0B h1zB
  have hMC := g3pMass_toReal_split h0C h1z
  rw [h1] at hMB
  have hcB : 0 ≤ cB := ENNReal.toReal_nonneg
  have hcC : 0 ≤ cC := ENNReal.toReal_nonneg
  have hltB : ∀ ℓ, g3pX γ (g3wCut γ i.η) i (ω, ℓ) ∈ reg1 i → cB < ℓ := fun ℓ hx =>
    lt_of_lenLeft_mem hB hmB hx
  have hltC : ∀ ℓ, g3pX γ (g3wProf γ) i (ω, ℓ) ∈ reg1 i → cC < ℓ := fun ℓ hx =>
    lt_of_lenLeft_mem hB hmC hx
  ext ℓ
  constructor
  · rintro ⟨⟨hK, hx⟩, h0, hle⟩
    have hl := hltB ℓ hx
    refine ⟨hK, ?_, ?_⟩
    · show 0 < ℓ + (cC - cB); linarith
    · show ℓ + (cC - cB) ≤ _; rw [hMC]; rw [hMB] at hle; linarith
  · rintro ⟨hK, h0, hle⟩
    have hK' : (ω, ℓ + (cC - cB)) ∈ K := hK
    have hxC : g3pX γ (g3wProf γ) i (ω, ℓ + (cC - cB)) ∈ reg1 i := hKE hK'
    have hl := hltC _ hxC
    have e := g3pX_transfer (g := g3wProf γ) (g' := g3wCut γ i.η) h1.symm h1z h0C h0B finC finB hxC
    rw [show ℓ + (cC - cB) - cC + cB = ℓ by ring] at e
    refine ⟨⟨hK', ?_⟩, ?_, ?_⟩
    · show g3pX γ (g3wCut γ i.η) i (ω, ℓ) ∈ reg1 i
      rw [e]; exact hxC
    · show 0 < ℓ; linarith
    · show ℓ ≤ _
      have hle' : ℓ + (cC - cB) ≤ (g3pMass γ (g3wProf γ) i ω).toReal := hle
      rw [hMB]; rw [hMC] at hle'; linarith

/-- **Change of variables between the Palm laws of `B` and `C`** on the event that the Palm
point lies in region 1. -/
theorem g3pPalm_cv {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {K : Set (Ω₀ × ℝ)}
    (hK : MeasurableSet K) (hKE : K ⊆ g3pX γ (g3wProf γ) i ⁻¹' reg1 i) :
    g3pZ γ (g3wCut γ i.η) i *
        g3pPalmLaw γ (g3wCut γ i.η) i (g3Φ γ i ⁻¹' K ∩ g3pX γ (g3wCut γ i.η) i ⁻¹' reg1 i) =
      g3pZ γ (g3wProf γ) i * g3pPalmLaw γ (g3wProf γ) i K := by
  have hZB := g3pBZ_pos_lt_top hγ hγ2 i
  have hZC := g3pZ_pos_lt_top hγ hγ2 i
  have hXB : Measurable (g3pX γ (g3wCut γ i.η) i) :=
    (measurable_g3pX γ _ i).mono (sig_le_g3 i _ _) le_rfl
  have hSB : MeasurableSet (g3Φ γ i ⁻¹' K ∩ g3pX γ (g3wCut γ i.η) i ⁻¹' reg1 i) :=
    (measurable_g3Φ γ i hK).inter (hXB measurableSet_Ioo)
  rw [g3pPalmLaw_apply_eq_lebesgue _ _ _ hZB hSB, g3pPalmLaw_apply_eq_lebesgue _ _ _ hZC hK,
    ← mul_assoc, ← mul_assoc, ENNReal.mul_inv_cancel hZB.1.ne' hZB.2.ne,
    ENNReal.mul_inv_cancel hZC.1.ne' hZC.2.ne, one_mul, one_mul]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_gap_null hγ hγ2] with ω hω
  rw [section_g3Φ (hω i).1 (hω i).2.1 (hω i).2.2 hKE, measure_preimage_add_right]

end R18
end QuantumZipper
