import QuantumZipper.Proofs.Thm18.G3RPalm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 (R-c): the region-2 densities of schemes `B` and `C`

Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71, and Remark 5.7 (D85 update 18:30).
In the coordinates of scheme `C` (length `ℓ` read by `C`), for `h` a function of region 2, the
outside field and `ℓ`, supported where `R(x)` of `C` lies in region 2:

* `Z_C ∫ h dP_C = ∫ h · F_C d(P ⊗ Leb)` with `F_C(ω, ℓ) = 1{ℓ > 0} F(ω, ℓ − a_C)`
  (`lintegral_g3pC_FC`);
* `Z_B ∫ (h ∘ Ψ) 1{R_B ∈ region 2} dP_B = ∫ h · F_B d(P ⊗ Leb)` with
  `F_B(ω, ℓ) = F(ω, ℓ − D − a_B)`, `D = d_C − d_B` (`lintegral_g3pB_FB`),

where `F` is the conditional tail of the region-1 mass (`g3F`) and `Ψ` the shift of
`R18G3TXSide`'s kind (`g3Ψ`). Both densities are measurable for the outside field and `ℓ`.
Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-- The product measure `P ⊗ Leb`. -/
abbrev g3Leb : Measure (Ω₀ × ℝ) := gffBase.P.prod volume

/-- The shift of `Ψ`. -/
def g3Dsh (γ : ℝ) (i : G3Idx) (ω : Ω₀) : ℝ :=
  g3pd γ (g3wProf γ) i ω - g3pd γ (g3wCut γ i.η) i ω

/-- Density of scheme `C`. -/
def g3FC (γ : ℝ) (i : G3Idx) (p : Ω₀ × ℝ) : ℝ≥0∞ :=
  (Ioi 0).indicator 1 p.2 * g3F γ i p.1 (p.2 - g3a γ (g3wProf γ) i p.1)

/-- Density of scheme `B` (in `C`-coordinates). -/
def g3FB (γ : ℝ) (i : G3Idx) (p : Ω₀ × ℝ) : ℝ≥0∞ :=
  g3F γ i p.1 (p.2 - g3Dsh γ i p.1 - g3a γ (g3wCut γ i.η) i p.1)

/-- A shift of the length by a function of the first coordinate is measurable for any product
σ-algebra whose first factor measures the shift. -/
theorem measurable_shift_prod {m : MeasurableSpace Ω₀} {c : Ω₀ → ℝ} (hc : Measurable[m] c) :
    @Measurable (Ω₀ × ℝ) (Ω₀ × ℝ) (@Prod.instMeasurableSpace Ω₀ ℝ m _)
      (@Prod.instMeasurableSpace Ω₀ ℝ m _) fun p => (p.1, p.2 + c p.1) :=
  Measurable.prodMk (m := @Prod.instMeasurableSpace Ω₀ ℝ m _) (@measurable_fst Ω₀ ℝ m _)
    ((@measurable_snd Ω₀ ℝ m _).add (hc.comp (@measurable_fst Ω₀ ℝ m _)))

theorem measurable_g3pd_O (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) : Measurable[g3O i] (g3pd γ g i) :=
  measurable_g3pd_out γ g i

theorem measurable_g3Dsh (γ : ℝ) (i : G3Idx) : Measurable[g3O i] (g3Dsh γ i) :=
  (measurable_g3pd_O γ _ i).sub (measurable_g3pd_O γ _ i)

theorem measurable_g3FC (γ : ℝ) (i : G3Idx) :
    Measurable[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] (g3FC γ i) := by
  have h1 : Measurable[@Prod.instMeasurableSpace Ω₀ ℝ (g3O i) _] fun p : Ω₀ × ℝ =>
      (Ioi (0 : ℝ)).indicator (1 : ℝ → ℝ≥0∞) p.2 :=
    (measurable_const.indicator measurableSet_Ioi).comp (@measurable_snd Ω₀ ℝ (g3O i) _)
  have h2 := (measurable_g3F γ i).comp (measurable_shift_prod (m := g3O i)
    ((measurable_g3a γ (g3wProf γ) i).neg))
  have e : (fun p : Ω₀ × ℝ => g3F γ i p.1 (p.2 - g3a γ (g3wProf γ) i p.1)) =
      (fun p : Ω₀ × ℝ => g3F γ i p.1 p.2) ∘
        (fun p : Ω₀ × ℝ => (p.1, p.2 + (-g3a γ (g3wProf γ) i) p.1)) := by
    funext p; simp [sub_eq_add_neg]
  have h2' : Measurable[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂]
      fun p : Ω₀ × ℝ => g3F γ i p.1 (p.2 - g3a γ (g3wProf γ) i p.1) := by
    rw [e]; exact h2
  exact h1.mul h2'

theorem measurable_g3FB (γ : ℝ) (i : G3Idx) :
    Measurable[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] (g3FB γ i) := by
  have h2 := (measurable_g3F γ i).comp (measurable_shift_prod (m := g3O i)
    (((measurable_g3Dsh γ i).add (measurable_g3a γ (g3wCut γ i.η) i)).neg))
  have e : g3FB γ i = (fun p : Ω₀ × ℝ => g3F γ i p.1 p.2) ∘
      (fun p : Ω₀ × ℝ => (p.1, p.2 + (-(g3Dsh γ i + g3a γ (g3wCut γ i.η) i)) p.1)) := by
    funext p
    simp only [g3FB, Function.comp, Pi.neg_apply, Pi.add_apply]
    congr 1
    ring
  rw [e]
  exact h2

theorem outsidePalm_le_sig₂ (i : G3Idx) :
    outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂ ≤ sig₂ i := le_sup_right

/-- `Ψ` is measurable for `sig₂`. -/
theorem measurable_g3Ψ_sig₂ (γ : ℝ) (i : G3Idx) :
    @Measurable (Ω₀ × ℝ) (Ω₀ × ℝ) (sig₂ i) (sig₂ i) (g3Ψ γ i) := by
  rw [sig₂_eq_prod]
  exact measurable_shift_prod (m := localSigma X₀ i.t₂ i.r₂ ⊔ g3O i)
    ((measurable_g3Dsh γ i).mono le_sup_right le_rfl)

/-- `Ψ` is measurable for the outside σ-algebra. -/
theorem measurable_g3Ψ_O (γ : ℝ) (i : G3Idx) :
    @Measurable (Ω₀ × ℝ) (Ω₀ × ℝ) (outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂)
      (outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂) (g3Ψ γ i) :=
  measurable_shift_prod (m := g3O i) (measurable_g3Dsh γ i)

/-- **Scheme `C`.** -/
theorem lintegral_g3pC_FC {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx)
    {f : Ω₀ × ℝ → ℝ≥0∞} (hf : Measurable[sig₂ i] f) :
    g3pZ γ (g3wProf γ) i * ∫⁻ p, f p ∂(g3pPalmLaw γ (g3wProf γ) i) =
      ∫⁻ p, f p * g3FC γ i p ∂g3Leb := by
  have hmeas : AEMeasurable (fun p => f p * g3FC γ i p) g3Leb :=
    ((hf.mono (sig_le_g3 i _ _) le_rfl).mul
      ((measurable_g3FC γ i).mono (outsideSigmaPalm_le_g3 i) le_rfl)).aemeasurable
  rw [lintegral_g3pPalm_region2 (g3wProf γ) i (g3pZ_pos_lt_top hγ hγ2 i) (fun _ => rfl) hf,
    lintegral_prod _ hmeas]
  refine lintegral_congr fun ω => lintegral_congr fun ℓ => ?_
  simp only [g3FC, mul_assoc]

/-- **Scheme `B`, in `C`-coordinates.** -/
theorem lintegral_g3pB_FB {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx)
    {h : Ω₀ × ℝ → ℝ≥0∞} (hh : Measurable[sig₂ i] h)
    (hsupp : ∀ p, h p ≠ 0 → g3pR γ (g3wProf γ) i p ∈ reg2 i) :
    g3pZ γ (g3wCut γ i.η) i * ∫⁻ p, h (g3Ψ γ i p) *
        (g3pR γ (g3wCut γ i.η) i ⁻¹' reg2 i).indicator 1 p ∂(g3pPalmLaw γ (g3wCut γ i.η) i) =
      ∫⁻ p, h p * g3FB γ i p ∂g3Leb := by
  have hRB : Measurable[sig₂ i] (g3pR γ (g3wCut γ i.η) i) := measurable_g3pR γ _ i
  have hm : Measurable[sig₂ i] fun p => h (g3Ψ γ i p) *
      (g3pR γ (g3wCut γ i.η) i ⁻¹' reg2 i).indicator 1 p :=
    (hh.comp (measurable_g3Ψ_sig₂ γ i)).mul
      (measurable_const.indicator (hRB measurableSet_Ioo))
  have hmeas : AEMeasurable (fun p => h p * g3FB γ i p) g3Leb :=
    ((hh.mono (sig_le_g3 i _ _) le_rfl).mul
      ((measurable_g3FB γ i).mono (outsideSigmaPalm_le_g3 i) le_rfl)).aemeasurable
  rw [lintegral_g3pPalm_region2 (g3wCut γ i.η) i (g3pBZ_pos_lt_top hγ hγ2 i)
      (fun ω => g3pν₁_cut_eq γ i ω) hm, lintegral_prod _ hmeas]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_gap2_null hγ hγ2] with ω hω
  obtain ⟨h0B, h0C, h2z⟩ := hω i
  rw [← lintegral_add_right_eq_self (μ := volume) (fun ℓ => h (ω, ℓ) * g3FB γ i (ω, ℓ))
    (g3Dsh γ i ω)]
  refine lintegral_congr fun ℓ => ?_
  have hΨ : g3Ψ γ i (ω, ℓ) = (ω, ℓ + g3Dsh γ i ω) := rfl
  have hFB : g3FB γ i (ω, ℓ + g3Dsh γ i ω) = g3F γ i ω (ℓ - g3a γ (g3wCut γ i.η) i ω) := by
    simp only [g3FB, add_sub_cancel_right]
  simp only [hΨ, hFB]
  by_cases h0 : h (ω, ℓ + g3Dsh γ i ω) = 0
  · simp [h0]
  · have hR := hsupp _ h0
    rw [← hΨ] at hR
    have e := (g3pR_Ψ (p := (ω, ℓ)) h0B h0C h2z).2 hR
    have hRB' : g3pR γ (g3wCut γ i.η) i (ω, ℓ) ∈ reg2 i := by rw [e]; exact hR
    have h2zB : g3pν₂ γ (g3wCut γ i.η) i ω (Icc 0 (i.t₂ - i.r₂)) = 0 := by
      rw [g3pν₂_cut_eq]; exact h2z
    have hlt := lt_of_g3pR_mem h2zB hRB'
    have hd0 : 0 ≤ g3pd γ (g3wCut γ i.η) i ω := ENNReal.toReal_nonneg
    have hℓ : ℓ ∈ Ioi (0 : ℝ) := show 0 < ℓ by linarith
    rw [indicator_of_mem (show (ω, ℓ) ∈ g3pR γ (g3wCut γ i.η) i ⁻¹' reg2 i from hRB'),
      indicator_of_mem hℓ]
    simp

end R18
end QuantumZipper
