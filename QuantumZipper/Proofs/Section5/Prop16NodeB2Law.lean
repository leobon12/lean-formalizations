import QuantumZipper.Proofs.Section5.Prop16PalmMask

/-!
# Proposition 1.6, Palm node B′: the point law and the assembly from windows

Items (8) and "window → `(a,b)`" of the D30 list for node B′ (`Prop16PalmIdMaskStmt`).

* `palmPre P ν a b`: the unnormalized weighted law `E[δ_ω ⊗ ν_ω|_{[a,b]}]` (so
  `prop16Law P ν a b = Z⁻¹ • palmPre P ν a b`, `Z = E ν[a,b]`);
* `palmMean P ν a b`: the mean (intensity) measure `A ↦ E ν(A ∩ (a,b))` of the boundary measure;
  `palmPoint P ν a b = Z⁻¹ • palmMean P ν a b`: **the Palm point law `ρ`** of node B′. It is a
  probability measure carried by `(a,b)` (`isProbabilityMeasure_palmPoint`, `palmPoint_compl`).
  By the window Palm formula (`palm_formula_prop16_window` with `G = 1_S(x)`) its restriction to
  each window is `ρ(x) dx`, `ρ(x) = Z⁻¹ exp(γ h0(x)/2 + γ² k(x,x)/8)`; the intensity form is used
  here because it does not depend on the window (nor on the window's M6 kernel `k`).
* `palmPre_eq_of_windows`: an identity `palmPre (T ∩ Ω × (a',b')) = ∫_{(a',b')} f dI` for all
  windows `a < a' < b' < b` extends to `(a,b)` and then to all of `T` (continuity from below along
  the windows; no measurability of `T` needed, `palmPre` is used as an outer measure).
* `Prop16PalmWinMaskStmt` (**remaining node**, stated exactly): a jointly measurable
  Palm-side version `F C` of the masked zoom coordinates, identified with `palmFixedMask` for
  `palmMean`-a.e. `x`, satisfying the Palm identity on every window.
* `prop16PalmIdMaskStmt_of_win`: node B′ from it, with `ρ = palmPoint`.

Source: the Palm identity is Duplantier–Sheffield, *Liouville quantum gravity and KPZ*,
arXiv:0808.1560, §3.3 (rooted measure, p. 22), as used in Sheffield, arXiv:1012.4797, proof of
Prop. 1.6 (p. 25). The normalization and window bookkeeping here are own elementary arguments.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν : Ω → Measure ℝ} {a b : ℝ}

/-- The unnormalized weighted law `E[δ_ω ⊗ ν_ω|_{[a,b]}]` (`prop16Law = Z⁻¹ • palmPre`). -/
def palmPre (P : Measure Ω) (ν : Ω → Measure ℝ) (a b : ℝ) : Measure (Ω × ℝ) :=
  P.bind fun ω => (Measure.dirac ω).prod ((ν ω).restrict (Icc a b))

/-- The mean (intensity) measure `A ↦ E ν(A ∩ (a,b))` of the random boundary measure. -/
def palmMean (P : Measure Ω) (ν : Ω → Measure ℝ) (a b : ℝ) : Measure ℝ :=
  P.bind fun ω => (ν ω).restrict (Ioo a b)

/-- **The Palm point law** `ρ = palmMean / E ν[a,b]`. -/
def palmPoint (P : Measure Ω) (ν : Ω → Measure ℝ) (a b : ℝ) : Measure ℝ :=
  (∫⁻ ω, ν ω (Icc a b) ∂P)⁻¹ • palmMean P ν a b

theorem prop16Law_eq_smul_palmPre :
    prop16Law P ν a b = (∫⁻ ω, ν ω (Icc a b) ∂P)⁻¹ • palmPre P ν a b := rfl

theorem aemeasurable_restrict_of_aemeasurable (hν : AEMeasurable ν P) {I : Set ℝ}
    (hI : MeasurableSet I) : AEMeasurable (fun ω => (ν ω).restrict I) P := by
  refine ⟨fun ω => (hν.mk ν ω).restrict I, Measure.measurable_of_measurable_coe _ fun s hs => ?_,
    hν.ae_eq_mk.mono fun ω hω => by simp only [hω]⟩
  simp_rw [Measure.restrict_apply hs]
  exact (Measure.measurable_coe (hs.inter hI)).comp hν.measurable_mk

theorem palmMean_apply (hν : AEMeasurable ν P) {s : Set ℝ} (hs : MeasurableSet s) :
    palmMean P ν a b s = ∫⁻ ω, ν ω (s ∩ Ioo a b) ∂P := by
  rw [palmMean, Measure.bind_apply hs (aemeasurable_restrict_of_aemeasurable hν measurableSet_Ioo)]
  simp_rw [Measure.restrict_apply hs]

theorem palmMean_compl (hν : AEMeasurable ν P) : palmMean P ν a b (Ioo a b)ᶜ = 0 := by
  rw [palmMean_apply hν measurableSet_Ioo.compl]
  simp

theorem measure_Icc_eq_Ioo_of_null {μ : Measure ℝ} (h : μ (Ioo a b)ᶜ = 0) :
    μ (Icc a b) = μ (Ioo a b) := by
  refine le_antisymm ?_ (measure_mono Ioo_subset_Icc_self)
  calc μ (Icc a b) ≤ μ (Ioo a b ∪ (Ioo a b)ᶜ) := measure_mono (by simp)
    _ ≤ μ (Ioo a b) + μ (Ioo a b)ᶜ := measure_union_le _ _
    _ = μ (Ioo a b) := by rw [h, add_zero]

theorem palmMean_univ (hν : AEMeasurable ν P) (hnull : ∀ ω, ν ω (Ioo a b)ᶜ = 0) :
    palmMean P ν a b univ = ∫⁻ ω, ν ω (Icc a b) ∂P := by
  rw [palmMean_apply hν MeasurableSet.univ, univ_inter]
  exact lintegral_congr fun ω => (measure_Icc_eq_Ioo_of_null (hnull ω)).symm

theorem isProbabilityMeasure_palmPoint (hν : AEMeasurable ν P)
    (hnull : ∀ ω, ν ω (Ioo a b)ᶜ = 0) (hpos : 0 < ∫⁻ ω, ν ω (Icc a b) ∂P)
    (hfin : ∫⁻ ω, ν ω (Icc a b) ∂P < ⊤) : IsProbabilityMeasure (palmPoint P ν a b) := by
  constructor
  rw [palmPoint, Measure.smul_apply, smul_eq_mul, palmMean_univ hν hnull]
  exact ENNReal.inv_mul_cancel hpos.ne' hfin.ne

theorem palmPoint_compl (hν : AEMeasurable ν P) : palmPoint P ν a b (Ioo a b)ᶜ = 0 := by
  rw [palmPoint, Measure.smul_apply, palmMean_compl hν, smul_zero]

/-- `palmPre` does not charge `Ω × (a,b)ᶜ` when every `ν ω` is carried by `(a,b)`. -/
theorem palmPre_compl (hν : AEMeasurable ν P) (hfin : ∫⁻ ω, ν ω (Icc a b) ∂P < ⊤)
    (hnull : ∀ ω, ν ω (Ioo a b)ᶜ = 0) : palmPre P ν a b (univ ×ˢ (Ioo a b)ᶜ) = 0 := by
  rw [palmPre, Measure.bind_apply (MeasurableSet.univ.prod measurableSet_Ioo.compl)
    (aemeasurable_prop16Kernel hν hfin)]
  refine lintegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards [ae_nu_ne_top hν hfin] with ω hω
  rw [prop16Kernel_apply_prod ω hω measurableSet_Ioo.compl]
  simp [measure_mono_null inter_subset_left (hnull ω)]

/-- Continuity from below along the windows `(a + ε_n, b - ε_n)`. -/
theorem iUnion_windows (hab : a < b) :
    (⋃ n : ℕ, Ioo (a + (b - a) / (2 * (n + 2))) (b - (b - a) / (2 * (n + 2)))) = Ioo a b := by
  ext x
  simp only [mem_iUnion, mem_Ioo]
  constructor
  · rintro ⟨n, h1, h2⟩
    have : 0 < (b - a) / (2 * (n + 2)) := div_pos (by linarith) (by positivity)
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / min (x - a) (b - x))
    have hm : 0 < min (x - a) (b - x) := lt_min (by linarith) (by linarith)
    have hlt : (b - a) / (2 * (n + 2)) < min (x - a) (b - x) := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hm] at hn
      nlinarith [min_le_left (x - a) (b - x)]
    exact ⟨n, by linarith [min_le_left (x - a) (b - x)], by linarith [min_le_right (x - a) (b - x)]⟩

theorem window_lt (hab : a < b) (n : ℕ) :
    a < a + (b - a) / (2 * (n + 2)) ∧ b - (b - a) / (2 * (n + 2)) < b := by
  have : 0 < (b - a) / (2 * (n + 2)) := div_pos (by linarith) (by positivity)
  constructor <;> linarith

theorem monotone_windows (hab : a < b) :
    Monotone fun n : ℕ => Ioo (a + (b - a) / (2 * (n + 2))) (b - (b - a) / (2 * (n + 2))) := by
  intro n m hnm
  have h : (b - a) / (2 * ((m : ℝ) + 2)) ≤ (b - a) / (2 * (n + 2)) :=
    div_le_div_of_nonneg_left (by linarith) (by positivity)
      (by have : (n : ℝ) ≤ m := by exact_mod_cast hnm
          linarith)
  exact Ioo_subset_Ioo (by linarith) (by linarith)

/-- **From windows to `(a,b)`.** If `palmPre (T ∩ Ω × (a',b')) = ∫_{(a',b')} f dI` for all
windows, then `palmPre T = ∫ f dI`, for any measure `I` carried by `(a,b)`. -/
theorem palmPre_eq_of_windows (hab : a < b) (hν : AEMeasurable ν P)
    (hfin : ∫⁻ ω, ν ω (Icc a b) ∂P < ⊤) (hnull : ∀ ω, ν ω (Ioo a b)ᶜ = 0) {I : Measure ℝ}
    (hI : I (Ioo a b)ᶜ = 0) (T : Set (Ω × ℝ)) (f : ℝ → ℝ≥0∞)
    (hwin : ∀ a' b', a < a' → b' < b →
      palmPre P ν a b (T ∩ univ ×ˢ Ioo a' b') = ∫⁻ x in Ioo a' b', f x ∂I) :
    palmPre P ν a b T = ∫⁻ x, f x ∂I := by
  set w : ℕ → Set ℝ := fun n => Ioo (a + (b - a) / (2 * (n + 2))) (b - (b - a) / (2 * (n + 2)))
  have hmono := monotone_windows hab
  have hU := iUnion_windows hab
  -- left side
  have hL : palmPre P ν a b T = palmPre P ν a b (T ∩ univ ×ˢ Ioo a b) := by
    refine le_antisymm ?_ (measure_mono inter_subset_left)
    calc palmPre P ν a b T ≤ palmPre P ν a b (T ∩ univ ×ˢ Ioo a b ∪ univ ×ˢ (Ioo a b)ᶜ) :=
          measure_mono fun p hp => by
            by_cases h : p.2 ∈ Ioo a b
            · exact Or.inl ⟨hp, trivial, h⟩
            · exact Or.inr ⟨trivial, h⟩
      _ ≤ _ := measure_union_le _ _
      _ = _ := by rw [palmPre_compl hν hfin hnull, add_zero]
  have hmonoT : Monotone fun n => T ∩ univ ×ˢ w n :=
    fun n m h => inter_subset_inter_right _ (prod_mono subset_rfl (hmono h))
  have hUT : (⋃ n, T ∩ univ ×ˢ w n) = T ∩ univ ×ˢ Ioo a b := by
    rw [← inter_iUnion, ← prod_iUnion, hU]
  have hR : ∫⁻ x, f x ∂I = ⨆ n, ∫⁻ x in w n, f x ∂I := by
    have hIr : I.restrict (Ioo a b) = I := Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hI)
    calc ∫⁻ x, f x ∂I = ∫⁻ x in Ioo a b, f x ∂I := by rw [hIr]
      _ = I.withDensity f (Ioo a b) := (withDensity_apply f measurableSet_Ioo).symm
      _ = I.withDensity f (⋃ n, w n) := by rw [hU]
      _ = ⨆ n, I.withDensity f (w n) := hmono.measure_iUnion
      _ = ⨆ n, ∫⁻ x in w n, f x ∂I := iSup_congr fun n => withDensity_apply f measurableSet_Ioo
  rw [hL, ← hUT, hmonoT.measure_iUnion, hR]
  exact iSup_congr fun n => hwin _ _ (window_lt hab n).1 (window_lt hab n).2

end Abstract

/-! ## Node B′ from the window Palm identity -/

/-- **Remaining node (window Palm identity for the masked zoom coordinates).** A jointly
measurable Palm-side version `F C` of the masked zoom coordinates, equal for `palmMean`-a.e. `x`
and every `C` to the masked zoom coordinates of the Palm-shifted field at `x` (`P`-a.s.), such
that on every window `(a',b')`, `a < a' < b' < b`,
`E ν{x ∈ (a',b') : palmCanonMask C (ω, x) ∈ A} = ∫_{(a',b')} P(F C (·, x) ∈ A) dE ν(x)`. -/
def Prop16PalmWinMaskStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16PalmHyp γ D c d a b h0 P X →
    (∀ C, AEMeasurable (palmCanonMask γ C D a b h0 X) (prop16Q γ h0 a b P X)) →
    ∃ F : ℝ → Ω × ℝ → (ℕ → ℝ), (∀ C, Measurable (F C)) ∧
      (∀ᵐ x ∂palmMean P (fun ω => prop16Nu γ h0 a b (X ω)) a b, ∀ C, ∀ᵐ ω ∂P,
        F C (ω, x) = palmFixedMask γ C D c d a b h0 X x ω) ∧
      ∀ C (A : Set (ℕ → ℝ)), MeasurableSet A → ∀ a' b' : ℝ, a < a' → b' < b →
        palmPre P (fun ω => prop16Nu γ h0 a b (X ω)) a b
            (palmCanonMask γ C D a b h0 X ⁻¹' A ∩ univ ×ˢ Ioo a' b') =
          ∫⁻ x in Ioo a' b', P {ω | F C (ω, x) ∈ A}
            ∂palmMean P (fun ω => prop16Nu γ h0 a b (X ω)) a b

/-- **Node B′ from the window Palm identity**, with the Palm point law `ρ = palmPoint`. -/
theorem prop16PalmIdMaskStmt_of_win (hW : Prop16PalmWinMaskStmt) : Prop16PalmIdMaskStmt := by
  intro γ D c d a b h0 Ω _ P X hH hmeas
  obtain ⟨F, hF, hae, hwin⟩ := hW γ D c d a b h0 P X hH hmeas
  obtain ⟨⟨-, -, -, hab, -, -, -, hP, -, hpos, hfin⟩, hν, -⟩ := hH
  set ν : Ω → Measure ℝ := fun ω => prop16Nu γ h0 a b (X ω) with hνdef
  have hnull : ∀ ω, ν ω (Ioo a b)ᶜ = 0 := fun ω => prop16Nu_compl γ h0 (X ω)
  have := isProbabilityMeasure_palmPoint hν hnull hpos hfin
  refine ⟨palmPoint P ν a b, F, inferInstance, palmPoint_compl hν, hF, Measure.ae_smul_measure hae _,
    fun C => ?_⟩
  ext A hA
  rw [Measure.map_apply_of_aemeasurable (hmeas C) hA, Measure.map_apply (hF C) hA,
    show prop16Q γ h0 a b P X = _ from prop16Law_eq_smul_palmPre, Measure.smul_apply,
    palmPre_eq_of_windows hab hν hfin hnull (palmMean_compl hν) _
      (fun x => P {ω | F C (ω, x) ∈ A}) (hwin C A hA),
    Measure.prod_apply_symm (hF C hA), palmPoint, lintegral_smul_measure]
  rfl

end Prop16Asm

end QuantumZipper
