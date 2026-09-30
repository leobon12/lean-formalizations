import QuantumZipper.Proofs.Thm18.G3ZqG2Fix
import QuantumZipper.Proofs.Thm18.G2RootXPalmAsm
import QuantumZipper.Proofs.Thm18.G2RootRPalm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 engine with an abstract zoom: the Palm layer (objects, nodes, `x`-side assembly)

Generalized copy (D92) of `G2RootXPalm.lean`, `G2RootXPalmAsm.lean` and `G2RootRPalm.lean`,
with the plain zoom `zoomLaw γ C` replaced by an abstract zoom `Z C h y : LawD` (the plain
engine is `Z = zoomLaw γ`). Zoom-free objects (`outMap`, `xPalm`, `rhoX`, `outEv`, `CondR`,
`g3MassP`, `g3PalmCondR`, `truncSet`, Doob–Dynkin, the pointwise and two-sided bounds) are reused
from the originals. The assembly `g2RootXCutStmtZ_of_palm` uses no property of the zoom at all.

Sheffield, arXiv:1012.4797, proof of Prop. 5.5, pp. 65–66; Duplantier–Sheffield,
arXiv:0808.1560, §3.3 (Palm identity). Own elementary bookkeeping copied from the originals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

section ZoomAbsPalm

variable (Z : ℝ → FieldSample → ℝ → LawD)

/-! ## `x` side -/

/-- `g3RootXPalmEv` with the abstract zoom `Z`. -/
def g3RootXPalmEvZ (γ : ℝ) (i : G3Idx) (s : Set LawD) (m κ : ℝ)
    (G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ)) (x : ℝ) : Set Ω₀ :=
  {ω | Z i.C (normField γ (xPalm γ x) ω) x ∈ s ∧ |x - i.t₁| + m < i.r₁ ∧
    (outMap i (xPalm γ x ω),
      (qBoundaryMeasure γ (normField γ (xPalm γ x) ω) (Icc (x + κ) 0)).toReal) ∈ G'}

theorem g3RootXPalmEvZ_univ_univ (γ : ℝ) (i : G3Idx) (m κ x : ℝ) :
    g3RootXPalmEvZ Z γ i univ m κ univ x = {_ω | |x - i.t₁| + m < i.r₁} := by
  ext _ω; simp [g3RootXPalmEvZ]

/-- `G2RootXPalmIdStmt` (node P) with the abstract zoom `Z`. -/
def G2RootXPalmIdStmtZ (γ : ℝ) : Prop :=
  ∀ (i : G3Idx) (s : Set LawD), MeasurableSet s → ∀ m κ : ℝ, 0 < m → 0 < κ →
    ∀ G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ), MeasurableSet G' →
      g3RootInt γ i ((g3RootEvXcZ Z γ i s m κ (outEv i G')).indicator 1) =
        ∫⁻ x in Icc (-i.δ) 0,
          ENNReal.ofReal (rhoX γ x) * gffBase.P (g3RootXPalmEvZ Z γ i s m κ G' x) ∧
      AEMeasurable
        (fun x => ENNReal.ofReal (rhoX γ x) * gffBase.P (g3RootXPalmEvZ Z γ i s m κ G' x))
        (volume.restrict (Icc (-i.δ) 0))

/-- `G2RootXFixStmt` (node F, conditional zoom at a fixed point) with the abstract zoom `Z`. -/
def G2RootXFixStmtZ (γ : ℝ) (μ : Measure LawD) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m κ : ℝ, 0 < κ → κ < m → ∀ x : ℝ, ∀ ε > 0,
    ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) →
      ∀ G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ), MeasurableSet G' →
        |(gffBase.P (g3RootXPalmEvZ Z γ i s m κ G' x)).toReal -
          μ.real s * (gffBase.P (g3RootXPalmEvZ Z γ i univ m κ G' x)).toReal| ≤ ε

/-! ## `R` side -/

/-- `g3PalmEvR` with the abstract zoom `Z`. -/
def g3PalmEvRZ (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ : ℝ) (G'' : Set (CondR i)) (y : ℝ) :
    Set Ω₀ :=
  {ω | Z i.C (normField γ (xPalm γ y) ω) y ∈ t ∧ |y - i.t₂| + m < i.r₂ ∧
    g3PalmCondR γ i κ y ω ∈ G''}

/-- `g3RootEvRcc` with the abstract zoom `Z`. -/
def g3RootEvRccZ (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ : ℝ) (G'' : Set (CondR i)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | Z i.C (normField γ X₀ q.1) q.2.2 ∈ t ∧ |q.2.2 - i.t₂| + m < i.r₂ ∧
    (outMap i (X₀ q.1), g3CutLenR γ κ q.1 q.2.2, g3Mass γ i q.1) ∈ G''}

theorem g3RootEvRcZ_eq (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ : ℝ)
    (G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ)) :
    g3RootEvRcZ Z γ i t m κ (outEv i G') = g3RootEvRccZ Z γ i t m κ (truncSet i G') := by
  ext q; simp [g3RootEvRcZ, g3RootEvRccZ, truncSet, outEv]

theorem g3PalmEvRZ_univ_univ (γ : ℝ) (i : G3Idx) (m κ y : ℝ) :
    g3PalmEvRZ Z γ i univ m κ univ y = {_ω | |y - i.t₂| + m < i.r₂} := by
  ext _ω; simp [g3PalmEvRZ]

/-- `G2RootRPalmIdStmt` (node P, `R` side) with the abstract zoom `Z`. -/
def G2RootRPalmIdStmtZ (γ : ℝ) : Prop :=
  ∀ (i : G3Idx) (t : Set LawD), MeasurableSet t → ∀ m κ : ℝ, 0 < m → 0 < κ →
    ∀ G'' : Set (CondR i), MeasurableSet G'' →
      g3RootIntR γ i ((g3RootEvRccZ Z γ i t m κ G'').indicator 1) =
        ∫⁻ y in Icc 0 (i.t₂ + i.r₂),
          ENNReal.ofReal (rhoX γ y) * gffBase.P (g3PalmEvRZ Z γ i t m κ G'' y) ∧
      AEMeasurable (fun y => ENNReal.ofReal (rhoX γ y) * gffBase.P (g3PalmEvRZ Z γ i t m κ G'' y))
        (volume.restrict (Icc 0 (i.t₂ + i.r₂)))

/-- `G2RootRFixStmt` (node F, `R` side) with the abstract zoom `Z`. -/
def G2RootRFixStmtZ (γ : ℝ) (ν : Measure LawD) : Prop :=
  ∀ t ∈ lawCyl, ∀ δ η m κ : ℝ, 0 < κ → κ < m → ∀ y : ℝ, ∀ ε > 0,
    ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) →
      ∀ G'' : Set (CondR i), MeasurableSet G'' →
        |(gffBase.P (g3PalmEvRZ Z γ i t m κ G'' y)).toReal -
          ν.real t * (gffBase.P (g3PalmEvRZ Z γ i univ m κ G'' y)).toReal| ≤ ε

variable {Z}

/-! ## `x`-side assembly (copy of `g2RootXCutStmt_of_palm`) -/

/-- **The cut node from the Palm identity and the fixed-point zoom.** -/
theorem g2RootXCutStmtZ_of_palm {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : Measure LawD}
    [IsProbabilityMeasure μ] (hP : G2RootXPalmIdStmtZ Z γ) (hF : G2RootXFixStmtZ Z γ μ) :
    G2RootXCutStmtZ Z γ μ := by
  classical
  intro s hs δ η m κ hκ hκm ε hε
  have hsm : MeasurableSet s := measurableSet_lawCyl hs
  have hm : 0 < m := hκ.trans hκm
  by_cases h0 : ∃ i₀ : G3Idx, i₀.1.1 = δ ∧ i₀.1.2.1 = η
  swap
  · exact Eventually.of_forall fun C i hi => absurd ⟨i, by rw [hi], by rw [hi]⟩ h0
  obtain ⟨i₀, hδ₀, hη₀⟩ := h0
  set c : ℝ := μ.real s with hc
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hc1 : c ≤ 1 := measureReal_le_one
  -- the reference density on the margin window, and its finite mass
  set ρ₀ : ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (rhoX γ x) * gffBase.P (g3RootXPalmEvZ Z γ i₀ univ m κ univ x) with hρ₀
  obtain ⟨hP₀, hρ₀m⟩ := hP i₀ univ MeasurableSet.univ m κ hm hκ univ MeasurableSet.univ
  set M : Measure ℝ := (volume.restrict (Icc (-i₀.δ) 0)).withDensity ρ₀ with hM
  have hMu : M univ = ∫⁻ x in Icc (-i₀.δ) 0, ρ₀ x := by
    rw [hM, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hMfin : M univ ≠ ⊤ := by
    rw [hMu, ← hP₀]
    exact ((g3RootInt_indicator_le_g3Z hγ hγ2 i₀ _).trans_lt (g3Z_pos_lt_top hγ hγ2 i₀).2).ne
  have : IsFiniteMeasure M := ⟨lt_top_iff_ne_top.2 hMfin⟩
  set Zt : ℝ := (M univ).toReal with hZ
  have hZ0 : 0 ≤ Zt := ENNReal.toReal_nonneg
  set ε' : ℝ := ε / (2 * (Zt + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hε'Zt : ε' * Zt ≤ ε / 2 := by
    have e : ε' * (Zt + 1) = ε / 2 := by rw [hε']; field_simp
    nlinarith
  -- the bad set of points (not known to be measurable)
  set bad : ℝ → ℝ → ℝ≥0∞ := fun C x => if (∀ i : G3Idx, i.1 = (δ, η, C) →
      ∀ G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ), MeasurableSet G' →
        |(gffBase.P (g3RootXPalmEvZ Z γ i s m κ G' x)).toReal -
          c * (gffBase.P (g3RootXPalmEvZ Z γ i univ m κ G' x)).toReal| ≤ ε') then 0 else 1 with hbad
  have hbad01 : ∀ C x, bad C x = 0 ∨ bad C x = 1 := fun C x => by
    simp only [hbad]; split_ifs <;> simp
  have hbad1 : ∀ C x, bad C x ≤ 1 := fun C x => by
    rcases hbad01 C x with h | h <;> rw [h]; exact zero_le_one
  have hlim : Tendsto (fun C => ∫⁻ x, bad C x ∂M) atTop (𝓝 0) :=
    D3Plus.tendsto_lintegral_of_ae_tendsto_nonmeas bad hbad1 (ae_of_all _ fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hF s hs δ η m κ hκ hκm x ε' hε'0] with C hC
      simp only [hbad]; rw [ite_eq_left_iff.2 fun h => absurd hC h])
  have hη : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.2 (by positivity)
  filter_upwards [hlim.eventually (gt_mem_nhds hη)] with C hC i hi G hG
  obtain ⟨G', hG', hGe⟩ := exists_outsideSigmaPalm_preimage i hG
  have hGe' : G = outEv i G' := hGe
  subst hGe'
  have hi₁ : i.1.1 = i₀.1.1 := by rw [hi, hδ₀]
  have hi₂ : i.1.2.1 = i₀.1.2.1 := by rw [hi, hη₀]
  obtain ⟨ht, hr⟩ := G3Idx.t₁_r₁_congr hi₁ hi₂
  have hiδ : i.δ = i₀.δ := hi₁
  obtain ⟨hPa, hma⟩ := hP i s hsm m κ hm hκ G' hG'
  obtain ⟨hPb, hmb⟩ := hP i univ MeasurableSet.univ m κ hm hκ G' hG'
  rw [hiδ] at hma hmb
  rw [← g3RootEvXcZ_univ Z, hPa, hPb, hiδ]
  set a : ℝ → ℝ≥0∞ := fun x => gffBase.P (g3RootXPalmEvZ Z γ i s m κ G' x) with ha
  set b : ℝ → ℝ≥0∞ := fun x => gffBase.P (g3RootXPalmEvZ Z γ i univ m κ G' x) with hb
  set ρ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (rhoX γ x) with hρ
  have hma' : AEMeasurable (fun x => ρ x * a x) (volume.restrict (Icc (-i₀.δ) 0)) := hma
  have hmb' : AEMeasurable (fun x => ρ x * b x) (volume.restrict (Icc (-i₀.δ) 0)) := hmb
  have hpt : ∀ x, (ρ x * a x ≤ ENNReal.ofReal c * (ρ x * b x) +
      ρ₀ x * (ENNReal.ofReal ε' + bad C x) ∧
      ENNReal.ofReal c * (ρ x * b x) ≤ ρ x * a x + ρ₀ x * (ENNReal.ofReal ε' + bad C x)) ∧
      ρ x * a x ≤ ρ₀ x ∧ ρ x * b x ≤ ρ₀ x := by
    intro x
    by_cases hx : |x - i.t₁| + m < i.r₁
    · have hset : {_ω : Ω₀ | |x - i₀.t₁| + m < i₀.r₁} = univ :=
        eq_univ_of_forall fun _ => by rw [← ht, ← hr]; exact hx
      have hρ₀x : ρ₀ x = ρ x := by
        simp only [hρ₀, hρ, g3RootXPalmEvZ_univ_univ, hset, measure_univ, mul_one]
      have hax : a x ≤ 1 := prob_le_one
      have hbx : b x ≤ 1 := prob_le_one
      have hgood : bad C x ≠ 1 → |(a x).toReal - c * (b x).toReal| ≤ ε' := fun h => by
        simp only [hbad] at h
        split_ifs at h with hcond
        · exact hcond i hi G' hG'
        · exact absurd rfl h
      obtain ⟨p1, p2⟩ := palm_pointwise hc0 hc1 hε'0.le hax hbx (bad C x) hgood (hbad01 C x)
      rw [hρ₀x]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · calc ρ x * a x ≤ ρ x * (ENNReal.ofReal c * b x + (ENNReal.ofReal ε' + bad C x)) :=
              by gcongr
          _ = _ := by rw [mul_add, mul_left_comm]
      · calc ENNReal.ofReal c * (ρ x * b x) = ρ x * (ENNReal.ofReal c * b x) := mul_left_comm _ _ _
          _ ≤ ρ x * (a x + (ENNReal.ofReal ε' + bad C x)) := by gcongr
          _ = _ := by rw [mul_add]
      · exact (show ρ x * a x ≤ ρ x * 1 by gcongr).trans_eq (mul_one _)
      · exact (show ρ x * b x ≤ ρ x * 1 by gcongr).trans_eq (mul_one _)
    · have hempty : ∀ s' : Set LawD, g3RootXPalmEvZ Z γ i s' m κ G' x = ∅ := fun s' =>
        eq_empty_of_forall_notMem fun ω hω => hx hω.2.1
      have ha0 : a x = 0 := by simp only [ha, hempty, measure_empty]
      have hb0 : b x = 0 := by simp only [hb, hempty, measure_empty]
      simp only [ha0, hb0, mul_zero, zero_add, zero_le, and_self]
  have hfin₀ : ∀ᵐ x ∂(volume.restrict (Icc (-i₀.δ) 0)), ρ₀ x < ⊤ := ae_of_all _ fun x =>
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (prob_le_one.trans_lt ENNReal.one_lt_top)
  have hWD : ∫⁻ x in Icc (-i₀.δ) 0, ρ₀ x * (ENNReal.ofReal ε' + bad C x) =
      ENNReal.ofReal ε' * M univ + ∫⁻ x, bad C x ∂M := by
    rw [← lintegral_const, ← lintegral_add_left measurable_const]
    exact (lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hρ₀m hfin₀ _).symm
  set E : ℝ≥0∞ := ENNReal.ofReal ε' * M univ + ∫⁻ x, bad C x ∂M with hE
  have hI1 : ∫⁻ x in Icc (-i₀.δ) 0, ρ x * a x ≤
      ENNReal.ofReal c * (∫⁻ x in Icc (-i₀.δ) 0, ρ x * b x) + E := by
    calc ∫⁻ x in Icc (-i₀.δ) 0, ρ x * a x
        ≤ ∫⁻ x in Icc (-i₀.δ) 0, (ENNReal.ofReal c * (ρ x * b x) +
            ρ₀ x * (ENNReal.ofReal ε' + bad C x)) := lintegral_mono fun x => (hpt x).1.1
      _ = (∫⁻ x in Icc (-i₀.δ) 0, ENNReal.ofReal c * (ρ x * b x)) +
            ∫⁻ x in Icc (-i₀.δ) 0, ρ₀ x * (ENNReal.ofReal ε' + bad C x) :=
          lintegral_add_left' (hmb'.const_mul _) _
      _ = _ := by rw [hWD]; congr 1; exact lintegral_const_mul'' _ hmb'
  have hI2 : ENNReal.ofReal c * ∫⁻ x in Icc (-i₀.δ) 0, ρ x * b x ≤
      (∫⁻ x in Icc (-i₀.δ) 0, ρ x * a x) + E := by
    calc ENNReal.ofReal c * ∫⁻ x in Icc (-i₀.δ) 0, ρ x * b x
        = ∫⁻ x in Icc (-i₀.δ) 0, ENNReal.ofReal c * (ρ x * b x) :=
          (lintegral_const_mul'' _ hmb').symm
      _ ≤ ∫⁻ x in Icc (-i₀.δ) 0, (ρ x * a x + ρ₀ x * (ENNReal.ofReal ε' + bad C x)) :=
          lintegral_mono fun x => (hpt x).1.2
      _ = (∫⁻ x in Icc (-i₀.δ) 0, ρ x * a x) +
            ∫⁻ x in Icc (-i₀.δ) 0, ρ₀ x * (ENNReal.ofReal ε' + bad C x) :=
          lintegral_add_left' hma' _
      _ = _ := by rw [hWD]
  have hA : ∫⁻ x in Icc (-i₀.δ) 0, ρ x * a x ≠ ⊤ :=
    ne_top_of_le_ne_top (hMu ▸ hMfin) (lintegral_mono fun x => (hpt x).2.1)
  have hB : ∫⁻ x in Icc (-i₀.δ) 0, ρ x * b x ≠ ⊤ :=
    ne_top_of_le_ne_top (hMu ▸ hMfin) (lintegral_mono fun x => (hpt x).2.2)
  have hbadfin : ∫⁻ x, bad C x ∂M ≠ ⊤ := (hC.trans ENNReal.ofReal_lt_top).ne
  have hEfin : E ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMfin, hbadfin⟩
  have hEle : E.toReal ≤ ε := by
    rw [hE, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMfin) hbadfin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hε'0.le, ← hZ]
    have h2 : (∫⁻ x, bad C x ∂M).toReal ≤ ε / 2 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hC.le
    linarith
  exact (abs_toReal_sub_le_of_two_sided hc0 hA hB hEfin hI1 hI2).trans hEle

end ZoomAbsPalm

end Thm18Asm
end QuantumZipper
