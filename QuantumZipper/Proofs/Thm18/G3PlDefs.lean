import QuantumZipper.Proofs.Thm18.R18G3TSplit
import QuantumZipper.Proofs.Thm18.R18G3TXSide3
import QuantumZipper.Proofs.Thm18.G3PalmRTightMom
import QuantumZipper.Proofs.LQG.MeasurabilityAE

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b): the plain wedge scheme, Palm-window part

`G3TWedgePlainStmt` (R18G3TGeoSplit) compares the normalized plain Palm-window integral of the
wedge with the weighted Palm integral of scheme `C` (field `h_C = normField + g3wProf γ`), with the
weight `w = 1{ℓ ≤ U} · Z/U` of D85. This file and `G3PlMain.lean` do the scheme-`C` side of that
comparison (Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71: the Palm point `x` is sampled
from the boundary length on a window, `R(x)` is its length partner):

* the weighted Palm integral of scheme `C` is `U⁻¹ E Leb{ℓ ∈ (0, U ∧ ν_C[−δ, 0]] : …}`
  (`g3pPalmLaw_apply_eq_lebesgue`, the Palm length is uniform given the field);
* on the event that `ν_C[−δ/2, 0]` and `ν_C[0, 1/4]` exceed `U` and `ℓ` exceeds the masses of
  `[−3m, 0]` and `[0, 3m]`, the scheme's Palm point and partner are the honest ones read from
  `ν_C` (F2-C, `ae_g3pFid_sets`) and lie a margin `m` inside the two half-discs;
* the exceptional Palm mass is `o(U)` as `m → 0` (no atom of `ν_C` at `0`) and the probability
  that `ν_C[−δ/2, 0]` or `ν_C[0, 1/4]` is below `U` tends to `0` as `U → 0` (a.s. positivity,
  Sheffield §5.1 p. 61, `Positivity.ae_forall_pos_qBoundaryMeasure_Ioo`).

What remains is the honest comparison `G3PlHonestStmt`: the plain wedge Palm-window integral is
close to the same Palm-window integral of `h_C` read with `ν_C` (wedge law, unit-area dilation,
locality of the zooms). Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- The field of scheme `C`. -/
abbrev g3plF (γ : ℝ) (ω : Ω₀) : FieldSample := g3pField γ (g3wProf γ) ω

/-- Its (honest) boundary length measure `ν_C`. -/
abbrev g3plV (γ : ℝ) (ω : Ω₀) : Measure ℝ := qBoundaryMeasure γ (g3plF γ ω)

/-- The honest Palm-window set: Palm lengths `ℓ ∈ (0, U]` with `ℓ ≤ ν_C[−δ, 0]` whose zooms at
the point `x` at length `ℓ` left of `0` and at its partner `R(x)` lie in `s` and `t`. -/
def g3plHonSet (γ δ U L : ℝ) (s t : Set LawD) (ω : Ω₀) : Set ℝ :=
  {ℓ | ℓ ∈ Ioc 0 U ∧ ENNReal.ofReal ℓ ≤ g3plV γ ω (Icc (-δ) 0) ∧
    zoomLaw γ L (g3plF γ ω) (lenLeft (g3plV γ ω) ℓ) ∈ s ∧
    zoomLaw γ L (g3plF γ ω) (lenRight (g3plV γ ω) ℓ) ∈ t}

/-- The honest Palm-window integral of scheme `C` (unnormalized). -/
def g3plHon (γ δ U L : ℝ) (s t : Set LawD) : ℝ≥0∞ :=
  ∫⁻ ω, volume (g3plHonSet γ δ U L s t ω) ∂gffBase.P

/-! ## Points by length: deterministic facts -/

section Len

variable {m m' : Measure ℝ} {ℓ a b : ℝ}

/-- Infima of two sets bounded below by `0` agree if both contain `a` and they agree below `a`. -/
theorem sInf_eq_of_agree_le {S T : Set ℝ} (hS0 : ∀ y ∈ S, 0 ≤ y) (hT0 : ∀ y ∈ T, 0 ≤ y)
    (haS : a ∈ S) (haT : a ∈ T) (h : ∀ y, y ≤ a → (y ∈ S ↔ y ∈ T)) : sInf S = sInf T := by
  have key : ∀ {S T : Set ℝ}, (∀ y ∈ S, 0 ≤ y) → a ∈ S → a ∈ T →
      (∀ y, y ≤ a → y ∈ T → y ∈ S) → sInf S ≤ sInf T := by
    intro S T hS0 haS haT h
    have hbdd : BddBelow S := ⟨0, hS0⟩
    refine le_csInf ⟨a, haT⟩ fun y hy => ?_
    by_cases hya : y ≤ a
    · exact csInf_le hbdd (h y hya hy)
    · exact (csInf_le hbdd haS).trans (not_le.1 hya).le
  exact le_antisymm (key hS0 haS haT fun y hy => (h y hy).2)
    (key hT0 haT haS fun y hy => (h y hy).1)

theorem lenLeft_eq_of_agree (ha : 0 < a) (hℓ : ENNReal.ofReal ℓ ≤ m (Icc (-a) 0))
    (hag : ∀ y, 0 < y → y ≤ a → m (Icc (-y) 0) = m' (Icc (-y) 0)) :
    lenLeft m ℓ = lenLeft m' ℓ := by
  unfold lenLeft
  congr 1
  refine sInf_eq_of_agree_le (a := a) (fun y hy => hy.1.le) (fun y hy => hy.1.le) ⟨ha, hℓ⟩
    ⟨ha, (hag a ha le_rfl) ▸ hℓ⟩ fun y hy => ?_
  constructor
  · rintro ⟨h0, h1⟩; exact ⟨h0, (hag y h0 hy) ▸ h1⟩
  · rintro ⟨h0, h1⟩; exact ⟨h0, (hag y h0 hy).symm ▸ h1⟩

theorem lenRight_eq_of_agree (ha : 0 < a) (hℓ : ENNReal.ofReal ℓ ≤ m (Icc 0 a))
    (hag : ∀ y, 0 < y → y ≤ a → m (Icc 0 y) = m' (Icc 0 y)) :
    lenRight m ℓ = lenRight m' ℓ := by
  unfold lenRight
  refine sInf_eq_of_agree_le (a := a) (fun y hy => hy.1.le) (fun y hy => hy.1.le) ⟨ha, hℓ⟩
    ⟨ha, (hag a ha le_rfl) ▸ hℓ⟩ fun y hy => ?_
  constructor
  · rintro ⟨h0, h1⟩; exact ⟨h0, (hag y h0 hy) ▸ h1⟩
  · rintro ⟨h0, h1⟩; exact ⟨h0, (hag y h0 hy).symm ▸ h1⟩

theorem neg_le_lenLeft (ha : 0 < a) (hℓ : ENNReal.ofReal ℓ ≤ m (Icc (-a) 0)) :
    -a ≤ lenLeft m ℓ := by
  unfold lenLeft
  exact neg_le_neg (csInf_le ⟨0, fun y hy => hy.1.le⟩ ⟨ha, hℓ⟩)

theorem lenLeft_le_neg (ha : 0 < a) (hℓ : ENNReal.ofReal ℓ ≤ m (Icc (-a) 0))
    (hb : m (Icc (-b) 0) < ENNReal.ofReal ℓ) : lenLeft m ℓ ≤ -b := by
  unfold lenLeft
  refine neg_le_neg (le_csInf ⟨a, ha, hℓ⟩ fun y hy => ?_)
  by_contra hyb
  exact absurd (hy.2.trans (measure_mono (Icc_subset_Icc_left (by linarith [not_le.1 hyb]))))
    (not_le.2 hb)

theorem lenRight_le (ha : 0 < a) (hℓ : ENNReal.ofReal ℓ ≤ m (Icc 0 a)) : lenRight m ℓ ≤ a :=
  csInf_le ⟨0, fun y hy => hy.1.le⟩ ⟨ha, hℓ⟩

theorem le_lenRight (ha : 0 < a) (hℓ : ENNReal.ofReal ℓ ≤ m (Icc 0 a))
    (hb : m (Icc 0 b) < ENNReal.ofReal ℓ) : b ≤ lenRight m ℓ := by
  refine le_csInf ⟨a, ha, hℓ⟩ fun y hy => ?_
  by_contra hyb
  exact absurd (hy.2.trans (measure_mono (Icc_subset_Icc_right (not_le.1 hyb).le))) (not_le.2 hb)

/-- `Leb{ℓ ∈ (0, U] : ℓ ≤ c} ≤ min U c`. -/
theorem volume_Ioc_le_min {U : ℝ} (c : ℝ≥0∞) :
    volume {ℓ : ℝ | ℓ ∈ Ioc 0 U ∧ ENNReal.ofReal ℓ ≤ c} ≤ min (ENNReal.ofReal U) c := by
  refine le_min ((measure_mono fun ℓ hℓ => hℓ.1).trans (by rw [Real.volume_Ioc, sub_zero])) ?_
  by_cases hc : c = ⊤
  · rw [hc]; exact le_top
  · calc volume {ℓ : ℝ | ℓ ∈ Ioc 0 U ∧ ENNReal.ofReal ℓ ≤ c} ≤ volume (Ioc 0 c.toReal) :=
          measure_mono fun ℓ hℓ => ⟨hℓ.1.1, (ENNReal.ofReal_le_iff_le_toReal hc).1 hℓ.2⟩
      _ = c := by rw [Real.volume_Ioc, sub_zero, ENNReal.ofReal_toReal hc]

end Len

/-! ## A.s. facts about `ν_C` -/

theorem aemeasurable_g3plV {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    AEMeasurable (g3plV γ) gffBase.P :=
  LQGMeasAE.aemeasurable_qBoundaryMeasure_of_ae
    (fun μ => (measurable_pi_apply μ).comp (measurable_g3pField γ (g3wProf γ)))
    ((ae_g3pField_good hγ hγ2).mono fun _ h => h.1)

/-- A.s. `ν_C` charges every open interval not containing `0`. -/
theorem ae_g3plV_Ioo_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂gffBase.P, ∀ a b : ℝ, a < b → (0 ≤ a ∨ b ≤ 0) → 0 < g3plV γ ω (Ioo a b) := by
  filter_upwards [ae_g3pField_good hγ hγ2, Positivity.ae_forall_pos_qBoundaryMeasure_Ioo
    (isFreeGFFModConstH_zField gffBase.gff 1) hγ hγ2] with ω hω hpos a b hab h0
  obtain ⟨-, -, -, hform⟩ := hω
  set νZ := qBoundaryMeasure γ (BdryExist.zField gffBase.X 1 ω)
  have hρ : Measurable fun t : ℝ => ENNReal.ofReal (|t - 0| ^ (-(αC γ * γ / 2))) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_id.sub continuous_const).abs.measurable.pow_const _)
  refine pos_iff_ne_zero.2 fun hz => ?_
  change qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω) (Ioo a b) = 0 at hz
  rw [hform, withDensity_apply_eq_zero' hρ.aemeasurable,
    Measure.restrict_apply' (measurableSet_singleton 0).compl] at hz
  have hsub : Ioo a b ⊆ ({t | ENNReal.ofReal (|t - 0| ^ (-(αC γ * γ / 2))) ≠ 0} ∩ Ioo a b) ∩
      ({0} : Set ℝ)ᶜ := by
    intro t ht
    have ht0 : t ≠ 0 := by
      rcases h0 with h0 | h0
      · exact (lt_of_le_of_lt h0 ht.1).ne'
      · exact (lt_of_lt_of_le ht.2 h0).ne
    refine ⟨⟨?_, ht⟩, ht0⟩
    simp only [sub_zero, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos (abs_pos.2 ht0) _
  exact (hpos a b hab).ne' (measure_mono_null hsub hz)

end R18
end QuantumZipper
