import QuantumZipper.Proofs.Thm18.RT6MOData
import QuantumZipper.Proofs.Thm18.R18RTMeasTime

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT6b: Borel readings of the pieces flow

Sheffield (arXiv:1012.4797, p. 26) treats `Z^LEN_t` as measurable maps. For the inverse argument
(RT6MOGroup.lean) it suffices that each `zipLenMO γ ℓ` be read on the encoded data
(`encR`, RT6MOData.lean) by a Borel map `g` on a Borel set `Bs` carrying the wedge data
(`PiecesReadStmt`), deterministically for continuous drivers. For `ℓ < 0` this is RT3
(`DownDataMeasCStmt`) transported to the encoding by a measurable decoding `decM` (continuous
drivers are recovered from their dyadic values by `limsup`); for `ℓ ≥ 0` it is the zip-up
analogue of RT3 (`UpPiecesReadStmt`, open). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- Dyadic lower approximation of `s ≥ 0`. -/
def dyQ (n : ℕ) (s : ℝ≥0) : ℚ := (⌊(s : ℝ) * 2 ^ n⌋₊ : ℚ) / 2 ^ n

theorem dyQ_nonneg (n : ℕ) (s : ℝ≥0) : (0 : ℝ) ≤ (dyQ n s : ℝ) := by
  unfold dyQ; push_cast; positivity

theorem abs_dyQ_sub_le (n : ℕ) (s : ℝ≥0) : |(dyQ n s : ℝ) - s| ≤ 1 / 2 ^ n := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have h1 := Nat.floor_le (show (0 : ℝ) ≤ (s : ℝ) * 2 ^ n by positivity)
  have h2 := Nat.lt_floor_add_one ((s : ℝ) * 2 ^ n)
  have e : (dyQ n s : ℝ) = (⌊(s : ℝ) * 2 ^ n⌋₊ : ℝ) / 2 ^ n := by unfold dyQ; push_cast; ring
  rw [e, abs_le]
  constructor
  · rw [show -(1 / (2 : ℝ) ^ n) = ((s : ℝ) * 2 ^ n - 1) / 2 ^ n - s by field_simp; ring]
    exact sub_le_sub_right (div_le_div_of_nonneg_right (by linarith) hp.le) _
  · have : (⌊(s : ℝ) * 2 ^ n⌋₊ : ℝ) / 2 ^ n ≤ s := by
      rw [div_le_iff₀ hp]; exact h1
    have h3 : (0 : ℝ) ≤ 1 / 2 ^ n := by positivity
    linarith

theorem tendsto_ratNN_dyQ (s : ℝ≥0) : Tendsto (fun n => ratNN (dyQ n s)) atTop (𝓝 s) := by
  rw [← NNReal.tendsto_coe]
  have e : (fun n => ((ratNN (dyQ n s) : ℝ≥0) : ℝ)) = fun n => (dyQ n s : ℝ) := by
    funext n; show max (dyQ n s : ℝ) 0 = _; exact max_eq_left (dyQ_nonneg n s)
  rw [e]
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
    simp only [one_div, ← inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0)
  rw [Real.norm_eq_abs]; exact abs_dyQ_sub_le n s

/-- Measurable extension of a function of the rational times. -/
def extM (g : ℚ → ℝ) (s : ℝ≥0) : ℝ := limsup (fun n => g (dyQ n s)) atTop

/-- Measurable decoding. -/
def decM (y : RD) : (ℕ → ℝ) × (ℝ≥0 → ℝ) := (y.1.1, extM y.1.2)

theorem measurable_decM : Measurable decM := by
  refine (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun s => ?_)
  exact Measurable.limsup fun n => (measurable_pi_apply _).comp (measurable_snd.comp measurable_fst)

theorem decM_encR {e : (ℕ → ℝ) × (ℝ≥0 → ℝ)} (hc : Continuous e.2) : decM (encR e) = e := by
  refine Prod.ext rfl (funext fun s => ?_)
  exact ((hc.tendsto s).comp (tendsto_ratNN_dyQ s)).limsup_eq

/-- Measurable encoding with the flag set. -/
def encT' (e : (ℕ → ℝ) × (ℝ≥0 → ℝ)) : RD := ((e.1, fun q => e.2 (ratNN q)), 1)

theorem measurable_encT' : Measurable encT' := by
  refine Measurable.prodMk (Measurable.prodMk measurable_fst ?_) measurable_const
  exact measurable_pi_iff.2 fun q => (measurable_pi_apply _).comp measurable_snd

theorem encR_eq_encT' {e : (ℕ → ℝ) × (ℝ≥0 → ℝ)} (hc : Continuous e.2) : encR e = encT' e := by
  simp [encR, encT', hc]

/-- **Borel readings of the pieces flow** on the encoded data. -/
def PiecesReadStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ ℓ : ℝ,
      ∃ (Bs : Set RD) (g : RD → RD), MeasurableSet Bs ∧ Measurable g ∧
        (∀ e : (ℕ → ℝ) × (ℝ≥0 → ℝ), Continuous e.2 → encR e ∈ Bs →
          g (encR e) = encR (πdO (zipRead γ ℓ e))) ∧
        ∀ᵐ ω ∂P, encR (πdO (wedgeAConfig γ B Y ω)) ∈ Bs

/-- **Borel reading of zipping up the pieces** (open; the zip-up analogue of RT3,
`DownDataMeasCStmt`, and of D81 for the pieces). -/
def UpPiecesReadStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ ℓ : ℝ, 0 ≤ ℓ →
      ∃ (Bs : Set RD) (g : RD → RD), MeasurableSet Bs ∧ Measurable g ∧
        (∀ e : (ℕ → ℝ) × (ℝ≥0 → ℝ), Continuous e.2 → encR e ∈ Bs →
          g (encR e) = encR (πdO (zipRead γ ℓ e))) ∧
        ∀ᵐ ω ∂P, encR (πdO (wedgeAConfig γ B Y ω)) ∈ Bs

/-- The Borel readings of the pieces flow, from RT3 (unzipping) and the zip-up reading. -/
theorem piecesReadStmt_of (hDM : DownDataMeasCStmt) (hUp : UpPiecesReadStmt) :
    PiecesReadStmt := by
  intro γ Ω _ P _ B Y hS hIn ℓ
  by_cases hℓ : 0 ≤ ℓ
  · exact hUp γ P B Y hS hIn ℓ hℓ
  obtain ⟨G, Dm, hGm, hDmm, hDmEq, hG0⟩ := hDM γ P B Y hS hIn (-ℓ) (by linarith)
  refine ⟨decM ⁻¹' G ∩ {y | y.2 = 1}, fun y => encT' (Dm (decM y)),
    (measurable_decM hGm).inter (measurableSet_eq_fun measurable_snd measurable_const),
    measurable_encT'.comp (hDmm.comp measurable_decM), fun e hc he => ?_, ?_⟩
  · have hG : e ∈ G := by have := he.1; rwa [Set.mem_preimage, decM_encR hc] at this
    have hD := hDmEq (liftπ e) hG hc
    have hin : Continuous (configOfData γ (liftπ e)).drv :=
      hc.comp (continuous_real_toNNReal)
    have hout := (zipLenDownA_drv_good (γ := γ) (ℓ := -ℓ) hin).1
    show encT' (Dm (decM (encR e))) = _
    have hz : zipRead γ ℓ e = zipLenDownA γ (-ℓ) (configOfData γ (liftπ e)) := by
      unfold zipRead; rw [if_neg hℓ]
    rw [decM_encR hc, hz, encR_eq_encT' (show Continuous
      (πdO (zipLenDownA γ (-ℓ) (configOfData γ (liftπ e)))).2 from hout.comp continuous_subtype_val)]
    exact congrArg encT' hD
  · filter_upwards [hG0, D74.ae_wedgeConfig_snd_good hS] with ω h hg
    have hc : Continuous (πdO (wedgeAConfig γ B Y ω)).2 := hg.1.comp continuous_subtype_val
    refine ⟨?_, ?_⟩
    · show decM (encR (πdO _)) ∈ G
      rw [decM_encR hc]; exact h
    · show (encR (πdO _)).2 = 1
      simp [encR, hc]

end R18
end QuantumZipper
