import QuantumZipper.Proofs.Thm18.A1RS3Path
import QuantumZipper.Proofs.Thm18.A1RS2FixB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS3 (6b): `ratCauchy_Z_of_X` for a positively rescaled parametrization

The rational Cauchy estimate is not invariant under rescaling the parameters (rational points go
to irrational ones), while the side map `g1zSideMap` is only determined up to such a rescaling
(`uniformizer` is a choice). This file records `ratCauchy_Z_of_X_e`, the proof of
`ratCauchy_Z_of_X` (A1RS2ZC.lean) for the family `p ↦ ν_{parScale c p, ρ}`, `c > 0`, and
`exists_smearBox_of_compact` (a compact subset of `smearU` lies in a parameter box).
Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm

/-- A compact subset of `smearU` lies in a parameter box. -/
theorem exists_smearBox_of_compact {K : Set (Fin 4 → ℝ)} (hK : IsCompact K) (hKU : K ⊆ smearU)
    (hne : K.Nonempty) : ∃ t₀ T : ℝ, 0 < t₀ ∧ t₀ ≤ T ∧ ∃ R : ℕ, K ⊆ smearBox t₀ T R := by
  obtain ⟨p0, hp0K, hmin0⟩ := hK.exists_isMinOn hne (continuous_apply 0).continuousOn
  obtain ⟨p1, hp1K, hmax0⟩ := hK.exists_isMaxOn hne (continuous_apply 0).continuousOn
  obtain ⟨p3, hp3K, hmin3⟩ := hK.exists_isMinOn hne (continuous_apply 3).continuousOn
  obtain ⟨p4, -, hmax3⟩ := hK.exists_isMaxOn hne (continuous_apply 3).continuousOn
  obtain ⟨p5, -, hmaxD⟩ := hK.exists_isMaxOn hne (continuous_norm.comp continuous_parD).continuousOn
  have hm3 : 0 < p3 3 := (hKU hp3K).2
  obtain ⟨R, hR⟩ := exists_nat_ge (‖parD p5‖ + |Real.log (p3 3)| + p4 3)
  have hle0 : p0 0 ≤ p1 0 := hmax0 hp0K
  refine ⟨p0 0, p1 0, (hKU hp0K).1, hle0, R, fun p hp => ?_⟩
  have h1 : p0 0 ≤ p 0 := hmin0 hp
  have h2 : p 0 ≤ p1 0 := hmax0 hp
  have h3 : p3 3 ≤ p 3 := hmin3 hp
  have h4 : p 3 ≤ p4 3 := hmax3 hp
  have h5 : ‖parD p‖ ≤ ‖parD p5‖ := hmaxD hp
  have hp4 : 0 ≤ p4 3 := hm3.le.trans (h3.trans h4)
  refine ⟨⟨h1, h2⟩, ?_, ?_, ?_⟩
  · have := abs_nonneg (Real.log (p3 3))
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    linarith
  · have hle : -(R : ℝ) ≤ Real.log (p3 3) := by
      linarith [neg_abs_le (Real.log (p3 3)), norm_nonneg (parD p5)]
    calc Real.exp (-(R : ℝ)) ≤ Real.exp (Real.log (p3 3)) := Real.exp_le_exp.2 hle
      _ = p3 3 := Real.exp_log hm3
      _ ≤ p 3 := h3
  · have := Real.add_one_le_exp (R : ℝ)
    linarith [norm_nonneg (parD p5), abs_nonneg (Real.log (p3 3))]

/-- **Rational Cauchy estimate for `Z` from the free-field one.** -/
theorem ratCauchy_Z_of_X_e {κ : ℝ} {X Z : FieldSample} {FX : ℂ × ℝ → ℝ} {G : ℂ → ℝ}
    (hFX : IsRegularWith X FX) (hGc : Continuous G)
    (hZfc : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      Z (foldedCircle d r) = (X + F2.logSingField κ + ofFun G) (foldedCircle d r))
    {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool) {c : Fin 4 → ℝ} (hc : ∀ i, 0 < c i)
    (hCX : ∀ a b : Fin 4 → ℚ, GenUC.ratBox a b ⊆ smearU → ∀ n : ℕ, ∃ N : ℕ, ∀ r : ℚ, 0 < r →
      (r : ℝ) < 1 / ((N : ℝ) + 1) → ∀ q : Fin 4 → ℚ, ratPt q ∈ GenUC.ratBox a b →
        |evalReg X (smearFam W left (parScale c (ratPt q)) r) - evalReg X (smearFam W left (parScale c (ratPt q)) 0)| <
          1 / ((n : ℝ) + 1))
    (hconv : ∀ q : Fin 4 → ℚ, parScale c (ratPt q) ∈ smearU → ∀ r : ℚ, 0 ≤ r → r ≤ 1 →
      Tendsto (fun k : ℕ => ∫ w, avgReg X k w ∂(smearFam W left (parScale c (ratPt q)) r)) atTop
        (𝓝 (evalReg X (smearFam W left (parScale c (ratPt q)) r)))) :
    ∀ a b : Fin 4 → ℚ, GenUC.ratBox a b ⊆ smearU → ∀ n : ℕ, ∃ N : ℕ, ∀ r : ℚ, 0 < r →
      (r : ℝ) < 1 / ((N : ℝ) + 1) → ∀ q : Fin 4 → ℚ, ratPt q ∈ GenUC.ratBox a b →
        |evalReg Z (smearFam W left (parScale c (ratPt q)) r) - evalReg Z (smearFam W left (parScale c (ratPt q)) 0)| <
          1 / ((n : ℝ) + 1) := by
  intro a b hsub n
  rcases (GenUC.ratBox a b).eq_empty_or_nonempty with he | ⟨p₀, hp₀⟩
  · refine ⟨0, fun r _ _ q hq => ?_⟩
    rw [he] at hq; exact hq.elim
  have hcU : MapsTo (parScale c) smearU smearU := parScale_mapsTo (hc 0) (hc 3)
  obtain ⟨t₀, T, ha0, hab0, R, hbox'⟩ := exists_smearBox_of_compact
    ((GenUC.isCompact_ratBox a b).image (continuous_parScale c))
    (by rintro _ ⟨p, hp, rfl⟩; exact hcU (hsub hp)) ⟨_, p₀, hp₀, rfl⟩
  have hbox : ∀ {p : Fin 4 → ℝ}, p ∈ GenUC.ratBox a b → parScale c p ∈ smearBox t₀ T R :=
    fun hp => hbox' ⟨_, hp, rfl⟩
  obtain ⟨α, CF, Rs, hα, hfacts⟩ := smearFam_box_facts hG left ha0 hab0 R
  set α₀ : ℝ := Real.sqrt κ - 2 / Real.sqrt κ with hα₀
  set prof : (Fin 4 → ℝ) × ℝ → ℝ := fun x =>
    α₀ * (-∫ w, Real.log ‖w‖ ∂(smearFam W left (parScale c x.1) x.2)) +
      ∫ w, G w ∂(smearFam W left (parScale c x.1) x.2) with hprof
  set K : Set ((Fin 4 → ℝ) × ℝ) := GenUC.ratBox a b ×ˢ Icc 0 1 with hK
  have hfc : Continuous fun x : (Fin 4 → ℝ) × ℝ => (parScale c x.1, x.2) :=
    ((continuous_parScale c).comp continuous_fst).prodMk continuous_snd
  have hprofc : ContinuousOn prof K := by
    have h1 := (continuousOn_integral_log_smearFam hG left).comp hfc.continuousOn
      fun x (hx : x ∈ K) => (⟨hcU (hsub hx.1), hx.2⟩ : (parScale c x.1, x.2) ∈ smearU ×ˢ Icc 0 1)
    have h2 := (continuousOn_integral_smearFam hG left hGc.continuousOn hGc.measurable).comp
      hfc.continuousOn fun x (hx : x ∈ K) =>
        (⟨hcU (hsub hx.1), show (0 : ℝ) ≤ x.2 from hx.2.1⟩ : (parScale c x.1, x.2) ∈ smearU ×ˢ Ici 0)
    exact (h1.neg.const_smul α₀).add h2
  have hKc : IsCompact K := (GenUC.isCompact_ratBox a b).prod isCompact_Icc
  have huc := hKc.uniformContinuousOn_of_continuous hprofc
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδc⟩ := huc (1 / (2 * ((n : ℝ) + 1))) (by positivity)
  obtain ⟨N₁, hN₁⟩ := hCX a b hsub (2 * n + 1)
  obtain ⟨N₂, hN₂⟩ := exists_nat_one_div_lt (lt_min hδ one_pos)
  refine ⟨max N₁ N₂, fun r hr0 hrN q hq => ?_⟩
  have hmono : ∀ M : ℕ, M ≤ max N₁ N₂ → 1 / ((max N₁ N₂ : ℕ) + 1 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by
    intro M hM
    apply one_div_le_one_div_of_le (by positivity)
    have : (M : ℝ) ≤ (max N₁ N₂ : ℕ) := by exact_mod_cast hM
    linarith
  have hr1 : (r : ℝ) < 1 / ((N₁ : ℝ) + 1) := hrN.trans_le (hmono N₁ (le_max_left _ _))
  have hr2 : (r : ℝ) < min δ 1 := (hrN.trans_le (hmono N₂ (le_max_right _ _))).trans hN₂
  have hrI : (r : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by exact_mod_cast hr0.le,
    (hr2.trans_le (min_le_right _ _)).le⟩
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  -- the split at `r` and at `0`
  have hqU : parScale c (ratPt q) ∈ smearU := hcU (hsub hq)
  have hsplit : ∀ ρ : ℚ, 0 ≤ ρ → ρ ≤ 1 → evalReg Z (smearFam W left (parScale c (ratPt q)) ρ) =
      evalReg X (smearFam W left (parScale c (ratPt q)) ρ) + prof (ratPt q, ρ) := by
    intro ρ hρ0 hρ1
    have hρI : (ρ : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by exact_mod_cast hρ0, by exact_mod_cast hρ1⟩
    obtain ⟨hP, hsupp, hF⟩ := hfacts _ (hbox hq) _ hρI
    rw [evalReg_Z_split hFX hGc hZfc hsupp hF hα (hconv q hqU ρ hρ0 hρ1)]
    simp only [hprof]
    ring
  have e1 := hsplit r hr0.le (by exact_mod_cast hrI.2)
  have e0 := hsplit 0 le_rfl zero_le_one
  simp only [Rat.cast_zero] at e0
  rw [e1, e0]
  have hX := hN₁ r hr0 hr1 q hq
  have hP := hδc (ratPt q, (r : ℝ)) ⟨hq, hrI⟩ (ratPt q, 0) ⟨hq, h0I⟩ (by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, abs_of_nonneg hrI.1]
    exact max_lt hδ (hr2.trans_le (min_le_left _ _)))
  rw [Real.dist_eq] at hP
  have hn : (1 : ℝ) / (((2 * n + 1 : ℕ) : ℝ) + 1) = 1 / (2 * ((n : ℝ) + 1)) := by
    push_cast; ring_nf
  rw [hn] at hX
  have htwo : 1 / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1)) = 1 / ((n : ℝ) + 1) := by
    field_simp; ring
  calc |evalReg X (smearFam W left (parScale c (ratPt q)) ↑r) + prof (ratPt q, ↑r) -
        (evalReg X (smearFam W left (parScale c (ratPt q)) 0) + prof (ratPt q, 0))|
      ≤ |evalReg X (smearFam W left (parScale c (ratPt q)) ↑r) - evalReg X (smearFam W left (parScale c (ratPt q)) 0)| +
        |prof (ratPt q, ↑r) - prof (ratPt q, 0)| := by
          rw [show ∀ a b c d : ℝ, a + b - (c + d) = (a - c) + (b - d) by intros; ring]
          exact abs_add_le _ _
    _ < 1 / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1)) := add_lt_add hX hP
    _ = 1 / ((n : ℝ) + 1) := htwo

end A1RS
end R18
end QuantumZipper
