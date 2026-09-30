import QuantumZipper.Proofs.Thm18.LWRenew2HitMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LWS-0′-HIT: the hitting time after a stopping time is a.s. a stopping time

`lwr_hit_stop`: for `0 < κ < 4`, the first time after the stopping time `σ` at which the SLE trace
meets the random closed set `closure (c '' {j | ω ∈ M j})` (the `M j` being `𝓕_σ`-events) is
almost surely equal to a stopping time of the raw natural filtration, namely the guarded hitting
time `hitTime` (LWRenew2HitMain.lean). On the a.s. event of Rohde–Schramm's radial bound
(`RS.ae_sleTrace_good`; RS *Basic properties of SLE*, Thm 3.6 and 5.1) the guard holds on every
`[0,N]` for some level `C`, and the two hitting times agree.

Source for the classical part: Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*,
Problem 1.2.7; Revuz–Yor, *Continuous Martingales and Brownian Motion*, Prop. I.4.5. The guard
device (needed because the filtration is not completed) is own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

lemma withTop_eq_of_le_iff {x y : WithTop ℝ≥0} (h : ∀ u : ℝ≥0, x ≤ u ↔ y ≤ u) : x = y := by
  induction x using WithTop.recTopCoe with
  | top =>
    induction y using WithTop.recTopCoe with
    | top => rfl
    | coe b => exact absurd ((h b).2 le_rfl) (not_le.2 (WithTop.coe_lt_top _))
  | coe a =>
    induction y using WithTop.recTopCoe with
    | top => exact absurd ((h a).1 le_rfl) (not_le.2 (WithTop.coe_lt_top _))
    | coe b => exact le_antisymm ((h b).2 le_rfl) ((h a).1 le_rfl)

lemma coe_le_ofReal_iff' {s0 : ℝ≥0} {t : ℝ} (ht : 0 ≤ t) :
    ((s0 : WithTop ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal t ↔ (s0 : ℝ) ≤ t := by
  show (s0 : ℝ≥0∞) ≤ _ ↔ _
  rw [ENNReal.ofReal, ENNReal.coe_le_coe, Real.le_toNNReal_iff_coe_le ht]

/-- The radial bound of `RS.ae_sleTrace_good` gives the guard on `[0,N]`. -/
lemma radGuard_of_bound {W : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) {γ : ℝ → ℂ} {N C : ℝ} (hN : 0 ≤ N)
    (h : ∀ t ∈ Icc (0 : ℝ) N, ∀ y ∈ Ioc (0 : ℝ) 1,
      ‖fwdMapInv W t (y * Complex.I) - γ t‖ ≤ C * y ^ δ) :
    ∃ C' : ℕ, RadGuard W δ C' N := by
  have hC : 0 ≤ C := by
    have := h 0 ⟨le_rfl, hN⟩ 1 ⟨one_pos, le_rfl⟩
    rw [Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  refine ⟨⌈2 * C⌉₊, fun t ht y hy y' hy' => ?_⟩
  have h1 := h t ht y hy
  have h2 := h t ht y' ⟨hy'.1, hy'.2.trans hy.2⟩
  have hyy : y' ^ δ ≤ y ^ δ := Real.rpow_le_rpow hy'.1.le hy'.2 hδ.le
  have hyd : 0 ≤ y ^ δ := Real.rpow_nonneg hy.1.le _
  have h3 : C * y' ^ δ ≤ C * y ^ δ := mul_le_mul_of_nonneg_left hyy hC
  calc dist (fwdMapInv W t (↑y * Complex.I)) (fwdMapInv W t (↑y' * Complex.I))
      ≤ dist (fwdMapInv W t (↑y * Complex.I)) (γ t) +
          dist (fwdMapInv W t (↑y' * Complex.I)) (γ t) := dist_triangle_right _ _ _
    _ ≤ C * y ^ δ + C * y' ^ δ := by rw [dist_eq_norm, dist_eq_norm]; exact add_le_add h1 h2
    _ ≤ (2 * C) * y ^ δ := by linarith
    _ ≤ (⌈2 * C⌉₊ : ℝ) * y ^ δ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hyd

/-- **LWS-0′-HIT.** The hitting time, after a stopping time, of a random closed set given by
countably many `𝓕_σ`-events is a.s. equal to a stopping time of the raw natural filtration. -/
theorem lwr_hit_stop {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} (hS : SMSetup P B 𝓕)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓕 σ)
    (c : ℕ → ℂ) (M : ℕ → Set Ω) (hM : ∀ j (t : ℝ≥0), MeasurableSet[𝓕 t] (M j ∩ {ω | σ ω ≤ t})) :
    ∃ τ' : Ω → WithTop ℝ≥0, IsStoppingTime 𝓕 τ' ∧ ∀ᵐ ω ∂P,
      τ' ω = (sInf (ENNReal.ofReal '' {t : ℝ | 0 ≤ t ∧ (σ ω : ℝ≥0∞) ≤ ENNReal.ofReal t ∧
        sleTrace κ B ω t ∈ closure (c '' {j | ω ∈ M j})}) : WithTop ℝ≥0) := by
  obtain ⟨δ, hδ, hgood⟩ := RS.ae_sleTrace_good hS.brownian hκ (by linarith)
  refine ⟨hitTime κ δ B σ c M, isStoppingTime_hitTime hS κ hδ hσ c M hM, ?_⟩
  filter_upwards [hgood] with ω hω
  obtain ⟨-, -, hbd⟩ := hω
  set K := c '' {j | ω ∈ M j} with hK
  set A := {t : ℝ | 0 ≤ t ∧ (σ ω : ℝ≥0∞) ≤ ENNReal.ofReal t ∧ sleTrace κ B ω t ∈ closure K}
    with hA
  have hW := drive_continuous (κ := κ) (hS.cont ω)
  have hW0 := drive_zero (κ := κ) (hS.zero ω)
  have hguard : ∀ N : ℕ, ∃ C : ℕ, RadGuard (drive κ B ω) δ C N := fun N => by
    obtain ⟨C, hC⟩ := hbd N
    exact radGuard_of_bound hδ (Nat.cast_nonneg N) hC
  refine withTop_eq_of_le_iff fun u => ?_
  rw [hitTime_le_iff hS hδ ω u]
  show _ ↔ sInf (ENNReal.ofReal '' A) ≤ (u : ℝ≥0∞)
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨s0, hs0, s, hs, -, hsK⟩ := (mem_hitEv_iff hS hδ).1 hC
    have hs0' : (0 : ℝ) ≤ s := s0.coe_nonneg.trans hs.1
    have hsA : s ∈ A := ⟨hs0', by rw [hs0]; exact (coe_le_ofReal_iff' hs0').2 hs.1, hsK⟩
    calc sInf (ENNReal.ofReal '' A) ≤ ENNReal.ofReal s := sInf_le ⟨s, hsA, rfl⟩
      _ ≤ ENNReal.ofReal u := ENNReal.ofReal_le_ofReal hs.2
      _ = u := ENNReal.ofReal_coe_nnreal
  · intro hT
    have hlt : sInf (ENNReal.ofReal '' A) < (u : ℝ≥0∞) + 1 :=
      hT.trans_lt (ENNReal.lt_add_right ENNReal.coe_ne_top one_ne_zero)
    obtain ⟨_, ⟨t, htA, rfl⟩, htlt⟩ := sInf_lt_iff.1 hlt
    have htu : t < u + 1 := by
      have : ENNReal.ofReal t < ENNReal.ofReal ((u : ℝ) + 1) := by
        rwa [ENNReal.ofReal_add u.coe_nonneg zero_le_one, ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 this
    have hN : (u : ℝ) + 1 ≤ (⌈(u : ℝ) + 1⌉₊ : ℕ) := Nat.le_ceil _
    obtain ⟨C, hCg⟩ := hguard ⌈(u : ℝ) + 1⌉₊
    obtain ⟨s0, hs0⟩ : ∃ s0 : ℝ≥0, σ ω = s0 := by
      have hne : σ ω ≠ ⊤ := by
        intro htop
        have h' := htA.2.1
        rw [htop] at h'
        exact ENNReal.ofReal_ne_top (top_le_iff.1 h')
      obtain ⟨s0, h⟩ := WithTop.ne_top_iff_exists.1 hne
      exact ⟨s0, h.symm⟩
    have hts0 : (s0 : ℝ) ≤ t := by
      have h' := htA.2.1; rw [hs0] at h'; exact (coe_le_ofReal_iff' htA.1).1 h'
    obtain ⟨m, hmσ, hmG, hmK, hmin⟩ := exists_first_guardedHit hW hW0 hδ s0.coe_nonneg K
      ⟨t, hts0, hCg.mono (by linarith), htA.2.2⟩
    have hmt : m ≤ t := hmin t hts0 (hCg.mono (by linarith)) htA.2.2
    have hlb : ENNReal.ofReal m ≤ sInf (ENNReal.ofReal '' A) := by
      refine le_sInf ?_
      rintro _ ⟨t', ht'A, rfl⟩
      refine ENNReal.ofReal_le_ofReal ?_
      by_cases ht'N : t' ≤ (⌈(u : ℝ) + 1⌉₊ : ℕ)
      · have h' := ht'A.2.1
        rw [hs0] at h'
        exact hmin t' ((coe_le_ofReal_iff' ht'A.1).1 h') (hCg.mono ht'N) ht'A.2.2
      · push Not at ht'N
        linarith
    have hmu : m ≤ u := by
      have h' := hlb.trans hT
      rw [← ENNReal.ofReal_coe_nnreal] at h'
      exact (ENNReal.ofReal_le_ofReal_iff u.coe_nonneg).1 h'
    exact ⟨C, (mem_hitEv_iff hS hδ).2 ⟨s0, hs0, m, ⟨hmσ, hmu⟩, hmG, hmK⟩⟩

end LWFar
end Thm18Asm
end QuantumZipper
