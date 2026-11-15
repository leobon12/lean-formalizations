/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedOmit
import InteractingSLE.Spec.ZhanGT4.DualSeedBoundInterval

/-!
# Order of integrated seed coordinates and uniform interval clearance

Packet PROVE-ZHAN-GT4-A22. A real point alive for the Loewner flow stays on
its original side of both seed coordinates. Consequently every point between
two seed coordinates is omitted by the alive real flow. A19's uniform
clearance theorem then applies to the entire interval, with one constant.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

/-- A seed force coordinate in the integrated equation, before its lifetime. -/
structure IsSeedCoordinate (W V : ℝ → ℝ) (T : ℝ) : Prop where
  cont : ContinuousOn V (Icc 0 T)
  zero : V 0 = W 0
  ne : ∀ s ∈ Ioc 0 T, V s ≠ W s
  integrable : ∀ s ∈ Icc 0 T,
    IntervalIntegrable (fun r => 2 / (V r - W r)) volume 0 s
  eq : ∀ s ∈ Icc 0 T, V s = V 0 + ∫ r in (0 : ℝ)..s, 2 / (V r - W r)

namespace IsSeedCoordinate

variable {W V : ℝ → ℝ} {T : ℝ} (h : IsSeedCoordinate W V T)
include h

/-- Restriction of an integrated seed coordinate. -/
theorem restrict {S : ℝ} (hS : S ≤ T) : IsSeedCoordinate W V S where
  cont := h.cont.mono (Icc_subset_Icc_right hS)
  zero := h.zero
  ne := fun s hs => h.ne s ⟨hs.1, hs.2.trans hS⟩
  integrable := fun s hs => h.integrable s ⟨hs.1, hs.2.trans hS⟩
  eq := fun s hs => h.eq s ⟨hs.1, hs.2.trans hS⟩

/-- An alive real flow cannot cross a seed coordinate. The strict order is
the same as that of their initial points. -/
theorem lt_gmap (hW : Continuous W) {y : ℝ} (hy : W 0 < y)
    {u : ℝ → ℂ} (hu : IsForwardSol W (y : ℂ) T u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : V t < (u t).re + W t := by
  let f : ℝ → ℝ := fun s => (u s).re + W s - V s
  have hfc : ContinuousOn f (Icc 0 T) :=
    ((continuous_re.comp_continuousOn hu.1).add hW.continuousOn).sub h.cont
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hf0 : 0 < f 0 := by
    dsimp [f]
    rw [QuantumZipper.FwdHolo.sol_zero hu hT, h.zero]
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith only [hy]
  have hfne : ∀ s ∈ Icc (0 : ℝ) T, f s ≠ 0 := by
    intro s hs
    rcases hs.1.eq_or_lt with h0 | hpos
    · subst s; exact hf0.ne'
    · have hu' := isForwardSol_restrict hu hs.2
      have h' := h.restrict hs.2
      have hne := seed_ne_fwdMap hW hpos h'.cont h'.zero h'.ne h'.integrable h'.eq hy.ne' hu'
      intro he
      apply hne
      apply Complex.ext
      · change (u s).re + W s = V s
        exact sub_eq_zero.1 he
      · simp only [Complex.add_im, Complex.ofReal_im, add_zero]
        exact im_eq_zero_of_isForwardSol_real hW hu hs
  have hft : 0 < f t := by
    by_contra hn
    obtain ⟨s, hs, he⟩ := intermediate_value_Icc' ht.1
      (hfc.mono (Icc_subset_Icc_right ht.2)) ⟨le_of_not_gt hn, hf0.le⟩
    exact hfne s ⟨hs.1, hs.2.trans ht.2⟩ he
  exact sub_pos.1 hft

/-- The reflected order for an alive real point initially left of the seed. -/
theorem gmap_lt (hW : Continuous W) {y : ℝ} (hy : y < W 0)
    {u : ℝ → ℂ} (hu : IsForwardSol W (y : ℂ) T u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : (u t).re + W t < V t := by
  let f : ℝ → ℝ := fun s => V s - ((u s).re + W s)
  have hfc : ContinuousOn f (Icc 0 T) :=
    h.cont.sub ((continuous_re.comp_continuousOn hu.1).add hW.continuousOn)
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hf0 : 0 < f 0 := by
    dsimp [f]
    rw [QuantumZipper.FwdHolo.sol_zero hu hT, h.zero]
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith only [hy]
  have hfne : ∀ s ∈ Icc (0 : ℝ) T, f s ≠ 0 := by
    intro s hs
    rcases hs.1.eq_or_lt with h0 | hpos
    · subst s; exact hf0.ne'
    · have hu' := isForwardSol_restrict hu hs.2
      have h' := h.restrict hs.2
      have hne := seed_ne_fwdMap hW hpos h'.cont h'.zero h'.ne h'.integrable h'.eq hy.ne hu'
      intro he
      apply hne
      apply Complex.ext
      · change (u s).re + W s = V s
        exact (sub_eq_zero.1 he).symm
      · simp only [Complex.add_im, Complex.ofReal_im, add_zero]
        exact im_eq_zero_of_isForwardSol_real hW hu hs
  have hft : 0 < f t := by
    by_contra hn
    obtain ⟨s, hs, he⟩ := intermediate_value_Icc' ht.1
      (hfc.mono (Icc_subset_Icc_right ht.2)) ⟨le_of_not_gt hn, hf0.le⟩
    exact hfne s ⟨hs.1, hs.2.trans ht.2⟩ he
  exact sub_pos.1 hft

end IsSeedCoordinate

/-- The whole interval between two seed coordinates is omitted by the
alive real flow, including at time zero. -/
theorem seed_interval_ne_gmap {W Vlo Vhi : ℝ → ℝ} {T t x y : ℝ}
    (hW : Continuous W) (hlo : IsSeedCoordinate W Vlo T)
    (hhi : IsSeedCoordinate W Vhi T) (ht : t ∈ Icc (0 : ℝ) T)
    (hx : x ∈ uIcc (Vlo t) (Vhi t)) (hy : y ≠ W 0)
    {u : ℝ → ℂ} (hu : IsForwardSol W (y : ℂ) t u) :
    u t + (W t : ℂ) ≠ (x : ℂ) := by
  intro he
  have hre : (u t).re + W t = x := by
    simpa only [Complex.add_re, Complex.ofReal_re] using congrArg Complex.re he
  rcases lt_or_gt_of_ne hy with hyleft | hyright
  · have hleft := (hlo.restrict ht.2).gmap_lt hW hyleft hu ⟨ht.1, le_rfl⟩
    have hright := (hhi.restrict ht.2).gmap_lt hW hyleft hu ⟨ht.1, le_rfl⟩
    exact (not_lt_of_ge hx.1) (hre ▸ lt_min hleft hright)
  · have hleft := (hlo.restrict ht.2).lt_gmap hW hyright hu ⟨ht.1, le_rfl⟩
    have hright := (hhi.restrict ht.2).lt_gmap hW hyright hu ⟨ht.1, le_rfl⟩
    exact (not_lt_of_ge hx.2) (hre ▸ max_lt hleft hright)

/-- One enclosure-dependent clearance works for every point between the two
seed coordinates, uniformly over all admissible paths and times. -/
theorem exists_le_norm_fwdMap_sub_seed_interval_uniform {H₁ S₂ : Set ℂ}
    (hH₁ : IsHPHull H₁) (hS₂ : Bornology.IsBounded S₂) (hS₂H : S₂ ⊆ H)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ a ∈ S₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖) :
    ∃ r > 0, ∀ (W Vlo Vhi : ℝ → ℝ) (T : ℝ), Continuous W →
      ((W 0 : ℝ) : ℂ) ∈ closure H₁ → fwdHull W T ⊆ H₁ →
      IsSeedCoordinate W Vlo T → IsSeedCoordinate W Vhi T →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ S₂, ∀ x ∈ uIcc (Vlo t) (Vhi t),
        r ≤ ‖fwdMap W t a + W t - x‖ := by
  obtain ⟨r, hr, hmain⟩ := exists_le_norm_fwdMap_sub_uniform hH₁ hS₂ hS₂H hδ hsep
  refine ⟨r, hr, ?_⟩
  intro W Vlo Vhi T hW hW0 hKH hlo hhi t ht a ha x hx
  exact hmain W hW hW0 T hKH t ht a ha x fun y u hy hu =>
    seed_interval_ne_gmap hW hlo hhi ht hx hy hu

end InteractingSLE.ZhanGT4
