import QuantumZipper.Proofs.Zipper.SWCoreNA2Final
import QuantumZipper.Proofs.Zipper.SWCoreA6Flow
import QuantumZipper.Proofs.Zipper.SWCoreB8FBox

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE3 (5): the area map class of a side map, and the scale family

* `exists_areaClass`: a map holomorphic, injective and with nonvanishing derivative on `ℍ`, mapping
  `ℍ` into `ℍ`, lies in an area class `AreaClass a b c d ρ M m` of every rectangle
  `[a,b] × [c,d] ⊂ ℍ` (compactness).
* `scaleFam`: the family `q ↦ s(q) ψ` with centre `z(q)` and radius factor `α(q)`, the parameters
  `(s, α, Re z, Im z)` clamped to `[1/N, N] × [1,2] × [a,b] × [c,d]`; it satisfies the hypotheses
  `SwcNA2Unif` of the repository's finite-parameter area core (`scaleFam_unif`).

Sheffield–Wang, arXiv:1605.06171, proof of Thm 1.4, through the repository's area cores;
own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology

namespace QuantumZipper
namespace G1Side

open SWCore

/-- **Area class of a map of `ℍ`.** -/
theorem exists_areaClass {ψ : ℂ → ℂ} (hd : DifferentiableOn ℂ ψ H) (hi : InjOn ψ H)
    (hH : MapsTo ψ H H) (h0 : ∀ z ∈ H, deriv ψ z ≠ 0) {a b c d : ℝ} (hc : 0 < c) :
    ∃ ρ M m : ℝ, 0 < ρ ∧ 0 < m ∧ ψ ∈ AreaClass a b c d ρ M m := by
  set K := rectC a b c d with hKdef
  set C := rectC (a - c / 2) (b + c / 2) (c / 2) (d + c / 2) with hCdef
  have hc2 : (0 : ℝ) < c / 2 := by linarith
  have hCH : C ⊆ H := fun z hz => show 0 < z.im from lt_of_lt_of_le hc2 hz.2.1
  have hKH : K ⊆ H := fun z hz => show 0 < z.im from lt_of_lt_of_le hc hz.2.1
  have hthick : thickening (c / 2) K ⊆ C := by
    intro w hw
    obtain ⟨z, hz, hd'⟩ := mem_thickening_iff.1 hw
    have h1 : |w.re - z.re| ≤ dist w z := by
      rw [dist_eq_norm]; simpa using Complex.abs_re_le_norm (w - z)
    have h2 : |w.im - z.im| ≤ dist w z := by
      rw [dist_eq_norm]; simpa using Complex.abs_im_le_norm (w - z)
    obtain ⟨⟨hz1, hz2⟩, ⟨hz3, hz4⟩⟩ := hz
    rw [abs_le] at h1 h2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hCc : IsCompact C := swA6_isCompact_rectC _ _ _ _
  have hψC : ContinuousOn ψ C := (hd.mono hCH).continuousOn
  have hImc : IsCompact (ψ '' C) := hCc.image_of_continuousOn hψC
  obtain ⟨M₀, hM₀⟩ := hImc.isBounded.exists_norm_le
  obtain ⟨δ, hδ, hδF⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ ψ '' C, δ ≤ w.im := by
    rcases (ψ '' C).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨w₀, hw₀, hmin⟩ := hImc.exists_isMinOn hne Complex.continuous_im.continuousOn
      obtain ⟨z₀, hz₀, rfl⟩ := hw₀
      exact ⟨(ψ z₀).im, hH (hCH hz₀), fun w hw => hmin hw⟩
  -- the derivative is continuous and nonvanishing on `K`
  have hHo : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  have hdc : ContinuousOn (fun z => ‖deriv ψ z‖) K :=
    (((hd.analyticOnNhd hHo).deriv).continuousOn.mono hKH).norm
  obtain ⟨m₀, hm₀, hmK⟩ : ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ z ∈ K, m₀ ≤ ‖deriv ψ z‖ := by
    rcases K.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨z₀, hz₀, hmin⟩ := (swA6_isCompact_rectC _ _ _ _).exists_isMinOn hne hdc
      exact ⟨_, norm_pos_iff.2 (h0 z₀ (hKH hz₀)), fun z hz => hmin hz⟩
  refine ⟨min (c / 2) δ, M₀, m₀, lt_min hc2 hδ, hm₀, ?_⟩
  have hthρ : thickening (min (c / 2) δ) K ⊆ C :=
    (thickening_mono (min_le_left _ _) K).trans hthick
  refine ⟨hd.mono (hthρ.trans hCH), hi.mono (hthρ.trans hCH), fun z hz => ?_, hmK⟩
  have hmem : ψ z ∈ ψ '' C := mem_image_of_mem ψ (hthρ hz)
  exact ⟨hM₀ _ hmem, (min_le_right _ _).trans (hδF _ hmem)⟩

/-- The clamped parameters of the scale family. -/
def famS (N : ℕ) (q : Fin 4 → ℝ) : ℝ := swcN2Clamp (1 / (N : ℝ)) N (q 0)
def famA (q : Fin 4 → ℝ) : ℝ := swcN2Clamp 1 2 (q 1)
def famZ (a b c d : ℝ) (q : Fin 4 → ℝ) : ℂ :=
  ⟨swcN2Clamp a b (q 2), swcN2Clamp c d (q 3)⟩

/-- The scale family of a map `ψ`. -/
def famF (ψ : ℂ → ℂ) (N : ℕ) (q : Fin 4 → ℝ) : ℂ → ℂ := fun u => (famS N q : ℂ) * ψ u

theorem famS_mem {N : ℕ} (hN : 1 ≤ N) (q : Fin 4 → ℝ) : famS N q ∈ Icc (1 / (N : ℝ)) N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact swcN2Clamp_mem (by rw [div_le_iff₀ (by linarith)]; nlinarith) _

theorem famS_pos {N : ℕ} (hN : 1 ≤ N) (q : Fin 4 → ℝ) : 0 < famS N q := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact lt_of_lt_of_le (by positivity) (famS_mem hN q).1

/-- **The scale family satisfies the hypotheses of the area core.** -/
theorem scaleFam_unif {ψ : ℂ → ℂ} {a b c d ρ M m : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hc : 0 < c)
    (hρ : 0 < ρ) (hm : 0 < m) (hψ : ψ ∈ AreaClass a b c d ρ M m) {N : ℕ} (hN : 1 ≤ N) :
    SwcNA2Unif (famF ψ N) (famZ a b c d) famA a b c d (ρ / N) (N * M) (m / N)
      (max (|M|) 2) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hthk : thickening (ρ / N) (rectC a b c d) ⊆ thickening ρ (rectC a b c d) :=
    thickening_mono (div_le_self hρ.le hN1) _
  refine ⟨hc, by positivity, by positivity, by positivity, fun q => ?_, fun q => ?_, fun q => ?_,
    fun q => ?_, fun q q' => ?_, fun q q' => ?_, fun q q' w hw => ?_⟩
  · -- the class
    have hs := famS_mem hN q
    have hs0 := famS_pos hN q
    have hsc : ((famS N q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    refine ⟨(differentiableOn_const _).mul (hψ.1.mono hthk), fun u hu v hv huv => ?_,
      fun u hu => ?_, fun u hu => ?_⟩
    · exact hψ.2.1 (hthk hu) (hthk hv) (mul_left_cancel₀ hsc huv)
    · obtain ⟨h1, h2⟩ := hψ.2.2.1 u (hthk hu)
      refine ⟨?_, ?_⟩
      · simp only [famF, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
        exact mul_le_mul hs.2 h1 (norm_nonneg _) hN0.le
      · simp only [famF, Complex.im_ofReal_mul]
        calc ρ / N = (1 / N) * ρ := by ring
          _ ≤ famS N q * (ψ u).im := mul_le_mul hs.1 h2 hρ.le hs0.le
    · have hdψ : DifferentiableAt ℂ ψ u :=
        hψ.1.differentiableAt (isOpen_thickening.mem_nhds (self_subset_thickening hρ _ hu))
      have e : deriv (famF ψ N q) u = (famS N q : ℂ) * deriv ψ u := by
        exact deriv_const_mul _ hdψ
      rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      calc m / N = (1 / N) * m := by ring
        _ ≤ famS N q * ‖deriv ψ u‖ := mul_le_mul hs.1 (hψ.2.2.2 u hu) hm.le hs0.le
  · exact ⟨swcN2Clamp_mem hab _, swcN2Clamp_mem hcd _⟩
  · exact (swcN2Clamp_mem (by norm_num) _).1
  · exact (swcN2Clamp_mem (by norm_num) _).2
  · -- Lipschitz centre
    have h2 := (swcN2Clamp_lip a b (q 2) (q' 2)).trans (abs_coord_le_norm' q q' 2)
    have h3 := (swcN2Clamp_lip c d (q 3) (q' 3)).trans (abs_coord_le_norm' q q' 3)
    calc ‖famZ a b c d q - famZ a b c d q'‖
        ≤ |(famZ a b c d q - famZ a b c d q').re| + |(famZ a b c d q - famZ a b c d q').im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ ‖q - q'‖ + ‖q - q'‖ := add_le_add h2 h3
      _ = 2 * ‖q - q'‖ := by ring
      _ ≤ max (|M|) 2 * ‖q - q'‖ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · have h1 := (swcN2Clamp_lip 1 2 (q 1) (q' 1)).trans (abs_coord_le_norm' q q' 1)
    exact h1.trans (le_mul_of_one_le_left (norm_nonneg _) ((by norm_num : (1 : ℝ) ≤ 2).trans
      (le_max_right _ _)))
  · have h0 := (swcN2Clamp_lip (1 / (N : ℝ)) N (q 0) (q' 0)).trans (abs_coord_le_norm' q q' 0)
    have hMb := (hψ.2.2.1 w (hthk hw)).1
    simp only [famF]
    rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    calc |famS N q - famS N q'| * ‖ψ w‖ ≤ ‖q - q'‖ * |M| :=
          mul_le_mul h0 (hMb.trans (le_abs_self _)) (norm_nonneg _) (norm_nonneg _)
      _ ≤ max (|M|) 2 * ‖q - q'‖ := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

end G1Side
end QuantumZipper
