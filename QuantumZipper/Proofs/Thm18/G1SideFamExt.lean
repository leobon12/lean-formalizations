import QuantumZipper.Proofs.Thm18.G1ZBdryTransp
import QuantumZipper.Proofs.Zipper.SWCoreB8FBox

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (3): the reflected side map is a boundary class map on a side window

From reflection data `SideReflGood left ψ Φ` (Schwarz reflection, Ahlfors, *Complex Analysis*,
Ch. 4 §6.5, used only through `SideReflGood`), on a compact window `[E₁, E₂]` of the side
half-line the holomorphic extension `Ψe` lies in `BdryClass E₁ E₂ ρ₀ M₀ m₀` and stays at distance
`≥ c₁ > 0` from `0` on the `ρ₀`-thickening (`sideExt_class`). Also: multiplying a class map by a
real `c ∈ [1/N, N]` gives a class map (`const_mul_mem_class`), and a window lemma.
Own elementary bookkeeping (compactness, continuity of `Ψe` and `Ψe'`).
-/

noncomputable section

open Set Metric Function
open scoped Topology NNReal

namespace QuantumZipper
namespace G1Side

open SWCore Thm18Asm

theorem zero_notMem_g1SideHalf (left : Bool) : (0 : ℝ) ∉ g1SideHalf left := by
  cases left <;> simp [g1SideHalf]

/-- A margin `e` around `[p,q]` whose doubled window stays in the side half-line. -/
theorem exists_side_margin {left : Bool} {p q : ℝ} (hpq : p < q)
    (hsub : Icc p q ⊆ g1SideHalf left) :
    ∃ e > 0, Icc (min (p - e) (2 * (p - e))) (max (q + e) (2 * (q + e))) ⊆ g1SideHalf left := by
  cases left
  · have hp : 0 < p := by simpa [g1SideHalf] using hsub ⟨le_rfl, hpq.le⟩
    refine ⟨p / 2, by positivity, fun x hx => ?_⟩
    simp only [g1SideHalf, Bool.false_eq_true, ↓reduceIte, mem_Ioi]
    have h1 : 0 < min (p - p / 2) (2 * (p - p / 2)) := lt_min (by linarith) (by linarith)
    linarith [hx.1]
  · have hq : q < 0 := by simpa [g1SideHalf] using hsub ⟨hpq.le, le_rfl⟩
    refine ⟨-q / 2, by linarith, fun x hx => ?_⟩
    simp only [g1SideHalf, ↓reduceIte, mem_Iio]
    have h1 : max (q + -q / 2) (2 * (q + -q / 2)) < 0 := max_lt (by linarith) (by linarith)
    linarith [hx.2]

theorem dil_mem_window {a' b' c t : ℝ} (hc : c ∈ Icc (1 : ℝ) 2) (ht : t ∈ Icc a' b') :
    c * t ∈ Icc (min a' (2 * a')) (max b' (2 * b')) := by
  rcases le_total 0 t with h | h
  · constructor
    · exact (min_le_left _ _).trans (by nlinarith [hc.1, ht.1])
    · exact le_trans (by nlinarith [hc.2, ht.2]) (le_max_right _ _)
  · constructor
    · exact (min_le_right _ _).trans (by nlinarith [hc.2, ht.1])
    · exact le_trans (by nlinarith [hc.1, ht.2]) (le_max_left _ _)

/-- Multiplying a class map by a real constant `c ∈ [1/N, N]`. -/
theorem const_mul_mem_class {a b ρ M m : ℝ} {ψ : ℂ → ℂ} (hψ : ψ ∈ BdryClass a b ρ M m)
    (hρ : 0 < ρ) (hm : 0 ≤ m) {N c : ℝ} (hN : 0 < N) (hc1 : 1 / N ≤ c) (hc2 : c ≤ N) :
    (fun z => (c : ℂ) * ψ z) ∈ BdryClass a b ρ (N * M) (m / N) := by
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc1
  refine ⟨(hψ.1.const_mul _), fun z hz => ?_, fun t ht => ?_, ?_, fun t ht => ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    exact mul_le_mul hc2 (hψ.2.1 z hz) (norm_nonneg _) hN.le
  · simp [Complex.mul_im, hψ.2.2.1 t ht]
  · intro t ht s hs hts
    have h := hψ.2.2.2.1 ht hs hts
    simp only [Complex.re_ofReal_mul]
    exact mul_lt_mul_of_pos_left h hc0
  · have hd : DifferentiableAt ℂ ψ (t : ℂ) := hψ.1.differentiableAt (isOpen_thickening.mem_nhds
      (self_subset_thickening hρ _ (ofReal_mem_segC ht)))
    rw [deriv_const_mul _ hd, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    have h1 := hψ.2.2.2.2 t ht
    calc m / N = 1 / N * m := by ring
      _ ≤ c * ‖deriv ψ t‖ := mul_le_mul hc1 h1 hm hc0.le

/-- **The reflected side map is a class map on a side window**, bounded away from `0`. -/
theorem sideExt_class {left : Bool} {ψ : ℂ → ℂ} {Φ : ℝ ≃o ℝ} (hR : SideReflGood left ψ Φ)
    {E₁ E₂ : ℝ} (hE : E₁ < E₂) (hEs : Icc E₁ E₂ ⊆ g1SideHalf left) :
    ∃ (Ψe : ℂ → ℂ) (ρ₀ M₀ m₀ c₁ : ℝ), 0 < ρ₀ ∧ 0 ≤ M₀ ∧ 0 < m₀ ∧ 0 < c₁ ∧
      Ψe ∈ BdryClass E₁ E₂ ρ₀ M₀ m₀ ∧ (∀ z ∈ thickening ρ₀ (segC E₁ E₂), c₁ ≤ ‖Ψe z‖) ∧
      EqOn ψ Ψe H ∧ ∀ t ∈ Icc E₁ E₂, Ψe t = (Φ t : ℂ) := by
  obtain ⟨h0, hwin⟩ := hR
  obtain ⟨U, Ψe, hU, hEU, hd, hreal, hder, heq⟩ := hwin E₁ E₂ hE hEs
  have hΦ0 : ∀ t ∈ Icc E₁ E₂, Φ t ≠ 0 := fun t ht h => by
    have := Φ.injective (h.trans h0.symm)
    exact zero_notMem_g1SideHalf left (this ▸ hEs ht)
  set V : Set ℂ := U ∩ Ψe ⁻¹' ({0}ᶜ : Set ℂ) with hVdef
  have hV : IsOpen V := hd.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  have hSc : IsCompact (segC E₁ E₂) := isCompact_Icc.image Complex.continuous_ofReal
  have hSV : segC E₁ E₂ ⊆ V := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨hEU t ht, ?_⟩
    simp only [mem_preimage, mem_compl_iff, mem_singleton_iff]
    rw [hreal t ht]
    exact_mod_cast hΦ0 t ht
  obtain ⟨δ, hδ, hδV⟩ := hSc.exists_cthickening_subset_open hV hSV
  have hK1 : IsCompact (cthickening δ (segC E₁ E₂)) := hSc.cthickening
  have hK1U : cthickening δ (segC E₁ E₂) ⊆ U := hδV.trans inter_subset_left
  have hcont : ContinuousOn Ψe (cthickening δ (segC E₁ E₂)) := hd.continuousOn.mono hK1U
  obtain ⟨M₀, hM₀⟩ := hK1.exists_bound_of_continuousOn hcont
  have hE1 : ((E₁ : ℝ) : ℂ) ∈ cthickening δ (segC E₁ E₂) :=
    self_subset_cthickening _ (ofReal_mem_segC ⟨le_rfl, hE.le⟩)
  obtain ⟨x0, hx0, hmin⟩ := hK1.exists_isMinOn ⟨_, hE1⟩
    (continuous_norm.comp_continuousOn hcont)
  have hc1 : 0 < ‖Ψe x0‖ := norm_pos_iff.2 (hδV hx0).2
  have hdd : ContinuousOn (deriv Ψe) U := (hd.deriv hU).continuousOn
  have hdr : ContinuousOn (fun t : ℝ => ‖deriv Ψe (t : ℂ)‖) (Icc E₁ E₂) :=
    continuous_norm.comp_continuousOn
      (hdd.comp Complex.continuous_ofReal.continuousOn fun t ht => hEU t ht)
  obtain ⟨t0, ht0, htmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hE.le) hdr
  have hm0 : 0 < ‖deriv Ψe (t0 : ℂ)‖ := norm_pos_iff.2 (hder t0 ht0)
  refine ⟨Ψe, δ, M₀, ‖deriv Ψe (t0 : ℂ)‖, ‖Ψe x0‖, hδ, (norm_nonneg _).trans (hM₀ _ hE1), hm0,
    hc1, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, heq, hreal⟩
  · exact hd.mono ((thickening_subset_cthickening δ _).trans hK1U)
  · exact fun z hz => hM₀ z (thickening_subset_cthickening _ _ hz)
  · intro t ht; rw [hreal t ht]; simp
  · intro s hs t ht hst
    show (Ψe s).re < (Ψe t).re
    rw [hreal s hs, hreal t ht]
    simpa using Φ.strictMono hst
  · exact fun t ht => htmin ht
  · exact fun z hz => hmin (thickening_subset_cthickening _ _ hz)

end G1Side
end QuantumZipper
