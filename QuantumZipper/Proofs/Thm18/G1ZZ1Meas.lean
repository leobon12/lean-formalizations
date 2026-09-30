import QuantumZipper.Proofs.Thm18.G1ZBdryTransp
import QuantumZipper.Proofs.Thm18.G1ZSplitDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-Z1 (2): the deterministic measure part of the change of variables (Theorem 1.8, G1 zoom)

For an atomless measure `m` (the wedge boundary measure `ν_Y`) and an order isomorphism `Φ` fixing `0`, with `ν = (m|_S).map Φ⁻¹`
(`S = g1SideHalf left`, the side transport of `G1SideTransportStmt`):

* `window_transport`: the integral over the Palm window of `ν` of any function `f` is the integral
  over the Palm window of `m` of `f ∘ Φ⁻¹` (a `MeasurableEquiv` change of variables; own
  elementary proof);
* `g1zBdryPre_eq`: for `SideReflGood left ψ Φ`, `g1zBdryPre x = Φ⁻¹ x` for `x ∈ S`.

Source: the boundary change of variables of Sheffield, arXiv:1012.4797, pp. 69–71.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1ZZ1

theorem measurable_seg_mass (m : Measure ℝ) (left : Bool) :
    Measurable fun x : ℝ => m (g1SideSeg left x) := by
  cases left
  · have h : Monotone fun x : ℝ => m (g1SideSeg false x) := fun a b hab =>
      measure_mono (show Icc 0 a ⊆ Icc 0 b from Icc_subset_Icc_right hab)
    exact h.measurable
  · have h : Antitone fun x : ℝ => m (g1SideSeg true x) := fun a b hab =>
      measure_mono (show Icc b 0 ⊆ Icc a 0 from Icc_subset_Icc_left hab)
    exact h.measurable

theorem measurableSet_win (m : Measure ℝ) (left : Bool) (c : ℝ≥0∞) :
    MeasurableSet {x : ℝ | x ∈ g1SideHalf left ∧ m (g1SideSeg left x) ≤ c} :=
  (measurableSet_g1SideHalf left).inter
    (measurableSet_le (measurable_seg_mass m left) measurable_const)

theorem measurableSet_seg (left : Bool) (b : ℝ) : MeasurableSet (g1SideSeg left b) := by
  cases left <;> simp [g1SideSeg, measurableSet_Icc]

theorem image_seg {Φ : ℝ ≃o ℝ} (h0 : Φ 0 = 0) (left : Bool) (b : ℝ) :
    Φ '' g1SideSeg left b = g1SideSeg left (Φ b) := by
  cases left
  · show Φ '' Icc 0 b = Icc 0 (Φ b)
    rw [OrderIso.image_Icc, h0]
  · show Φ '' Icc b 0 = Icc (Φ b) 0
    rw [OrderIso.image_Icc, h0]

theorem seg_inter_half {m : Measure ℝ} (hatom : m {0} = 0) (left : Bool) (x : ℝ) :
    m (g1SideSeg left x ∩ g1SideHalf left) = m (g1SideSeg left x) := by
  refine le_antisymm (measure_mono inter_subset_left) ?_
  have hsub : g1SideSeg left x ⊆ (g1SideSeg left x ∩ g1SideHalf left) ∪ {0} := by
    intro y hy
    by_cases hyh : y ∈ g1SideHalf left
    · exact Or.inl ⟨hy, hyh⟩
    · refine Or.inr ?_
      cases left
      · have h1 : y ∈ Icc 0 x := hy
        have h2 : ¬ 0 < y := hyh
        exact le_antisymm (by linarith [h1.1]) h1.1
      · have h1 : y ∈ Icc x 0 := hy
        have h2 : ¬ y < 0 := hyh
        exact le_antisymm h1.2 (not_lt.1 h2)
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (by rw [hatom, add_zero]))

theorem mem_half_symm_iff {Φ : ℝ ≃o ℝ} (h0 : Φ 0 = 0) (left : Bool) (x : ℝ) :
    Φ.symm x ∈ g1SideHalf left ↔ x ∈ g1SideHalf left := by
  constructor
  · intro h
    have := mem_image_of_mem Φ h
    rwa [image_g1SideHalf h0, OrderIso.apply_symm_apply] at this
  · intro h
    rw [← image_g1SideHalf h0 left] at h
    obtain ⟨y, hy, rfl⟩ := h
    simpa using hy

/-- **Change of variables for the Palm window.** -/
theorem window_transport {m : Measure ℝ} {Φ : ℝ ≃o ℝ} (h0 : Φ 0 = 0) (hatom : m {0} = 0)
    (left : Bool) (c : ℝ≥0∞) (f : ℝ → ℝ≥0∞) :
    ∫⁻ b in {b | b ∈ g1SideHalf left ∧
        ((m.restrict (g1SideHalf left)).map Φ.symm) (g1SideSeg left b) ≤ c}, f b
        ∂((m.restrict (g1SideHalf left)).map Φ.symm) =
      ∫⁻ x in {x | x ∈ g1SideHalf left ∧ m (g1SideSeg left x) ≤ c}, f (Φ.symm x)
        ∂(m.restrict (g1SideHalf left)) := by
  have hemb : MeasurableEmbedding (Φ.symm : ℝ → ℝ) := Φ.symm.toHomeomorph.measurableEmbedding
  rw [hemb.restrict_map, hemb.lintegral_map]
  have hν : ∀ x : ℝ, ((m.restrict (g1SideHalf left)).map Φ.symm) (g1SideSeg left (Φ.symm x)) =
      m (g1SideSeg left x) := fun x => by
    rw [pull_apply Φ (measurableSet_seg left _), image_seg h0, OrderIso.apply_symm_apply,
      seg_inter_half hatom]
  have hS : (Φ.symm : ℝ → ℝ) ⁻¹' {b | b ∈ g1SideHalf left ∧
      ((m.restrict (g1SideHalf left)).map Φ.symm) (g1SideSeg left b) ≤ c} =
      {x | x ∈ g1SideHalf left ∧ m (g1SideSeg left x) ≤ c} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq]
    rw [hν x, mem_half_symm_iff h0]
  rw [hS]

/-- Boundary values of the side map: `ψ → Φ t` at the real points `t` of the side half-line. -/
theorem tendsto_of_reflGood {left : Bool} {ψ : ℂ → ℂ} {Φ : ℝ ≃o ℝ}
    (h : SideReflGood left ψ Φ) {t : ℝ} (ht : t ∈ g1SideHalf left) :
    Tendsto ψ (𝓝[H] (t : ℂ)) (𝓝 ((Φ t : ℝ) : ℂ)) := by
  obtain ⟨p, q, hpq, hIcc, hKw⟩ := exists_side_window left (isCompact_singleton (x := t))
    (singleton_subset_iff.2 ht)
  obtain ⟨U, Ψ, hU, hJU, hΨ, hΨΦ, -, hEq⟩ := h.2 p q hpq hIcc
  have htI : t ∈ Icc p q := Ioo_subset_Icc_self (hKw (mem_singleton t))
  have hc : ContinuousAt Ψ (t : ℂ) :=
    (hΨ.differentiableAt (hU.mem_nhds (hJU t htI))).continuousAt
  have hT : Tendsto Ψ (𝓝[H] (t : ℂ)) (𝓝 (Ψ t)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  rw [hΨΦ t htI] at hT
  exact hT.congr' (eventually_nhdsWithin_of_forall fun z hz => (hEq hz).symm)

theorem neBot_nhdsWithin_H (t : ℝ) : (𝓝[H] (t : ℂ)).NeBot := by
  refine mem_closure_iff_nhdsWithin_neBot.1 ?_
  rw [show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]
  show 0 ≤ ((t : ℂ)).im
  simp

/-- **Identification of the boundary preimage**: `g1zBdryPre x = Φ⁻¹ x` on the side half-line. -/
theorem g1zBdryPre_eq {left : Bool} {W : ℝ → ℝ} {Φ : ℝ ≃o ℝ}
    (h : SideReflGood left (g1zSideMap left W) Φ) {x : ℝ} (hx : x ∈ g1SideHalf left) :
    g1zBdryPre left W x = Φ.symm x := by
  have hb : Φ.symm x ∈ g1SideHalf left := (mem_half_symm_iff h.1 left x).2 hx
  have hex : ∃ b ∈ g1SideHalf left,
      Tendsto (g1zSideMap left W) (𝓝[H] (b : ℂ)) (𝓝 (x : ℂ)) :=
    ⟨Φ.symm x, hb, by simpa using tendsto_of_reflGood h hb⟩
  rw [g1zBdryPre, dite_cond_eq_true (eq_true hex)]
  obtain ⟨hb', hT'⟩ := hex.choose_spec
  have hT2 := tendsto_of_reflGood h hb'
  have := neBot_nhdsWithin_H hex.choose
  have hu := tendsto_nhds_unique hT' hT2
  have hx' : x = Φ hex.choose := Complex.ofReal_injective hu
  exact (Φ.symm_apply_eq.2 hx').symm

end G1ZZ1
end Thm18Asm
end QuantumZipper
