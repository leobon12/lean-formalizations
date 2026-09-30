import QuantumZipper.Proofs.Thm18.G1Side3RepMain
import QuantumZipper.Proofs.Thm18.G1Side3Tr

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE3 (18): the selected-map area node from the infinite-area node

`G1Z2SideAreaSelStmt` (D88) has three clauses for the pulled-back canonical representative: the area
limit (proved: `G1Side.ae_areaLimit_rep`, with limit `pullMu μ_w (s ψ)`), mass `< 1` near every
real point (proved here: continuity from above of `pullMu`, the side map being bounded near
finite points and `μ_w` finite on bounded sets), and infinite total mass. The last one is the
node `G1Z2SideTopSelStmt`: the unscaled wedge area of the dilated side domain `s D = s ψ(ℍ)` is
infinite (the side of the curve is an infinite-area surface; Sheffield, arXiv:1012.4797, §1.6,
proof of Theorem 1.8: by the scaling argument, `law(μ_h(D)) = law(e^{γC} μ_h(D))`).
`g1Z2SideAreaSelStmt_of_top`; headline `R18.theorem1_8Paper_of_frontier11`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open G1Side

/-- **Node: the side domain has infinite quantum area** (selected maps, representative). -/
def G1Z2SideTopSelStmt : Prop :=
  G1RepSetting fun γ _ _ P B _ _ P' X A => ∀ Ψ, G1PsiSel γ Ψ →
    ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool, ∀ᵐ ω' ∂P',
      qAreaMeasure γ (wU γ X A ω')
        ((fun u => (scaleParam γ (wU γ X A ω') : ℂ) * Ψ left a u) '' H) = ⊤

/-- Mass `< 1` near real points for the pullback of a measure finite on bounded sets. -/
theorem pullMu_small {Φ : ℂ → ℂ} (hc : ContinuousOn Φ H) (hi : InjOn Φ H) {ν : Measure ℂ}
    (hb : ∀ R : ℝ, ∃ M : ℝ, ∀ z ∈ H, ‖z‖ ≤ R → ‖Φ z‖ ≤ M)
    (hν : ∀ R : ℝ, ν (Metric.ball 0 R ∩ H) < ⊤) (hΦH : MapsTo Φ H H) (p : ℝ) :
    ∃ a : ℝ, 0 < a ∧ pullMu ν Φ (Metric.ball (p : ℂ) a ∩ H) < 1 := by
  set S : ℕ → Set ℂ := fun n => Metric.ball (p : ℂ) (1 / (n + 1 : ℝ)) ∩ H with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n => measurableSet_ball.inter isOpen_H'.measurableSet
  have hanti : Antitone S := fun i j hij => by
    have hij' : (i : ℝ) + 1 ≤ j + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
    exact inter_subset_inter_left _ (ball_subset_ball (one_div_le_one_div_of_le (by positivity) hij'))
  have hfin : pullMu ν Φ (S 0) ≠ ⊤ := by
    rw [pullMu_apply hc hi (hSm 0)]
    obtain ⟨M, hM⟩ := hb (|p| + 1)
    refine ne_top_of_le_ne_top (hν (|M| + 1)).ne (measure_mono ?_)
    rintro _ ⟨z, ⟨⟨hz1, hzH⟩, -⟩, rfl⟩
    refine ⟨mem_ball_zero_iff.2 ?_, hΦH hzH⟩
    have hz : ‖z‖ ≤ |p| + 1 := by
      have h1 := mem_ball.1 hz1
      simp only [hS, Nat.cast_zero, zero_add, div_one] at h1
      calc ‖z‖ ≤ ‖(p : ℂ)‖ + dist z p := by
            rw [dist_eq_norm]; exact norm_le_norm_add_norm_sub' _ _
        _ ≤ |p| + 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith
    linarith [hM z hzH hz, le_abs_self M]
  have hinter : ⋂ n, S n = ∅ := by
    ext z
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    by_cases hz : z ∈ H
    · have hd : 0 < dist z p := dist_pos.2 fun h => by
        have h1 : (0 : ℝ) < z.im := hz
        rw [h] at h1; simp at h1
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hd
      exact ⟨n, fun h => absurd (mem_ball.1 h.1) (not_lt.2 hn.le)⟩
    · exact ⟨0, fun h => hz h.2⟩
  have ht := tendsto_measure_iInter_atTop (fun n => (hSm n).nullMeasurableSet) hanti ⟨0, hfin⟩
  rw [hinter, measure_empty] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds zero_lt_one)).exists
  exact ⟨1 / (n + 1 : ℝ), by positivity, hn⟩

/-- **`G1Z2SideAreaSelStmt` from the infinite-area node.** -/
theorem g1Z2SideAreaSelStmt_of_top (hT : G1Z2SideTopSelStmt) : G1Z2SideAreaSelStmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  have hbd : ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool,
      ∀ R : ℝ, ∃ M : ℝ, ∀ z ∈ H, ‖z‖ ≤ R → ‖Ψ left a z‖ ≤ M :=
    G1RC.ae_map_pathOf_of_chord G1RC.g1RegPathChordStmt hγ hγ2 hB hΨ
      (fun ms => ∀ left : Bool, ∀ R : ℝ, ∃ M : ℝ, ∀ z ∈ H, ‖z‖ ≤ R → ‖ms left z‖ ≤ M)
      (fun a hc hs left => (G1RC.psiGood_of_sel hΨ hc hs left).2.2.2.2)
  filter_upwards [ae_areaLimit_rep γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ,
    hT γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ, hbd] with a hlim htop hb left
  filter_upwards [hlim left, htop left, E6.ae_areaAll_wedgeField hγ hγ2 hαQ hX hA hXA,
    WedgeCan4.ae_wedge_canonical_spec_of_inputs
      (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hαQ) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hαQ)
      hγ hγ2 hαQ hX hA hXA] with ω ⟨hfac, hL⟩ ht hall hcan
  obtain ⟨hψm, hψd, hψi, hψH, hψ0, -⟩ := hfac
  set s := scaleParam γ (wU γ X A ω) with hsdef
  have hs : 0 < s := hcan.1
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hΦc : ContinuousOn (fun u => (s : ℂ) * Ψ left a u) H :=
    continuousOn_const.mul hψd.continuousOn
  have hΦi : InjOn (fun u => (s : ℂ) * Ψ left a u) H :=
    fun u hu v hv h => hψi hu hv (mul_left_cancel₀ hsc h)
  have hΦH : MapsTo (fun u => (s : ℂ) * Ψ left a u) H H := fun u hu => by
    show 0 < ((s : ℂ) * Ψ left a u).im
    rw [Complex.im_ofReal_mul]; exact mul_pos hs (hψH hu)
  refine ⟨_, hL, fun p => pullMu_small hΦc hΦi (fun R => ?_) hall.1 hΦH p, ?_⟩
  · obtain ⟨M, hM⟩ := hb left R
    refine ⟨s * M, fun z hz hzR => ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
    exact mul_le_mul_of_nonneg_left (hM z hz hzR) hs.le
  · rw [pullMu_apply hΦc hΦi isOpen_H'.measurableSet, inter_self]
    exact ht

end Thm18Asm

namespace R18

open Thm18Asm

end R18
end QuantumZipper
