import LQGMetric.Field.StandardBorelRange
import LQGMetric.Field.RandomDistVersion

 


















set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped ENNReal Distributions
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 
abbrev ordSeminorm (k N : ℕ) : Seminorm ℝ 𝓓^{⊤}_{exhaustK ⊤ k}(ℂ, ℝ) :=
  ContDiffMapSupportedIn.supSeminorm ℝ ℂ ℝ ⊤ (exhaustK ⊤ k) N

 

def ordCoord (k N : ℕ) (a : CoordJ → ℝ) : ℝ≥0∞ :=
  ⨆ j : ℕ, ENNReal.ofReal |a (Finsupp.single (k, j) 1)| /
    ENNReal.ofReal (ordSeminorm k N (denseSeqK ⊤ k j))

 
abbrev OrdCoords : Type := ℕ × ℕ → ℝ≥0∞

 
def ordCoords (a : CoordJ → ℝ) : OrdCoords := fun p => ordCoord p.1 p.2 a

theorem measurable_ordCoords : Measurable ordCoords := by
  refine measurable_pi_iff.2 fun p => ?_
  refine Measurable.iSup fun j => ?_
  have hm : Measurable fun a : CoordJ → ℝ => |a (Finsupp.single (p.1, j) 1)| :=
    continuous_abs.measurable.comp (measurable_pi_apply _)
  exact hm.ennreal_ofReal.div_const _

theorem pairJ_single (T : DistC) (j : ℕ × ℕ) :
    pairJ ⊤ T (Finsupp.single j 1) = T (distGen ⊤ j) := by
  simp only [pairJ, comb_single]

theorem iotaK_denseSeqK (k j : ℕ) :
    iotaK ⊤ k (denseSeqK ⊤ k j) = distGen ⊤ (k, j) := rfl

 
theorem ordCoord_anti (k : ℕ) {N N' : ℕ} (hN : N ≤ N') (a : CoordJ → ℝ) :
    ordCoord k N' a ≤ ordCoord k N a := by
  refine iSup_mono fun j => ENNReal.div_le_div_left ?_ _
  exact ENNReal.ofReal_le_ofReal (supSeminorm_mono (exhaustK ⊤ k) hN _)

 
theorem ordCoord_le_of_bound (T : DistC) (k N : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ f : 𝓓^{⊤}_{exhaustK ⊤ k}(ℂ, ℝ),
      |T (iotaK ⊤ k f)| ≤ C * ordSeminorm k N f) :
    ordCoord k N (pairJ ⊤ T) ≤ ENNReal.ofReal C := by
  refine iSup_le fun j => ENNReal.div_le_of_le_mul ?_
  rw [pairJ_single, ← iotaK_denseSeqK, ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal (hb _)

 

theorem exists_ordCoord_lt_top (T : DistC) (k : ℕ) :
    ∃ N, ordCoord k N (pairJ ⊤ T) < ⊤ := by
  let L : 𝓓^{⊤}_{exhaustK ⊤ k}(ℂ, ℝ) →L[ℝ] ℝ :=
    (T : TestOn ⊤ →L[ℝ] ℝ).comp (iotaK ⊤ k)
  let q : Seminorm ℝ 𝓓^{⊤}_{exhaustK ⊤ k}(ℂ, ℝ) :=
    (normSeminorm ℝ ℝ).comp L.toLinearMap
  have hq : Continuous q := continuous_norm.comp L.continuous
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms' ℝ ℂ ℝ ⊤ (exhaustK ⊤ k)) q hq
  refine ⟨s.sup id, lt_of_le_of_lt (ordCoord_le_of_bound T k _ C.2 fun f => ?_)
    ENNReal.ofReal_lt_top⟩
  have h1 : |T (iotaK ⊤ k f)| = q f := by
    simp only [q, L, Seminorm.comp_apply, coe_normSeminorm, Real.norm_eq_abs]
    rfl
  have h2 : q f ≤ C * (s.sup (ContDiffMapSupportedIn.supSeminorm ℝ ℂ ℝ ⊤
      (exhaustK ⊤ k))) f := hC f
  have h3 : (s.sup (ContDiffMapSupportedIn.supSeminorm ℝ ℂ ℝ ⊤ (exhaustK ⊤ k))) f ≤
      ordSeminorm k (s.sup id) f :=
    (Finset.sup_le fun i hi => supSeminorm_mono _ (Finset.le_sup (f := id) hi)) f
  rw [h1]
  exact h2.trans (mul_le_mul_of_nonneg_left h3 C.2)

 
theorem abs_apply_le_of_ordCoord_le (T : DistC) {k N : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h : ordCoord k N (pairJ ⊤ T) ≤ ENNReal.ofReal B)
    (f : 𝓓^{⊤}_{exhaustK ⊤ k}(ℂ, ℝ)) :
    |T (iotaK ⊤ k f)| ≤ B * ordSeminorm k N f := by
  have hp : Continuous (ordSeminorm k N) :=
    (ContDiffMapSupportedIn.withSeminorms' ℝ ℂ ℝ ⊤ (exhaustK ⊤ k)).continuous_seminorm N
  have hT : Continuous fun f : 𝓓^{⊤}_{exhaustK ⊤ k}(ℂ, ℝ) => T (iotaK ⊤ k f) :=
    (map_continuous T).comp (iotaK ⊤ k).continuous
  refine (denseRange_denseSeqK ⊤ k).induction_on f
    (isClosed_le hT.abs (continuous_const.mul hp)) fun j => ?_
  have hj : ENNReal.ofReal |T (iotaK ⊤ k (denseSeqK ⊤ k j))| /
      ENNReal.ofReal (ordSeminorm k N (denseSeqK ⊤ k j)) ≤ ENNReal.ofReal B := by
    refine le_trans ?_ h
    rw [ordCoord]
    have := le_iSup (fun j : ℕ => ENNReal.ofReal |pairJ ⊤ T (Finsupp.single (k, j) 1)| /
      ENNReal.ofReal (ordSeminorm k N (denseSeqK ⊤ k j))) j
    simpa only [pairJ_single, ← iotaK_denseSeqK] using this
  rcases (apply_nonneg (ordSeminorm k N) (denseSeqK ⊤ k j)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    by_contra hne
    have hne' : ENNReal.ofReal |T (iotaK ⊤ k (denseSeqK ⊤ k j))| ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact lt_of_not_ge hne
    rw [← h0, ENNReal.ofReal_zero, ENNReal.div_zero hne'] at hj
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hj)
  · rw [ENNReal.div_le_iff (ENNReal.ofReal_pos.2 hpos).ne' ENNReal.ofReal_ne_top,
      ← ENNReal.ofReal_mul hB] at hj
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB hpos.le)).1 hj

end SupercriticalLQGUniqueness.B2.DG20Lim
