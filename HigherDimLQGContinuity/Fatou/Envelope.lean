import HigherDimLQGContinuity.Fatou.Basic

/-!
# A measurable real envelope from extended liminf

The cutoff envelopes have a real value at each scale, but their liminf can be infinite.
The extended liminf and Fatou's lemma produce a finite real envelope almost surely.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HigherDimLQGContinuity

/-- A uniform positive moment bound for measurable envelopes passes to the extended liminf.
On its finite event, the liminf is represented by a measurable real envelope at least one. -/
theorem fatou_real_envelope {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {p B : ℝ} (hp : 0 < p) (Hk : ℕ → Ω → ℝ)
    (hm : ∀ k, Measurable (Hk k)) (h1 : ∀ k ω, 1 ≤ Hk k ω)
    (hbound : ∀ k, ∫⁻ ω, ENNReal.ofReal (Hk k ω ^ p) ∂P ≤ ENNReal.ofReal B) :
    ∃ H : Ω → ℝ, Measurable H ∧ (∀ ω, 1 ≤ H ω) ∧
      (∫⁻ ω, ENNReal.ofReal (H ω ^ p) ∂P ≤ ENNReal.ofReal B) ∧
      ∀ᵐ ω ∂P, ENNReal.ofReal (H ω) =
        liminf (fun k => ENNReal.ofReal (Hk k ω)) atTop := by
  let L : Ω → ℝ≥0∞ := fun ω => liminf (fun k => ENNReal.ofReal (Hk k ω)) atTop
  have hLm : Measurable L := Measurable.liminf fun k => (hm k).ennreal_ofReal
  have hL1 (ω : Ω) : 1 ≤ L ω := by
    apply Filter.le_liminf_of_le (hf := by isBoundedDefault)
    exact Eventually.of_forall fun k => by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (h1 k ω)
  have hpowlim (ω : Ω) : (L ω) ^ p =
      liminf (fun k => ENNReal.ofReal (Hk k ω) ^ p) atTop := by
    exact (ENNReal.monotone_rpow_of_nonneg hp.le).map_liminf_of_continuousAt
      (fun k => ENNReal.ofReal (Hk k ω)) ENNReal.continuous_rpow_const.continuousAt
  have hboundL : ∫⁻ ω, (L ω) ^ p ∂P ≤ ENNReal.ofReal B := by
    calc
      ∫⁻ ω, (L ω) ^ p ∂P =
          ∫⁻ ω, liminf (fun k => ENNReal.ofReal (Hk k ω) ^ p) atTop ∂P := by
            congr 1
            funext ω
            exact hpowlim ω
      _ ≤ liminf (fun k => ∫⁻ ω, ENNReal.ofReal (Hk k ω) ^ p ∂P) atTop :=
        lintegral_liminf_le' fun k => ((hm k).ennreal_ofReal).pow_const p |>.aemeasurable
      _ ≤ ENNReal.ofReal B := by
        apply liminf_le_of_frequently_le'
        apply Frequently.of_forall
        intro k
        rw [lintegral_congr (fun ω => ENNReal.ofReal_rpow_of_nonneg
          (by linarith [h1 k ω]) hp.le)]
        exact hbound k
  let H : Ω → ℝ := fun ω => if L ω = ⊤ then 1 else (L ω).toReal
  have hHm : Measurable H := by
    apply Measurable.ite
    · exact measurableSet_eq_fun hLm measurable_const
    · exact measurable_const
    · exact hLm.ennreal_toReal
  have hH1 (ω : Ω) : 1 ≤ H ω := by
    by_cases htop : L ω = ⊤
    · simp [H, htop]
    · have hle := (ENNReal.toReal_le_toReal ENNReal.one_ne_top htop).2 (hL1 ω)
      simpa [H, htop] using hle
  have hHp (ω : Ω) : ENNReal.ofReal (H ω ^ p) ≤ (L ω) ^ p := by
    by_cases htop : L ω = ⊤
    · simpa only [H, htop, ite_true, Real.one_rpow, ENNReal.ofReal_one] using
        ENNReal.one_le_rpow (hL1 ω) hp
    · rw [show H ω = (L ω).toReal by simp [H, htop],
        ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le,
        ENNReal.ofReal_toReal htop]
  refine ⟨H, hHm, hH1, (lintegral_mono hHp).trans hboundL, ?_⟩
  have hfin : ∀ᵐ ω ∂P, (L ω) ^ p < ⊤ := ae_lt_top (hLm.pow_const p)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hboundL)
  filter_upwards [hfin] with ω hω
  have hnot : L ω ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.top_rpow_of_pos hp] at hω
    exact (lt_irrefl ⊤ hω)
  change ENNReal.ofReal (H ω) = L ω
  rw [show H ω = (L ω).toReal by simp [H, hnot]]
  exact ENNReal.ofReal_toReal hnot

end HigherDimLQGContinuity
