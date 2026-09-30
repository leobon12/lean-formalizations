import QuantumZipper.Proofs.Thm18.G1Z2MeasMain
import QuantumZipper.Proofs.Thm18.G1ZA1bArea
import QuantumZipper.Proofs.Zipper.ZipLenField

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-B2R (3): regularity package of a pulled-back field plus a constant, and of its translates

Theorem 1.8, G1 zoom, node B2-R. Sheffield, arXiv:1012.4797, proof of Proposition 1.7,
pp. 25–26 (adding a constant, then re-embedding by the unit-area radius).

For a regular sample `x` with the PAIR-LIM clause of `G1.ChoiceRegularCore`, an area limit
that is small near real points and of infinite total mass (the clauses of `G1Z2Good`):

* `g1zB2r_shift_pack`: the same package holds for `addConst x C` (the PAIR-LIM limits are shifted
  by `C` because the folded-circle values of a regular sample shift by `C`; the area limit is
  multiplied by `e^{γC}`, `GoodSample.hasAreaLimit_add_ofFun`; smallness near real points passes
  by continuity of the finite measure from above).
* `g1zB2r_tpack`: consequently every real translate of such a field is regular, has an area limit,
  a positive scale parameter and scale-consistent test pairings (`g1z2_scaleConsistent_translate`).

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization

/-- The PAIR-LIM clause of `G1.ChoiceRegularCore` for a field. -/
def G1ZB2RPair (x : FieldSample) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H, ∀ σ : ℂ → ℝ, (σ = ρ.1 ∨ σ = fun z => -ρ.1 z) →
    (∀ s : ℝ, 0 < s → Integrable (fun u => evalReg x (foldedCircle u s))
      ((G1.tmeas σ).map fun z => (c : ℂ) * z)) ∧
    ∃ L : ℝ, Tendsto (fun s => ∫ u, evalReg x (foldedCircle u s)
      ∂((G1.tmeas σ).map fun z => (c : ℂ) * z)) (𝓝[>] 0) (𝓝 L)

/-- The area package: an area limit that is small near real points, of infinite total mass. -/
def G1ZB2RArea (γ : ℝ) (x : FieldSample) : Prop :=
  ∃ μ : Measure ℂ, HasAreaLimit γ x μ ∧
    (∀ p : ℝ, ∃ a : ℝ, 0 < a ∧ μ (Metric.ball (p : ℂ) a ∩ H) < 1) ∧ μ H = ⊤

/-- Smallness near a real point improves to any positive threshold. -/
theorem g1zB2r_small {μ : Measure ℂ} {p : ℝ}
    (h : ∃ a : ℝ, 0 < a ∧ μ (Metric.ball (p : ℂ) a ∩ H) < 1) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ μ (Metric.ball (p : ℂ) a ∩ H) < ε := by
  obtain ⟨a₀, ha₀, h₀⟩ := h
  set s : ℕ → Set ℂ := fun n => Metric.ball (p : ℂ) (a₀ / ((n : ℝ) + 1)) ∩ H with hs
  have hsm : ∀ n, NullMeasurableSet (s n) μ := fun n =>
    (Metric.isOpen_ball.inter isOpen_H).measurableSet.nullMeasurableSet
  have hanti : Antitone s := fun m n hmn => by
    refine inter_subset_inter_left _ (Metric.ball_subset_ball ?_)
    have : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
    exact div_le_div_of_nonneg_left ha₀.le (by positivity) this
  have hfin : ∃ n, μ (s n) ≠ ⊤ := ⟨0, by
    have : s 0 = Metric.ball (p : ℂ) a₀ ∩ H := by simp [hs]
    rw [this]; exact (h₀.trans ENNReal.one_lt_top).ne⟩
  have hiInter : (⋂ n, s n) = ∅ := by
    ext z
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    by_contra hall
    push_neg at hall
    have hzH : z ∈ H := (hall 0).2
    have hz : z = (p : ℂ) := by
      by_contra hne
      have hd : 0 < dist z (p : ℂ) := dist_pos.2 hne
      obtain ⟨n, hn⟩ := exists_nat_gt (a₀ / dist z (p : ℂ))
      have h1 : a₀ / ((n : ℝ) + 1) < dist z (p : ℂ) := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hd] at hn
        nlinarith
      have := (hall n).1
      rw [Metric.mem_ball] at this
      linarith
    rw [hz] at hzH
    exact absurd hzH (by simp [H])
  have ht := tendsto_measure_iInter_atTop (μ := μ) hsm hanti hfin
  rw [hiInter, measure_empty] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨a₀ / ((n : ℝ) + 1), by positivity, hn⟩

/-- **The package passes to `addConst x C`.** -/
theorem g1zB2r_shift_pack {γ : ℝ} (C : ℝ) {x : FieldSample} (hx : IsRegularSample x)
    (hp : G1ZB2RPair x) (ha : G1ZB2RArea γ x) :
    IsRegularSample (addConst x C) ∧ G1ZB2RPair (addConst x C) ∧ G1ZB2RArea γ (addConst x C) := by
  refine ⟨hx.addConst' C, ?_, ?_⟩
  · intro c hc ρ σ hσ
    obtain ⟨hint, L, hL⟩ := hp c hc ρ σ hσ
    have hσ1 : Continuous σ := by
      rcases hσ with rfl | rfl
      · exact ρ.2.1.continuous
      · exact ρ.2.1.continuous.neg
    have hσ2 : HasCompactSupport σ := by
      rcases hσ with rfl | rfl
      · exact ρ.2.2.1
      · exact ρ.2.2.1.neg
    have := G1.isFiniteMeasure_tmeas hσ1 hσ2
    have e : ∀ s : ℝ, 0 < s → (fun u => evalReg (addConst x C) (foldedCircle u s)) =
        fun u => evalReg x (foldedCircle u s) + C := fun s hs => by
      funext u
      exact B3d.ZipLen.evalReg_addConst_fc_of_regular hx C u hs
    refine ⟨fun s hs => ?_, L + C * (((G1.tmeas σ).map fun z => (c : ℂ) * z).real univ), ?_⟩
    · rw [e s hs]; exact (hint s hs).add (integrable_const C)
    · have h2 : Tendsto (fun s => ∫ u, evalReg (addConst x C) (foldedCircle u s)
          ∂((G1.tmeas σ).map fun z => (c : ℂ) * z)) (𝓝[>] 0)
          (𝓝 (L + C * (((G1.tmeas σ).map fun z => (c : ℂ) * z).real univ))) := by
        refine (hL.add_const (C * (((G1.tmeas σ).map fun z => (c : ℂ) * z).real univ))).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
        rw [e s hs, integral_add (hint s hs) (integrable_const C)]
        simp [integral_const, mul_comm]
      exact h2
  · obtain ⟨μ, hμ, hsmall, htop⟩ := ha
    have hc0 : ENNReal.ofReal (Real.exp (γ * C)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    have hA := GoodSample.hasAreaLimit_add_ofFun (γ := γ) hx hμ (φ := fun _ => C)
      continuousOn_const
    rw [← GoodSample.addConst_eq_add_ofFun, withDensity_const] at hA
    refine ⟨_, hA, fun p => ?_, ?_⟩
    · obtain ⟨a, ha, h⟩ := g1zB2r_small (hsmall p) (ε := (ENNReal.ofReal (Real.exp (γ * C)))⁻¹)
        (ENNReal.inv_pos.2 ENNReal.ofReal_ne_top)
      refine ⟨a, ha, ?_⟩
      rw [Measure.smul_apply, smul_eq_mul]
      calc ENNReal.ofReal (Real.exp (γ * C)) * μ (Metric.ball (p : ℂ) a ∩ H)
          < ENNReal.ofReal (Real.exp (γ * C)) * (ENNReal.ofReal (Real.exp (γ * C)))⁻¹ :=
            by
              have := (ENNReal.mul_lt_mul_left hc0 ENNReal.ofReal_ne_top) h
              simpa [mul_comm] using this
        _ = 1 := ENNReal.mul_inv_cancel hc0 ENNReal.ofReal_ne_top
    · rw [Measure.smul_apply, smul_eq_mul, htop, ENNReal.mul_top hc0]

/-- **Translates of a packaged field**: regular, an area limit, positive scale parameter,
scale-consistent test pairings. -/
theorem g1zB2r_tpack {γ : ℝ} {y : FieldSample} (hy : IsRegularSample y) (hp : G1ZB2RPair y)
    (ha : G1ZB2RArea γ y) (p : ℝ) :
    IsRegularSample (translate y (p : ℂ)) ∧ (∃ μ, HasAreaLimit γ (translate y (p : ℂ)) μ) ∧
      0 < scaleParam γ (translate y (p : ℂ)) ∧
      ∀ b : ℝ, 0 < b → ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H, ∀ σ : ℂ → ℝ,
        (σ = ρ.1 ∨ σ = fun z => -ρ.1 z) →
        G1.ScaleConsistentAt (translate y (p : ℂ)) (Qc γ) b
          ((G1.tmeas σ).map fun z => (c : ℂ) * z) := by
  obtain ⟨F, hF⟩ := hy
  obtain ⟨μ, hμ, hsmall, htop⟩ := ha
  have hyF := hF.translate' p
  have hμy := GoodTransforms.hasAreaLimit_translate ⟨F, hF⟩ hμ p
  obtain ⟨hs1, hs2⟩ := g1z2_translate_mass p (hsmall p) htop
  exact ⟨⟨_, hyF⟩, ⟨_, hμy⟩, g1z2_scaleParam_pos ⟨_, hyF⟩ hμy hs1 hs2,
    fun b hb c hc ρ σ hσ => g1z2_scaleConsistent_translate hF hp p hb hc ρ σ hσ⟩

end Thm18Asm
end QuantumZipper
