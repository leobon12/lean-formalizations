import QuantumZipper.Proofs.Thm18.G2DisintRB
import QuantumZipper.Proofs.Thm18.G2DisintXC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration, `R` side: pointwise consequences of the identifications

For one sample with `ν_h = e^{αg} ν₀`, `ν₀ = e^{−αg} ν_h`, `ν_h[−δ, 0] < ∞`, `ν_h(J) > 0`:
margin roots are good, the root kernel is `ν_h|_M`, the length is `g2rf (h₀, x) α`, and the cut
length is the length minus the `α`-free gap `g2rgap`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open Classical in
/-- The `α`-free gap `ν₀[x, x + κ)` (junk `0` off the good set). -/
def g2rgap (γ : ℝ) (i : G3Idx) (m κ : ℝ) (ξ : (AdmIdx → ℝ) × ℝ) : ℝ :=
  if ξ ∈ g2rGood γ i m then
    (g2rκW γ i m ξ.1 (Icc 0 ξ.2)).toReal - (g2rκW γ i m ξ.1 (Icc 0 (ξ.2 - κ))).toReal
  else 0

theorem g2rgap_nonneg (γ : ℝ) (i : G3Idx) (m : ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (ξ : (AdmIdx → ℝ) × ℝ) : 0 ≤ g2rgap γ i m κ ξ := by
  unfold g2rgap
  split_ifs with h
  · have hfin : g2rκW γ i m ξ.1 (Icc 0 ξ.2) ≠ ⊤ := by
      rw [g2rκW_apply_good h, Measure.restrict_apply measurableSet_Icc]
      exact ((measure_mono inter_subset_right).trans_lt h.1).ne
    have hsub : Icc 0 (ξ.2 - κ) ⊆ Icc 0 ξ.2 := fun t ht => ⟨ht.1, by linarith [ht.2]⟩
    have := ENNReal.toReal_mono hfin (measure_mono hsub (μ := g2rκW γ i m ξ.1))
    linarith
  · exact le_rfl

theorem measurable_g2rgap (γ : ℝ) (i : G3Idx) (m κ : ℝ) : Measurable (g2rgap γ i m κ) := by
  classical
  have hk : ∀ c : ℝ, Measurable fun ξ : (AdmIdx → ℝ) × ℝ => g2rκW γ i m ξ.1 (Icc 0 (ξ.2 - c)) := by
    intro c
    have hS : MeasurableSet {q : ((AdmIdx → ℝ) × ℝ) × ℝ | q.2 ∈ Icc 0 (q.1.2 - c)} :=
      (measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd ((measurable_snd.comp measurable_fst).sub_const c))
    have := Kernel.measurable_kernel_prodMk_left (κ := (g2rκW γ i m).comap Prod.fst measurable_fst) hS
    convert this using 2 with ξ
    rw [Kernel.comap_apply]
    rfl
  have h0 : Measurable fun ξ : (AdmIdx → ℝ) × ℝ => g2rκW γ i m ξ.1 (Icc 0 ξ.2) := by
    simpa using hk 0
  exact Measurable.ite (measurableSet_g2rGood γ i m) (h0.ennreal_toReal.sub (hk _).ennreal_toReal)
    measurable_const

/-- **Pointwise consequences for one good sample.** -/
theorem g2r_pw {γ : ℝ} (hγ : 0 < γ) (i : G3Idx) {m : ℝ} (hm : 0 < m) {ν : Measure ℝ} {a : ℝ}
    (y : AdmIdx → ℝ)
    (hA : ν = (g2ν₀ γ (g2rφ i m) y).withDensity (g2rD γ i m a))
    (hB : g2ν₀ γ (g2rφ i m) y = ν.withDensity (g2rD γ i m (-a)))
    (hW : ν (Icc 0 (g2rW i m)) < ⊤) (hJ : 0 < ν (g2rJ i m)) :
    (∀ x ∈ g2rM i m, (y, x) ∈ g2rGood γ i m) ∧
    g2FinKer (g2ν₀ γ (g2rφ i m)) (measurable_g2ν₀ _ _) (measurableSet_g2rM i m) y =
      ν.restrict (g2rM i m) ∧
    (∀ x ∈ g2rM i m, g2rf γ i m (y, x) a = (ν (Icc 0 x)).toReal) ∧
    (∀ κ : ℝ, 0 ≤ κ → κ < g2rR i m → ∀ x ∈ g2rM i m,
      (ν (Icc 0 (x - κ))).toReal = g2rf γ i m (y, x) a - g2rgap γ i m κ (y, x)) := by
  set ν₀ := g2ν₀ γ (g2rφ i m) y with hν₀
  have hWm : MeasurableSet (Icc 0 (g2rW i m) : Set ℝ) := measurableSet_Icc
  have hν₀W : ν₀ (Icc 0 (g2rW i m)) < ⊤ := by
    rw [hB, withDensity_apply _ hWm]
    calc ∫⁻ t in Icc 0 (g2rW i m), g2rD γ i m (-a) t ∂ν
        ≤ ∫⁻ _ in Icc 0 (g2rW i m), ENNReal.ofReal (Real.exp (γ / 2 * |-a|)) ∂ν :=
          lintegral_mono fun t => g2rD_le hγ i m (-a) t
      _ < ⊤ := by
          rw [setLIntegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW
  have hν₀J : 0 < ν₀ (g2rJ i m) :=
    pos_of_withDensity_ge' measurableSet_Ioo hB (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
      (fun t _ => g2rD_ge hγ i m (-a) t) hJ
  have hgood : ∀ x ∈ g2rM i m, (y, x) ∈ g2rGood γ i m := fun x hx =>
    ⟨hν₀W, hν₀J, g2rM_le_W i hm hx, by linarith [g2rM_right i hm hx, g2rR_pos i hm]⟩
  have hsubW : ∀ x ∈ g2rM i m, Icc 0 x ⊆ Icc 0 (g2rW i m) := fun x hx =>
    Icc_subset_Icc_right (g2rM_le_W i hm hx)
  have hleft : ∀ x ∈ g2rM i m, ∀ κ, κ < g2rR i m → ∀ t ∈ Ioc (x - κ) x,
      g2rP i m + g2rR i m ≤ t := fun x hx κ hκ t ht => by
    linarith [ht.1, g2rM_right i hm hx]
  have hlen : ∀ x ∈ g2rM i m, g2rf γ i m (y, x) a = (ν (Icc 0 x)).toReal := by
    intro x hx
    have hg := hgood x hx
    simp only [g2rf, if_pos hg]
    rw [g2rF_eq_good hg, Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.2 (hsubW x hx)]
    have hfin : IsFiniteMeasure (ν₀.restrict (Icc 0 x)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono (hsubW x hx)).trans_lt hν₀W⟩
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t => (Real.exp_pos _).le)
      ((Real.measurable_exp.comp ((measurable_g2rg γ i m).const_mul a)).aestronglyMeasurable),
      hA, withDensity_apply _ measurableSet_Icc]
    congr 1
    refine lintegral_congr fun t => ?_
    simp only [g2rD, g2rg]
    ring_nf
  refine ⟨hgood, ?_, ?_, ?_⟩
  · rw [g2FinKer_apply, ← hν₀, if_pos ((measure_mono (fun t (ht : t ∈ g2rM i m) =>
      (⟨ht.2.1, g2rM_le_W i hm ht⟩ : t ∈ Icc 0 (g2rW i m)))).trans_lt hν₀W), hB,
      restrict_withDensity (measurableSet_g2rM i m)]
    conv_rhs => rw [← withDensity_one (μ := ν.restrict (g2rM i m))]
    refine withDensity_congr_ae (ae_restrict_of_forall_mem (measurableSet_g2rM i m) fun t ht => ?_)
    exact g2rD_right i hm _ (by linarith [g2rM_right i hm ht, g2rR_pos i hm])
  · exact hlen
  · intro κ hκ0 hκ x hx
    have hg := hgood x hx
    have hx0 : 0 ≤ x - κ := by
      linarith [g2rM_right i hm hx, g2rR_pos i hm, g2r_bump_pos i hm]
    have hsplit : Icc 0 x = Icc 0 (x - κ) ∪ Ioc (x - κ) x := by
      ext t; simp only [mem_Icc, mem_Ioc, mem_union]
      constructor
      · rintro ⟨h1, h2⟩; by_cases h : t ≤ x - κ
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr ⟨not_le.1 h, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, by linarith⟩
        · exact ⟨by linarith, h2⟩
    have hdisj : Disjoint (Icc 0 (x - κ)) (Ioc (x - κ) x) :=
      disjoint_left.2 fun t h1 h2 => absurd h1.2 (not_le.2 h2.1)
    have hIoc : Ioc (x - κ) x ⊆ Icc 0 x := fun t ht => ⟨by linarith [ht.1], ht.2⟩
    have hIcc : Icc 0 (x - κ) ⊆ Icc 0 x := Icc_subset_Icc_right (by linarith)
    have hνfin : ∀ S ⊆ Icc 0 x, ν S ≠ ⊤ := fun S hS =>
      ((measure_mono (hS.trans (hsubW x hx))).trans_lt hW).ne
    have hν₀fin : ∀ S ⊆ Icc 0 x, ν₀ S ≠ ⊤ := fun S hS =>
      ((measure_mono (hS.trans (hsubW x hx))).trans_lt hν₀W).ne
    have e1 : ν (Icc 0 x) = ν (Icc 0 (x - κ)) + ν (Ioc (x - κ) x) := by
      rw [hsplit, measure_union hdisj measurableSet_Ioc]
    have e2 : ν₀ (Icc 0 x) = ν₀ (Icc 0 (x - κ)) + ν₀ (Ioc (x - κ) x) := by
      rw [hsplit, measure_union hdisj measurableSet_Ioc]
    have e3 : ν (Ioc (x - κ) x) = ν₀ (Ioc (x - κ) x) := by
      rw [hA]
      exact g2x_withDensity_eq_on measurableSet_Ioc fun t ht =>
        g2rD_right i hm a (hleft x hx κ hκ t ht)
    have hκW : ∀ c : ℝ, c ≤ x → g2rκW γ i m (y, x).1 (Icc 0 c) = ν₀ (Icc 0 c) := fun c hc => by
      rw [g2rκW_apply_good hg, Measure.restrict_apply measurableSet_Icc,
        inter_eq_left.2 (Icc_subset_Icc_right (hc.trans (g2rM_le_W i hm hx)))]
    rw [hlen x hx]
    simp only [g2rgap, if_pos hg]
    rw [hκW x le_rfl, hκW (x - κ) (by linarith), e1, e2, e3,
      ENNReal.toReal_add (hνfin _ hIcc) (hν₀fin _ hIoc),
      ENNReal.toReal_add (hν₀fin _ hIcc) (hν₀fin _ hIoc)]
    ring

end Thm18Asm
end QuantumZipper
