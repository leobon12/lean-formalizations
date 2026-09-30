import QuantumZipper.Proofs.Thm18.G2DisintXB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration, `x` side: pointwise consequences of the identifications

For one sample with `ν_h = e^{αg} ν₀`, `ν₀ = e^{−αg} ν_h`, `ν_h[−δ, 0] < ∞`, `ν_h(J) > 0`:
margin roots are good, the root kernel is `ν_h|_M`, the length is `g2xf (h₀, x) α`, and the cut
length is the length minus the `α`-free gap `g2xgap`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open Classical in
/-- The `α`-free gap `ν₀[x, x + κ)` (junk `0` off the good set). -/
def g2xgap (γ : ℝ) (i : G3Idx) (m κ : ℝ) (ξ : (AdmIdx → ℝ) × ℝ) : ℝ :=
  if ξ ∈ g2xGood γ i m then
    (g2xκW γ i m ξ.1 (Icc ξ.2 0)).toReal - (g2xκW γ i m ξ.1 (Icc (ξ.2 + κ) 0)).toReal
  else 0

theorem g2xgap_nonneg (γ : ℝ) (i : G3Idx) (m : ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (ξ : (AdmIdx → ℝ) × ℝ) : 0 ≤ g2xgap γ i m κ ξ := by
  unfold g2xgap
  split_ifs with h
  · have hfin : g2xκW γ i m ξ.1 (Icc ξ.2 0) ≠ ⊤ := by
      rw [g2xκW_apply_good h, Measure.restrict_apply measurableSet_Icc]
      exact ((measure_mono inter_subset_right).trans_lt h.1).ne
    have := ENNReal.toReal_mono hfin (measure_mono (Icc_subset_Icc_left (by linarith) :
      Icc (ξ.2 + κ) 0 ⊆ Icc ξ.2 0) (μ := g2xκW γ i m ξ.1))
    linarith
  · exact le_rfl

theorem measurable_g2xgap (γ : ℝ) (i : G3Idx) (m κ : ℝ) : Measurable (g2xgap γ i m κ) := by
  classical
  have hk : ∀ c : ℝ, Measurable fun ξ : (AdmIdx → ℝ) × ℝ => g2xκW γ i m ξ.1 (Icc (ξ.2 + c) 0) := by
    intro c
    have hS : MeasurableSet {q : ((AdmIdx → ℝ) × ℝ) × ℝ | q.2 ∈ Icc (q.1.2 + c) 0} :=
      (measurableSet_le ((measurable_snd.comp measurable_fst).add_const c) measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)
    have := Kernel.measurable_kernel_prodMk_left (κ := (g2xκW γ i m).comap Prod.fst measurable_fst) hS
    convert this using 2 with ξ
    rw [Kernel.comap_apply]
    rfl
  have h0 : Measurable fun ξ : (AdmIdx → ℝ) × ℝ => g2xκW γ i m ξ.1 (Icc ξ.2 0) := by
    simpa using hk 0
  exact Measurable.ite (measurableSet_g2xGood γ i m) (h0.ennreal_toReal.sub (hk _).ennreal_toReal)
    measurable_const

theorem g2x_withDensity_eq_on {ν₀ : Measure ℝ} {D : ℝ → ℝ≥0∞} {S : Set ℝ} (hS : MeasurableSet S)
    (hD : ∀ t ∈ S, D t = 1) : ν₀.withDensity D S = ν₀ S := by
  rw [withDensity_apply _ hS, setLIntegral_congr_fun hS hD, setLIntegral_one]

/-- **Pointwise consequences for one good sample.** -/
theorem g2x_pw {γ : ℝ} (hγ : 0 < γ) (i : G3Idx) {m : ℝ} (hm : 0 < m) {ν : Measure ℝ} {a : ℝ}
    (y : AdmIdx → ℝ)
    (hA : ν = (g2ν₀ γ (g2xφ i m) y).withDensity (g2xD γ i m a))
    (hB : g2ν₀ γ (g2xφ i m) y = ν.withDensity (g2xD γ i m (-a)))
    (hW : ν (Icc (-i.δ) 0) < ⊤) (hJ : 0 < ν (g2xJ i m)) :
    (∀ x ∈ g2xM i m, (y, x) ∈ g2xGood γ i m) ∧
    g2FinKer (g2ν₀ γ (g2xφ i m)) (measurable_g2ν₀ _ _) (measurableSet_g2xM i m) y =
      ν.restrict (g2xM i m) ∧
    (∀ x ∈ g2xM i m, g2xf γ i m (y, x) a = (ν (Icc x 0)).toReal) ∧
    (∀ κ : ℝ, 0 ≤ κ → κ < g2xR i m → ∀ x ∈ g2xM i m,
      (ν (Icc (x + κ) 0)).toReal = g2xf γ i m (y, x) a - g2xgap γ i m κ (y, x)) := by
  set ν₀ := g2ν₀ γ (g2xφ i m) y with hν₀
  have hWm : MeasurableSet (Icc (-i.δ) 0 : Set ℝ) := measurableSet_Icc
  have hν₀W : ν₀ (Icc (-i.δ) 0) < ⊤ := by
    rw [hB, withDensity_apply _ hWm]
    calc ∫⁻ t in Icc (-i.δ) 0, g2xD γ i m (-a) t ∂ν
        ≤ ∫⁻ _ in Icc (-i.δ) 0, ENNReal.ofReal (Real.exp (γ / 2 * |-a|)) ∂ν :=
          lintegral_mono fun t => g2xD_le hγ i m (-a) t
      _ < ⊤ := by
          rw [setLIntegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW
  have hν₀J : 0 < ν₀ (g2xJ i m) :=
    pos_of_withDensity_ge' measurableSet_Ioo hB (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
      (fun t _ => g2xD_ge hγ i m (-a) t) hJ
  have hgood : ∀ x ∈ g2xM i m, (y, x) ∈ g2xGood γ i m := fun x hx =>
    ⟨hν₀W, hν₀J, hx.2.1, by linarith [g2xM_left i hm hx, g2xR_pos i hm]⟩
  have hsubW : ∀ x ∈ g2xM i m, Icc x 0 ⊆ Icc (-i.δ) 0 := fun x hx => Icc_subset_Icc_left hx.2.1
  have hleft : ∀ x ∈ g2xM i m, ∀ κ, κ < g2xR i m → ∀ t ∈ Ico x (x + κ),
      t ≤ g2xP i m - g2xR i m := fun x hx κ hκ t ht => by
    linarith [ht.2, g2xM_left i hm hx]
  have hlen : ∀ x ∈ g2xM i m, g2xf γ i m (y, x) a = (ν (Icc x 0)).toReal := by
    intro x hx
    have hg := hgood x hx
    simp only [g2xf, if_pos hg]
    rw [g2xF_eq_good hg, Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.2 (hsubW x hx)]
    have hfin : IsFiniteMeasure (ν₀.restrict (Icc x 0)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono (hsubW x hx)).trans_lt hν₀W⟩
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t => (Real.exp_pos _).le)
      ((Real.measurable_exp.comp ((measurable_g2xg γ i m).const_mul a)).aestronglyMeasurable),
      hA, withDensity_apply _ measurableSet_Icc]
    congr 1
    refine lintegral_congr fun t => ?_
    simp only [g2xD, g2xg]
    ring_nf
  refine ⟨hgood, ?_, ?_, ?_⟩
  · rw [g2FinKer_apply, ← hν₀, if_pos ((measure_mono (fun t ht => ht.2)).trans_lt hν₀W), hB,
      restrict_withDensity (measurableSet_g2xM i m)]
    conv_rhs => rw [← withDensity_one (μ := ν.restrict (g2xM i m))]
    refine withDensity_congr_ae (ae_restrict_of_forall_mem (measurableSet_g2xM i m) fun t ht => ?_)
    exact g2xD_left i hm _ (by linarith [g2xM_left i hm ht, g2xR_pos i hm])
  · exact hlen
  · intro κ hκ0 hκ x hx
    have hg := hgood x hx
    have hx0 : x + κ ≤ 0 := by linarith [g2xM_left i hm hx, g2xR_pos i hm, g2x_bump_neg i hm]
    have hsplit : Icc x 0 = Ico x (x + κ) ∪ Icc (x + κ) 0 := by
      ext t; simp only [mem_Icc, mem_Ico, mem_union]
      constructor
      · rintro ⟨h1, h2⟩; by_cases h : t < x + κ
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr ⟨not_lt.1 h, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, by linarith⟩
        · exact ⟨by linarith, h2⟩
    have hdisj : Disjoint (Ico x (x + κ)) (Icc (x + κ) 0) :=
      disjoint_left.2 fun t h1 h2 => absurd h2.1 (not_le.2 h1.2)
    have hνfin : ∀ S ⊆ Icc x 0, ν S ≠ ⊤ := fun S hS =>
      ((measure_mono (hS.trans (hsubW x hx))).trans_lt hW).ne
    have hν₀fin : ∀ S ⊆ Icc x 0, ν₀ S ≠ ⊤ := fun S hS =>
      ((measure_mono (hS.trans (hsubW x hx))).trans_lt hν₀W).ne
    have e1 : ν (Icc x 0) = ν (Ico x (x + κ)) + ν (Icc (x + κ) 0) := by
      rw [hsplit, measure_union hdisj measurableSet_Icc]
    have e2 : ν₀ (Icc x 0) = ν₀ (Ico x (x + κ)) + ν₀ (Icc (x + κ) 0) := by
      rw [hsplit, measure_union hdisj measurableSet_Icc]
    have e3 : ν (Ico x (x + κ)) = ν₀ (Ico x (x + κ)) := by
      rw [hA]
      exact g2x_withDensity_eq_on measurableSet_Ico fun t ht =>
        g2xD_left i hm a (hleft x hx κ hκ t ht)
    have hκW : ∀ c : ℝ, x ≤ c → g2xκW γ i m (y, x).1 (Icc c 0) = ν₀ (Icc c 0) := fun c hc => by
      rw [g2xκW_apply_good hg, Measure.restrict_apply measurableSet_Icc,
        inter_eq_left.2 (Icc_subset_Icc_left (hx.2.1.trans hc))]
    have hIco : Ico x (x + κ) ⊆ Icc x 0 := fun t ht => ⟨ht.1, by linarith [ht.2]⟩
    rw [hlen x hx]
    simp only [g2xgap, if_pos hg]
    rw [hκW x le_rfl, hκW (x + κ) (by linarith), e1, e2, e3,
      ENNReal.toReal_add (hν₀fin _ hIco) (hνfin _ (Icc_subset_Icc_left (by linarith))),
      ENNReal.toReal_add (hν₀fin _ hIco) (hν₀fin _ (Icc_subset_Icc_left (by linarith)))]
    ring

end Thm18Asm
end QuantumZipper
