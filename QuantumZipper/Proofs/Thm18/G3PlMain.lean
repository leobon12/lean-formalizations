import QuantumZipper.Proofs.Thm18.G3PlCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b): the plain wedge scheme from the honest comparison

`g3TWedgePlainStmt_of_honest : G3PlHonestStmt → G3TWedgePlainStmt`. The weight is
`w = 1{ℓ ≤ U} · Z/U` (D85). The scheme-`C` Palm integrals are compared with the honest
Palm-window integral up to the exceptional set of `G3PlCore.lean`, whose mass is made `≤ ε U`
by choosing `U` small (a.s. positivity of `ν_C` on intervals, Sheffield §5.1 p. 61) and then the
margin `m` small (no atom of `ν_C` at `0`). Own bookkeeping (AGENT_GUIDE cost rule); Sheffield,
arXiv:1012.4797, proof of Theorem 1.8, p. 71.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- **The exceptional-set comparison.** -/
theorem g3pl_core {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {U m : ℝ} (hU : 0 < U)
    (hm0 : 0 < m) (hmδ : m ≤ i.δ / 4) (hm16 : m ≤ 1 / 16) (hηm : i.η ≤ m) (s t : Set LawD) :
    let A := g3pUf γ (g3wProf γ) i ⁻¹' s ∩ g3pVf γ (g3wProf γ) i ⁻¹' t ∩
      g3pMarg γ (g3wProf γ) i m
    let K := ∫⁻ ω, volume ({ℓ | (ω, ℓ) ∈ A ∩ g3plWin U} ∩
      Ioc 0 (g3pMass γ (g3wProf γ) i ω).toReal) ∂gffBase.P
    let Km := ∫⁻ ω, volume ({ℓ | (ω, ℓ) ∈ g3pMarg γ (g3wProf γ) i m ∩ g3plWin U} ∩
      Ioc 0 (g3pMass γ (g3wProf γ) i ω).toReal) ∂gffBase.P
    let Bd := ∫⁻ ω, g3plBd i.δ U m (g3plV γ ω) ∂gffBase.P
    K ≤ g3plHon γ i.δ U i.C s t + Bd ∧ g3plHon γ i.δ U i.C s t ≤ K + Bd ∧
      ENNReal.ofReal U ≤ Km + Bd ∧ Km ≤ ENNReal.ofReal U := by
  intro A K Km Bd
  have hBm : AEMeasurable (fun ω => g3plBd i.δ U m (g3plV γ ω)) gffBase.P :=
    (measurable_g3plBd _ _ _).comp_aemeasurable (aemeasurable_g3plV hγ hγ2)
  -- the fine alternative, pointwise
  have fine : ∀ᵐ ω ∂gffBase.P, ∀ ℓ, ℓ ∈ Ioc 0 U → ℓ ∉ g3plN i.δ U m (g3plV γ ω) →
      ENNReal.ofReal ℓ ≤ g3plV γ ω (Icc (-i.δ) 0) ∧ ℓ ≤ (g3pMass γ (g3wProf γ) i ω).toReal ∧
      g3pX γ (g3wProf γ) i (ω, ℓ) = lenLeft (g3plV γ ω) ℓ ∧
      g3pR γ (g3wProf γ) i (ω, ℓ) = lenRight (g3plV γ ω) ℓ ∧
      (ω, ℓ) ∈ g3pMarg γ (g3wProf γ) i m := by
    filter_upwards [ae_g3pFid_sets hγ hγ2] with ω hF ℓ hℓ hN
    have hN' : ¬(g3plBadE i.δ U (g3plV γ ω) = 1 ∨
        ENNReal.ofReal ℓ ≤ g3plV γ ω (Icc (-(3 * m)) 0) ∨
        ENNReal.ofReal ℓ ≤ g3plV γ ω (Icc 0 (3 * m))) := fun h => hN ⟨hℓ, h⟩
    push Not at hN'
    exact g3pl_fine i hm0 hmδ hm16 hηm (hF i).1 (hF i).2 hN'.1 hℓ hN'.2.1 hN'.2.2
  have hK : K ≤ g3plHon γ i.δ U i.C s t + Bd := by
    unfold g3plHon
    rw [← lintegral_add_right' _ hBm]
    refine lintegral_mono_ae (fine.mono fun ω hω => ?_)
    refine (measure_mono (t := g3plHonSet γ i.δ U i.C s t ω ∪ g3plN i.δ U m (g3plV γ ω))
      ?_).trans ((measure_union_le _ _).trans (add_le_add le_rfl (volume_g3plN_le _ _ _ _)))
    rintro ℓ ⟨⟨⟨⟨hs, ht⟩, -⟩, hW⟩, hI⟩
    have hℓ : ℓ ∈ Ioc 0 U := ⟨hI.1, hW⟩
    by_cases hN : ℓ ∈ g3plN i.δ U m (g3plV γ ω)
    · exact Or.inr hN
    · obtain ⟨h1, -, hX, hR, -⟩ := hω ℓ hℓ hN
      refine Or.inl ⟨hℓ, h1, ?_, ?_⟩
      · have : zoomLaw γ i.C (g3pField γ (g3wProf γ) ω) (g3pX γ (g3wProf γ) i (ω, ℓ)) ∈ s := hs
        rwa [hX] at this
      · have : zoomLaw γ i.C (g3pField γ (g3wProf γ) ω) (g3pR γ (g3wProf γ) i (ω, ℓ)) ∈ t := ht
        rwa [hR] at this
  have hH : g3plHon γ i.δ U i.C s t ≤ K + Bd := by
    unfold g3plHon
    rw [← lintegral_add_right' _ hBm]
    refine lintegral_mono_ae (fine.mono fun ω hω => ?_)
    refine (measure_mono (t := ({ℓ | (ω, ℓ) ∈ A ∩ g3plWin U} ∩
      Ioc 0 (g3pMass γ (g3wProf γ) i ω).toReal) ∪ g3plN i.δ U m (g3plV γ ω))
      ?_).trans ((measure_union_le _ _).trans (add_le_add le_rfl (volume_g3plN_le _ _ _ _)))
    rintro ℓ ⟨hℓ, -, hs, ht⟩
    by_cases hN : ℓ ∈ g3plN i.δ U m (g3plV γ ω)
    · exact Or.inr hN
    · obtain ⟨-, h2, hX, hR, hM⟩ := hω ℓ hℓ hN
      refine Or.inl ⟨⟨⟨⟨?_, ?_⟩, hM⟩, hℓ.2⟩, hℓ.1, h2⟩
      · show zoomLaw γ i.C (g3pField γ (g3wProf γ) ω) (g3pX γ (g3wProf γ) i (ω, ℓ)) ∈ s
        rw [hX]; exact hs
      · show zoomLaw γ i.C (g3pField γ (g3wProf γ) ω) (g3pR γ (g3wProf γ) i (ω, ℓ)) ∈ t
        rw [hR]; exact ht
  have hM1 : ENNReal.ofReal U ≤ Km + Bd := by
    rw [← lintegral_add_right' _ hBm]
    calc ENNReal.ofReal U = ∫⁻ _ω, ENNReal.ofReal U ∂gffBase.P := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ _ := by
        refine lintegral_mono_ae (fine.mono fun ω hω => ?_)
        calc ENNReal.ofReal U = volume (Ioc 0 U) := by rw [Real.volume_Ioc, sub_zero]
          _ ≤ volume (({ℓ | (ω, ℓ) ∈ g3pMarg γ (g3wProf γ) i m ∩ g3plWin U} ∩
              Ioc 0 (g3pMass γ (g3wProf γ) i ω).toReal) ∪ g3plN i.δ U m (g3plV γ ω)) := by
            refine measure_mono fun ℓ hℓ => ?_
            by_cases hN : ℓ ∈ g3plN i.δ U m (g3plV γ ω)
            · exact Or.inr hN
            · obtain ⟨-, h2, -, -, hM⟩ := hω ℓ hℓ hN
              exact Or.inl ⟨⟨hM, hℓ.2⟩, hℓ.1, h2⟩
          _ ≤ _ := (measure_union_le _ _).trans (add_le_add le_rfl (volume_g3plN_le _ _ _ _))
  have hM2 : Km ≤ ENNReal.ofReal U := by
    calc Km ≤ ∫⁻ _ω, ENNReal.ofReal U ∂gffBase.P := by
          refine lintegral_mono fun ω => ?_
          calc _ ≤ volume (Ioc 0 U) := measure_mono fun ℓ hℓ => ⟨hℓ.2.1, hℓ.1.2⟩
            _ = _ := by rw [Real.volume_Ioc, sub_zero]
      _ = ENNReal.ofReal U := by rw [lintegral_const, measure_univ, mul_one]
  exact ⟨hK, hH, hM1, hM2⟩

/-! ## Choice of the window `U` and of the margin `m` -/

theorem g3plBadE_le_one (δ U : ℝ) (ν : Measure ℝ) : g3plBadE δ U ν ≤ 1 := by
  classical
  unfold g3plBadE; split_ifs <;> simp

theorem g3plBadE_mono {δ U U' : ℝ} (h : U ≤ U') (ν : Measure ℝ) :
    g3plBadE δ U ν ≤ g3plBadE δ U' ν := by
  classical
  have hle := ENNReal.ofReal_le_ofReal h
  unfold g3plBadE
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso; apply h2
    rcases h1 with h1 | h1
    · exact Or.inl (h1.trans_le hle)
    · exact Or.inr (h1.trans_le hle)
  · exact bot_le
  · exact le_rfl

/-- **Choice of `U₀`.** -/
theorem g3pl_exists_U₀ {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ : ℝ} (hδ : 0 < δ) {e : ℝ}
    (he : 0 < e) : ∃ U₀ : ℝ, 0 < U₀ ∧ ∀ U : ℝ, U ≤ U₀ →
      ∫⁻ ω, g3plBadE δ U (g3plV γ ω) ∂gffBase.P ≤ ENNReal.ofReal e := by
  have hV := aemeasurable_g3plV hγ hγ2
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using this
  have hT : Tendsto (fun n : ℕ => ∫⁻ ω, g3plBadE δ (1 / ((n : ℝ) + 1)) (g3plV γ ω) ∂gffBase.P)
      atTop (𝓝 (∫⁻ _ω, (0 : ℝ≥0∞) ∂gffBase.P)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun _ => 1)
      (fun n => (measurable_g3plBadE _ _).comp_aemeasurable hV)
      (fun n => Filter.Eventually.of_forall fun ω => g3plBadE_le_one _ _ _) (by simp) ?_
    filter_upwards [ae_g3plV_Ioo_pos hγ hγ2] with ω hpos
    have p1 : 0 < g3plV γ ω (Icc (-(δ / 2)) 0) :=
      (hpos _ _ (by linarith) (Or.inr le_rfl)).trans_le (measure_mono Ioo_subset_Icc_self)
    have p2 : 0 < g3plV γ ω (Icc 0 (1 / 4)) :=
      (hpos _ _ (by norm_num) (Or.inl le_rfl)).trans_le (measure_mono Ioo_subset_Icc_self)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(tendsto_order.1 ht).2 _ (lt_min p1 p2)] with n hn
    classical
    unfold g3plBadE
    rw [if_neg]
    push Not
    exact ⟨hn.le.trans (min_le_left _ _), hn.le.trans (min_le_right _ _)⟩
  rw [lintegral_zero] at hT
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hT).2 _ (ENNReal.ofReal_pos.2 he)).exists
  refine ⟨1 / ((n : ℝ) + 1), by positivity, fun U hU => ?_⟩
  exact (lintegral_mono fun ω => g3plBadE_mono hU _).trans hn.le

/-- The masses of `[−3c, 0]` and `[0, 3c]` tend to `0` as `c → 0` along `c/(n+1)`. -/
theorem g3pl_tendsto_small (ν : Measure ℝ) (hfin : ∀ a b : ℝ, ν (Icc a b) ≠ ⊤) (h0 : ν {0} = 0)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => ν (Icc (-(3 * (c / ((n : ℝ) + 1)))) 0)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ν (Icc 0 (3 * (c / ((n : ℝ) + 1))))) atTop (𝓝 0) := by
  have hmono : ∀ n n' : ℕ, n ≤ n' → c / ((n' : ℝ) + 1) ≤ c / ((n : ℝ) + 1) := fun n n' h =>
    div_le_div_of_nonneg_left hc.le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)
  have hsmall : ∀ x : ℝ, 0 < x → ∃ n : ℕ, 3 * (c / ((n : ℝ) + 1)) < x := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < x / (3 * c) by positivity)
    refine ⟨n, ?_⟩
    have : 3 * (c / ((n : ℝ) + 1)) = 3 * c * (1 / ((n : ℝ) + 1)) := by ring
    rw [this]
    calc 3 * c * (1 / ((n : ℝ) + 1)) < 3 * c * (x / (3 * c)) :=
          mul_lt_mul_of_pos_left hn (by positivity)
      _ = x := by field_simp
  constructor
  · have h := tendsto_measure_iInter_atTop (μ := ν)
      (s := fun n : ℕ => Icc (-(3 * (c / ((n : ℝ) + 1)))) 0)
      (fun n => measurableSet_Icc.nullMeasurableSet)
      (fun n n' hnn => Icc_subset_Icc_left (by linarith [hmono n n' hnn])) ⟨0, hfin _ _⟩
    have hI : ν (⋂ n : ℕ, Icc (-(3 * (c / ((n : ℝ) + 1)))) 0) = 0 := by
      refine measure_mono_null (fun x hx => ?_) h0
      rw [mem_iInter] at hx
      have hx0 : x ≤ 0 := (hx 0).2
      by_contra hne
      have hneg : x < 0 := lt_of_le_of_ne hx0 hne
      obtain ⟨n, hn⟩ := hsmall (-x) (by linarith)
      linarith [(hx n).1]
    rw [hI] at h; exact h
  · have h := tendsto_measure_iInter_atTop (μ := ν)
      (s := fun n : ℕ => Icc 0 (3 * (c / ((n : ℝ) + 1))))
      (fun n => measurableSet_Icc.nullMeasurableSet)
      (fun n n' hnn => Icc_subset_Icc_right (by linarith [hmono n n' hnn])) ⟨0, hfin _ _⟩
    have hI : ν (⋂ n : ℕ, Icc 0 (3 * (c / ((n : ℝ) + 1)))) = 0 := by
      refine measure_mono_null (fun x hx => ?_) h0
      rw [mem_iInter] at hx
      have hx0 : 0 ≤ x := (hx 0).1
      by_contra hne
      have hpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hne)
      obtain ⟨n, hn⟩ := hsmall x hpos
      linarith [(hx n).2]
    rw [hI] at h; exact h

/-- **Choice of the margin `m`.** -/
theorem g3pl_exists_m {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ : ℝ} (hδ : 0 < δ) {U : ℝ}
    (hU : 0 < U) {e : ℝ} (he : 0 < e) : ∃ m : ℝ, 0 < m ∧ m ≤ δ / 4 ∧ m ≤ 1 / 16 ∧
      ∫⁻ ω, (min (ENNReal.ofReal U) (g3plV γ ω (Icc (-(3 * m)) 0)) +
        min (ENNReal.ofReal U) (g3plV γ ω (Icc 0 (3 * m)))) ∂gffBase.P ≤
        ENNReal.ofReal U * ENNReal.ofReal e := by
  have hV := aemeasurable_g3plV hγ hγ2
  set c : ℝ := min (δ / 4) (1 / 16) with hc
  have hc0 : 0 < c := lt_min (by linarith) (by norm_num)
  have hT : Tendsto (fun n : ℕ => ∫⁻ ω, (min (ENNReal.ofReal U)
      (g3plV γ ω (Icc (-(3 * (c / ((n : ℝ) + 1)))) 0)) + min (ENNReal.ofReal U)
      (g3plV γ ω (Icc 0 (3 * (c / ((n : ℝ) + 1)))))) ∂gffBase.P)
      atTop (𝓝 (∫⁻ _ω, (0 : ℝ≥0∞) ∂gffBase.P)) := by
    refine tendsto_lintegral_of_dominated_convergence'
      (fun _ => ENNReal.ofReal U + ENNReal.ofReal U)
      (fun n => (((measurable_const.min (Measure.measurable_coe measurableSet_Icc)).add
        (measurable_const.min (Measure.measurable_coe measurableSet_Icc))).comp_aemeasurable hV))
      (fun n => Filter.Eventually.of_forall fun ω =>
        add_le_add (min_le_left _ _) (min_le_left _ _)) (by simp) ?_
    filter_upwards [ae_g3pField_good hγ hγ2] with ω hω
    obtain ⟨h1, h2⟩ := g3pl_tendsto_small (g3plV γ ω)
      (fun a b => (qBoundaryMeasure_Icc_lt_top γ _ a b).ne) (hω.2.2.1 0) hc0
    have := (tendsto_const_nhds (x := ENNReal.ofReal U)).min h1 |>.add
      ((tendsto_const_nhds (x := ENNReal.ofReal U)).min h2)
    simpa using this
  rw [lintegral_zero] at hT
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hT).2 _ (ENNReal.mul_pos
    (ENNReal.ofReal_pos.2 hU).ne' (ENNReal.ofReal_pos.2 he).ne')).exists
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hcm : c / ((n : ℝ) + 1) ≤ c := div_le_self hc0.le hn1
  exact ⟨c / ((n : ℝ) + 1), by positivity, hcm.trans (min_le_left _ _),
    hcm.trans (min_le_right _ _), hn.le⟩

end R18
end QuantumZipper
