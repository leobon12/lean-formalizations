import QuantumZipper.Proofs.Thm18.R18AreaNullFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-AREANULL, part 2: independent random Lebesgue-null closed sets carry no quantum area

Let `S ω = closure {T m ω | m ∈ ℕ}` be a random closed set given by a measurable sequence
`T : Ω → ℕ → ℂ`, **independent** of the free field `X`, with `volume (S ω) = 0` a.s. Then a.s.
`μ_X(S ω) = 0` (`ae_qAreaMeasure_free_indep_null`), and the same for the wedge reference field
(`ae_qAreaMeasure_wedgeField_indep_null`).

Source: this is the step "η is a measure zero set independent of h, hence `µ_h(η) = 0`" of
Sheffield (arXiv:1012.4797), §4.1, p. 48, with the mean formula of Duplantier–Sheffield
(arXiv:0808.1560), Prop. 1.2 (2), p. 5 (the mean area has a bounded density on compacts of `ℍ`).
Proof: by independence and Fubini, `E μ_{2^{-k}}(V) ≤ C E|V|` for the random open
`ρ`-neighbourhood `V` of `S` (inside a region `{1/a < Im} ∩ B(0,a)`), `|V| → |S| = 0` as `ρ ↓ 0`
(dominated convergence), Fatou and the portmanteau bound `μ(V) ≤ liminf μ_{2^{-k}}(V)`
(`measure_le_liminf_of_isVagueLimitOn`). The bookkeeping is our own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

/-- The `ρ`-neighbourhood of the points `t m` inside `regionR a`. -/
def nbhdR (a ρ : ℝ) (t : ℕ → ℂ) : Set ℂ := regionR a ∩ ⋃ m, ball (t m) ρ

theorem isOpen_nbhdR (a ρ : ℝ) (t : ℕ → ℂ) : IsOpen (nbhdR a ρ t) :=
  (isOpen_regionR a).inter (isOpen_iUnion fun _ => isOpen_ball)

theorem measurableSet_nbhdR_prod (a ρ : ℝ) :
    MeasurableSet {p : (ℕ → ℂ) × ℂ | p.2 ∈ nbhdR a ρ p.1} := by
  have e : {p : (ℕ → ℂ) × ℂ | p.2 ∈ nbhdR a ρ p.1} =
      {p | p.2 ∈ regionR a} ∩ ⋃ m, {p | dist p.2 (p.1 m) < ρ} := by
    ext p; simp [nbhdR, mem_ball]
  rw [e]
  exact (measurable_snd (isOpen_regionR a).measurableSet).inter (MeasurableSet.iUnion fun m =>
    measurableSet_lt (continuous_snd.dist ((continuous_apply m).comp continuous_fst)).measurable
      measurable_const)

/-- The normalized field `aZ` as a function of the sample. -/
def aZf (R : ℝ) (x : FieldSample) : FieldSample := addConst x (-x (foldedCircle 0 R))

theorem measurable_aZf (R : ℝ) : Measurable (aZf R) := by
  refine measurable_pi_iff.mpr fun μ => ?_
  simp only [aZf, addConst]
  exact (measurable_pi_apply μ).add ((measurable_pi_apply _).neg.mul_const _)

/-- Joint measurability of `(t, x) ↦ μ_{2^{-k}}(aZ x)(V_ρ(t))`. -/
theorem measurable_areaApprox_nbhdR (γ R a ρ : ℝ) (k : ℕ) :
    Measurable fun q : (ℕ → ℂ) × FieldSample => areaApprox γ (aZf R q.2) k (nbhdR a ρ q.1) := by
  set D : FieldSample × ℂ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg p.1 k p.2)) with hD
  have hDm : Measurable D := ENNReal.measurable_ofReal.comp
    ((Real.measurable_exp.comp ((measurable_avgReg k).const_mul γ)).const_mul _)
  have e : ∀ q : (ℕ → ℂ) × FieldSample, areaApprox γ (aZf R q.2) k (nbhdR a ρ q.1) =
      ∫⁻ z, {p : ((ℕ → ℂ) × FieldSample) × ℂ | p.2 ∈ nbhdR a ρ p.1.1}.indicator
        (fun p => D (aZf R p.1.2, p.2)) (q, z) ∂(volume.restrict H) := by
    intro q
    unfold areaApprox
    rw [withDensity_apply _ (isOpen_nbhdR a ρ q.1).measurableSet, ← lintegral_indicator
      (isOpen_nbhdR a ρ q.1).measurableSet]
    rfl
  simp_rw [e]
  refine Measurable.lintegral_prod_right' (Measurable.indicator ?_ ?_)
  · exact hDm.comp (((measurable_aZf R).comp (measurable_snd.comp measurable_fst)).prodMk
      measurable_snd)
  · exact (measurableSet_nbhdR_prod a ρ).preimage
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

theorem nbhdR_antitone (a : ℝ) (t : ℕ → ℂ) :
    Antitone fun n : ℕ => nbhdR a ((n : ℝ) + 1)⁻¹ t := by
  intro i j hij z hz
  refine ⟨hz.1, ?_⟩
  obtain ⟨m, hm⟩ := mem_iUnion.1 hz.2
  refine mem_iUnion.2 ⟨m, ball_subset_ball ?_ hm⟩
  gcongr

theorem iInter_nbhdR_subset (a : ℝ) (t : ℕ → ℂ) :
    (⋂ n : ℕ, nbhdR a ((n : ℝ) + 1)⁻¹ t) ⊆ closure (range t) := by
  intro z hz
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨m, hm⟩ := mem_iUnion.1 (mem_iInter.1 hz n).2
  refine ⟨t m, mem_range_self m, ?_⟩
  exact lt_of_lt_of_le (mem_ball.1 hm) (by simpa [one_div] using hn.le)

theorem subset_nbhdR {a ρ : ℝ} (hρ : 0 < ρ) (t : ℕ → ℂ) :
    closure (range t) ∩ regionR a ⊆ nbhdR a ρ t := by
  intro z ⟨hz, hr⟩
  obtain ⟨b, ⟨m, rfl⟩, hb⟩ := Metric.mem_closure_iff.1 hz ρ hρ
  exact ⟨hr, mem_iUnion.2 ⟨m, mem_ball.2 hb⟩⟩

section Indep

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Independent random null sets, localized.** -/
theorem ae_qAreaMeasure_free_indep_region_null [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {T : Ω → ℕ → ℂ}
    (hT : Measurable T) (hind : IndepFun T X P)
    (hS : ∀ᵐ ω ∂P, volume (closure (range (T ω))) = 0) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂P, qAreaMeasure γ (X ω) (closure (range (T ω)) ∩ regionR a) = 0 := by
  set δ : ℝ := a + 2 * a⁻¹ with hδdef
  have hd : 0 < a⁻¹ := inv_pos.2 ha
  have hδ : 0 < δ := by positivity
  have hXm : Measurable X := measurable_pi_iff.mpr fun μ => hX.measurable_coord μ
  set V : ℕ → (ℕ → ℂ) → Set ℂ := fun n t => nbhdR a ((n : ℝ) + 1)⁻¹ t with hV
  set F : ℕ → ℕ → (ℕ → ℂ) × FieldSample → ℝ≥0∞ := fun n k q =>
    areaApprox γ (aZf δ q.2) k (V n q.1) with hF
  have hFm : ∀ n k, Measurable (F n k) := fun n k => measurable_areaApprox_nbhdR γ δ a _ k
  have hvm : ∀ n, Measurable fun t => volume (V n t) := fun n =>
    measurable_measure_prodMk_left (measurableSet_nbhdR_prod a ((n : ℝ) + 1)⁻¹)
  have hlaw : P.map (fun ω => (T ω, X ω)) = (P.map T).prod (P.map X) :=
    (indepFun_iff_map_prod_eq_prod_map_map hT.aemeasurable hXm.aemeasurable).1 hind
  set c0 : ℝ≥0∞ := ENNReal.ofReal (δ ^ (1 * (γ ^ 2 / 2)) *
    Real.exp ((2 * Real.log δ - 2 * Real.log δ).toNNReal * (1 * γ) ^ 2 / 2)) with hc0
  set c1 : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 / 2 * Real.log (δ / (2 * a⁻¹)))) with hc1
  obtain ⟨k₀, hk₀⟩ := FinArea.exists_radius_le hd
  -- the mean bound for a frozen set
  have hfix : ∀ n k, k₀ ≤ k → ∀ t : ℕ → ℂ,
      ∫⁻ ω, F n k (t, X ω) ∂P ≤ c0 * c1 * volume (V n t) := by
    intro n k hk t
    have hr : radius k ≤ a⁻¹ := (AreaExist.aradius_anti hk).trans hk₀
    have hadm : FinArea.Adm 0 δ a⁻¹ k (V n t) := ⟨hr, fun z hz => by
      have h2 : ‖z‖ < a := mem_ball_zero_iff.1 hz.1.2
      refine ⟨le_of_lt hz.1.1, ?_⟩
      simp only [Complex.ofReal_zero, sub_zero, hδdef]
      linarith⟩
    have h := FinArea.lintegral_areaApprox_rpow_le hX γ (R := δ) hδ hd (by simp) one_pos le_rfl
      (isOpen_nbhdR a _ t).measurableSet hadm
    simp only [ENNReal.rpow_one] at h
    rw [mul_assoc]
    exact h
  have hmean : ∀ n k, k₀ ≤ k →
      ∫⁻ ω, F n k (T ω, X ω) ∂P ≤ c0 * c1 * ∫⁻ ω, volume (V n (T ω)) ∂P := by
    intro n k hk
    rw [← lintegral_map (hFm n k) (hT.prodMk hXm), hlaw,
      lintegral_prod _ (hFm n k).aemeasurable, ← lintegral_map (hvm n) hT,
      ← lintegral_const_mul _ (hvm n)]
    refine lintegral_mono fun t => ?_
    rw [lintegral_map (f := fun y => F n k (t, y)) ((hFm n k).comp measurable_prodMk_left) hXm]
    exact hfix n k hk t
  have hreg : volume (regionR a) < ⊤ :=
    (measure_mono inter_subset_right).trans_lt measure_ball_lt_top
  have hvol : Tendsto (fun n => ∫⁻ ω, volume (V n (T ω)) ∂P) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence (μ := P) (f := fun _ => 0)
      (fun _ => volume (regionR a)) (fun n => (hvm n).comp hT)
      (fun n => Eventually.of_forall fun ω => measure_mono inter_subset_left)
      (by rw [lintegral_const, measure_univ, mul_one]; exact hreg.ne) ?_
    · simpa using h
    filter_upwards [hS] with ω hω
    have h1 := tendsto_measure_iInter_atTop (μ := volume) (s := fun n => V n (T ω))
      (fun n => (isOpen_nbhdR a _ _).measurableSet.nullMeasurableSet) (nbhdR_antitone a (T ω))
      ⟨0, ((measure_mono inter_subset_left).trans_lt hreg).ne⟩
    have h0 : volume (⋂ n, V n (T ω)) = 0 := measure_mono_null (iInter_nbhdR_subset a (T ω)) hω
    rw [h0] at h1
    exact h1
  set G : Ω → ℝ≥0∞ := fun ω => ⨅ n, liminf (fun k => F n k (T ω, X ω)) atTop with hG
  have hGm : Measurable G :=
    Measurable.iInf fun n => Measurable.liminf fun k => (hFm n k).comp (hT.prodMk hXm)
  have hGn : ∀ n, ∫⁻ ω, G ω ∂P ≤ c0 * c1 * ∫⁻ ω, volume (V n (T ω)) ∂P := by
    intro n
    refine (lintegral_mono fun ω =>
      iInf_le (fun n => liminf (fun k => F n k (T ω, X ω)) atTop) n).trans ?_
    refine (lintegral_liminf_le' fun k => ((hFm n k).comp (hT.prodMk hXm)).aemeasurable).trans ?_
    exact liminf_le_of_frequently_le'
      (Eventually.frequently (eventually_atTop.2 ⟨k₀, fun k hk => hmean n k hk⟩))
  have hC : c0 * c1 ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hint : ∫⁻ ω, G ω ∂P = 0 := by
    have ht : Tendsto (fun n => c0 * c1 * ∫⁻ ω, volume (V n (T ω)) ∂P) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hvol (Or.inr hC)
    exact le_antisymm (ge_of_tendsto' ht hGn) bot_le
  have hz := (lintegral_eq_zero_iff hGm).1 hint
  filter_upwards [hz, AreaExist.ae_isVagueLimitOn_qAreaMeasure_aZ hX (P := P) hγ hγ2 δ,
    FinArea.ae_qAreaMeasure_aZ_eq_smul hX hγ hγ2 δ] with ω h0 hv hsm
  have hZ : qAreaMeasure γ (AreaExist.aZ X δ ω) (closure (range (T ω)) ∩ regionR a) = 0 := by
    refine le_antisymm ?_ bot_le
    have hle : ∀ n, qAreaMeasure γ (AreaExist.aZ X δ ω) (closure (range (T ω)) ∩ regionR a) ≤
        liminf (fun k => F n k (T ω, X ω)) atTop := fun n =>
      (measure_mono (subset_nbhdR (by positivity) (T ω))).trans
        (measure_le_liminf_of_isVagueLimitOn hv (isOpen_nbhdR a _ _)
          (isBounded_ball.subset (inter_subset_left.trans inter_subset_right))
          ((closure_mono inter_subset_left).trans (closure_regionR_subset_H ha)))
    exact (le_iInf hle).trans (le_of_eq h0)
  rw [hsm, Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hZ
  refine hZ.resolve_left ?_
  rw [ENNReal.ofReal_eq_zero, not_le]
  exact Real.exp_pos _

/-- **Independent random Lebesgue-null closed sets carry no free-field quantum area**
(Sheffield p. 48; Duplantier–Sheffield 2011 Prop. 1.2 (2)). -/
theorem ae_qAreaMeasure_free_indep_null [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {T : Ω → ℕ → ℂ}
    (hT : Measurable T) (hind : IndepFun T X P)
    (hS : ∀ᵐ ω ∂P, volume (closure (range (T ω))) = 0) :
    ∀ᵐ ω ∂P, qAreaMeasure γ (X ω) (closure (range (T ω))) = 0 := by
  have h : ∀ m : ℕ, ∀ᵐ ω ∂P,
      qAreaMeasure γ (X ω) (closure (range (T ω)) ∩ regionR ((m : ℝ) + 1)) = 0 :=
    fun m => ae_qAreaMeasure_free_indep_region_null hX hγ hγ2 hT hind hS (by positivity)
  rw [← ae_all_iff] at h
  filter_upwards [h, AreaExist.ae_isVagueLimitOn_qAreaMeasure hX (P := P) hγ hγ2] with ω hω hv
  have hsub : closure (range (T ω)) ⊆
      Hᶜ ∪ ⋃ m : ℕ, closure (range (T ω)) ∩ regionR ((m : ℝ) + 1) := by
    intro z hz
    by_cases hzH : z ∈ H
    · right
      have him : 0 < z.im := hzH
      obtain ⟨m, hm⟩ := exists_nat_gt (max ‖z‖ (z.im)⁻¹)
      have h1 : ‖z‖ < (m : ℝ) + 1 := by linarith [le_max_left ‖z‖ (z.im)⁻¹]
      have h2 : (z.im)⁻¹ < (m : ℝ) + 1 := by linarith [le_max_right ‖z‖ (z.im)⁻¹]
      exact mem_iUnion.2 ⟨m, hz, inv_lt_of_inv_lt₀ him h2, mem_ball_zero_iff.2 h1⟩
    · exact Or.inl hzH
  exact measure_mono_null hsub (measure_union_null hv.1 (measure_iUnion_null hω))

/-- The same for the wedge reference field `wedgeField (lateralPart X) A Q` (area `e^{γ g} μ_X`),
for a random set independent of `X`. -/
theorem ae_qAreaMeasure_wedgeField_indep_null [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Q : ℝ}
    {A : ℝ → Ω → ℝ} (hA : ∀ᵐ ω ∂P, Continuous fun t => A t ω) {T : Ω → ℕ → ℂ}
    (hT : Measurable T) (hind : IndepFun T X P)
    (hS : ∀ᵐ ω ∂P, volume (closure (range (T ω))) = 0) :
    ∀ᵐ ω ∂P, qAreaMeasure γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) Q)
      (closure (range (T ω))) = 0 := by
  filter_upwards [WedgeCan4.ae_qAreaMeasure_wedgeField_eq hX hγ hγ2 (Q := Q) hA,
    ae_qAreaMeasure_free_indep_null hX hγ hγ2 hT hind hS] with ω h hn
  rw [h.1]
  exact withDensity_absolutelyContinuous _ _ hn

end Indep

end R18
end QuantumZipper
