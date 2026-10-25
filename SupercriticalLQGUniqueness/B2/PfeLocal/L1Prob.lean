import SupercriticalLQGUniqueness.B2.PfeLocal.L1Scale
import SupercriticalLQGUniqueness.B2.DG20Pt.HeatAnnulusTranslatedSmallLower
import SupercriticalLQGUniqueness.B2.DG20Pt.OpenCrossingLaw
import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedCanonicalModel
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge
import LQGMetric.Field.CircleAvgAffine
import LQGMetric.Papers.DFGPS.L2_8GenHeat
import LQGMetric.Papers.DDDF.LenCountable

 



















set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 
def l1UnitGood (ξ : ℝ) (b : Set.Ioi (0 : ℝ)) (ψ : C(ℂ, ℝ)) (q : Finset ℂ) (C : ℝ) : Prop :=
  (∀ i ∈ q, ENNReal.ofReal C⁻¹ < l1AcrossUnit ξ b ψ i) ∧
    ∀ k : Fin 4, l1AroundCost ξ b ψ 0 1 k < ENNReal.ofReal C

 

def l1HeatGood (ξ : ℝ) (a b : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (q : Finset ℂ) (z : ℂ) (r : ℝ)
    (C c : ℝ) : Prop :=
  (∀ i ∈ q, ENNReal.ofReal (C⁻¹ * (r * b / a) * Real.exp (ξ * c)) <
      l1AcrossCost ξ a φ z r i) ∧
    ∀ k : Fin 4, l1AroundCost ξ a φ z r k <
      ENNReal.ofReal (C * (r * b / a) * Real.exp (ξ * c))

theorem l1_heatGood_iff_unitGood (ξ : ℝ) (a b : Set.Ioi (0 : ℝ)) (φ ψ : C(ℂ, ℝ))
    (q : Finset ℂ) (z : ℂ) {r : ℝ} (hr : 0 < r) (C c : ℝ)
    (hψ : ∀ u, φ (z + (r : ℂ) * u) = ψ u + c) :
    l1HeatGood ξ a b φ q z r C c ↔ l1UnitGood ξ b ψ q C := by
  have ha : (0 : ℝ) < a := a.2
  have hb : (0 : ℝ) < b := b.2
  set K : ℝ := r * b / a * Real.exp (ξ * c) with hK
  have hK0 : 0 < K := by positivity
  have hK0' : ENNReal.ofReal K ≠ 0 := (ENNReal.ofReal_pos.2 hK0).ne'
  have e1 : ∀ x : ℝ, ENNReal.ofReal (x * (r * b / a) * Real.exp (ξ * c)) =
      ENNReal.ofReal K * ENNReal.ofReal x := by
    intro x
    rcases le_or_gt 0 x with hx | hx
    · rw [← ENNReal.ofReal_mul hK0.le, hK]; congr 1; ring
    · rw [ENNReal.ofReal_of_nonpos (by nlinarith [hK0]), ENNReal.ofReal_of_nonpos hx.le,
        mul_zero]
  unfold l1HeatGood l1UnitGood
  simp only [l1_acrossCost_scale ξ a b φ ψ z hr c hψ, l1_aroundCost_scale ξ a b φ ψ z hr c hψ,
    e1, ← hK]
  simp_rw [ENNReal.mul_lt_mul_iff_right hK0' ENNReal.ofReal_ne_top]

 
theorem l1_isHeatSmoothing_canonical (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    (δ : Set.Ioi (0 : ℝ)) : IsHeatSmoothing normGFFLaw id δ (V δ) := by
  obtain ⟨-, hcan⟩ := PfeAxioms.normalized_canonical_model
  obtain ⟨X, hXeq, hXlim⟩ := exists_heatVersion hcan (δ : ℝ) δ.2
  intro z
  filter_upwards [hXlim z, hXeq, hV δ] with g h1 h2 h3
  rw [show V δ g z = X g z by rw [h3 z, h2 z]; rfl]
  exact h1

theorem l1_measurable_acrossUnit (ξ : ℝ) (b : Set.Ioi (0 : ℝ)) {W : DistC → C(ℂ, ℝ)}
    (hW : Measurable W) (i : ℂ) : Measurable fun g => l1AcrossUnit ξ b (W g) i :=
  measurable_const.mul (DDDF.measurable_crossLenIn (isCompact_closedBall _ _)
    (Y := fun x g => W g x) (fun g => (W g).continuous)
    (fun x => (continuous_eval_const x).measurable.comp hW))

theorem l1_measurable_aroundUnit (ξ : ℝ) (b : Set.Ioi (0 : ℝ)) {W : DistC → C(ℂ, ℝ)}
    (hW : Measurable W) (k : Fin 4) : Measurable fun g => l1AroundCost ξ b (W g) 0 1 k :=
  measurable_const.mul (B2.DG20Pt.measurable_crossLenIn_open ξ
    ⟨l1AroundOpen 0 1 k, isOpen_l1AroundOpen 0 1 k⟩ _ _ (fun x g => W g x)
    (fun g => (W g).continuous) (fun x => (continuous_eval_const x).measurable.comp hW))

theorem l1_measurableSet_unitGood (ξ : ℝ) (b : Set.Ioi (0 : ℝ)) {W : DistC → C(ℂ, ℝ)}
    (hW : Measurable W) (q : Finset ℂ) (C : ℝ) :
    MeasurableSet {g | l1UnitGood ξ b (W g) q C} := by
  have e : {g | l1UnitGood ξ b (W g) q C} =
      (⋂ i ∈ (q : Set ℂ), {g | ENNReal.ofReal C⁻¹ < l1AcrossUnit ξ b (W g) i}) ∩
        ⋂ k : Fin 4, {g | l1AroundCost ξ b (W g) 0 1 k < ENNReal.ofReal C} := by
    ext g; simp [l1UnitGood]
  rw [e]
  exact (MeasurableSet.biInter q.countable_toSet fun i _ =>
      measurableSet_lt measurable_const (l1_measurable_acrossUnit ξ b hW i)).inter
    (MeasurableSet.iInter fun k =>
      measurableSet_lt (l1_measurable_aroundUnit ξ b hW k) measurable_const)

 
theorem l1_unit_tails (hS4 : Iface.DG20Section4) (hPerc : Iface.DG20PercEstimate')
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    (q : Finset ℂ) (η : ℝ) (hη : 0 < η) :
    ∃ C ε₀ : ℝ, 1 < C ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ δ : Set.Ioi (0 : ℝ), (δ : ℝ) < ε₀ →
      normGFFLaw {g | ¬ l1UnitGood ξ (m δ) (V δ g) q C} ≤
        ENNReal.ofReal ((q.card + 4) * η) := by
  obtain ⟨hprob, hcan⟩ := PfeAxioms.normalized_canonical_model
  have hX := l1_isHeatSmoothing_canonical V hV
  
  have hA : ∀ i : ℂ, ∃ T ε₀ : ℝ, 0 < T ∧ 0 < ε₀ ∧
      ∀ ε : Set.Ioo (0 : ℝ) 1, (ε : ℝ) < ε₀ →
        normGFFLaw {g | ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
          crossLenIn ξ (V ⟨ε, ε.property.1⟩ g)
            (closedBall i l1d) (sphere i (l1d / 16))
            (sphere i (3 * l1d / 4)) < ENNReal.ofReal T⁻¹} ≤ ENNReal.ofReal η := fun i =>
    B2.DG20Pt.dg20_heat_annulus_translated_small_lower_of_perc hPerc ξ m hm normGFFLaw id hcan
      V hX i l1d (by norm_num [l1d]) (by norm_num [l1d]) η hη
  choose T ε₁ hT hε₁ hAtail using hA
  
  have hO : ∀ k : Fin 4, ∃ M : ℝ, 0 < M ∧ ∀ ε : Set.Ioo (0 : ℝ) 1,
      normGFFLaw {g | ENNReal.ofReal M < l1AroundCost ξ (m ⟨ε, ε.property.1⟩)
        (V ⟨ε, ε.property.1⟩ g) 0 1 k} ≤ ENNReal.ofReal η := by
    intro k
    have htight := (hS4 ξ Q hQ m hm).1 normGFFLaw id hcan V hX
      ⟨l1AroundOpen 0 1 k, isOpen_l1AroundOpen 0 1 k⟩ (isConnected_l1AroundOpen 0 1 k)
      (l1Start 0 1 k) (l1End 0 1 k) (l1Start_mem_aroundOpen 0 1 k)
      (l1End_mem_aroundOpen 0 1 k) (l1Start_ne_end 0 1 k)
    obtain ⟨M, hM, hMt⟩ := htight.2 η hη
    exact ⟨M, hM, fun ε => (hMt ε).1⟩
  choose M hM hOtail using hO
  
  set Tq : ℝ := ∑ i ∈ q, T i with hTq
  set Mq : ℝ := ∑ k : Fin 4, M k with hMq
  have hTle : ∀ i ∈ q, T i ≤ Tq := fun i hi =>
    Finset.single_le_sum (f := T) (fun j _ => (hT j).le) hi
  have hMle : ∀ k, M k ≤ Mq := fun k =>
    Finset.single_le_sum (f := M) (fun j _ => (hM j).le) (Finset.mem_univ k)
  have hTq0 : 0 ≤ Tq := Finset.sum_nonneg fun j _ => (hT j).le
  have hMq0 : 0 < Mq := Finset.sum_pos (fun j _ => hM j) Finset.univ_nonempty
  clear_value Tq Mq
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = Tq + Mq + 1 := ⟨_, rfl⟩
  have hC1 : 1 < C := by
    rw [hC]; linarith
  have hTC : ∀ i ∈ q, T i < C := fun i hi => by linarith [hTle i hi]
  have hMC : ∀ k, M k < C := fun k => by linarith [hMle k]
  set S : Finset ℝ := insert 1 (q.image ε₁) with hS
  have hSne : S.Nonempty := Finset.insert_nonempty _ _
  set ε₀ : ℝ := S.min' hSne with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def, Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · norm_num
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact hε₁ i
  have hε₀1 : ε₀ ≤ 1 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hε₀i : ∀ i ∈ q, ε₀ ≤ ε₁ i := fun i hi =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hi))
  refine ⟨C, ε₀, hC1, hε₀pos, hε₀1, fun δ hδ => ?_⟩
  have hδ1 : (δ : ℝ) < 1 := lt_of_lt_of_le hδ hε₀1
  let e : Set.Ioo (0 : ℝ) 1 := ⟨δ, δ.2, hδ1⟩
  have hsub : {g | ¬ l1UnitGood ξ (m δ) (V δ g) q C} ⊆
      (⋃ i ∈ q, {g | ENNReal.ofReal (m ⟨e, e.property.1⟩ : ℝ)⁻¹ *
          crossLenIn ξ (V ⟨e, e.property.1⟩ g)
            (closedBall i l1d) (sphere i (l1d / 16))
            (sphere i (3 * l1d / 4)) < ENNReal.ofReal (T i)⁻¹}) ∪
        ⋃ k : Fin 4, {g | ENNReal.ofReal (M k) < l1AroundCost ξ (m ⟨e, e.property.1⟩)
          (V ⟨e, e.property.1⟩ g) 0 1 k} := by
    intro g hg
    simp only [mem_ofPred_eq, l1UnitGood, not_and_or, not_forall, not_lt] at hg
    rcases hg with ⟨i, hi, hle⟩ | ⟨k, hk⟩
    · left
      refine mem_biUnion hi ?_
      simp only [mem_ofPred_eq]
      refine lt_of_le_of_lt hle ?_
      exact (ENNReal.ofReal_lt_ofReal_iff (inv_pos.2 (hT i))).2
        (inv_strictAnti₀ (hT i) (hTC i hi))
    · right
      refine mem_iUnion.2 ⟨k, ?_⟩
      exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith [hM k])).2 (hMC k)) hk
  have hsum : ∑ i ∈ q, ENNReal.ofReal η + ∑ k : Fin 4, ENNReal.ofReal η =
      ENNReal.ofReal ((q.card + 4) * η) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      nsmul_eq_mul, ← add_mul, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_natCast,
      ENNReal.ofReal_ofNat]
    norm_num
  calc normGFFLaw {g | ¬ l1UnitGood ξ (m δ) (V δ g) q C}
      ≤ normGFFLaw ((⋃ i ∈ q, {g | ENNReal.ofReal (m ⟨e, e.property.1⟩ : ℝ)⁻¹ *
          crossLenIn ξ (V ⟨e, e.property.1⟩ g)
            (closedBall i l1d) (sphere i (l1d / 16))
            (sphere i (3 * l1d / 4)) < ENNReal.ofReal (T i)⁻¹}) ∪
        ⋃ k : Fin 4, {g | ENNReal.ofReal (M k) < l1AroundCost ξ (m ⟨e, e.property.1⟩)
          (V ⟨e, e.property.1⟩ g) 0 1 k}) := measure_mono hsub
    _ ≤ ∑ i ∈ q, ENNReal.ofReal η + ∑ k : Fin 4, ENNReal.ofReal η := by
      refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
      · exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun i hi =>
          hAtail i e (lt_of_lt_of_le hδ (hε₀i i hi)))
      · exact (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun k _ =>
          hOtail k e)
    _ = ENNReal.ofReal ((q.card + 4) * η) := hsum

 
def l1Pull (z : ℂ) (r : ℝ) (g : DistC) : DistC :=
  addConst (affineComp r z g) (-circleAvg g r z)

theorem measurable_l1Pull (z : ℂ) (r : ℝ) : Measurable (l1Pull z r) :=
  LQGMetric.DFGPS.L219.measurable_addConst_of (measurable_affineComp r z)
    (measurable_circleAvg_left r z).neg

 
theorem l1_map_pull (z : ℂ) {r : ℝ} (hr : 0 < r) :
    normGFFLaw.map (l1Pull z r) = normGFFLaw := by
  obtain ⟨-, hcan⟩ := PfeAxioms.normalized_canonical_model
  have h := LQGMetric.CircleAvg.map_affine_sub_circleAvg
    (Uniqueness.Toolkit.AnnulusIteration.normalized_old_of_new hcan) hr z
  rw [Measure.map_id] at h
  exact h

 
theorem l1_ae_pull_heat (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    (z : ℂ) {r : ℝ} (hr : 0 < r) (ε : Set.Ioi (0 : ℝ)) :
    ∀ᵐ g ∂normGFFLaw, ∀ u, V ε g (z + (r : ℂ) * u) =
      V ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos ε.2 hr)⟩ (l1Pull z r g) u +
        circleAvg g r z := by
  obtain ⟨-, hcan⟩ := PfeAxioms.normalized_canonical_model
  have hG := hcan.1
  set ε' : Set.Ioi (0 : ℝ) := ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos ε.2 hr)⟩
  have hεr : (ε : ℝ) / r ≠ 0 := (div_pos ε.2 hr).ne'
  have h1 := hV ε
  have h2 : ∀ᵐ g ∂normGFFLaw, ∀ u, V ε' (l1Pull z r g) u =
      heatMollify (ε' : ℝ) (l1Pull z r g) u := by
    have := hV ε'
    rw [← l1_map_pull z hr] at this
    exact ae_of_ae_map (measurable_l1Pull z r).aemeasurable this
  have h3 := LQGMetric.DFGPS.ae_heatMollify_affineComp_trans hG (ε.2.ne') hr z
  have h4 := (hG.affineComp hr z).ae_tendstoLocallyUniformly_heatMollify ((ε : ℝ) / r) hεr
  filter_upwards [h1, h2, h3, h4] with g hg1 hg2 hg3 hg4 u
  simp only [id_eq] at hg3 hg4
  rw [hg2 u]
  change V ε g (z + (r : ℂ) * u) =
    heatMollify ((ε : ℝ) / r) (addConst (affineComp r z g) (-circleAvg g r z)) u +
      circleAvg g r z
  rw [LQGMetric.DFGPS.heatMollify_addConst_of_tendsto hεr
    ((tendstoLocallyUniformlyOn_univ.2 hg4.1).tendsto_at (mem_univ u))]
  rw [show heatMollify ((ε : ℝ) / r) (affineComp r z g) u =
    heatMollify (ε : ℝ) g (z + (r : ℂ) * u) from hg3 u, hg1 (z + (r : ℂ) * u)]
  ring

 
theorem l1_heat_good_prob (hS4 : Iface.DG20Section4) (hPerc : Iface.DG20PercEstimate')
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (hVm : ∀ δ, Measurable (V δ))
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    (q : Finset ℂ) (η : ℝ) (hη : 0 < η) :
    ∃ C ε₀ : ℝ, 1 < C ∧ 0 < ε₀ ∧ ∀ (z : ℂ) (r : ℝ) (hr : 0 < r) (ε : Set.Ioi (0 : ℝ)),
      (ε : ℝ) / r < ε₀ →
        normGFFLaw {g | ¬ l1HeatGood ξ (m ε)
          (m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos ε.2 hr)⟩) (V ε g) q z r C
            (circleAvg g r z)} ≤ ENNReal.ofReal ((q.card + 4) * η) := by
  obtain ⟨C, ε₀, hC1, hε₀, -, htail⟩ := l1_unit_tails hS4 hPerc ξ Q hQ m hm V hV q η hη
  refine ⟨C, ε₀, hC1, hε₀, fun z r hr ε hεr => ?_⟩
  set ε' : Set.Ioi (0 : ℝ) := ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos ε.2 hr)⟩
  have hae := l1_ae_pull_heat V hV z hr ε
  have hset : {g | ¬ l1HeatGood ξ (m ε) (m ε') (V ε g) q z r C (circleAvg g r z)} =ᵐ[normGFFLaw]
      (l1Pull z r) ⁻¹' {g' | l1UnitGood ξ (m ε') (V ε' g') q C}ᶜ := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [hae] with g hg
    simp only [mem_ofPred_eq, mem_preimage, mem_compl_iff]
    rw [l1_heatGood_iff_unitGood ξ (m ε) (m ε') (V ε g) (V ε' (l1Pull z r g)) q z hr C
      (circleAvg g r z) hg]
  rw [measure_congr hset, ← Measure.map_apply (measurable_l1Pull z r)
    (l1_measurableSet_unitGood ξ (m ε') (hVm ε') q C).compl, l1_map_pull z hr]
  exact htail ε' hεr

end SupercriticalLQGUniqueness.B2.PfeLocal
