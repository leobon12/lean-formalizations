import SLUMetricAPI
import LQGMetric.Topo.Disconnect
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import LQGMetric.Metric.CurveNatural
import LQGMetric.Metric.Internal
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

 




















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace SupercriticalLQGUniqueness

namespace LSCMetric


theorem edist_pt (D : LSCMetric) (x y : ℂ) : edist (D.pt x) (D.pt y) = D (x, y) :=
  rfl

theorem len_eq_curveLength (D : LSCMetric) (P : ℝ → ℂ) (a b : ℝ) :
    D.len P a b = LQGMetric.MetricGeometry.curveLength (D.pt ∘ P) a b :=
  rfl

 

theorem len_eq_partitionSup (D : LSCMetric) (P : ℝ → ℂ) (a b : ℝ) :
    D.len P a b = ⨆ (n : ℕ) (t : ℕ → ℝ) (_ : StrictMonoOn t (Iic n)) (_ : t 0 = a)
      (_ : t n = b), ∑ i ∈ Finset.range n, D (P (t (i + 1)), P (t i)) :=
  LQGMetric.MetricGeometry.curveLength_eq_partitionLengthSup (D.pt ∘ P) a b

theorem apply_le_len (D : LSCMetric) (P : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    D (P a, P b) ≤ D.len P a b :=
  eVariationOn.edist_le (D.pt ∘ P) (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)

 

theorem IsCurve.apply_lt_top {D : LSCMetric} {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) :
    D (P a, P b) < ∞ := by
  have hpre : IsPreconnected ((D.pt ∘ P) '' Icc a b) := isPreconnected_Icc.image _ hP.2
  have hclopen : IsClopen (Metric.eball (D.pt (P a)) ⊤) :=
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have hsub := hpre.subset_isClopen hclopen
    ⟨D.pt (P a), ⟨a, left_mem_Icc.2 hP.1, rfl⟩, Metric.mem_eball_self ENNReal.zero_lt_top⟩
  have hb : D.pt (P b) ∈ Metric.eball (D.pt (P a)) ⊤ := hsub ⟨b, right_mem_Icc.2 hP.1, rfl⟩
  rw [Metric.mem_eball, edist_comm] at hb
  exact hb

 


theorem literal_iff (D : LSCMetric) :
    (∀ x y : ℂ, ∀ ε : ℝ, 0 < ε → ∃ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b ∧ P a = x ∧
        P b = y ∧ D.len P a b ≤ D (x, y) + ENNReal.ofReal ε) ↔
      D.IsLengthSpace ∧ ∀ x y : ℂ, D (x, y) < ∞ := by
  constructor
  · intro h
    refine ⟨fun x y _ ε hε => h x y ε hε, fun x y => ?_⟩
    obtain ⟨P, a, b, hP, rfl, rfl, -⟩ := h x y 1 one_pos
    exact hP.apply_lt_top
  · intro h x y ε hε
    exact h.1 x y (h.2 x y) ε hε

 


theorem isLengthSpace_iff_eq_iInf (D : LSCMetric) :
    D.IsLengthSpace ↔ ∀ x y : ℂ, D (x, y) =
      ⨅ (P : ℝ → ℂ) (a : ℝ) (b : ℝ) (_ : D.IsCurve P a b) (_ : P a = x) (_ : P b = y),
        D.len P a b := by
  constructor
  · intro hD x y
    refine le_antisymm (le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun ha => le_iInf fun hb => ?_) ?_
    · rw [← ha, ← hb]
      exact D.apply_le_len P hP.1
    refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt => ?_
    obtain ⟨P, a, b, hP, ha, hb, hlen⟩ := hD x y hlt ε (by exact_mod_cast hε)
    rw [ENNReal.ofReal_coe_nnreal] at hlen
    calc ⨅ (P : ℝ → ℂ) (a : ℝ) (b : ℝ) (_ : D.IsCurve P a b) (_ : P a = x) (_ : P b = y),
          D.len P a b
        ≤ D.len P a b := iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
          iInf_le_of_le hP <| iInf_le_of_le ha <| iInf_le_of_le hb le_rfl
      _ ≤ D (x, y) + ε := hlen
  · intro hD x y hxy ε hε
    have hlt : ⨅ (P : ℝ → ℂ) (a : ℝ) (b : ℝ) (_ : D.IsCurve P a b) (_ : P a = x)
        (_ : P b = y), D.len P a b < D (x, y) + ENNReal.ofReal ε := by
      rw [← hD x y]
      exact ENNReal.lt_add_right hxy.ne (ENNReal.ofReal_pos.2 hε).ne'
    simp only [iInf_lt_iff] at hlt
    obtain ⟨P, a, b, hP, ha, hb, hlen⟩ := hlt
    exact ⟨P, a, b, hP, ha, hb, hlen.le⟩

 

theorem internal_eq_internalEDist (D : LSCMetric) (Y : Set ℂ) (p : Y × Y) :
    D.internal Y p =
      LQGMetric.MetricGeometry.internalEDist (D.pt '' Y) (D.pt p.1) (D.pt p.2) := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun γ => ?_
    have htr : ∀ t ∈ Icc (0 : ℝ) 1, (γ.1.extend t : ℂ) ∈ Y := by
      intro t ht
      obtain ⟨x, hx, hxt⟩ := γ.2 ⟨t, ht⟩
      rw [Path.extend_apply γ.1 ht, ← hxt]
      exact hx
    exact iInf_le_of_le (fun t => (γ.1.extend t : ℂ)) <| iInf_le_of_le 0 <| iInf_le_of_le 1 <|
      iInf_le_of_le ⟨zero_le_one, γ.1.continuous_extend.continuousOn⟩ <| iInf_le_of_le htr <|
      iInf_le_of_le γ.1.extend_zero <| iInf_le_of_le γ.1.extend_one le_rfl
  · refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP => le_iInf fun hY =>
      le_iInf fun ha => le_iInf fun hb => ?_
    have h := LQGMetric.MetricGeometry.internalEDist_le_curveLength (X := D.Space)
      (Y := D.pt '' Y) (P := D.pt ∘ P) hP.1 hP.2 (fun t ht => ⟨P t, hY t ht, rfl⟩)
    have ha' : (D.pt ∘ P) a = D.pt p.1 := congrArg D.pt ha
    have hb' : (D.pt ∘ P) b = D.pt p.2 := congrArg D.pt hb
    rw [ha', hb'] at h
    exact h

 

theorem isExtMetric_internal (D : LSCMetric) (Y : Set ℂ) : IsExtMetric (D.internal Y) := by
  refine ⟨fun x => ?_, fun x y h => ?_, fun x y => ?_, fun x y z => ?_⟩
  · rw [internal_eq_internalEDist]
    exact LQGMetric.MetricGeometry.internalEDist_self ⟨x.1, x.2, rfl⟩
  · rw [internal_eq_internalEDist] at h
    have h1 := (LQGMetric.MetricGeometry.edist_le_internalEDist _ _ _).trans h.le
    exact Subtype.ext (D.isExtMetric.eq_of_eq_zero _ _ (le_antisymm h1 bot_le))
  · simp only [internal_eq_internalEDist]
    exact LQGMetric.MetricGeometry.internalEDist_comm _ _ _
  · simp only [internal_eq_internalEDist]
    exact LQGMetric.MetricGeometry.internalEDist_triangle _ _ _ _

 
theorem isLengthSpace_iff_internal_univ (D : LSCMetric) :
    D.IsLengthSpace ↔ ∀ x y : ℂ,
      D (x, y) = D.internal univ (⟨x, mem_univ x⟩, ⟨y, mem_univ y⟩) := by
  rw [isLengthSpace_iff_eq_iInf]
  simp only [internal, mem_univ, implies_true, iInf_pos]

end LSCMetric

 

section CurveEuclidean

variable {D : LSCMetric} {P : ℝ → ℂ} {a b : ℝ}

 


theorem LSCMetric.IsCurve.isClosed_inter_preimage (hP : D.IsCurve P a b) {F : Set ℂ}
    (hF : IsCompact F) : IsClosed (Icc a b ∩ P ⁻¹' F) := by
  refine IsSeqClosed.isClosed fun t t₀ ht htt₀ => ?_
  have ht₀ : t₀ ∈ Icc a b :=
    isClosed_Icc.mem_of_tendsto htt₀ (Eventually.of_forall fun n => (ht n).1)
  obtain ⟨y, hyF, φ, hφ, hy⟩ := hF.tendsto_subseq (fun n => (ht n).2)
  have hcont : Tendsto (fun k => D.pt (P (t (φ k)))) atTop (𝓝 (D.pt (P t₀))) :=
    (hP.2 t₀ ht₀).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨htt₀.comp hφ.tendsto_atTop, Eventually.of_forall fun k => (ht (φ k)).1⟩)
  have hD0 : Tendsto (fun k => D (P (t (φ k)), P t₀)) atTop (𝓝 0) :=
    tendsto_iff_edist_tendsto_0.1 hcont
  have hlsc := (lowerSemicontinuous_iff_seq.1 D.lowerSemicontinuous)
    (fun k => (P (t (φ k)), P t₀)) (y, P t₀) (hy.prodMk_nhds tendsto_const_nhds)
  rw [hD0.liminf_eq] at hlsc
  have hy0 : y = P t₀ := D.isExtMetric.eq_of_eq_zero _ _ (le_antisymm hlsc bot_le)
  refine ⟨ht₀, ?_⟩
  rw [Set.mem_preimage, ← hy0]
  exact hyF

 
theorem LSCMetric.IsCurve.measurable_restrict (hP : D.IsCurve P a b) :
    Measurable ((Icc a b).domRestrict P) := by
  refine measurable_of_isClosed fun s hs => ?_
  have hrw : (Icc a b).domRestrict P ⁻¹' s =
      ⋃ n : ℕ, Subtype.val ⁻¹' (Icc a b ∩ P ⁻¹' (s ∩ Metric.closedBall 0 n)) := by
    ext t
    simp only [Set.mem_preimage, Set.domRestrict_apply, Set.mem_iUnion, Set.mem_inter_iff,
      Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_ge ‖P t‖
      exact ⟨n, t.2, h, hn⟩
    · rintro ⟨n, -, h, -⟩
      exact h
  rw [hrw]
  exact MeasurableSet.iUnion fun n =>
    (hP.isClosed_inter_preimage ((isCompact_closedBall 0 (n : ℝ)).inter_left hs)).measurableSet.preimage
      measurable_subtype_coe

theorem LSCMetric.IsCurve.aemeasurable (hP : D.IsCurve P a b) :
    AEMeasurable P (volume.restrict (Icc a b)) :=
  (aemeasurable_restrict_iff_comap_subtype measurableSet_Icc).2 hP.measurable_restrict.aemeasurable

 


theorem weylScale_integrand_aemeasurable (ξ : ℝ) (f : C(ℂ, ℝ)) {L : ℝ} (hP : D.IsCurve P 0 L) :
    AEMeasurable (fun t => ENNReal.ofReal (Real.exp (ξ * f (P t)))) (volume.restrict (Icc 0 L)) :=
  (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul f.continuous.measurable))).comp_aemeasurable hP.aemeasurable

 
theorem LSCMetric.IsCurve.continuousOn_of_mapsTo (hP : D.IsCurve P a b) {B : Set ℂ}
    (hB : IsCompact B) (hPB : MapsTo P (Icc a b) B) : ContinuousOn P (Icc a b) := by
  rw [continuousOn_iff_isClosed]
  intro F hF
  refine ⟨Icc a b ∩ P ⁻¹' (F ∩ B), hP.isClosed_inter_preimage (hB.inter_left hF), ?_⟩
  ext t
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨hF', ht⟩
    exact ⟨⟨ht, hF', hPB ht⟩, ht⟩
  · rintro ⟨⟨-, hF', -⟩, ht⟩
    exact ⟨hF', ht⟩

 

theorem LSCMetric.IsCurve.isClosed_image (hP : D.IsCurve P a b) : IsClosed (P '' Icc a b) := by
  refine IsSeqClosed.isClosed fun y y₀ hy hyy₀ => ?_
  choose t ht hty using hy
  obtain ⟨t₀, ht₀, φ, hφ, htφ⟩ := isCompact_Icc.tendsto_subseq ht
  have hcont : Tendsto (fun k => D.pt (P (t (φ k)))) atTop (𝓝 (D.pt (P t₀))) :=
    (hP.2 t₀ ht₀).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨htφ, Eventually.of_forall fun k => ht (φ k)⟩)
  have hD0 : Tendsto (fun k => D (P (t (φ k)), P t₀)) atTop (𝓝 0) :=
    tendsto_iff_edist_tendsto_0.1 hcont
  have hyφ : Tendsto (fun k => P (t (φ k))) atTop (𝓝 y₀) := by
    simp only [hty]
    exact hyy₀.comp hφ.tendsto_atTop
  have hlsc := (lowerSemicontinuous_iff_seq.1 D.lowerSemicontinuous)
    (fun k => (P (t (φ k)), P t₀)) (y₀, P t₀) (hyφ.prodMk_nhds tendsto_const_nhds)
  rw [hD0.liminf_eq] at hlsc
  exact ⟨t₀, ht₀, (D.isExtMetric.eq_of_eq_zero _ _ (le_antisymm hlsc bot_le)).symm⟩

end CurveEuclidean

 


theorem disconnects_iff_lqgMetric_disconnects {K E F : Set ℂ} (hK : IsClosed K) :
    Disconnects K E F ↔ LQGMetric.Disconnects K E F := by
  constructor
  · intro h x y γ hx hy
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    exact h ⟨range γ, isPreconnected_range γ.continuous,
      fun z hz hzK => (Set.eq_empty_iff_forall_notMem.1 hne) z ⟨hz, hzK⟩,
      ⟨x, ⟨0, γ.source⟩, hx⟩, ⟨y, ⟨1, γ.target⟩, hy⟩⟩
  · rintro h ⟨S, hS, hSK, ⟨x, hxS, hxE⟩, ⟨y, hyS, hyF⟩⟩
    have hC : IsPathConnected (connectedComponentIn Kᶜ x) :=
      (hK.isOpen_compl.connectedComponentIn.isConnected_iff_isPathConnected).1
        (isConnected_connectedComponentIn_iff.2 (hSK hxS))
    have hSC : S ⊆ connectedComponentIn Kᶜ x := hS.subset_connectedComponentIn hxS hSK
    obtain ⟨γ, hγ⟩ := hC.joinedIn x (hSC hxS) y (hSC hyS)
    obtain ⟨z, ⟨t, rfl⟩, hzK⟩ := h x y γ hxE hyF
    exact connectedComponentIn_subset _ _ (hγ t) hzK

 

namespace EuclideanAnnulus

variable (A : EuclideanAnnulus)

theorem toSet_eq :
    A.toSet = {z | A.innerRadius < dist z A.center ∧ dist z A.center < A.outerRadius} := by
  ext z
  simp only [toSet, closure_ball _ A.innerRadius_pos.ne', Set.mem_sdiff,
    Metric.mem_ball, Metric.mem_closedBall, not_le, Set.mem_ofPred_eq]
  exact and_comm

theorem isOpen_toSet : IsOpen A.toSet :=
  Metric.isOpen_ball.sdiff isClosed_closure

theorem closure_toSet :
    closure A.toSet = {z | A.innerRadius ≤ dist z A.center ∧ dist z A.center ≤ A.outerRadius} := by
  apply Subset.antisymm
  · apply closure_minimal
    · rw [toSet_eq]
      exact fun z hz => ⟨hz.1.le, hz.2.le⟩
    · exact (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
        (isClosed_le (continuous_id.dist continuous_const) continuous_const)
  · intro z hz
    have hρ : 0 < dist z A.center := A.innerRadius_pos.trans_le hz.1
    let g : ℝ → ℂ := fun s => A.center + (s / dist z A.center) • (z - A.center)
    have hg : Continuous g := by fun_prop
    have hgdist : ∀ s, 0 ≤ s → dist (g s) A.center = s := by
      intro s hs
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hs hρ.le), ← dist_eq_norm, div_mul_cancel₀ s hρ.ne']
    have hgρ : g (dist z A.center) = z := by
      simp only [g, div_self hρ.ne', one_smul, add_sub_cancel]
    have hmem : dist z A.center ∈ closure (Ioo A.innerRadius A.outerRadius) := by
      rw [closure_Ioo A.innerRadius_lt_outerRadius.ne]
      exact hz
    refine closure_mono ?_ (image_closure_subset_closure_image hg ⟨_, hmem, hgρ⟩)
    rintro _ ⟨s, hs, rfl⟩
    rw [toSet_eq]
    have hs0 : 0 ≤ s := A.innerRadius_pos.le.trans hs.1.le
    exact ⟨(hgdist s hs0).symm ▸ hs.1, (hgdist s hs0).symm ▸ hs.2⟩

 

theorem frontier_toSet : frontier A.toSet = A.innerBoundary ∪ A.outerBoundary := by
  rw [A.isOpen_toSet.frontier_eq, closure_toSet, toSet_eq]
  ext z
  simp only [innerBoundary, outerBoundary, Set.mem_sdiff, Set.mem_union, Metric.mem_sphere,
    Set.mem_ofPred_eq, not_and_or, not_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3 | h3⟩
    · exact Or.inl (le_antisymm h3 h1)
    · exact Or.inr (le_antisymm h2 h3)
  · rintro (h | h)
    · exact ⟨⟨h.ge, h.le.trans A.innerRadius_lt_outerRadius.le⟩, Or.inl h.le⟩
    · exact ⟨⟨A.innerRadius_lt_outerRadius.le.trans h.ge, h.le⟩, Or.inr h.ge⟩

theorem isConnected_innerBoundary : IsConnected A.innerBoundary :=
  isConnected_sphere (by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat) A.center
    A.innerRadius_pos.le

theorem isConnected_outerBoundary : IsConnected A.outerBoundary :=
  isConnected_sphere (by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat) A.center
    (A.innerRadius_pos.trans A.innerRadius_lt_outerRadius).le

 
theorem toSet_dilate (r : ℝ) (hr : 0 < r) : (A.dilate r hr).toSet = r • A.toSet := by
  have hr0 : r ≠ 0 := hr.ne'
  have h1 : 0 < A.innerRadius := A.2.1
  have hinj : Function.Injective (fun x : ℂ => r • x) := smul_right_injective ℂ hr0
  have hc : (A.dilate r hr).center = r • A.center := rfl
  have hi : (A.dilate r hr).innerRadius = r * A.innerRadius := rfl
  have ho : (A.dilate r hr).outerRadius = r * A.outerRadius := rfl
  rw [← Set.image_smul]
  unfold EuclideanAnnulus.toSet
  rw [hc, hi, ho, Set.image_sdiff hinj, Set.image_smul, Set.image_smul,
    closure_ball _ h1.ne', closure_ball _ (mul_pos hr h1).ne', smul_closedBall _ _ h1.le,
    smul_ball hr0, Real.norm_eq_abs, abs_of_pos hr]

theorem innerBoundary_dilate (r : ℝ) (hr : 0 < r) :
    (A.dilate r hr).innerBoundary = r • A.innerBoundary := by
  rw [innerBoundary, innerBoundary, smul_sphere' hr.ne', Real.norm_of_nonneg hr.le]
  rfl

theorem outerBoundary_dilate (r : ℝ) (hr : 0 < r) :
    (A.dilate r hr).outerBoundary = r • A.outerBoundary := by
  rw [outerBoundary, outerBoundary, smul_sphere' hr.ne', Real.norm_of_nonneg hr.le]
  rfl

 
theorem disconnects_sphere {ρ : ℝ} (h₁ : A.innerRadius < ρ) (h₂ : ρ < A.outerRadius) :
    Disconnects (Metric.sphere A.center ρ) A.innerBoundary A.outerBoundary := by
  rintro ⟨S, hS, hSK, ⟨x, hxS, hx⟩, ⟨y, hyS, hy⟩⟩
  have himg : IsPreconnected ((fun z => dist z A.center) '' S) :=
    hS.image _ (continuous_id.dist continuous_const).continuousOn
  have hx' : dist x A.center = A.innerRadius := Metric.mem_sphere.1 hx
  have hy' : dist y A.center = A.outerRadius := Metric.mem_sphere.1 hy
  obtain ⟨z, hzS, hz⟩ := himg.Icc_subset ⟨x, hxS, rfl⟩ ⟨y, hyS, rfl⟩
    ⟨by simp only [hx']; exact h₁.le, by simp only [hy']; exact h₂.le⟩
  exact hSK hzS (Metric.mem_sphere.2 hz)

 

theorem not_disconnects_empty : ¬ Disconnects (∅ : Set ℂ) A.innerBoundary A.outerBoundary := by
  intro h
  have hr₂ : 0 < A.outerRadius := A.innerRadius_pos.trans A.innerRadius_lt_outerRadius
  refine h ⟨(fun s : ℝ => A.center + (s : ℂ)) '' Icc A.innerRadius A.outerRadius,
    isPreconnected_Icc.image _ (by fun_prop), by simp,
    ⟨A.center + A.innerRadius, ⟨A.innerRadius, left_mem_Icc.2 A.innerRadius_lt_outerRadius.le,
      rfl⟩, ?_⟩,
    ⟨A.center + A.outerRadius, ⟨A.outerRadius, right_mem_Icc.2 A.innerRadius_lt_outerRadius.le,
      rfl⟩, ?_⟩⟩
  · simp [innerBoundary, abs_of_pos A.innerRadius_pos]
  · simp [outerBoundary, abs_of_pos hr₂]

end EuclideanAnnulus

 

 

theorem hasUnitSpeedOn_iff (D : LSCMetric) (P : ℝ → ℂ) (L : ℝ) :
    HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L) ↔
      ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, s ≤ t → D.len P s t = ENNReal.ofReal (t - s) := by
  constructor
  · intro h s hs t ht hst
    have h1 := h hs ht
    rwa [Set.inter_eq_right.2 (Icc_subset_Icc hs.1 ht.2), NNReal.coe_one, one_mul] at h1
  · intro h s hs t ht
    rcases le_or_gt s t with hst | hts
    · rw [Set.inter_eq_right.2 (Icc_subset_Icc hs.1 ht.2), NNReal.coe_one, one_mul]
      exact h s hs t ht hst
    · rw [Set.Icc_eq_empty (not_le.2 hts), Set.inter_empty,
        eVariationOn.subsingleton _ Set.subsingleton_empty, NNReal.coe_one, one_mul,
        ENNReal.ofReal_of_nonpos (sub_nonpos.2 hts.le)]

end SupercriticalLQGUniqueness

