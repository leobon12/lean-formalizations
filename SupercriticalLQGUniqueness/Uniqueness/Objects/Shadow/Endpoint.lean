import SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow.Planar
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import LQGMetric.Metric.InternalOps
import LQGMetric.Metric.Geodesic
import LQGMetric.Topo.Disconnect




 
set_option autoImplicit false

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

open Set MeasureTheory

 

theorem volume_periodic_Ico_eq {A : Set ℝ} {T : ℝ}
    (hT : 0 < T) (hA : MeasurableSet A)
    (hper : Function.Periodic (fun x : ℝ => x ∈ A) T)
    (s t : ℝ) :
    volume (A ∩ Ico s (s + T)) = volume (A ∩ Ico t (t + T)) := by
  have hinv (g : AddSubgroup.zmultiples T) :
      (fun x : ℝ => g +ᵥ x) ⁻¹' A = A := by
    ext x
    exact Iff.of_eq (hper.map_vadd_zmultiples g x)
  have hbase :=
    (isAddFundamentalDomain_Ioc hT s).measure_set_eq
      (isAddFundamentalDomain_Ioc hT t) hA hinv
  calc
    volume (A ∩ Ico s (s + T)) = volume (A ∩ Ioc s (s + T)) :=
      measure_congr (Filter.EventuallyEq.inter Filter.EventuallyEq.rfl Ico_ae_eq_Ioc)
    _ = volume (A ∩ Ioc t (t + T)) := hbase
    _ = volume (A ∩ Ico t (t + T)) :=
      measure_congr (Filter.EventuallyEq.inter Filter.EventuallyEq.rfl Ico_ae_eq_Ioc).symm


end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

open Set Metric

 

theorem finite_greedy_centers {ι : Type*} {S : Set ι} (hS : S.Finite)
    (center : ι → ℂ) {h : ℝ} (hh : 0 < h) :
    ∃ T : Set ι, T ⊆ S ∧ T.Finite ∧
      (∀ e ∈ T, ∀ e' ∈ T, e ≠ e' →
        6 * h ≤ dist (center e) (center e')) ∧
      (∀ e ∈ S, ∃ e' ∈ T, dist (center e) (center e') < 6 * h) := by
  classical
  let Good : Set (Set ι) :=
    {T | T ⊆ S ∧ ∀ e ∈ T, ∀ e' ∈ T,
      e ≠ e' → 6 * h ≤ dist (center e) (center e')}
  have hfin : Good.Finite := (hS.finite_subsets).subset (by
    intro T hT
    exact hT.1)
  have hne : Good.Nonempty := ⟨∅, by simp [Good]⟩
  obtain ⟨T, hT⟩ := hfin.exists_maximal hne
  have hcover : ∀ e ∈ S, ∃ e' ∈ T,
      dist (center e) (center e') < 6 * h := by
    intro e he
    by_contra hno
    have hfar : ∀ e' ∈ T, 6 * h ≤ dist (center e) (center e') := by
      push_neg at hno
      exact hno
    have heT : e ∉ T := by
      intro het
      have := hfar e het
      simp [dist_self] at this
      linarith
    have hnew : insert e T ∈ Good := by
      constructor
      · exact insert_subset he hT.1.1
      · intro x hx y hy hxy
        rcases (mem_insert_iff.mp hx) with rfl | hxT
        · rcases (mem_insert_iff.mp hy) with rfl | hyT
          · exact (hxy rfl).elim
          · exact hfar y hyT
        · rcases (mem_insert_iff.mp hy) with rfl | hyT
          · simpa [dist_comm] using hfar x hxT
          · exact hT.1.2 x hxT y hyT hxy
    have hsubset : insert e T ⊆ T := hT.2 hnew (subset_insert e T)
    exact heT (hsubset (mem_insert e T))
  exact ⟨T, hT.1.1, hS.subset hT.1.1, hT.1.2, hcover⟩


 
theorem cap_subset_seven {y y' : ℂ} {H h : ℝ}
    (hH : H < h) (hy : dist y y' < 6 * h) :
    closedBall y H ⊆ ball y' (7 * h) := by
  intro z hz
  have hz' : dist z y ≤ H := hz
  have htri := dist_triangle z y y'
  show dist z y' < 7 * h
  linarith

 
theorem triple_reach_disjoint {y y' : ℂ} {H H' h : ℝ}
    (hH : H < h) (hH' : H' < h)
    (hsep : 6 * h ≤ dist y y') :
    Disjoint (closedBall y (3 * H)) (closedBall y' (3 * H')) := by
  apply closedBall_disjoint_closedBall
  linarith


end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

open Set Metric

 


theorem first_hit_inside_open_collar {P : ℝ → ℂ} {a b R : ℝ} {y : ℂ}
    {K : Set ℂ} (hP : ContinuousOn P (Icc a b))
    (hK : IsClosed K) (haK : P a ∉ K)
    (hHit : ∃ t ∈ Icc a b, P t ∈ K)
    (hKB : K ⊆ ball y R)
    (hBarrier : ∀ s ∈ Icc a b, R ≤ dist (P s) y →
      ∃ t ∈ Icc a s, P t ∈ K) :
    ∃ t ∈ Icc a b, P t ∈ K ∧ a < t ∧
      (∀ s ∈ Ico a t, P s ∉ K) ∧ MapsTo P (Icc a t) (ball y R) := by
  obtain ⟨t, ht, htK, hno⟩ :=
    LQGMetric.MetricGeometry.exists_first_hit hP hK hHit
  have hat : a < t :=
    lt_of_le_of_ne ht.1 (Ne.symm (fun h => haK (h ▸ htK)))
  refine ⟨t, ht, htK, hat, hno, ?_⟩
  intro s hs
  rcases hs.2.eq_or_lt with heq | hlt
  · rw [heq]
    exact hKB htK
  · by_contra hnot
    have hR : R ≤ dist (P s) y := le_of_not_gt hnot
    obtain ⟨v, hv, hvK⟩ := hBarrier s ⟨hs.1, hs.2.trans ht.2⟩ hR
    exact hno v ⟨hv.1, hv.2.trans_lt hlt⟩ hvK


end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

open Set Metric MeasureTheory Complex

 

theorem circle_chord_lower {R ψ θ : ℝ} (hR : 0 < R)
    (hθ : θ ∈ Icc (ψ - Real.pi) (ψ + Real.pi)) :
    (2 * R / Real.pi) * |θ - ψ| ≤
      ‖(R : ℂ) * cexp (θ * I) - (R : ℂ) * cexp (ψ * I)‖ := by
  have hnorm : ‖(R : ℂ) * cexp (θ * I) - (R : ℂ) * cexp (ψ * I)‖ =
      R * ‖cexp ((θ - ψ) * I) - 1‖ := by
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    have heq : cexp (θ * I) - cexp (ψ * I) =
        cexp (ψ * I) * (cexp ((θ - ψ) * I) - 1) := by
      have hprod : cexp (ψ * I) * cexp ((θ - ψ) * I) = cexp (θ * I) := by
        rw [← Complex.exp_add]
        congr 1
        ring_nf
      rw [mul_sub, mul_one, hprod]
    rw [heq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [hnorm]
  have hangle : |(θ - ψ) / 2| ≤ Real.pi / 2 := by
    rw [abs_le]
    constructor <;> linarith [hθ.1, hθ.2]
  have hsin := Real.mul_abs_le_abs_sin hangle
  have hchord : ‖cexp ((θ - ψ) * I) - 1‖ =
      2 * |Real.sin ((θ - ψ) / 2)| := by
    convert Complex.norm_exp_I_mul_ofReal_sub_one (θ - ψ) using 1 <;>
      simp [Complex.ofReal_sub, mul_comm, Real.norm_eq_abs]
  rw [hchord]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hhalf : |(θ - ψ) / 2| = |θ - ψ| / 2 := by rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [hhalf] at hsin
  have hres : (2 / Real.pi) * |θ - ψ| ≤ 2 * |Real.sin ((θ - ψ) / 2)| := by
    nlinarith [hsin]
  have := mul_le_mul_of_nonneg_left hres hR.le
  calc
    (2 * R / Real.pi) * |θ - ψ| = R * ((2 / Real.pi) * |θ - ψ|) := by ring
    _ ≤ R * (2 * |Real.sin ((θ - ψ) / 2)|) := this

 


theorem circle_cap_outer_bound {c : ℂ} {R ψ h : ℝ}
    (hR : 0 < R) (_hh : 0 ≤ h) :
    ENNReal.ofReal R * volume
      {θ ∈ Ico (ψ - Real.pi) (ψ + Real.pi) |
        ‖(c + (R : ℂ) * cexp (θ * I)) -
          (c + (R : ℂ) * cexp (ψ * I))‖ ≤ h} ≤ ENNReal.ofReal (Real.pi * h) := by
  let cap : Set ℝ := {θ ∈ Ico (ψ - Real.pi) (ψ + Real.pi) |
        ‖(c + (R : ℂ) * cexp (θ * I)) -
          (c + (R : ℂ) * cexp (ψ * I))‖ ≤ h}
  have hcap : cap ⊆ Icc (ψ - Real.pi * h / (2 * R)) (ψ + Real.pi * h / (2 * R)) := by
    intro θ hθ
    have hangle : θ ∈ Icc (ψ - Real.pi) (ψ + Real.pi) := ⟨hθ.1.1, hθ.1.2.le⟩
    have hchord := circle_chord_lower hR hangle
    have hdist : ‖(R : ℂ) * cexp (θ * I) - (R : ℂ) * cexp (ψ * I)‖ ≤ h := by
      convert hθ.2 using 1; ring
    have hpi : 0 < Real.pi := Real.pi_pos
    have hangle' : |θ - ψ| ≤ Real.pi * h / (2 * R) := by
      have hcoef : 0 < 2 * R / Real.pi := by positivity
      calc
        |θ - ψ| ≤ h / (2 * R / Real.pi) :=
          (le_div_iff₀ hcoef).2 (by simpa [mul_comm] using hchord.trans hdist)
        _ = Real.pi * h / (2 * R) := by field_simp
    obtain ⟨hlo, hhi⟩ := abs_le.mp hangle'
    exact ⟨by linarith, by linarith⟩
  calc
    ENNReal.ofReal R * volume cap ≤
        ENNReal.ofReal R * volume (Icc (ψ - Real.pi * h / (2 * R))
          (ψ + Real.pi * h / (2 * R))) := by gcongr
    _ = ENNReal.ofReal R * ENNReal.ofReal (Real.pi * h / R) := by
      rw [Real.volume_Icc]
      congr 1
      field_simp
      ring_nf
    _ = ENNReal.ofReal (Real.pi * h) := by
      rw [← ENNReal.ofReal_mul hR.le]
      congr 1
      field_simp


end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

open Set Metric

 


theorem finite_radial_cap_cover {P : ℝ → ℂ} {c : ℂ} {R a b δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) {S : Set (ℝ × ℝ)}
    (hS : ∀ e ∈ S, a ≤ e.1 ∧ δ ≤ e.2 - e.1 ∧ e.2 ≤ b ∧
      ‖P e.1 - c‖ = R ∧ ‖P e.2 - c‖ = R ∧
      ∀ t ∈ Ioo e.1 e.2, R < ‖P t - c‖)
    (H : ℝ × ℝ → ℝ)
    (hReach : ∀ e ∈ S, ∀ t ∈ Icc e.1 e.2, ‖P t - P e.1‖ ≤ H e)
    {W : Set ℂ}
    (hWitness : ∀ w ∈ W, ∃ e ∈ S, ∃ t ∈ Icc e.1 e.2,
      R ≤ ‖P t - c‖ ∧ w = LQGMetric.Topo.Crosscut.rproj c R (P t)) :
    S.Finite ∧ W ⊆ ⋃ e ∈ S, sphere c R ∩ closedBall (P e.1) (H e) := by
  have hfinite : S.Finite :=
    finite_maximal_exterior_excursions (f := fun t => ‖P t - c‖) hδ hS
  refine ⟨hfinite, ?_⟩
  intro w hw
  obtain ⟨e, he, t, ht, htR, rfl⟩ := hWitness w hw
  have hy : P e.1 ∈ sphere c R := by
    rw [mem_sphere, dist_eq_norm]
    exact (hS e he).2.2.2.1
  have hzc : P t ≠ c := by
    intro h
    rw [h, sub_self, norm_zero] at htR
    linarith
  have hwS : LQGMetric.Topo.Crosscut.rproj c R (P t) ∈ sphere c R :=
    LQGMetric.Topo.Crosscut.rproj_mem_sphere hR.le hzc
  have hcap : ‖LQGMetric.Topo.Crosscut.rproj c R (P t) - P e.1‖ ≤ H e :=
    (norm_rproj_sub_le hR hy htR).trans (hReach e he t ht)
  exact mem_iUnion.2 ⟨e, mem_iUnion.2 ⟨he, ⟨hwS, by simpa [mem_closedBall, dist_eq_norm] using hcap⟩⟩⟩


end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

open Set Metric LQGMetric.MetricGeometry

 



theorem splice_first_hit_back {X : Type*} [PseudoEMetricSpace X]
    {U : Set X} {P : ℝ → X} {u : X} {a b s t₁ L q : ℝ} {A C : ENNReal}
    (has : a ≤ s) (hsb : s ≤ b) (hs0 : 0 ≤ s) (hst : s < t₁)
    (htL : t₁ ≤ L) (_hq : 0 < q) (hsmall : t₁ - s < 2 * q)
    (hP : ContinuousOn P (Icc s t₁)) (hU : MapsTo P (Icc s t₁) U)
    (hunit : HasUnitSpeedOn P (Icc 0 L))
    (hattach : internalEDist U (P t₁) u ≤ A)
    (hbudget : A + ENNReal.ofReal (2 * q) ≤ C) :
    ∃ t ∈ Icc a b, internalEDist U (P t) u ≤ C := by
  rcases le_or_gt t₁ b with ht₁b | hbt₁
  · refine ⟨t₁, ⟨has.trans hst.le, ht₁b⟩, ?_⟩
    exact hattach.trans ((le_add_right le_rfl).trans hbudget)
  · have hbt : b ≤ t₁ := hbt₁.le
    have hbI : Icc b t₁ ⊆ Icc s t₁ := Icc_subset_Icc hsb le_rfl
    have hb0 : b ∈ Icc 0 L := ⟨hs0.trans hsb, hbt.trans htL⟩
    have ht0 : t₁ ∈ Icc 0 L := ⟨hs0.trans hst.le, htL⟩
    have hlen : internalEDist U (P b) (P t₁) ≤ ENNReal.ofReal (t₁ - b) := by
      calc
        internalEDist U (P b) (P t₁) ≤ curveLength P b t₁ :=
          internalEDist_le_curveLength hbt (hP.mono hbI) (hU.mono_left hbI)
        _ = ENNReal.ofReal (t₁ - b) := curveLength_of_hasUnitSpeedOn hunit hb0 ht0
    have htime : ENNReal.ofReal (t₁ - b) ≤ ENNReal.ofReal (2 * q) := by
      apply ENNReal.ofReal_le_ofReal
      linarith
    refine ⟨b, ⟨has.trans hsb, le_rfl⟩, ?_⟩
    calc
      internalEDist U (P b) u ≤
          internalEDist U (P b) (P t₁) + internalEDist U (P t₁) u :=
        internalEDist_triangle U _ _ _
      _ ≤ ENNReal.ofReal (2 * q) + A := add_le_add (hlen.trans htime) hattach
      _ = A + ENNReal.ofReal (2 * q) := add_comm _ _
      _ ≤ C := hbudget


end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

open Set Metric

 


theorem first_separator_hit_inside_collar {P : ℝ → ℂ} {a b r R : ℝ}
    {y : ℂ} {K : Set ℂ} (hab : a ≤ b) (hrR : r ≤ R)
    (hP : ContinuousOn P (Icc a b)) (hK : IsClosed K)
    (hSep : LQGMetric.Disconnects K (sphere y r) (sphere y R))
    (hKB : K ⊆ ball y R)
    (ha : P a ∈ closedBall y r) (hb : P b ∈ (ball y R)ᶜ)
    (haK : P a ∉ K) :
    ∃ t ∈ Icc a b, P t ∈ K ∧ a < t ∧
      (∀ s ∈ Ico a t, P s ∉ K) ∧ MapsTo P (Icc a t) (ball y R) := by
  have hSep' : LQGMetric.Disconnects K (closedBall y r) (ball y R)ᶜ :=
    LQGMetric.Disconnects.closedBall_compl_ball hrR hSep
  have hhit : ∃ t ∈ Icc a b, P t ∈ K := by
    obtain ⟨z, hzPath, hzK⟩ := hSep' (P a) (P b)
      (LQGMetric.pathOfIcc P hab hP) ha hb
    obtain ⟨t, ht, hzt⟩ :=
      LQGMetric.range_pathOfIcc_subset P hab hP hzPath
    exact ⟨t, ht, hzt ▸ hzK⟩
  apply first_hit_inside_open_collar hP hK haK hhit hKB
  intro s hs hsR
  have has : a ≤ s := hs.1
  have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc le_rfl hs.2
  obtain ⟨z, hzPath, hzK⟩ := hSep' (P a) (P s)
    (LQGMetric.pathOfIcc P has (hP.mono hsub)) ha (by simpa [mem_compl_iff, mem_ball] using hsR)
  obtain ⟨t, ht, hzt⟩ :=
    LQGMetric.range_pathOfIcc_subset P has (hP.mono hsub) hzPath
  exact ⟨t, ht, hzt ▸ hzK⟩


end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

open Set Metric

 

theorem exists_excursion_reach {P : ℝ → ℂ} {a b α β : ℝ}
    (hP : ContinuousOn P (Icc a b)) (haα : a ≤ α) (hαβ : α ≤ β)
    (hβb : β ≤ b) :
    ∃ H : ℝ, 0 ≤ H ∧
      (∀ t ∈ Icc α β, ‖P t - P α‖ ≤ H) ∧
      ∃ t ∈ Icc α β, ‖P t - P α‖ = H := by
  have hsub : Icc α β ⊆ Icc a b := Icc_subset_Icc haα hβb
  have hcont : ContinuousOn (fun t => ‖P t - P α‖) (Icc α β) :=
    ((hP.mono hsub).sub continuousOn_const).norm
  obtain ⟨t, ht, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hαβ) hcont
  refine ⟨‖P t - P α‖, norm_nonneg _, ?_, t, ht, rfl⟩
  intro s hs
  exact hmax hs


end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

open Set Metric MeasureTheory Complex

 


noncomputable def circleOuter (c : ℂ) (R : NNReal) (θ₀ : ℝ) (S : Set ℂ) : ENNReal :=
  ENNReal.ofReal (R : ℝ) * volume
    {θ ∈ Ico θ₀ (θ₀ + 2 * Real.pi) |
      c + (R : ℂ) * cexp (θ * I) ∈ S}

 
theorem circleOuter_mono {c : ℂ} {R : NNReal} {θ₀ : ℝ} {S T : Set ℂ}
    (hST : S ⊆ T) : circleOuter c R θ₀ S ≤ circleOuter c R θ₀ T := by
  unfold circleOuter
  gcongr

 
theorem circleOuter_union_le (c : ℂ) (R : NNReal) (θ₀ : ℝ) (S T : Set ℂ) :
    circleOuter c R θ₀ (S ∪ T) ≤
      circleOuter c R θ₀ S + circleOuter c R θ₀ T := by
  unfold circleOuter
  let A : Set ℝ := {θ ∈ Ico θ₀ (θ₀ + 2 * Real.pi) |
      c + (R : ℂ) * cexp (θ * I) ∈ S}
  let B : Set ℝ := {θ ∈ Ico θ₀ (θ₀ + 2 * Real.pi) |
      c + (R : ℂ) * cexp (θ * I) ∈ T}
  have hU : {θ ∈ Ico θ₀ (θ₀ + 2 * Real.pi) |
      c + (R : ℂ) * cexp (θ * I) ∈ S ∪ T} = A ∪ B := by
    ext θ
    simp [A, B, and_or_left]
  rw [hU]
  calc
    ENNReal.ofReal (R : ℝ) * volume (A ∪ B) ≤
        ENNReal.ofReal (R : ℝ) * (volume A + volume B) := by
      gcongr
      exact measure_union_le A B
    _ = ENNReal.ofReal (R : ℝ) * volume A + ENNReal.ofReal (R : ℝ) * volume B :=
      mul_add _ _ _


end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

open Set Metric MeasureTheory Complex

 
theorem circleOuter_sphere (c : ℂ) (R : NNReal) (θ₀ : ℝ) :
    circleOuter c R θ₀ (sphere c (R : ℝ)) =
      ENNReal.ofReal (R : ℝ) * ENNReal.ofReal (2 * Real.pi) := by
  unfold circleOuter
  have hmem : ∀ θ : ℝ, c + (R : ℂ) * cexp (θ * I) ∈ sphere c (R : ℝ) := by
    intro θ
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul,
      Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact abs_of_nonneg (NNReal.coe_nonneg R)
  have hset : {θ ∈ Ico θ₀ (θ₀ + 2 * Real.pi) |
      c + (R : ℂ) * cexp (θ * I) ∈ sphere c (R : ℝ)} =
      Ico θ₀ (θ₀ + 2 * Real.pi) := by
    ext θ
    exact ⟨fun h => h.1, fun h => ⟨h, hmem θ⟩⟩
  rw [hset, Real.volume_Ico]
  congr 1
  ring


end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

open Set Metric MeasureTheory Complex

 

theorem radial_angle_preimage {c : ℂ} {R₀ R₁ : NNReal} {θ₀ : ℝ} {S : Set ℂ}
    (hR₀ : 0 < R₀) (hR₁ : 0 < R₁) :
    {θ ∈ Ico θ₀ (θ₀ + 2 * Real.pi) |
      c + (R₁ : ℂ) * cexp (θ * I) ∈
        (fun z : ℂ => c + ((R₁ : ℂ) / (R₀ : ℂ)) * (z - c)) '' S} =
    {θ ∈ Ico θ₀ (θ₀ + 2 * Real.pi) |
      c + (R₀ : ℂ) * cexp (θ * I) ∈ S} := by
  have h₀ : (R₀ : ℂ) ≠ 0 := by exact_mod_cast hR₀.ne'
  have h₁ : (R₁ : ℂ) ≠ 0 := by exact_mod_cast hR₁.ne'
  let T : ℂ → ℂ := fun z => c + ((R₁ : ℂ) / (R₀ : ℂ)) * (z - c)
  have hformula (θ : ℝ) : T (c + (R₀ : ℂ) * cexp (θ * I)) =
      c + (R₁ : ℂ) * cexp (θ * I) := by
    dsimp [T]
    field_simp
    ring
  have hinj : Function.Injective T := by
    intro z w h
    have hmul : ((R₁ : ℂ) / (R₀ : ℂ)) * (z - c) =
        ((R₁ : ℂ) / (R₀ : ℂ)) * (w - c) := add_left_cancel h
    have hsub : z - c = w - c := mul_left_cancel₀ (div_ne_zero h₁ h₀) hmul
    linear_combination hsub
  ext θ
  constructor
  · rintro ⟨hθ, z, hz, hzeq⟩
    have hz' : z = c + (R₀ : ℂ) * cexp (θ * I) :=
      hinj (hzeq.trans (hformula θ).symm)
    exact ⟨hθ, hz' ▸ hz⟩
  · rintro ⟨hθ, hS⟩
    exact ⟨hθ, c + (R₀ : ℂ) * cexp (θ * I), hS, hformula θ⟩

 

theorem circleOuter_radial_cross_mul {c : ℂ} {R₀ R₁ : NNReal}
    {θ₀ : ℝ} {S : Set ℂ} (hR₀ : 0 < R₀) (hR₁ : 0 < R₁) :
    ENNReal.ofReal (R₀ : ℝ) *
      circleOuter c R₁ θ₀
        ((fun z : ℂ => c + ((R₁ : ℂ) / (R₀ : ℂ)) * (z - c)) '' S) =
    ENNReal.ofReal (R₁ : ℝ) * circleOuter c R₀ θ₀ S := by
  unfold circleOuter
  rw [radial_angle_preimage hR₀ hR₁]
  ac_rfl


end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

open Set Metric MeasureTheory Complex

 


theorem circleOuter_radial_le_two {c : ℂ} {R₀ R₁ : NNReal}
    {θ₀ : ℝ} {S : Set ℂ} (hR₀ : 0 < R₀) (hR₁ : 0 < R₁)
    (hR : R₁ ≤ 2 * R₀) :
    circleOuter c R₁ θ₀
      ((fun z : ℂ => c + ((R₁ : ℂ) / (R₀ : ℂ)) * (z - c)) '' S) ≤
      2 * circleOuter c R₀ θ₀ S := by
  unfold circleOuter
  rw [radial_angle_preimage hR₀ hR₁]
  have hreal : (R₁ : ℝ) ≤ 2 * (R₀ : ℝ) := by exact_mod_cast hR
  calc
    ENNReal.ofReal (R₁ : ℝ) * volume
        {θ ∈ Ico θ₀ (θ₀ + 2 * Real.pi) |
          c + (R₀ : ℂ) * cexp (θ * I) ∈ S} ≤
      ENNReal.ofReal (2 * (R₀ : ℝ)) * volume
        {θ ∈ Ico θ₀ (θ₀ + 2 * Real.pi) |
          c + (R₀ : ℂ) * cexp (θ * I) ∈ S} := by gcongr
    _ = 2 * (ENNReal.ofReal (R₀ : ℝ) * volume
        {θ ∈ Ico θ₀ (θ₀ + 2 * Real.pi) |
          c + (R₀ : ℂ) * cexp (θ * I) ∈ S}) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
      rw [mul_assoc]


end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

open Set Metric MeasureTheory Complex

 

theorem circleOuter_good_radial_complement {c : ℂ} {R₀ R₁ : NNReal}
    {θ₀ lam s₀ : ℝ} {G N : Set ℂ}
    (hR₀ : 0 < R₀) (hR₁ : 0 < R₁) (hR : R₁ ≤ 2 * R₀)
    (hlam : 0 ≤ lam) (hs₀ : 0 ≤ s₀)
    (hbad : circleOuter c R₀ θ₀ (sphere c (R₀ : ℝ) \ G) ≤
      ENNReal.ofReal (lam * s₀ / 2))
    (hnear : circleOuter c R₀ θ₀ N ≤ ENNReal.ofReal (lam * s₀)) :
    circleOuter c R₁ θ₀
      (sphere c (R₁ : ℝ) \ ((fun z : ℂ =>
        c + ((R₁ : ℂ) / (R₀ : ℂ)) * (z - c)) '' (G \ N))) ≤
      ENNReal.ofReal (3 * lam * s₀) := by
  let T : ℂ → ℂ := fun z => c + ((R₁ : ℂ) / (R₀ : ℂ)) * (z - c)
  let B : Set ℂ := (sphere c (R₀ : ℝ) \ G) ∪ N
  have h₀ : (R₀ : ℂ) ≠ 0 := by exact_mod_cast hR₀.ne'
  have hformula (θ : ℝ) : T (c + (R₀ : ℂ) * cexp (θ * I)) =
      c + (R₁ : ℂ) * cexp (θ * I) := by
    dsimp [T]
    field_simp
    ring
  have hfirst : circleOuter c R₁ θ₀ (sphere c (R₁ : ℝ) \ T '' (G \ N)) ≤
      circleOuter c R₁ θ₀ (T '' B) := by
    unfold circleOuter
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply measure_mono
    intro θ hθ
    obtain ⟨hwin, _, hnot⟩ := hθ
    have hx : c + (R₀ : ℂ) * cexp (θ * I) ∈ sphere c (R₀ : ℝ) := by
      rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact abs_of_nonneg (NNReal.coe_nonneg R₀)
    have hnotGN : c + (R₀ : ℂ) * cexp (θ * I) ∉ G \ N := by
      intro h
      exact hnot ⟨_, h, hformula θ⟩
    have hB : c + (R₀ : ℂ) * cexp (θ * I) ∈ B := by
      by_cases hg : c + (R₀ : ℂ) * cexp (θ * I) ∈ G
      · right
        by_contra hn
        exact hnotGN ⟨hg, hn⟩
      · exact Or.inl ⟨hx, hg⟩
    exact ⟨hwin, _, hB, hformula θ⟩
  have hscale : circleOuter c R₁ θ₀ (T '' B) ≤ 2 * circleOuter c R₀ θ₀ B :=
    circleOuter_radial_le_two hR₀ hR₁ hR
  have hsub : circleOuter c R₀ θ₀ B ≤
      circleOuter c R₀ θ₀ (sphere c (R₀ : ℝ) \ G) + circleOuter c R₀ θ₀ N :=
    circleOuter_union_le c R₀ θ₀ _ _
  have htwo : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_num
  have hnum : (2 : ENNReal) *
      (ENNReal.ofReal (lam * s₀ / 2) + ENNReal.ofReal (lam * s₀)) =
      ENNReal.ofReal (3 * lam * s₀) := by
    rw [htwo, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  calc
    circleOuter c R₁ θ₀ (sphere c (R₁ : ℝ) \ T '' (G \ N)) ≤
      circleOuter c R₁ θ₀ (T '' B) := hfirst
    _ ≤ 2 * circleOuter c R₀ θ₀ B := hscale
    _ ≤ 2 * (circleOuter c R₀ θ₀ (sphere c (R₀ : ℝ) \ G) +
        circleOuter c R₀ θ₀ N) := mul_le_mul_of_nonneg_left hsub (by positivity)
    _ ≤ 2 * (ENNReal.ofReal (lam * s₀ / 2) + ENNReal.ofReal (lam * s₀)) :=
      mul_le_mul_of_nonneg_left (add_le_add hbad hnear) (by positivity)
    _ = ENNReal.ofReal (3 * lam * s₀) := hnum


end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

open Set Metric MeasureTheory Complex

 

theorem circleOuter_cap_centered {c : ℂ} {R : NNReal} {ψ h : ℝ}
    (hR : 0 < R) (hh : 0 ≤ h) :
    circleOuter c R (ψ - Real.pi)
      (sphere c (R : ℝ) ∩ closedBall
        (c + (R : ℂ) * cexp (ψ * I)) h) ≤
      ENNReal.ofReal (Real.pi * h) := by
  have hRreal : 0 < (R : ℝ) := hR
  have hcap := circle_cap_outer_bound (c := c) (R := (R : ℝ)) (ψ := ψ) (h := h)
    hRreal hh
  unfold circleOuter
  have hwin : (ψ - Real.pi) + 2 * Real.pi = ψ + Real.pi := by ring
  rw [hwin]
  have hset : {θ ∈ Ico (ψ - Real.pi) (ψ + Real.pi) |
      c + (R : ℂ) * cexp (θ * I) ∈
        sphere c (R : ℝ) ∩ closedBall (c + (R : ℂ) * cexp (ψ * I)) h} =
      {θ ∈ Ico (ψ - Real.pi) (ψ + Real.pi) |
        ‖(c + (R : ℂ) * cexp (θ * I)) -
          (c + (R : ℂ) * cexp (ψ * I))‖ ≤ h} := by
    ext θ
    simp only [mem_setOf_eq, mem_inter_iff, mem_closedBall, dist_eq_norm]
    constructor
    · rintro ⟨hθ, _, hc⟩
      exact ⟨hθ, hc⟩
    · rintro ⟨hθ, hc⟩
      have hs : c + (R : ℂ) * cexp (θ * I) ∈ sphere c (R : ℝ) := by
        rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one]
        exact abs_of_nonneg (NNReal.coe_nonneg R)
      exact ⟨hθ, hs, hc⟩
  rw [hset]
  exact hcap


 

theorem circleOuter_cap {c : ℂ} {R : NNReal} {ψ h θ₀ : ℝ}
    (hR : 0 < R) (hh : 0 ≤ h) :
    circleOuter c R θ₀
      (sphere c (R : ℝ) ∩ closedBall
        (c + (R : ℂ) * cexp (ψ * I)) h) ≤
      ENNReal.ofReal (Real.pi * h) := by
  let A : Set ℝ := {θ | ‖(c + (R : ℂ) * cexp (θ * I)) -
    (c + (R : ℂ) * cexp (ψ * I))‖ ≤ h}
  have hA : MeasurableSet A := by
    change MeasurableSet ((fun θ : ℝ =>
      ‖(c + (R : ℂ) * cexp (θ * I)) -
        (c + (R : ℂ) * cexp (ψ * I))‖) ⁻¹' Iic h)
    have hc : Continuous (fun θ : ℝ =>
      ‖(c + (R : ℂ) * cexp (θ * I)) -
        (c + (R : ℂ) * cexp (ψ * I))‖) := by fun_prop
    exact measurableSet_Iic.preimage hc.measurable
  have hper : Function.Periodic (fun θ : ℝ => θ ∈ A) (2 * Real.pi) := by
    intro θ
    dsimp [A]
    have hexp : cexp ((((θ + 2 * Real.pi) : ℝ) : ℂ) * I) =
        cexp ((θ : ℂ) * I) := by
      convert Complex.exp_mul_I_periodic θ using 1 <;> push_cast <;> ring
    rw [hexp]
  have hwin := volume_periodic_Ico_eq Real.two_pi_pos hA hper
    θ₀ (ψ - Real.pi)
  have hcenter : (ψ - Real.pi) + 2 * Real.pi = ψ + Real.pi := by ring
  rw [hcenter] at hwin
  have hset (s : ℝ) :
      {θ ∈ Ico s (s + 2 * Real.pi) |
        c + (R : ℂ) * cexp (θ * I) ∈
          sphere c (R : ℝ) ∩ closedBall
            (c + (R : ℂ) * cexp (ψ * I)) h} =
        A ∩ Ico s (s + 2 * Real.pi) := by
    ext θ
    simp only [mem_setOf_eq, mem_inter_iff, mem_closedBall, dist_eq_norm, A]
    constructor
    · rintro ⟨hs, _, hh'⟩
      exact ⟨hh', hs⟩
    · rintro ⟨hh', hs⟩
      have hcircle : c + (R : ℂ) * cexp (θ * I) ∈ sphere c (R : ℝ) := by
        rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one]
        exact abs_of_nonneg (NNReal.coe_nonneg R)
      exact ⟨hs, hcircle, hh'⟩
  have hwin' : circleOuter c R θ₀
      (sphere c (R : ℝ) ∩ closedBall
        (c + (R : ℂ) * cexp (ψ * I)) h) =
      circleOuter c R (ψ - Real.pi)
      (sphere c (R : ℝ) ∩ closedBall
        (c + (R : ℂ) * cexp (ψ * I)) h) := by
    unfold circleOuter
    rw [hset θ₀, hset (ψ - Real.pi), hcenter, hwin]
  rw [hwin']
  exact circleOuter_cap_centered hR hh


 
theorem circleOuter_cap_at_sphere {c y : ℂ} {R : NNReal} {h θ₀ : ℝ}
    (hR : 0 < R) (hy : y ∈ sphere c (R : ℝ)) (hh : 0 ≤ h) :
    circleOuter c R θ₀ (sphere c (R : ℝ) ∩ closedBall y h) ≤
      ENNReal.ofReal (Real.pi * h) := by
  have hnorm : ‖y - c‖ = (R : ℝ) := by
    simpa [mem_sphere, dist_eq_norm, dist_comm] using hy
  have hparam : y = c + (R : ℂ) * cexp (Complex.arg (y - c) * I) := by
    have h := Complex.norm_mul_exp_arg_mul_I (y - c)
    rw [hnorm] at h
    exact (eq_add_of_sub_eq' h.symm)
  rw [hparam]
  exact circleOuter_cap hR hh


 
theorem circleOuter_finset_iUnion_le {ι : Type*} (s : Finset ι)
    (F : ι → Set ℂ) (c : ℂ) (R : NNReal) (θ₀ : ℝ) :
    circleOuter c R θ₀ (⋃ i ∈ s, F i) ≤
      ∑ i ∈ s, circleOuter c R θ₀ (F i) := by
  unfold circleOuter
  have hset : {θ ∈ Ico θ₀ (θ₀ + 2 * Real.pi) |
      c + (R : ℂ) * cexp (θ * I) ∈ ⋃ i ∈ s, F i} =
      ⋃ i ∈ s, {θ ∈ Ico θ₀ (θ₀ + 2 * Real.pi) |
        c + (R : ℂ) * cexp (θ * I) ∈ F i} := by
    ext θ
    simp only [mem_setOf_eq, mem_iUnion, mem_Ico]
    aesop
  rw [hset]
  calc
    ENNReal.ofReal (R : ℝ) * volume
        (⋃ i ∈ s, {θ ∈ Ico θ₀ (θ₀ + 2 * Real.pi) |
          c + (R : ℂ) * cexp (θ * I) ∈ F i}) ≤
      ENNReal.ofReal (R : ℝ) *
        ∑ i ∈ s, volume
          {θ ∈ Ico θ₀ (θ₀ + 2 * Real.pi) |
            c + (R : ℂ) * cexp (θ * I) ∈ F i} := by
      gcongr
      exact measure_biUnion_finset_le s _
    _ = ∑ i ∈ s, ENNReal.ofReal (R : ℝ) * volume
        {θ ∈ Ico θ₀ (θ₀ + 2 * Real.pi) |
          c + (R : ℂ) * cexp (θ * I) ∈ F i} := by
      rw [Finset.mul_sum]


 

theorem finite_greedy_cap_measure {ι : Type*} {S : Set ι} (hS : S.Finite)
    (center : ι → ℂ) (H : ι → ℝ) {c : ℂ} {R : NNReal} {θ₀ h : ℝ}
    (hR : 0 < R) (hh : 0 < h)
    (hc : ∀ e ∈ S, center e ∈ sphere c (R : ℝ))
    (hH : ∀ e ∈ S, H e < h) :
    ∃ T : Finset ι, (↑T : Set ι) ⊆ S ∧
      (∀ e ∈ T, ∀ e' ∈ T, e ≠ e' →
        6 * h ≤ dist (center e) (center e')) ∧
      (∀ e ∈ S, ∃ e' ∈ T, dist (center e) (center e') < 6 * h) ∧
      circleOuter c R θ₀
        (⋃ e ∈ S, sphere c (R : ℝ) ∩ closedBall (center e) (H e)) ≤
        ∑ _e ∈ T, ENNReal.ofReal (Real.pi * (7 * h)) := by
  classical
  obtain ⟨T₀, hTS, hTf, hsep, hcover⟩ :=
    finite_greedy_centers hS center hh
  let T := hTf.toFinset
  have hTmem (e : ι) : e ∈ T ↔ e ∈ T₀ := by simp [T]
  have hsub :
      (⋃ e ∈ S, sphere c (R : ℝ) ∩ closedBall (center e) (H e)) ⊆
      ⋃ e ∈ T, sphere c (R : ℝ) ∩ closedBall (center e) (7 * h) := by
    intro z hz
    obtain ⟨e, he, hz⟩ := mem_iUnion₂.mp hz
    obtain ⟨e', he'T, hnear⟩ := hcover e he
    have hball : z ∈ closedBall (center e') (7 * h) :=
      (ball_subset_closedBall (cap_subset_seven (hH e he) hnear hz.2))
    exact mem_iUnion₂.mpr ⟨e', (hTmem e').2 he'T, ⟨hz.1, hball⟩⟩
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · intro e he
    exact hTS ((hTmem e).1 he)
  · intro e he e' he' hne
    exact hsep e ((hTmem e).1 he) e' ((hTmem e').1 he') hne
  · intro e he
    obtain ⟨e', he', hnear⟩ := hcover e he
    exact ⟨e', (hTmem e').2 he', hnear⟩
  · calc
      circleOuter c R θ₀
          (⋃ e ∈ S, sphere c (R : ℝ) ∩ closedBall (center e) (H e)) ≤
        circleOuter c R θ₀
          (⋃ e ∈ T, sphere c (R : ℝ) ∩ closedBall (center e) (7 * h)) :=
        circleOuter_mono hsub
      _ ≤ ∑ e ∈ T, circleOuter c R θ₀
          (sphere c (R : ℝ) ∩ closedBall (center e) (7 * h)) :=
        circleOuter_finset_iUnion_le T _ c R θ₀
      _ ≤ ∑ _e ∈ T, ENNReal.ofReal (Real.pi * (7 * h)) := by
        apply Finset.sum_le_sum
        intro e he
        exact circleOuter_cap_at_sphere hR (hc e (hTS ((hTmem e).1 he)))
          (by positivity)


end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow
