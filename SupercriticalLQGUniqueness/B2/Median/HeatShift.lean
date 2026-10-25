import SupercriticalLQGUniqueness.B2.Median.Barrier
import SupercriticalLQGUniqueness.B2.Iface.Statements
import LQGMetric.Papers.DFGPS.L2_12Moll
import LQGMetric.Papers.DFGPS.T12P6B

 






set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Metric
open LQGMetric (DistC addFun ofCont)

namespace SupercriticalLQGUniqueness.B2.Median

 



theorem isGFFPlusBddCont_addFun {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC) (hh : LQGMetric.IsGFFPlusBddCont h P)
    (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M) :
    LQGMetric.IsGFFPlusBddCont (fun ω => addFun (h ω) f) P := by
  obtain ⟨hhmeas, g, hgmeas, hgbdd, hgff⟩ := hh
  refine ⟨(LQGMetric.measurable_addFun_left f).comp hhmeas,
    fun ω => g ω + f, hgmeas.add measurable_const, ?_, ?_⟩
  · intro ω
    obtain ⟨N, hN⟩ := hgbdd ω
    refine ⟨N + M, fun z => ?_⟩
    calc
      |(g ω + f) z| ≤ |g ω z| + |f z| := by
        simpa only [ContinuousMap.add_apply] using abs_add_le (g ω z) (f z)
      _ ≤ N + M := add_le_add (hN z) (hM z)
  · convert hgff using 1
    funext ω
    simp only [addFun, LQGMetric.DFGPS.T12.ofCont_add']
    abel

theorem isHeatSmoothing_addFun {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC)
    (ε : Set.Ioi (0 : ℝ)) (X : Ω → C(ℂ, ℝ))
    (hX : IsHeatSmoothing P h ε X)
    (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M) :
    IsHeatSmoothing P (fun ω => addFun (h ω) f) ε
      (fun ω => X ω + LQGMetric.LFPP.mollCont ε ε.property.ne' f M hM) := by
  intro z
  filter_upwards [hX z] with ω hω
  have hf := LQGMetric.LFPP.tendsto_heatMollify_ofCont f M hM ε.property.ne' z
  have hsum := hω.add hf
  simpa [positiveHeatTrunc, addFun, LQGMetric.LFPP.mollCont,
    ContinuousMap.add_apply] using hsum

 


theorem tendstoUniformlyOn_heatMollify_fixed
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M)
    (R : ℝ) (hR : 0 < R) :
    TendstoUniformlyOn
      (fun n z => LQGMetric.heatMollify (ε n : ℝ) (ofCont f) z)
      ⇑f atTop (closedBall (0 : ℂ) R) := by
  apply LQGMetric.DFGPS.tendstoUniformlyOn_heatMollify_seq
    (fun n => (ε n).property.ne') hε
    (fun _ z => hM z) hM
  · intro R _
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    exact Eventually.of_forall (fun n z hz => by simpa using hη)
  · exact hR

theorem heatMollify_nonneg_of_nonneg
    (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M)
    (hf : ∀ z, 0 ≤ f z) (ε : Set.Ioi (0 : ℝ)) (z : ℂ) :
    0 ≤ LQGMetric.heatMollify (ε : ℝ) (ofCont f) z := by
  rw [LQGMetric.heatMollify_ofCont f M hM _ ε.property.ne' z]
  exact integral_nonneg fun w => mul_nonneg (hf w)
    (LQGMetric.heatKernel_nonneg _ (by positivity) z w)

theorem eventually_heatMollify_ge_on
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M)
    (R : ℝ) (hR : 0 < R) (S : Set ℂ)
    (hS : S ⊆ closedBall (0 : ℂ) R)
    (δ : ℝ) (hδ : 0 < δ)
    (hpart : ∀ z ∈ S, 2 * δ ≤ f z) :
    ∀ᶠ n in atTop, ∀ z ∈ S,
      δ ≤ LQGMetric.heatMollify (ε n : ℝ) (ofCont f) z := by
  have hconv := tendstoUniformlyOn_heatMollify_fixed ε hε f M hM R hR
  have hevent := (Metric.tendstoUniformlyOn_iff.mp hconv) δ hδ
  filter_upwards [hevent] with n hn z hz
  have hclose := hn z (hS hz)
  rw [Real.dist_eq] at hclose
  have hlo := le_abs_self (f z - LQGMetric.heatMollify (ε n : ℝ) (ofCont f) z)
  linarith [hpart z hz]

theorem eventually_penaltyField_heatMollify_ge
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (N : Set ℂ) (ρ : Set.Ioi (0 : ℝ))
    (M : ℝ) (hM : 0 < M) (R : ℝ) (hR : 0 < R) :
    ∀ᶠ n in atTop, ∀ z ∈ closedBall (0 : ℂ) R,
      1 / 2 ≤ distanceRatio N ρ z →
      M / 4 ≤ LQGMetric.heatMollify (ε n : ℝ)
        (ofCont (penaltyField N ρ M)) z := by
  have h := eventually_heatMollify_ge_on ε hε
    (penaltyField N ρ M) M (penaltyField_abs_le N ρ hM.le)
    R hR {z | z ∈ closedBall (0 : ℂ) R ∧ 1 / 2 ≤ distanceRatio N ρ z}
    (fun z hz => hz.1) (M / 4) (by positivity) (by
      intro z hz
      have hlo := penaltyField_ge_half N ρ hM.le hz.2
      linarith)
  filter_upwards [h] with n hn z hz hratio
  exact hn z ⟨hz, hratio⟩

end SupercriticalLQGUniqueness.B2.Median
