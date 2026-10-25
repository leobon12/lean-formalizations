import SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour.FiniteTour
import LQGMetric.Topo.Shortcut




 





set_option autoImplicit false
noncomputable section
open Set unitInterval
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour
open LQGMetric.MetricGeometry

 
def metricPath (D : LSCMetric) (P : ℝ → ℂ) {a b : ℝ}
    (hP : D.IsCurve P a b) : Path (D.pt (P a)) (D.pt (P b)) :=
  { toFun := fun t => D.pt (P (a + (b-a)*(t:ℝ)))
    continuous_toFun := by
      refine hP.2.comp_continuous (by fun_prop) fun t => ?_
      have h0 := t.2.1
      have h1 := t.2.2
      constructor <;> nlinarith [hP.1]
    source' := by simp
    target' := by simp }

theorem metricPath_range (D : LSCMetric) (P : ℝ → ℂ) {a b : ℝ}
    (hP : D.IsCurve P a b) :
    range (metricPath D P hP) = P '' Icc a b := by
  apply Subset.antisymm
  · rintro z ⟨t, rfl⟩
    refine ⟨a + (b-a)*(t:ℝ), ?_, rfl⟩
    have h0 := t.2.1
    have h1 := t.2.2
    constructor <;> nlinarith [hP.1]
  · rintro z ⟨s, hs, rfl⟩
    by_cases heq : a = b
    · have hsa : s = a := le_antisymm (heq ▸ hs.2) hs.1
      subst s
      refine ⟨0, ?_⟩
      change P (a + (b-a)*((0:unitInterval):ℝ)) = P a
      simp
    · have hlt : a < b := lt_of_le_of_ne hP.1 heq
      have hden : 0 < b-a := sub_pos.mpr hlt
      let v : unitInterval := ⟨(s-a)/(b-a), by
        constructor
        · exact div_nonneg (sub_nonneg.mpr hs.1) hden.le
        · exact (div_le_one hden).mpr (by linarith [hs.2])⟩
      refine ⟨v, ?_⟩
      change P (a + (b-a) * ((v : unitInterval) : ℝ)) = P s
      congr 1
      dsimp [v]
      field_simp
      ring

 
theorem metricPath_length (D : LSCMetric) (P : ℝ → ℂ) {a b : ℝ}
    (hP : D.IsCurve P a b) :
    pathLength (metricPath D P hP) = D.len P a b := by
  let φ : ℝ → ℝ := fun t => a + (b-a)*t
  have hφmono : Monotone φ := fun s t hst => by
    dsimp [φ]
    nlinarith [hP.1]
  unfold pathLength
  rw [curveLength_congr (Q := (D.pt ∘ P) ∘ φ) (by
    intro t ht
    rw [Path.extend_apply _ ht]
    rfl)]
  rw [curveLength_comp_of_continuousOn_monotoneOn _ zero_le_one (by fun_prop)
    (hφmono.monotoneOn _)]
  simp only [φ, mul_zero, add_zero, mul_one]
  have hab : a + (b-a) = b := by ring
  rw [hab]
  rfl

 
theorem path_isCurve (D : LSCMetric) {x y : D.Space} (pi : Path x y) :
    D.IsCurve (fun t : ℝ => (pi.extend t : ℂ)) 0 1 := by
  constructor
  · exact zero_le_one
  · change ContinuousOn pi.extend (Icc 0 1)
    exact pi.continuous_extend.continuousOn

theorem path_len (D : LSCMetric) {x y : D.Space} (pi : Path x y) :
    D.len (fun t : ℝ => (pi.extend t : ℂ)) 0 1 = pathLength pi := rfl

theorem path_trace (D : LSCMetric) {x y : D.Space} (pi : Path x y) :
    (fun t : ℝ => (pi.extend t : ℂ)) '' Icc 0 1 = range pi := by
  exact pi.image_extend_of_subset (Subset.rfl)


 

theorem finite_connected_metric_curves_tour {ι : Type*} [Fintype ι]
    (D : LSCMetric) (P : ι → ℝ → ℂ) (a b : ι → ℝ)
    (hP : ∀ i, D.IsCurve (P i) (a i) (b i)) (hne : Nonempty ι)
    (hconn : ∀ i j : ι, Relation.ReflTransGen
      (fun u v => ((P u) '' Icc (a u) (b u) ∩
        (P v) '' Icc (a v) (b v)).Nonempty) i j) :
    ∃ (pi : ℝ → ℂ) (s t : ℝ), D.IsCurve pi s t ∧
      pi '' Icc s t = ⋃ i : ι, (P i) '' Icc (a i) (b i) ∧
      D.len pi s t ≤ 2 * ∑ i : ι, D.len (P i) (a i) (b i) := by
  let Q (i : ι) : Path (D.pt (P i (a i))) (D.pt (P i (b i))) :=
    metricPath D (P i) (hP i)
  have hreach : ∀ i j : ι,
      Relation.ReflTransGen
        (fun u v => (range (Q u) ∩ range (Q v)).Nonempty) i j := by
    intro i j
    have hstep : (fun u v => ((P u) '' Icc (a u) (b u) ∩
        (P v) '' Icc (a v) (b v)).Nonempty) ≤
        (fun u v => (range (Q u) ∩ range (Q v)).Nonempty) := by
      intro u v huv
      rw [show range (Q u) = (P u) '' Icc (a u) (b u) from metricPath_range D (P u) (hP u),
        show range (Q v) = (P v) '' Icc (a v) (b v) from metricPath_range D (P v) (hP v)]
      exact huv
    exact (Relation.ReflTransGen.mono hstep) i j (hconn i j)
  obtain ⟨x,y,pi,htrace,hlen⟩ := finite_connected_paths_tour Q hne hreach
  refine ⟨fun t => (pi.extend t : ℂ), 0, 1, path_isCurve D pi, ?_, ?_⟩
  · have htraceSet : range pi = ⋃ i : ι, (P i) '' Icc (a i) (b i) := by
      rw [htrace]
      apply iUnion_congr
      intro i
      exact metricPath_range D (P i) (hP i)
    exact (path_trace D pi).trans htraceSet
  · rw [path_len D pi]
    simpa only [Q, metricPath_length] using hlen


end SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour
