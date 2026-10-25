import SupercriticalLQGUniqueness.B2.PfeAxioms.PatchWeylLength
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylBridge
import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.EA1
import SupercriticalLQGUniqueness.B2.PfeWeyl.WeightedPathChain

 













set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
def weylWt (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ)) : D.Space → ℝ :=
  fun z => Real.exp (ξ * f z)

 
def weylWL (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ)) (P : ℝ → ℂ) (a b : ℝ) : ℝ≥0∞ :=
  HigherDimLQGMetric.weightedLength (weylWt D ξ f) (D.pt ∘ P) a b

theorem weylScale_eq_weylDistOn_wt (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hforget : Continuous (PfeWeyl.euclidForget D)) (x y : ℂ) :
    weylScale ξ f D (x, y) =
      HigherDimLQGMetric.weylDistOn (weylWt D ξ f) Set.univ (D.pt x) (D.pt y) := by
  rw [Uniqueness.Toolkit.WeylLength.weylScale_eq_weylDistOn D ξ f hforget]
  rfl

 

theorem weylScale_le_weylWL (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hforget : Continuous (PfeWeyl.euclidForget D)) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) :
    weylScale ξ f D (P a, P b) ≤ weylWL D ξ f P a b := by
  rw [weylScale_eq_weylDistOn_wt D ξ f hforget]
  exact HigherDimLQGMetric.weylDistOn_le_of_curve hP.1 hP.2 (mapsTo_univ _ _)

 
theorem exists_curve_of_weylScale_lt (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hforget : Continuous (PfeWeyl.euclidForget D)) {x y : ℂ} {T : ℝ≥0∞}
    (h : weylScale ξ f D (x, y) < T) :
    ∃ P : ℝ → ℂ, D.IsCurve P 0 1 ∧ P 0 = x ∧ P 1 = y ∧ weylWL D ξ f P 0 1 < T := by
  rw [weylScale_eq_weylDistOn_wt D ξ f hforget] at h
  unfold HigherDimLQGMetric.weylDistOn at h
  simp only [iInf_lt_iff] at h
  obtain ⟨P, hc, h0, h1, -, hlt⟩ := h
  exact ⟨P, ⟨zero_le_one, hc⟩, h0, h1, hlt⟩

 


theorem len_eq_weylWL_of_eqOn (D E : LSCMetric) (ξ : ℝ) (f f' : C(ℂ, ℝ))
    (hforget : Continuous (PfeWeyl.euclidForget D))
    (hE : ∀ p : ℂ × ℂ, E p = weylScale ξ f' D p)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b)
    (hff : ∀ t ∈ Icc a b, f (P t) = f' (P t)) :
    E.len P a b = weylWL D ξ f P a b := by
  have hlenE : E.len P a b =
      HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => weylScale ξ f' D (x, y)) (D.pt ∘ P) a b := by
    rw [E.len_eq_curveLength]
    calc
      LQGMetric.MetricGeometry.curveLength (E.pt ∘ P) a b =
          HigherDimLQGMetric.curveLengthWith (fun x y : D.Space => E (x, y))
            (D.pt ∘ P) a b :=
        (HigherDimLQGMetric.curveLengthWith_edist (E.pt ∘ P) a b).symm
      _ = _ := by congr 1; funext x y; exact hE (x, y)
  have hwf : HigherDimLQGMetric.curveLengthWith
      (fun x y : D.Space => weylScale ξ f' D (x, y)) (D.pt ∘ P) a b =
      HigherDimLQGMetric.weightedLength (weylWt D ξ f') (D.pt ∘ P) a b := by
    convert Uniqueness.Toolkit.WeylLength.weylCurveLength_eq_weightedLength
      D ξ f' hforget hP using 1
    all_goals rfl
  rw [hlenE, hwf]
  unfold weylWL
  apply HigherDimLQGMetric.weightedLength_congr_weight
  intro t ht
  exact congrArg (fun q : ℝ => Real.exp (ξ * q)) (hff t ht).symm

 


theorem weylScale_le_internal_of_eqOn (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f f' : C(ℂ, ℝ)) (hforget : Continuous (PfeWeyl.euclidForget D))
    (hE : ∀ p : ℂ × ℂ, E p = weylScale ξ f' D p) (m : ℝ) (hm : ∀ z, m ≤ f' z)
    {V : Set ℂ} (hff : EqOn f f' V) (x y : V) :
    weylScale ξ f D ((x : ℂ), (y : ℂ)) ≤ E.internal V (x, y) := by
  unfold LSCMetric.internal
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun hPV => le_iInf fun ha => le_iInf fun hb => ?_
  have hD : D.IsCurve P a b :=
    Uniqueness.Toolkit.WeylShift.curve_back D E ξ hξ f' m hforget hE hm hP
  have h1 := weylScale_le_weylWL D ξ f hforget hD
  rw [ha, hb] at h1
  refine h1.trans (le_of_eq ?_)
  exact (len_eq_weylWL_of_eqOn D E ξ f f' hforget hE hD
    (fun t ht => hff (hPV t ht))).symm

 
theorem isCurve_weyl_of_bounded (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f' : C(ℂ, ℝ)) (hforget : Continuous (PfeWeyl.euclidForget D))
    (hE : ∀ p : ℂ × ℂ, E p = weylScale ξ f' D p) (m M : ℝ)
    (hb : ∀ z, m ≤ f' z ∧ f' z ≤ M) (hlen : D.IsLengthSpace)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) : E.IsCurve P a b :=
  Uniqueness.Toolkit.WeylShift.curve_forward D E ξ hξ f' m M hforget hE hb hlen hP

 
theorem exists_first_exit {P : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) {c : ℂ} {r : ℝ}
    (ha : P a ∈ Metric.ball c r) (hb : P b ∉ Metric.ball c r) :
    ∃ s ∈ Icc a b, P s ∈ Metric.sphere c r ∧ ∀ t ∈ Ico a s, P t ∈ Metric.ball c r := by
  set S : Set ℝ := Icc a b ∩ {t | r ≤ dist (P t) c}
  have hdist : ContinuousOn (fun t => dist (P t) c) (Icc a b) :=
    fun t ht => (hP t ht).dist continuousWithinAt_const
  have hSc : IsClosed S := hdist.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hbS : b ∈ S := ⟨⟨hab, le_rfl⟩, by
    have := hb; rw [Metric.mem_ball, not_lt] at this; exact this⟩
  have hSne : S.Nonempty := ⟨b, hbS⟩
  have hSbdd : BddBelow S := ⟨a, fun t ht => ht.1.1⟩
  set s := sInf S
  have hsS : s ∈ S := hSc.csInf_mem hSne hSbdd
  have hbefore : ∀ t ∈ Ico a s, P t ∈ Metric.ball c r := by
    intro t ht
    rw [Metric.mem_ball]
    by_contra hge
    have htS : t ∈ S := ⟨⟨ht.1, ht.2.le.trans hsS.1.2⟩, not_lt.mp hge⟩
    exact absurd (csInf_le hSbdd htS) (not_le.mpr ht.2)
  refine ⟨s, hsS.1, ?_, hbefore⟩
  rw [Metric.mem_sphere]
  apply le_antisymm _ hsS.2
  have has : a < s := by
    rcases eq_or_lt_of_le hsS.1.1 with h | h
    · exfalso
      have := hsS.2
      rw [← h] at this
      exact absurd ha (by rw [Metric.mem_ball]; exact not_lt.mpr this)
    · exact h
  have hwithin : Tendsto (fun t => dist (P t) c) (𝓝[Ico a s] s) (𝓝 (dist (P s) c)) :=
    ((hdist s hsS.1).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl hsS.1.2))).tendsto
  have : (𝓝[Ico a s] s).NeBot := right_nhdsWithin_Ico_neBot has
  exact le_of_tendsto hwithin (eventually_nhdsWithin_of_forall fun t ht =>
    (Metric.mem_ball.1 (hbefore t ht)).le)

end SupercriticalLQGUniqueness.B2.PfeAxioms
