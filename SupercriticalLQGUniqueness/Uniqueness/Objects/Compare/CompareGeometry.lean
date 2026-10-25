import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate
import LQGMetric.Topo.RectCross
import SLUMetricAPI2




 






set_option autoImplicit false
noncomputable section
open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Compare

 

theorem nested_annulus_geometry {y z : ℂ} {a b c d e : ℝ}
    (hnear : dist y z ≤ e) (hinner : a + e ≤ c) (houter : d + e ≤ b) :
    sphere y a ⊆ closedBall z c ∧
      sphere y b ⊆ (ball z d)ᶜ ∧
      Objects.CorrectedEvent.ann z c d ⊆ Objects.CorrectedEvent.ann y a b := by
  constructor
  · intro x hx
    change dist x z ≤ c
    have htri := dist_triangle x y z
    rw [mem_sphere] at hx
    rw [hx] at htri
    linarith
  constructor
  · intro x hx
    change ¬ dist x z < d
    have htri := dist_triangle x z y
    rw [mem_sphere] at hx
    rw [dist_comm z y, hx] at htri
    linarith
  · intro x hx
    change a < dist x y ∧ dist x y < b
    have htri1 := dist_triangle x y z
    have htri2 := dist_triangle x z y
    rw [dist_comm z y] at htri2
    change c < dist x z ∧ dist x z < d at hx
    constructor <;> linarith

 

theorem around_le_of_nested_annuli (D : LSCMetric)
    {y z : ℂ} {a b c d : ℝ}
    (hcd : c ≤ d)
    (hinner : sphere y a ⊆ closedBall z c)
    (houter : sphere y b ⊆ (ball z d)ᶜ)
    (hann : Objects.CorrectedEvent.ann z c d ⊆ Objects.CorrectedEvent.ann y a b) :
    Objects.CorrectedEvent.around D y a b ≤ Objects.CorrectedEvent.around D z c d := by
  unfold Objects.CorrectedEvent.around
  apply le_iInf
  intro P
  apply le_iInf
  intro s
  apply le_iInf
  intro t
  apply le_iInf
  intro hP
  apply le_iInf
  intro htrace
  apply le_iInf
  intro hsep
  have hsep' : LQGMetric.Disconnects (P '' Icc s t) (sphere y a) (sphere y b) :=
    (LQGMetric.Disconnects.closedBall_compl_ball hcd hsep).mono
      (Subset.rfl) hinner houter
  exact iInf_le_of_le P <| iInf_le_of_le s <| iInf_le_of_le t <|
    iInf_le_of_le hP <| iInf_le_of_le (htrace.trans hann) <|
      iInf_le_of_le hsep' le_rfl

 

theorem acr_le_of_nested_annuli (D : LSCMetric)
    {y z : ℂ} {a b c d : ℝ}
    (hcd : c ≤ d)
    (hinner : sphere y a ⊆ closedBall z c)
    (houter : sphere y b ⊆ (ball z d)ᶜ) :
    Objects.CorrectedEvent.acr D z c d ≤ Objects.CorrectedEvent.acr D y a b := by
  unfold Objects.CorrectedEvent.acr
  apply le_iInf
  intro P
  apply le_iInf
  intro s
  apply le_iInf
  intro t
  apply le_iInf
  intro hP
  apply le_iInf
  intro htrace
  apply le_iInf
  intro hs
  apply le_iInf
  intro ht
  have hbounded : MapsTo P (Icc s t) (closedBall y b) := by
    intro u hu
    exact (htrace ⟨u, hu, rfl⟩).2
  have hcont : ContinuousOn P (Icc s t) :=
    hP.continuousOn_of_mapsTo (isCompact_closedBall y b) hbounded
  have hrad : ContinuousOn (fun u => dist (P u) z) (Icc s t) := by
    fun_prop (disch := assumption)
  obtain ⟨s', t', hss', hs't', ht't, hsc, htd, hbetween⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hP.1 hrad hcd
      (hinner hs) (by simpa only [mem_compl_iff, mem_ball, not_lt] using houter ht)
  have hP' : D.IsCurve P s' t' :=
    ⟨hs't', hP.2.mono (Icc_subset_Icc hss' ht't)⟩
  have htrace' : P '' Icc s' t' ⊆ Objects.CorrectedEvent.cann z c d := by
    rintro x ⟨u, hu, rfl⟩
    exact hbetween u hu
  have hcost : Objects.CorrectedEvent.acr D z c d ≤ D.len P s' t' := by
    exact iInf_le_of_le P <| iInf_le_of_le s' <| iInf_le_of_le t' <|
      iInf_le_of_le hP' <| iInf_le_of_le htrace' <|
        iInf_le_of_le (mem_sphere.mpr hsc) <|
          iInf_le_of_le (mem_sphere.mpr htd) le_rfl
  exact hcost.trans (LQGMetric.MetricGeometry.curveLength_mono _ hss' ht't)

 

theorem acr_le_curve_of_endpoint_order (D : LSCMetric)
    {P : ℝ → ℂ} {s t c d : ℝ} {v : ℂ}
    (hP : D.IsCurve P s t) (hcont : ContinuousOn P (Icc s t))
    (hcd : c ≤ d) (hs : dist (P s) v ≤ c) (ht : d ≤ dist (P t) v) :
    Objects.CorrectedEvent.acr D v c d ≤ D.len P s t := by
  have hrad : ContinuousOn (fun u => dist (P u) v) (Icc s t) := by
    fun_prop (disch := assumption)
  obtain ⟨s', t', hss', hs't', ht't, hsc, htd, hbetween⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hP.1 hrad hcd hs ht
  have hP' : D.IsCurve P s' t' :=
    ⟨hs't', hP.2.mono (Icc_subset_Icc hss' ht't)⟩
  have htrace' : P '' Icc s' t' ⊆ Objects.CorrectedEvent.cann v c d := by
    rintro x ⟨u, hu, rfl⟩
    exact hbetween u hu
  have hcost : Objects.CorrectedEvent.acr D v c d ≤ D.len P s' t' := by
    exact iInf_le_of_le P <| iInf_le_of_le s' <| iInf_le_of_le t' <|
      iInf_le_of_le hP' <| iInf_le_of_le htrace' <|
        iInf_le_of_le (mem_sphere.mpr hsc) <|
          iInf_le_of_le (mem_sphere.mpr htd) le_rfl
  exact hcost.trans (LQGMetric.MetricGeometry.curveLength_mono _ hss' ht't)

 

theorem acr_le_internal_of_endpoint_order (D : LSCMetric)
    {U K : Set ℂ} {p : U × U} {v : ℂ} {c d : ℝ}
    (hK : IsCompact K) (hUK : U ⊆ K) (hcd : c ≤ d)
    (hs : dist (p.1 : ℂ) v ≤ c) (ht : d ≤ dist (p.2 : ℂ) v) :
    Objects.CorrectedEvent.acr D v c d ≤ D.internal U p := by
  unfold LSCMetric.internal
  apply le_iInf
  intro P
  apply le_iInf
  intro s
  apply le_iInf
  intro t
  apply le_iInf
  intro hP
  apply le_iInf
  intro hU
  apply le_iInf
  intro hPs
  apply le_iInf
  intro hPt
  have hcont : ContinuousOn P (Icc s t) :=
    hP.continuousOn_of_mapsTo hK (fun u hu => hUK (hU u hu))
  apply acr_le_curve_of_endpoint_order D hP hcont hcd
  · simpa only [hPs] using hs
  · simpa only [hPt] using ht


end SupercriticalLQGUniqueness.Uniqueness.Objects.Compare
