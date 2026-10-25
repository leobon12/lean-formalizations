import SLUMetricAPI2
import LQGMetric.Metric.Internal
import LQGMetric.Metric.Geodesic
import LQGMetric.Topo.Disconnect
import LQGMetric.Topo.RectCross
import Mathlib.Analysis.Convex.PathConnected




 






set_option autoImplicit false
noncomputable section

open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Mesh

 

theorem internal_trace_le_len (D : LSCMetric) (K : Set ℂ) (π : ℝ → ℂ)
    {s t : ℝ} (hπ : D.IsCurve π s t)
    (hπK : MapsTo π (Icc s t) K) {x y : ℂ}
    (hx : x ∈ π '' Icc s t) (hy : y ∈ π '' Icc s t) :
    internalEDist (D.pt '' K) (D.pt x) (D.pt y) ≤ D.len π s t := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  have hmap : MapsTo (D.pt ∘ π) (Icc s t) (D.pt '' K) := by
    intro q hq
    exact ⟨π q, hπK hq, rfl⟩
  rcases le_total u v with huv | hvu
  · have hsub : Icc u v ⊆ Icc s t := Icc_subset_Icc hu.1 hv.2
    exact (internalEDist_le_curveLength huv (hπ.2.mono hsub)
      (hmap.mono_left hsub)).trans
      (curveLength_mono (D.pt ∘ π) hu.1 hv.2)
  · rw [internalEDist_comm]
    have hsub : Icc v u ⊆ Icc s t := Icc_subset_Icc hv.1 hu.2
    exact (internalEDist_le_curveLength hvu (hπ.2.mono hsub)
      (hmap.mono_left hsub)).trans
      (curveLength_mono (D.pt ∘ π) hv.1 hu.2)

 
theorem pathHit_time {J E F : Set ℂ} {P : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    (hsep : LQGMetric.Disconnects J E F) (ha : P a ∈ E) (hb : P b ∈ F) :
    ∃ u ∈ Icc a b, P u ∈ J := by
  have hpc : IsPathConnected (P '' Icc a b) :=
    ((convex_Icc a b).isPathConnected ⟨a, ⟨le_rfl, hab⟩⟩).image' hP
  have hjoined : JoinedIn (P '' Icc a b) (P a) (P b) :=
    hpc.joinedIn (P a) ⟨a, ⟨le_rfl, hab⟩, rfl⟩
      (P b) ⟨b, ⟨hab, le_rfl⟩, rfl⟩
  obtain ⟨w, ⟨q, rfl⟩, hwJ⟩ := hsep (P a) (P b) hjoined.somePath ha hb
  obtain ⟨u, hu, hPu⟩ := hjoined.somePath_mem q
  exact ⟨u, hu, hPu ▸ hwJ⟩

 

theorem internal_geodesic_equation_of_internal
    (D : LSCMetric) (K : Set ℂ) {P : ℝ → ℂ} {T : ℝ}
    (hPK : MapsTo P (Icc 0 T) K)
    (hgeo : ∀ (u : Icc (0 : ℝ) T) (v : Icc (0 : ℝ) T), u.1 ≤ v.1 →
      D.internal K (⟨⟨P u.1, hPK u.2⟩, ⟨P v.1, hPK v.2⟩⟩) =
        ENNReal.ofReal (v.1 - u.1)) :
    ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist (D.pt '' K) (D.pt (P u)) (D.pt (P v)) =
        ENNReal.ofReal (v - u) := by
  intro u v hu hv huv
  simpa only [LSCMetric.internal_eq_internalEDist] using
    hgeo ⟨u, hu⟩ ⟨v, hv⟩ huv

 

theorem internal_separator_twoSidedShortcut
    (D : LSCMetric) (K : Set ℂ) (hK : IsCompact K)
    {P π : ℝ → ℂ} {T a c e b s t r R L : ℝ} {z : ℂ}
    (ha0 : 0 ≤ a) (hac : a < c) (hce : c ≤ e) (heb : e < b) (hbT : b ≤ T)
    (hP : D.IsCurve P 0 T) (hPK : MapsTo P (Icc 0 T) K)
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist (D.pt '' K) (D.pt (P u)) (D.pt (P v)) =
        ENNReal.ofReal (v - u))
    (_hr : 0 < r) (hrR : r < R)
    (ha : R ≤ dist (P a) z) (hc : dist (P c) z ≤ r)
    (he : dist (P e) z ≤ r) (hb : R ≤ dist (P b) z)
    (hπ : D.IsCurve π s t) (hπK : MapsTo π (Icc s t) K)
    (hsep : Disconnects (π '' Icc s t) (sphere z r) (sphere z R))
    (hann : π '' Icc s t ⊆ {w | r < dist w z ∧ dist w z < R})
    (hL : 0 ≤ L) (hlen : D.len π s t = ENNReal.ofReal L) :
    ∃ u v : ℝ, a < u ∧ u < c ∧ e < v ∧ v < b ∧
      e - c ≤ v - u ∧ v - u ≤ L := by
  have hpc : ContinuousOn P (Icc 0 T) :=
    hP.continuousOn_of_mapsTo hK hPK
  have hsep' : LQGMetric.Disconnects (π '' Icc s t) (sphere z r) (sphere z R) :=
    (disconnects_iff_lqgMetric_disconnects hπ.isClosed_image).1 hsep
  have hfor : LQGMetric.Disconnects (π '' Icc s t) (closedBall z r) (ball z R)ᶜ :=
    LQGMetric.Disconnects.closedBall_compl_ball hrR.le hsep'
  have hrev := hfor.symm
  have hacT : Icc a c ⊆ Icc 0 T :=
    Icc_subset_Icc ha0 (le_trans hce (le_trans heb.le hbT))
  have hebT : Icc e b ⊆ Icc 0 T :=
    Icc_subset_Icc (le_trans ha0 (le_trans hac.le hce)) hbT
  have haout : P a ∈ (ball z R)ᶜ := by simpa only [mem_compl_iff, mem_ball, not_lt] using ha
  have hbout : P b ∈ (ball z R)ᶜ := by simpa only [mem_compl_iff, mem_ball, not_lt] using hb
  have hcin : P c ∈ closedBall z r := by simpa only [mem_closedBall] using hc
  have hein : P e ∈ closedBall z r := by simpa only [mem_closedBall] using he
  obtain ⟨u, hu, huJ⟩ := pathHit_time hac.le (hpc.mono hacT) hrev haout hcin
  obtain ⟨v, hv, hvJ⟩ := pathHit_time heb.le (hpc.mono hebT) hfor hein hbout
  have huAnn := hann huJ
  have hvAnn := hann hvJ
  have hau : a < u := by
    by_contra h
    have hEq : u = a := le_antisymm (not_lt.mp h) hu.1
    rw [hEq] at huAnn
    exact (not_lt_of_ge ha) huAnn.2
  have huc : u < c := by
    by_contra h
    have hEq : u = c := le_antisymm hu.2 (not_lt.mp h)
    rw [hEq] at huAnn
    exact (not_lt_of_ge hc) huAnn.1
  have hev : e < v := by
    by_contra h
    have hEq : v = e := le_antisymm (not_lt.mp h) hv.1
    rw [hEq] at hvAnn
    exact (not_lt_of_ge he) hvAnn.1
  have hvb : v < b := by
    by_contra h
    have hEq : v = b := le_antisymm hv.2 (not_lt.mp h)
    rw [hEq] at hvAnn
    exact (not_lt_of_ge hb) hvAnn.2
  have huT : u ∈ Icc 0 T := hacT hu
  have hvT : v ∈ Icc 0 T := hebT hv
  have huv : u ≤ v := le_trans (le_trans huc.le hce) hev.le
  have hcost := internal_trace_le_len D K π hπ hπK huJ hvJ
  rw [hgeo u v huT hvT huv, hlen] at hcost
  have hreal : v - u ≤ L := (ENNReal.ofReal_le_ofReal_iff hL).mp hcost
  exact ⟨u, v, hau, huc, hev, hvb, by linarith, hreal⟩

 


theorem internal_separator_twoSidedShortcut_around
    (D : LSCMetric) (K : Set ℂ) (hK : IsCompact K) (A : EuclideanAnnulus)
    (hAK : A.toSet ⊆ K)
    {P : ℝ → ℂ} {T a c e b : ℝ}
    (ha0 : 0 ≤ a) (hac : a < c) (hce : c ≤ e) (heb : e < b) (hbT : b ≤ T)
    (hP : D.IsCurve P 0 T) (hPK : MapsTo P (Icc 0 T) K)
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist (D.pt '' K) (D.pt (P u)) (D.pt (P v)) =
        ENNReal.ofReal (v - u))
    (ha : A.outerRadius ≤ dist (P a) A.center)
    (hc : dist (P c) A.center ≤ A.innerRadius)
    (he : dist (P e) A.center ≤ A.innerRadius)
    (hb : A.outerRadius ≤ dist (P b) A.center) :
    ENNReal.ofReal (e - c) ≤ aroundDist D A := by
  unfold aroundDist
  apply le_iInf
  intro π
  apply le_iInf
  intro s
  apply le_iInf
  intro t
  apply le_iInf
  intro hπ
  apply le_iInf
  intro hY
  apply le_iInf
  intro hsep
  by_cases hfin : D.len π s t = ∞
  · simp only [hfin, le_top]
  · have hr : 0 < A.innerRadius := A.2.1
    have hrR : A.innerRadius < A.outerRadius := A.2.2
    have hann : π '' Icc s t ⊆
        {w | A.innerRadius < dist w A.center ∧ dist w A.center < A.outerRadius} := by
      intro w hw
      obtain ⟨q, hq, rfl⟩ := hw
      have hA : π q ∈ A.toSet := hY q hq
      change π q ∈ ball A.center A.outerRadius ∧
        π q ∉ closure (ball A.center A.innerRadius) at hA
      rw [closure_ball A.center (ne_of_gt hr)] at hA
      exact ⟨lt_of_not_ge (by simpa only [mem_closedBall] using hA.2),
        by simpa only [mem_ball] using hA.1⟩
    have hlen : D.len π s t = ENNReal.ofReal (D.len π s t).toReal :=
      (ENNReal.ofReal_toReal hfin).symm
    have hπK : MapsTo π (Icc s t) K := fun q hq => hAK (hY q hq)
    obtain ⟨u, v, _, _, _, _, hbound, htime⟩ :=
      internal_separator_twoSidedShortcut D K hK ha0 hac hce heb hbT
        hP hPK hgeo hr hrR ha hc he hb hπ hπK hsep hann
        ENNReal.toReal_nonneg hlen
    calc
      ENNReal.ofReal (e - c) ≤ ENNReal.ofReal ((D.len π s t).toReal) :=
        ENNReal.ofReal_le_ofReal (hbound.trans htime)
      _ = D.len π s t := ENNReal.ofReal_toReal hfin

 


theorem internal_hit_separator_prefix
    (D : LSCMetric) (K : Set ℂ) (hK : IsCompact K)
    {P π : ℝ → ℂ} {T q s t r R L : ℝ} {z : ℂ}
    (hq0 : 0 < q) (hqT : q < T)
    (hP : D.IsCurve P 0 T) (hPK : MapsTo P (Icc 0 T) K)
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist (D.pt '' K) (D.pt (P u)) (D.pt (P v)) =
        ENNReal.ofReal (v - u))
    (hr : 0 < r) (hrR : r < R)
    (h0 : R ≤ dist (P 0) z) (hq : dist (P q) z ≤ r)
    (hT : R ≤ dist (P T) z)
    (hπ : D.IsCurve π s t) (hπK : MapsTo π (Icc s t) K)
    (hsep : Disconnects (π '' Icc s t) (sphere z r) (sphere z R))
    (hann : π '' Icc s t ⊆ {w | r < dist w z ∧ dist w z < R})
    (hL : 0 ≤ L) (hlen : D.len π s t = ENNReal.ofReal L) :
    ∃ u v : ℝ, 0 < u ∧ u < q ∧ q < v ∧ v < T ∧ q - u ≤ L := by
  obtain ⟨u, v, hu0, huq, hqv, hvT, _, huv⟩ :=
    internal_separator_twoSidedShortcut D K hK
      (a := 0) (c := q) (e := q) (b := T)
      le_rfl hq0 le_rfl hqT le_rfl hP hPK hgeo
      hr hrR h0 hq hq hT hπ hπK hsep hann hL hlen
  exact ⟨u, v, hu0, huq, hqv, hvT, by linarith⟩

 

theorem acrossDist_le_internal_geodesic_time
    (D : LSCMetric) (K : Set ℂ) (hK : IsCompact K)
    (A : EuclideanAnnulus)
    {P : ℝ → ℂ} {T a b : ℝ}
    (h0a : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T)
    (hP : D.IsCurve P 0 T) (hPK : MapsTo P (Icc 0 T) K)
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist (D.pt '' K) (D.pt (P u)) (D.pt (P v)) =
        ENNReal.ofReal (v - u))
    (ha : A.outerRadius ≤ dist (P a) A.center)
    (hb : dist (P b) A.center ≤ A.innerRadius) :
    acrossDist D A ≤ ENNReal.ofReal (b - a) := by
  have hcont : ContinuousOn P (Icc a b) :=
    (hP.continuousOn_of_mapsTo hK hPK).mono
      (Icc_subset_Icc h0a hbT)
  have hf : ContinuousOn (fun t => dist (P t) A.center) (Icc a b) :=
    continuous_dist.comp_continuousOn (hcont.prodMk continuousOn_const)
  obtain ⟨s, t, has, hst, htb, hs, ht, _⟩ :=
    LQGMetric.RectCross.exists_sub_crossing' hab hf A.2.2.le ha hb
  have hsT : s ∈ Icc 0 T := ⟨h0a.trans has, hst.trans (htb.trans hbT)⟩
  have htT : t ∈ Icc 0 T := ⟨h0a.trans (has.trans hst), htb.trans hbT⟩
  have hcost : D (P t, P s) ≤ ENNReal.ofReal (t - s) := by
    have hi := edist_le_internalEDist (D.pt '' K) (D.pt (P s)) (D.pt (P t))
    change D (P s, P t) ≤ _ at hi
    rw [hgeo s t hsT htT hst] at hi
    rw [D.isExtMetric.2.2.1]
    exact hi
  have hacross : acrossDist D A ≤ D (P t, P s) := by
    unfold acrossDist
    exact iInf_le_of_le (P t) <| iInf_le_of_le (by
      change P t ∈ sphere A.center A.innerRadius
      simpa only [Metric.mem_sphere, EuclideanAnnulus.innerRadius] using ht) <|
      iInf_le_of_le (P s) <| iInf_le_of_le (by
        change P s ∈ sphere A.center A.outerRadius
        simpa only [Metric.mem_sphere, EuclideanAnnulus.outerRadius] using hs) le_rfl
  exact hacross.trans (hcost.trans (ENNReal.ofReal_le_ofReal (by linarith)))

 

theorem len_eq_internal_geodesic_time
    (D : LSCMetric) (K : Set ℂ)
    {P : ℝ → ℂ} {T a b : ℝ}
    (h0a : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T)
    (hP : D.IsCurve P 0 T) (hPK : MapsTo P (Icc 0 T) K)
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist (D.pt '' K) (D.pt (P u)) (D.pt (P v)) =
        ENNReal.ofReal (v - u)) :
    D.len P a b = ENNReal.ofReal (b - a) := by
  have habT : Icc a b ⊆ Icc 0 T := Icc_subset_Icc h0a hbT
  have hlip : LipschitzOnWith 1 (D.pt ∘ P) (Icc a b) := by
    intro s hs t ht
    rcases le_total s t with hst | hts
    · have hi := edist_le_internalEDist (D.pt '' K) (D.pt (P s)) (D.pt (P t))
      rw [hgeo s t (habT hs) (habT ht) hst] at hi
      simpa only [Function.comp_apply, ENNReal.coe_one, one_mul,
        edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst),
        neg_sub] using hi
    · have hi := edist_le_internalEDist (D.pt '' K) (D.pt (P t)) (D.pt (P s))
      rw [hgeo t s (habT ht) (habT hs) hts] at hi
      rw [edist_comm]
      simpa only [Function.comp_apply, ENNReal.coe_one, one_mul,
        edist_dist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)] using hi
  have hupper : D.len P a b ≤ ENNReal.ofReal (b - a) := by
    change eVariationOn (D.pt ∘ P) (Icc a b) ≤ _
    calc
      eVariationOn (D.pt ∘ P) (Icc a b) =
          eVariationOn ((D.pt ∘ P) ∘ id) (Icc a b) := rfl
      _ ≤ (1 : ℝ≥0) * eVariationOn id (Icc a b) :=
        hlip.comp_eVariationOn_le (mapsTo_id _)
      _ = ENNReal.ofReal (b - a) := by
        rw [eVariationOn_id_Icc]
        norm_num
  have hlower : ENNReal.ofReal (b - a) ≤ D.len P a b := by
    rw [← hgeo a b (habT (left_mem_Icc.mpr hab))
      (habT (right_mem_Icc.mpr hab)) hab]
    exact internalEDist_le_curveLength hab (hP.2.mono habT)
      (fun t ht => ⟨P t, hPK (habT ht), rfl⟩)
  exact le_antisymm hupper hlower


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Mesh
