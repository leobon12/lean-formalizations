import SupercriticalLQGUniqueness.B2.Final.DG20CoupledGoodCircles
import SupercriticalLQGUniqueness.B2.DG20Lim.NonconcentricDisconnect
import SupercriticalLQGUniqueness.B2.PfeWeyl.LFPPLength
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteLFPPAffine

 



































set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify ContMetric)
open SupercriticalLQGUniqueness.B2.Iface
open SupercriticalLQGUniqueness.B2.DG20Lim (RatCoords RData RatAnnulus RatCircle finiteRatCoords
  finiteAroundCoords normalizedContLFPP)

namespace SupercriticalLQGUniqueness.B2.Final

 

 
theorem disconnects_of_lqgDisconnects {X E F : Set ℂ} (hX : IsClosed X)
    (h : LQGMetric.Disconnects X E F) : Disconnects X E F := by
  rintro ⟨S, hS, hSX, ⟨x, hxS, hxE⟩, ⟨y, hyS, hyF⟩⟩
  have hU : IsOpen Xᶜ := hX.isOpen_compl
  have hsub : S ⊆ connectedComponentIn Xᶜ x := hS.subset_connectedComponentIn hxS hSX
  have hconn : IsConnected (connectedComponentIn Xᶜ x) :=
    isConnected_connectedComponentIn_iff.2 (hSX hxS)
  have hpath : IsPathConnected (connectedComponentIn Xᶜ x) :=
    (hU.connectedComponentIn.isConnected_iff_isPathConnected).1 hconn
  have hj := hpath.joinedIn x (hsub hxS) y (hsub hyS)
  obtain ⟨w, ⟨t, rfl⟩, hwX⟩ := h x y hj.somePath hxE hyF
  exact connectedComponentIn_subset _ _ (hj.somePath_mem t) hwX

 
theorem RatAnnulus.inner_radius_lt_two_mul (B : RatAnnulus) :
    ((B.inner.radius : ℚ) : ℝ) < 2 * (B.outer.radius : ℝ) := by
  have hci : B.inner.center ∈ B.outer.openDisk :=
    B.nested.2 (mem_closedBall_self (by exact_mod_cast B.inner.radius_nonneg))
  let p : ℂ := B.inner.center + ((B.inner.radius : ℝ) : ℂ)
  have hp : p ∈ B.inner.closedDisk := by
    simp [p, RatCircle.closedDisk, abs_of_nonneg
      (show (0 : ℝ) ≤ (B.inner.radius : ℝ) by exact_mod_cast B.inner.radius_nonneg)]
  have hpo : p ∈ B.outer.openDisk := B.nested.2 hp
  have hdp : dist p B.inner.center = (B.inner.radius : ℝ) := by
    simp [p, abs_of_nonneg
      (show (0 : ℝ) ≤ (B.inner.radius : ℝ) by exact_mod_cast B.inner.radius_nonneg)]
  have h1 : dist p B.outer.center < B.outer.radius := hpo
  have h2 : dist B.inner.center B.outer.center < B.outer.radius := hci
  calc ((B.inner.radius : ℚ) : ℝ) = dist p B.inner.center := hdp.symm
    _ ≤ dist p B.outer.center + dist B.inner.center B.outer.center :=
        dist_triangle_right _ _ _
    _ < _ := by linarith

 


theorem aroundDist_normalizedLFPP_le_finiteAround (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) (B : RatAnnulus) (A : EuclideanAnnulus)
    (hc : A.center = B.inner.center) (hin : A.innerRadius < B.inner.radius)
    (hout : B.outer.closedDisk ⊆ ball A.center A.outerRadius) :
    aroundDist (PfeWeyl.normalizedLFPPMetric ξ a φ) A ≤
      finiteAroundCoords (normalizedContLFPP ξ a φ) B := by
  set G := PfeWeyl.normalizedLFPPMetric ξ a φ
  set D := normalizedContLFPP ξ a φ
  have hedist : ∀ x y : ℂ, edist (G.pt x) (G.pt y) = edist (D.pt x) (D.pt y) := by
    intro x y
    rw [DG20Lim.normalizedContLFPP_edist_eq_lfppMetric, B2.Median.lfppMetric_apply]
    exact PfeWeyl.normalizedLFPPMetric_apply ξ a φ (x, y)
  let ι : D.Space → G.Space := fun x => G.pt x
  have hι : Isometry ι := fun x y => hedist x y
  simp only [finiteAroundCoords, ContMetric.aroundDist]
  refine le_iInf fun s => le_iInf fun t => le_iInf fun P => le_iInf fun hst =>
    le_iInf fun hPc => le_iInf fun hPB => le_iInf fun hdisc => ?_
  have hcurve : G.IsCurve P s t :=
    ⟨hst, hι.continuous.comp_continuousOn (D.continuous_pt.comp_continuousOn hPc)⟩
  have hsub : B.toSet ⊆ A.toSet := by
    intro w hw
    refine ⟨hout hw.1, fun hwc => hw.2 ?_⟩
    have h1 : dist w A.center ≤ A.innerRadius := closure_ball_subset_closedBall hwc
    rw [hc] at h1
    exact lt_of_le_of_lt h1 hin
  have hmem : ∀ u ∈ Icc s t, P u ∈ A.toSet := fun u hu => hsub (hPB ⟨u, hu, rfl⟩)
  have hclosed : IsClosed (P '' Icc s t) := (isCompact_Icc.image_of_continuousOn hPc).isClosed
  have hdis : Disconnects (P '' Icc s t) A.innerBoundary A.outerBoundary := by
    refine disconnects_of_lqgDisconnects hclosed ?_
    have hnest : closedBall B.inner.center (B.inner.radius : ℝ) ⊆
        ball B.outer.center (B.outer.radius : ℝ) := B.nested.2
    have h1 := DG20Lim.disconnects_nested_closedBall_compl_ball hnest hdisc
    refine h1.mono le_rfl ?_ ?_
    · intro w hw
      have hw' : dist w A.center = A.innerRadius := hw
      rw [hc] at hw'
      exact mem_closedBall.2 (hw'.le.trans hin.le)
    · intro w hw hwb
      have hw' : dist w A.center = A.outerRadius := hw
      have := hout (ball_subset_closedBall hwb)
      exact (lt_irrefl _) (hw' ▸ (mem_ball.1 this))
  have hlen : G.len P s t = D.len P s t := by
    change eVariationOn (G.pt ∘ P) (Icc s t) = eVariationOn (D.pt ∘ P) (Icc s t)
    simpa only [one_mul] using
      (LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist
        (F := G.pt ∘ P) (G := D.pt ∘ P) (c := 1)
        (fun u v => by rw [one_mul]; exact hedist (P u) (P v)) (Icc s t))
  calc aroundDist G A ≤ G.len P s t :=
        iInf_le_of_le P (iInf_le_of_le s (iInf_le_of_le t (iInf_le_of_le hcurve
          (iInf_le_of_le hmem (iInf_le_of_le hdis le_rfl)))))
    _ = D.len P s t := hlen

 

 
def IsRationalAnnulusQ (A : EuclideanAnnulus) : Prop :=
  ∃ x y r s : ℚ, 0 < r ∧ r < s ∧
    A.center = Complex.mk (x : ℝ) (y : ℝ) ∧ A.innerRadius = (r : ℝ) ∧ A.outerRadius = (s : ℝ)

theorem isRationalAnnulusQ_of_double {A : EuclideanAnnulus}
    (hA : PfeWeyl.IsRationalDoubleAnnulus A) : IsRationalAnnulusQ A := by
  obtain ⟨x, y, r, hr, hc, hin, hout⟩ := hA
  exact ⟨x, y, r, 2 * r, hr, by linarith, hc, hin, by rw [hout]; push_cast; ring⟩

 
theorem isRationalCircle_innerBoundary_Q {A : EuclideanAnnulus} (hA : IsRationalAnnulusQ A) :
    B2.Iface.IsRationalCircle A.innerBoundary := by
  obtain ⟨x, y, r, -, hr, -, hc, hin, -⟩ := hA
  exact ⟨x, y, r, hr.le, by rw [EuclideanAnnulus.innerBoundary, hc, hin]⟩

 
def SmallAnnulusCostsQ (G : ℕ → LSCMetric) (D : LSCMetric) (K' K'' : Set ℂ) : Prop :=
  ∀ z ∈ K', PfeWeyl.IsNonsingular D z →
    ∀ δ : ℝ, 0 < δ → ∀ ρ : ℝ, 0 < ρ →
      ∃ A : EuclideanAnnulus,
        IsRationalAnnulusQ A ∧
        dist z A.center < A.innerRadius ∧
        A.outerRadius < ρ ∧
        A.toSet ⊆ K'' ∧
        ∀ᶠ n in atTop, aroundDist (G n) A < ENNReal.ofReal δ

theorem smallAnnulusCostsQ_of_smallAnnulusCosts {G : ℕ → LSCMetric} {D : LSCMetric}
    {K' K'' : Set ℂ} (h : PfeWeyl.SmallAnnulusCosts G D K' K'') :
    SmallAnnulusCostsQ G D K' K'' := by
  intro z hz hns δ hδ ρ hρ
  obtain ⟨A, h1, h2, h3, h4, h5⟩ := h z hz hns δ hδ ρ hρ
  exact ⟨A, isRationalAnnulusQ_of_double h1, h2, h3, h4, h5⟩

 

def CoupledSmallAnnuliQ (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (hN : ℕ → Ω' → DistC)
    (L : Ω' → LSCMetric) : Prop :=
  ∀ k : ℕ, ∀ᵐ ω ∂P', SmallAnnulusCostsQ
    (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n)) (V (e n) (hN n ω)))
    (L ω) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1))

theorem coupledSmallAnnuliQ_of_coupledSmallAnnuli {ξ : Set.Ioi (0 : ℝ)}
    {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {e : ℕ → Set.Ioi (0 : ℝ)}
    {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)} {Ω' : Type} [MeasurableSpace Ω']
    {P' : Measure Ω'} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (h : CoupledSmallAnnuli ξ m e V P' hN L) : CoupledSmallAnnuliQ ξ m e V P' hN L :=
  fun k => (h k).mono fun _ hω => smallAnnulusCostsQ_of_smallAnnulusCosts hω

 

 

theorem smallAnnulusCostsQ_of_good (ξ : ℝ) (a : ℕ → Set.Ioi (0 : ℝ)) (φ : ℕ → C(ℂ, ℝ))
    (D : LSCMetric) (Zn : ℕ → RatCoords) (Zl : RatCoords) (R : RData) (C : ℝ≥0∞)
    (hZid : ∀ n, Zn n = finiteRatCoords (normalizedContLFPP ξ (a n) (φ n)))
    (hZconv : Tendsto Zn atTop (𝓝 Zl)) (hRa : R.around = Zl.2)
    (hgood : ∀ z : ℂ, ∃ B : ℕ → RatAnnulus,
        (∀ n, (B n).inner.Surrounds z ∧
          R.around (B n) ≤ C * R.across (B n).inner (B n).outer) ∧
        (∀ n, (B n).inner.SurroundsCircle (B (n + 1)).outer) ∧
        Tendsto (fun n => (((B n).outer.radius : ℝ))) atTop (𝓝 0) ∧
        ∀ w : ℂ, w ≠ z → D (z, w) < ⊤ →
          Tendsto (fun n => R.across (B n).inner (B n).outer) atTop (𝓝 0) ∧
          Tendsto (fun n => R.around (B n)) atTop (𝓝 0))
    (k : ℕ) :
    SmallAnnulusCostsQ (fun n => PfeWeyl.normalizedLFPPMetric ξ (a n) (φ n)) D
      (closedBall 0 k) (ball 0 ((k : ℝ) + 1)) := by
  intro z hz hns δ hδ ρ hρ
  obtain ⟨w, hwz, hw⟩ := hns
  obtain ⟨B, hBgood, -, hBrad, hconv⟩ := hgood z
  have hround := (hconv w hwz hw).2
  have hev1 : ∀ᶠ j in atTop, R.around (B j) < ENNReal.ofReal δ :=
    hround.eventually_lt_const (ENNReal.ofReal_pos.2 hδ)
  have hmin : (0 : ℝ) < min (1 / 6) (ρ / 4) := lt_min (by norm_num) (by linarith)
  have hev2 : ∀ᶠ j in atTop, (((B j).outer.radius : ℝ)) < min (1 / 6) (ρ / 4) :=
    hBrad.eventually_lt_const hmin
  obtain ⟨j, hj1, hj2⟩ := (hev1.and hev2).exists
  set Bj := B j
  have hsur := (hBgood j).1
  have hro : (0 : ℝ) < (Bj.outer.radius : ℝ) := by exact_mod_cast Bj.nested.1
  have hzi : dist z Bj.inner.center < (Bj.inner.radius : ℝ) := hsur.2
  obtain ⟨r', hr'1, hr'2⟩ := exists_rat_btwn hzi
  have hr'pos : (0 : ℝ) < (r' : ℝ) := lt_of_le_of_lt dist_nonneg hr'1
  have hri := RatAnnulus.inner_radius_lt_two_mul Bj
  let R' : ℚ := 4 * Bj.outer.radius
  have hR' : ((R' : ℚ) : ℝ) = 4 * (Bj.outer.radius : ℝ) := by simp [R']
  have hr'R' : (r' : ℝ) < (R' : ℝ) := by rw [hR']; linarith
  let A : EuclideanAnnulus := ⟨(Bj.inner.center, ((r' : ℝ), (R' : ℝ))), hr'pos, hr'R'⟩
  have hAc : A.center = Bj.inner.center := rfl
  have hAi : A.innerRadius = (r' : ℝ) := rfl
  have hAo : A.outerRadius = (R' : ℝ) := rfl
  have hci : dist Bj.inner.center Bj.outer.center < (Bj.outer.radius : ℝ) :=
    Bj.nested.2 (mem_closedBall_self (by exact_mod_cast Bj.inner.radius_nonneg))
  have hout : Bj.outer.closedDisk ⊆ ball A.center A.outerRadius := by
    intro u hu
    have hu' : dist u Bj.outer.center ≤ (Bj.outer.radius : ℝ) := hu
    rw [mem_ball, hAc, hAo, hR']
    calc dist u Bj.inner.center ≤ dist u Bj.outer.center + dist Bj.inner.center Bj.outer.center :=
          dist_triangle_right _ _ _
      _ < 4 * (Bj.outer.radius : ℝ) := by linarith
  refine ⟨A, ⟨Bj.inner.x, Bj.inner.y, r', R', by exact_mod_cast hr'pos,
    by exact_mod_cast hr'R', rfl, rfl, rfl⟩, by rw [hAc, hAi]; exact hr'1, ?_, ?_, ?_⟩
  · rw [hAo, hR']
    have := lt_of_lt_of_le hj2 (min_le_right _ _)
    linarith
  · intro u hu
    have hu1 : dist u Bj.inner.center < 4 * (Bj.outer.radius : ℝ) := by
      have := hu.1
      rwa [mem_ball, hAc, hAo, hR'] at this
    have hz0 : dist z 0 ≤ k := mem_closedBall.1 hz
    have h6 := lt_of_lt_of_le hj2 (min_le_left _ _)
    have h4 := dist_triangle4 u Bj.inner.center z 0
    rw [dist_comm Bj.inner.center z] at h4
    rw [mem_ball]
    linarith
  · have hcoord : Tendsto (fun n => (Zn n).2 Bj) atTop (𝓝 (Zl.2 Bj)) :=
      ((continuous_apply Bj).comp continuous_snd).continuousAt.tendsto.comp hZconv
    have hlt : Zl.2 Bj < ENNReal.ofReal δ := by rw [← hRa]; exact hj1
    filter_upwards [hcoord.eventually_lt_const hlt] with n hn
    refine lt_of_le_of_lt ?_ hn
    have hcmp := aroundDist_normalizedLFPP_le_finiteAround ξ (a n) (φ n) Bj A hAc
      (by rw [hAi]; exact hr'2) hout
    rw [hZid n]
    exact hcmp

 
theorem coupledSmallAnnuliQ_of_coords {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {e : ℕ → Set.Ioi (0 : ℝ)}
    {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hS4 : DG20Section4) (hPerc : DG20PercEstimate')
    (hB : DG20CouplingData ξ Q m e c V P' h' hN L)
    (hR : CoupledRatCoords ξ m e V P' hN L) : CoupledSmallAnnuliQ ξ m e V P' hN L := by
  obtain ⟨Z, Zlim, hZm, -, hZid, hZconv, hLink⟩ := hR
  obtain ⟨C, -, hGood⟩ := coupled_good_circles hS4 hPerc hB Z Zlim hZm hZid hZconv hLink
  intro k
  filter_upwards [hGood, hZid] with ω hG hid
  obtain ⟨R, -, hRa, -, hgood⟩ := hG
  exact smallAnnulusCostsQ_of_good (ξ : ℝ) (fun n => m (e n)) (fun n => V (e n) (hN n ω))
    (L ω) (fun n => Z n ω) (Zlim ω) R C hid (hZconv ω) hRa hgood k

 


theorem exists_dg20SmallAnnuliCouplingQ (hI : DG20Interfaces)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    ∃ φ₁ : ℕ → ℕ, StrictMono φ₁ ∧ ∃ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      ∃ V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ),
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (_ : StandardBorelSpace Ω') (P' : Measure Ω')
        (_ : IsProbabilityMeasure P') (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC)
        (L : Ω' → LSCMetric),
        DG20CouplingData ξ Q m (fun n => ε (φ₁ n)) c V P' h' hN L ∧
        CoupledSmallAnnuliQ ξ m (fun n => ε (φ₁ n)) V P' hN L ∧
        CoupledRatCoords ξ m (fun n => ε (φ₁ n)) V P' hN L := by
  obtain ⟨hS4, hPerc, hRatio, hRelation, hPositive, hTop⟩ := hI
  obtain ⟨φ₁, hφ₁, c, V, Ω', M', SB', P', hP', h', hN, L, hB, hR⟩ :=
    exists_dg20CouplingData_coords
      (DG20Lim.dg20LimitSkSBR_of_inputs hS4 hPerc hRatio hRelation hPositive hTop)
      hS4 ξ Q hQ m hm ε hε
  let _ : MeasurableSpace Ω' := M'
  have : IsProbabilityMeasure P' := hP'
  exact ⟨φ₁, hφ₁, c, V, Ω', M', SB', P', hP', h', hN, L, hB,
    coupledSmallAnnuliQ_of_coords hS4 hPerc hB hR, hR⟩

end SupercriticalLQGUniqueness.B2.Final
