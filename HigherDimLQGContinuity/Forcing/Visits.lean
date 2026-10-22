import HigherDimLQGContinuity.Forcing.Weights
import HigherDimLQGMetric.Trap.Confine

/-!
# Collector visits and geodesic subsegments

Elementary time and annulus facts used by Lemma 4.3.
-/

set_option autoImplicit false

noncomputable section

open Set Topology Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem q6_siteC_closed (d : ℕ) : IsClosed (siteC d) :=
  isClosed_annCl _ _ _

theorem q6_siteC_subset_B (d : ℕ) : siteC d ⊆ siteB d := by
  intro x hx
  change (3 / 2 : ℝ) ≤ ‖x - 0‖ ∧ ‖x - 0‖ ≤ 5 / 2 at hx
  change dist x 0 < (4 : ℝ)
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hx.2 (by norm_num)

theorem q6_siteC_subset_A (d : ℕ) : siteC d ⊆ siteA d := by
  intro x hx
  change (3 / 2 : ℝ) ≤ ‖x - 0‖ ∧ ‖x - 0‖ ≤ 5 / 2 at hx
  change (1 / 2 : ℝ) < ‖x - 0‖ ∧ ‖x - 0‖ < 7 / 2
  constructor <;> linarith [hx.1, hx.2]

theorem q6_dim_pos_of_mem_C {x : Rd d} (hx : x ∈ siteC d) : 0 < d := by
  by_contra hnot
  have hd : d = 0 := Nat.eq_zero_of_not_pos hnot
  subst d
  have hx0 : x = 0 := Subsingleton.elim _ _
  change (3 / 2 : ℝ) ≤ ‖x - 0‖ ∧ ‖x - 0‖ ≤ 5 / 2 at hx
  simp only [hx0, sub_self, norm_zero] at hx
  norm_num at hx

theorem q6_siteA_subset_B (d : ℕ) : siteA d ⊆ siteB d := by
  intro x hx
  change (1 / 2 : ℝ) < ‖x - 0‖ ∧ ‖x - 0‖ < 7 / 2 at hx
  change dist x 0 < (4 : ℝ)
  rw [dist_eq_norm]
  linarith [hx.2]

/-- The support lies strictly inside the closed network collar. -/
theorem q6_support_interior_V {D E : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀) :
    tsupport f ⊆ interior (cthickening h cert.U) := by
  have hh : h / 2 < h := by linarith [cert.h_pos]
  exact cert.f_supp |>.trans
    ((cthickening_subset_thickening' cert.h_pos hh cert.U).trans
      (thickening_subset_interior_cthickening h cert.U))

theorem q6_f_zero_off_V {D E : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    {x : Rd d} (hx : x ∉ cthickening h cert.U) : f x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  exact fun hxf => hx (interior_subset (q6_support_interior_V cert hxf))

theorem q6_f_zero_off_intC {D E : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    {x : Rd d} (hx : x ∉ interior (siteC d)) : f x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  exact fun hxf => hx (cert.hV (interior_subset (q6_support_interior_V cert hxf)))

/-- The first and last visits to a closed set are attained on a continuous compact time interval. -/
theorem q6_visit_times {P : ℝ → Rd d} {a c : ℝ} {F : Set (Rd d)}
    (hP : ContinuousOn P (Icc a c)) (hF : IsClosed F)
    (hvisit : ∃ t ∈ Icc a c, P t ∈ F) :
    firstVisit P a c F ∈ Icc a c ∧ P (firstVisit P a c F) ∈ F ∧
      lastVisit P a c F ∈ Icc a c ∧ P (lastVisit P a c F) ∈ F ∧
      firstVisit P a c F ≤ lastVisit P a c F := by
  let S : Set ℝ := Icc a c ∩ P ⁻¹' F
  have hSc : IsClosed S := hP.preimage_isClosed_of_isClosed isClosed_Icc hF
  have hSn : S.Nonempty := by
    obtain ⟨t, ht, hFt⟩ := hvisit
    exact ⟨t, ht, hFt⟩
  have hSb : BddBelow S := ⟨a, fun t ht => ht.1.1⟩
  have hSa : BddAbove S := ⟨c, fun t ht => ht.1.2⟩
  have hfirst : sInf S ∈ S := hSc.csInf_mem hSn hSb
  have hlast : sSup S ∈ S := hSc.csSup_mem hSn hSa
  have hle : sInf S ≤ sSup S :=
    (csInf_le hSb hlast).trans_eq rfl
  exact ⟨hfirst.1, hfirst.2, hlast.1, hlast.2, hle⟩

/-- A geodesic segment remains geodesic on every ordered subinterval. -/
theorem q6_geod_subsegment {D : ContMetric d} {P : ℝ → Rd d} {a c s t : ℝ}
    (hgeo : IsGeodSeg D P a c) (has : a ≤ s) (hst : s ≤ t) (htc : t ≤ c) :
    D.len P s t = ENNReal.ofReal (D.1 (P s, P t)) := by
  have hfin : edist (D.pt (P a)) (D.pt (P c)) ≠ ⊤ := by
    rw [D.edist_pt]
    exact ENNReal.ofReal_ne_top
  have hlen : curveLength (D.pt ∘ P) a c = edist (D.pt (P a)) (D.pt (P c)) := by
    rw [D.edist_pt]
    exact hgeo.2.2
  change curveLength (D.pt ∘ P) s t = _
  rw [curveLength_eq_edist_of_subinterval hlen hfin has hst htc]
  simpa only [Function.comp_apply] using D.edist_pt (P s) (P t)

/-- First and last collector visits occur strictly between the outside endpoints. -/
theorem q6_collector_visit_times {D : ContMetric d} {P : ℝ → Rd d} {a c : ℝ}
    (hgeo : IsGeodSeg D P a c) (ha : P a ∉ siteB d) (hc : P c ∉ siteB d)
    (hvisit : ∃ t ∈ Icc a c, P t ∈ siteC d) :
    a < firstVisit P a c (siteC d) ∧
    firstVisit P a c (siteC d) ≤ lastVisit P a c (siteC d) ∧
    lastVisit P a c (siteC d) < c ∧
    P (firstVisit P a c (siteC d)) ∈ siteC d ∧
    P (lastVisit P a c (siteC d)) ∈ siteC d := by
  obtain ⟨hf, hPf, hl, hPl, hfl⟩ := q6_visit_times hgeo.2.1 (q6_siteC_closed d) hvisit
  refine ⟨?_, hfl, ?_, hPf, hPl⟩
  · exact hf.1.lt_of_ne (by
      intro heq
      exact ha (q6_siteC_subset_B d (heq ▸ hPf)))
  · exact hl.2.lt_of_ne (by
      intro heq
      exact hc (q6_siteC_subset_B d (heq ▸ hPl)))

/-- The discounted plateau gives a short competitor between any two collector points. -/
theorem q6_short_competitor {D E D' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hW : IsWeylInternal ξ (-f) D D') (hξ : 0 ≤ ξ)
    {x z : Rd d} (hx : x ∈ siteC d) (hz : z ∈ siteC d) :
    ENNReal.ofReal (D'.1 (x, z)) ≤
      ENNReal.ofReal ε₀ + ENNReal.ofReal εnet + ENNReal.ofReal ε₀ := by
  obtain ⟨y, hy, hxy⟩ := cert.access x hx
  obtain ⟨w, hw, hwz⟩ := cert.access z hz
  have hAo : IsOpen (siteA d) := isOpen_ann _ _ _
  have hleft : ENNReal.ofReal (D'.1 (x, y)) ≤ ENNReal.ofReal ε₀ :=
    (D'.ofReal_le_internal (siteA d) x y).trans <|
      (q6_weyl_internal_bounds hW hξ cert.f_bd hAo x y).2.trans hxy
  have hright : ENNReal.ofReal (D'.1 (w, z)) ≤ ENNReal.ofReal ε₀ :=
    (D'.ofReal_le_internal (siteA d) w z).trans <|
      (q6_weyl_internal_bounds hW hξ cert.f_bd hAo w z).2.trans
        (by simpa only [D.internal_comm] using hwz)
  have hmid : ENNReal.ofReal (D'.1 (y, w)) ≤ ENNReal.ofReal εnet := by
    calc
      ENNReal.ofReal (D'.1 (y, w)) ≤ D'.internal cert.Uo y w :=
        D'.ofReal_le_internal cert.Uo y w
      _ = ENNReal.ofReal θ * D.internal cert.Uo y w := by
        rw [q6_weyl_internal_const hW cert.hUo (fun p hp => cert.f_eq p (cert.hUoU hp))]
        exact congrArg (fun r : ℝ => ENNReal.ofReal r * D.internal cert.Uo y w) cert.θ_eq.symm
      _ ≤ ENNReal.ofReal εnet := cert.net y hy w hw
  calc
    ENNReal.ofReal (D'.1 (x, z)) = edist (D'.pt x) (D'.pt z) := (D'.edist_pt x z).symm
    _ ≤ edist (D'.pt x) (D'.pt y) + edist (D'.pt y) (D'.pt w) +
          edist (D'.pt w) (D'.pt z) :=
      (edist_triangle _ (D'.pt w) _).trans
        (add_le_add (edist_triangle _ (D'.pt y) _) le_rfl)
    _ ≤ ENNReal.ofReal ε₀ + ENNReal.ofReal εnet + ENNReal.ofReal ε₀ := by
      rw [D'.edist_pt, D'.edist_pt, D'.edist_pt]
      exact add_le_add (add_le_add hleft hmid) hright

/-- The plateau network also shortcuts any pair of points in its closed collar. -/
theorem q6_attach_competitor {D E D' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hW : IsWeylInternal ξ (-f) D D') (hξ : 0 ≤ ξ)
    {x z : Rd d} (hx : x ∈ cthickening h cert.U)
    (hz : z ∈ cthickening h cert.U) :
    ENNReal.ofReal (D'.1 (x, z)) ≤
      ENNReal.ofReal εatt + ENNReal.ofReal εnet + ENNReal.ofReal εatt := by
  obtain ⟨y, hy, hxy⟩ := cert.attach x hx
  obtain ⟨w, hw, hwz⟩ := cert.attach z hz
  have hAo : IsOpen (siteA d) := isOpen_ann _ _ _
  have hleft : ENNReal.ofReal (D'.1 (x, y)) ≤ ENNReal.ofReal εatt :=
    (D'.ofReal_le_internal (siteA d) x y).trans <|
      (q6_weyl_internal_bounds hW hξ cert.f_bd hAo x y).2.trans hxy
  have hright : ENNReal.ofReal (D'.1 (w, z)) ≤ ENNReal.ofReal εatt :=
    (D'.ofReal_le_internal (siteA d) w z).trans <|
      (q6_weyl_internal_bounds hW hξ cert.f_bd hAo w z).2.trans
        (by simpa only [D.internal_comm] using hwz)
  have hmid : ENNReal.ofReal (D'.1 (y, w)) ≤ ENNReal.ofReal εnet := by
    calc
      ENNReal.ofReal (D'.1 (y, w)) ≤ D'.internal cert.Uo y w :=
        D'.ofReal_le_internal cert.Uo y w
      _ = ENNReal.ofReal θ * D.internal cert.Uo y w := by
        rw [q6_weyl_internal_const hW cert.hUo (fun p hp => cert.f_eq p (cert.hUoU hp))]
        exact congrArg (fun r : ℝ => ENNReal.ofReal r * D.internal cert.Uo y w) cert.θ_eq.symm
      _ ≤ ENNReal.ofReal εnet := cert.net y hy w hw
  calc
    ENNReal.ofReal (D'.1 (x, z)) = edist (D'.pt x) (D'.pt z) := (D'.edist_pt x z).symm
    _ ≤ edist (D'.pt x) (D'.pt y) + edist (D'.pt y) (D'.pt w) +
          edist (D'.pt w) (D'.pt z) :=
      (edist_triangle _ (D'.pt w) _).trans
        (add_le_add (edist_triangle _ (D'.pt y) _) le_rfl)
    _ ≤ ENNReal.ofReal εatt + ENNReal.ofReal εnet + ENNReal.ofReal εatt := by
      rw [D'.edist_pt, D'.edist_pt, D'.edist_pt]
      exact add_le_add (add_le_add hleft hmid) hright

/-- The access cost is positive in every nonzero dimension: a boundary collector point is
outside the plateau collar but must reach its open core. -/
theorem q6_eps0_pos {D E : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hd : 0 < d) : 0 < ε₀ := by
  let x : Rd d := (3 / 2 : ℝ) • HigherDimLFPP.e₁ d
  have hnorm : ‖x‖ = 3 / 2 := by
    simp only [x, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2),
      HigherDimLFPP.norm_e₁ hd, mul_one]
  have hx : x ∈ siteC d := by
    change (3 / 2 : ℝ) ≤ ‖x - 0‖ ∧ ‖x - 0‖ ≤ 5 / 2
    rw [sub_zero, hnorm]
    constructor <;> norm_num
  obtain ⟨y, hy, hxy⟩ := cert.access x hx
  have hyC : y ∈ interior (siteC d) :=
    cert.hV (self_subset_cthickening cert.U (cert.hUoU hy))
  have hne : x ≠ y := by
    intro heq
    subst y
    have hsub : siteC d ⊆ (ball (0 : Rd d) (3 / 2))ᶜ := by
      intro z hz
      change (3 / 2 : ℝ) ≤ ‖z - 0‖ ∧ ‖z - 0‖ ≤ 5 / 2 at hz
      change ¬ dist z 0 < (3 / 2 : ℝ)
      rw [dist_eq_norm]
      exact not_lt.2 hz.1
    have hnot : x ∈ (closedBall (0 : Rd d) (3 / 2))ᶜ := by
      have h := interior_mono hsub hyC
      rwa [interior_compl, closure_ball (0 : Rd d)
        (by norm_num : (3 / 2 : ℝ) ≠ 0)] at h
    apply hnot
    change dist x 0 ≤ (3 / 2 : ℝ)
    rw [dist_eq_norm, sub_zero, hnorm]
  have hpos : 0 < ENNReal.ofReal (D.1 (x, y)) :=
    ENNReal.ofReal_pos.2 (D.apply_pos hne)
  have hle : ENNReal.ofReal (D.1 (x, y)) ≤ ENNReal.ofReal ε₀ :=
    (D.ofReal_le_internal (siteA d) x y).trans hxy
  by_contra hnot
  have heps : ENNReal.ofReal ε₀ = 0 := ENNReal.ofReal_eq_zero.2 (le_of_not_gt hnot)
  rw [heps] at hle
  exact not_le_of_gt hpos hle

/-- The attachment cost is positive: an open core inside the bounded collector has a frontier
point in the closed plateau, and that point must attach to a distinct core point. -/
theorem q6_epsatt_pos {D E : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    {x₀ : Rd d} (hx₀ : x₀ ∈ siteC d) : 0 < εatt := by
  obtain ⟨y, hy, _⟩ := cert.access x₀ hx₀
  have hzero : (0 : Rd d) ∉ cert.Uo := by
    intro hmem
    have hV : (0 : Rd d) ∈ cthickening h cert.U :=
      self_subset_cthickening cert.U (cert.hUoU hmem)
    have hC : (0 : Rd d) ∈ siteC d := interior_subset (cert.hV hV)
    change (3 / 2 : ℝ) ≤ ‖(0 : Rd d) - 0‖ ∧ ‖(0 : Rd d) - 0‖ ≤ 5 / 2 at hC
    norm_num at hC
  let Q : ℝ → Rd d := fun t => (1 - t) • y
  have hQ : ContinuousOn Q (Icc 0 1) := by fun_prop
  obtain ⟨τ, hτ, hfront⟩ :=
    trap_exists_frontier cert.hUo (by norm_num : (0 : ℝ) ≤ 1) hQ
      (by simpa [Q] using hy) (by simpa [Q] using hzero)
  have hcl : Q τ ∈ closure cert.Uo :=
    (frontier_subset_closure hfront)
  have hnot : Q τ ∉ cert.Uo := by
    rw [cert.hUo.frontier_eq] at hfront
    exact hfront.2
  have hU : Q τ ∈ cert.U :=
    cert.hU.closure_subset (closure_mono cert.hUoU hcl)
  have hV : Q τ ∈ cthickening h cert.U := self_subset_cthickening cert.U hU
  obtain ⟨w, hw, hxw⟩ := cert.attach (Q τ) hV
  have hne : Q τ ≠ w := fun heq => hnot (heq ▸ hw)
  have hpos : 0 < ENNReal.ofReal (D.1 (Q τ, w)) :=
    ENNReal.ofReal_pos.2 (D.apply_pos hne)
  have hle : ENNReal.ofReal (D.1 (Q τ, w)) ≤ ENNReal.ofReal εatt :=
    (D.ofReal_le_internal (siteA d) (Q τ) w).trans hxw
  by_contra hnotε
  have heps : ENNReal.ofReal εatt = 0 := ENNReal.ofReal_eq_zero.2 (le_of_not_gt hnotε)
  rw [heps] at hle
  exact not_le_of_gt hpos hle

/-- The network cost is positive because an open core contains distinct points. -/
theorem q6_epsnet_pos {D E : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    {x₀ : Rd d} (hx₀ : x₀ ∈ siteC d) : 0 < εnet := by
  obtain ⟨y, hy, _⟩ := cert.access x₀ hx₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp cert.hUo y hy
  have hd : 0 < d := q6_dim_pos_of_mem_C hx₀
  let w : Rd d := y + (r / 2) • HigherDimLFPP.e₁ d
  have hnorm : ‖w - y‖ = r / 2 := by
    simp only [w, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by linarith only [hr] : (0 : ℝ) < r / 2),
      HigherDimLFPP.norm_e₁ hd, mul_one]
  have hw : w ∈ cert.Uo := hball (by
    change dist w y < r
    rw [dist_eq_norm, hnorm]
    linarith only [hr])
  have hne : y ≠ w := by
    intro heq
    have : ‖w - y‖ = 0 := by rw [← heq, sub_self, norm_zero]
    rw [hnorm] at this
    linarith only [this, hr]
  have hθ : 0 < θ := by rw [cert.θ_eq]; exact Real.exp_pos _
  have hD : 0 < D.internal cert.Uo y w :=
    (ENNReal.ofReal_pos.2 (D.apply_pos hne)).trans_le
      (D.ofReal_le_internal cert.Uo y w)
  have hpos : 0 < ENNReal.ofReal θ * D.internal cert.Uo y w :=
    ENNReal.mul_pos (ne_of_gt (ENNReal.ofReal_pos.2 hθ)) (ne_of_gt hD)
  have hle := cert.net y hy w hw
  by_contra hnotε
  have heps : ENNReal.ofReal εnet = 0 := ENNReal.ofReal_eq_zero.2 (le_of_not_gt hnotε)
  rw [heps] at hle
  exact not_le_of_gt hpos hle

end HigherDimLQGContinuity
