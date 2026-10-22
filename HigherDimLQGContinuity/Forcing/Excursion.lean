import HigherDimLQGContinuity.Forcing.Confinement
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Excursions between plateau visits

Numerical and metric lemmas for the excursion step of deterministic site forcing.
-/

set_option autoImplicit false

noncomputable section

open Set Topology Metric Filter
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- A real power bounded above near zero has nonnegative exponent. -/
theorem q6_rpow_nonneg_of_bounded_near_zero {b C r : ℝ} (hr : 0 < r)
    (h : ∀ t ∈ Ioo (0 : ℝ) r, t ^ b ≤ C) : 0 ≤ b := by
  by_contra hb
  have hb' : b < 0 := lt_of_not_ge hb
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), C + 1 ≤ t ^ b :=
    tendsto_atTop.mp (tendsto_rpow_neg_nhdsGT_zero hb') (C + 1)
  have hIoo : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 r := Ioo_mem_nhdsGT hr
  obtain ⟨t, ht, hbig⟩ := (hIoo.and hev).exists
  have hsmall := h t ht
  linarith only [hbig, hsmall]

/-- The budget inequality forces a positive lower-bound scale; positivity of both costs follows
from the open core and its frontier. -/
theorem q6_H_pos {D E : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    {x : Rd d} (hx : x ∈ siteC d) (hsep : 4 * h ≤ δsep)
    (hbudget : 2 * εatt + εnet < H⁻¹ * (δsep / 2) ^ b) : 0 < H := by
  have hatt : 0 < εatt := q6_epsatt_pos cert hx
  have hnet : 0 < εnet := q6_epsnet_pos cert hx
  have hδ : 0 < δsep / 2 := by linarith only [cert.h_pos, hsep]
  have hpow : 0 < (δsep / 2) ^ b := Real.rpow_pos_of_pos hδ b
  have hInv : 0 < H⁻¹ := by
    by_contra hnot
    have hnon : H⁻¹ ≤ 0 := le_of_not_gt hnot
    have hprod : H⁻¹ * (δsep / 2) ^ b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hnon hpow.le
    linarith only [hatt, hnet, hbudget, hprod]
  exact inv_pos.mp hInv

/-- The lower-modulus exponent is nonnegative, although the frozen certificate does not list
that sign separately.  Uniform network cost bounds the lower modulus on arbitrarily close
points of its open core. -/
theorem q6_b_nonneg {D E : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    {x₀ : Rd d} (hx₀ : x₀ ∈ siteC d) (hH : 0 < H) : 0 ≤ b := by
  obtain ⟨y, hy, _⟩ := cert.access x₀ hx₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp cert.hUo y hy
  have hd : 0 < d := q6_dim_pos_of_mem_C hx₀
  have hθ : 0 < θ := by rw [cert.θ_eq]; exact Real.exp_pos _
  have hnet : 0 ≤ εnet := (q6_epsnet_pos cert hx₀).le
  have hcoreC : ∀ z ∈ cert.Uo, z ∈ siteC d := by
    intro z hz
    exact interior_subset (cert.hV (self_subset_cthickening cert.U (cert.hUoU hz)))
  have hcoreA : cert.Uo ⊆ siteA d := fun z hz => q6_siteC_subset_A d (hcoreC z hz)
  apply q6_rpow_nonneg_of_bounded_near_zero hr (C := εnet / (θ * H⁻¹))
  intro t ht
  let w : Rd d := y + t • HigherDimLFPP.e₁ d
  have hnorm : ‖y - w‖ = t := by
    rw [norm_sub_rev]
    simp only [w, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht.1, HigherDimLFPP.norm_e₁ hd, mul_one]
  have hw : w ∈ cert.Uo := hball (by
    change dist w y < r
    rw [dist_eq_norm, norm_sub_rev, hnorm]
    exact ht.2)
  have hlower := cert.lower y (hcoreC y hy) w (hcoreC w hw)
  rw [hnorm] at hlower
  have hanti : D.internal (siteA d) y w ≤ D.internal cert.Uo y w :=
    D.internal_anti hcoreA y w
  have hENN : ENNReal.ofReal (θ * (H⁻¹ * t ^ b)) ≤ ENNReal.ofReal εnet := by
    rw [ENNReal.ofReal_mul hθ.le]
    calc
      ENNReal.ofReal θ * ENNReal.ofReal (H⁻¹ * t ^ b) ≤
          ENNReal.ofReal θ * D.internal (siteA d) y w :=
        mul_le_mul' le_rfl hlower
      _ ≤ ENNReal.ofReal θ * D.internal cert.Uo y w := mul_le_mul' le_rfl hanti
      _ ≤ ENNReal.ofReal εnet := cert.net y hy w hw
  have hreal : θ * (H⁻¹ * t ^ b) ≤ εnet :=
    (ENNReal.ofReal_le_ofReal_iff hnet).mp hENN
  have hcoeff : 0 < θ * H⁻¹ := mul_pos hθ (inv_pos.mpr hH)
  apply (le_div_iff₀ hcoeff).mpr
  nlinarith only [hreal]

/-- A geodesic excursion outside the network collar cannot connect two collar points separated
by at least half the node separation scale. -/
theorem q6_excursion_short {D E D' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hW : IsWeylInternal ξ (-f) D D') (hξ : 0 ≤ ξ)
    (hH : 0 < H) (hb : 0 ≤ b) (hsep : 4 * h ≤ δsep)
    (hbudget : 2 * εatt + εnet < H⁻¹ * (δsep / 2) ^ b)
    {P : ℝ → Rd d} {a c u v s t : ℝ}
    (hgeo : IsGeodSeg D' P a c) (hau : a ≤ u) (hus : u ≤ s) (hst : s < t)
    (htv : t ≤ v) (hvc : v ≤ c)
    (hA : ∀ r ∈ Icc u v, P r ∈ siteA d)
    (hsV : P s ∈ cthickening h cert.U) (htV : P t ∈ cthickening h cert.U)
    (hgap : ∀ r ∈ Ioo s t, P r ∉ cthickening h cert.U) :
    ‖P s - P t‖ < δsep / 2 := by
  have hPst : ContinuousOn P (Icc s t) :=
    hgeo.2.1.mono (Icc_subset_Icc (hau.trans hus) (htv.trans hvc))
  have hzero := q6_f_zero_on_gap cert hst hPst hgap
  have hlenzero : D'.len P s t = D.len P s t :=
    q6_weyl_len_zero hW hst.le hPst hzero
  have hlengeo : D'.len P s t = ENNReal.ofReal (D'.1 (P s, P t)) :=
    q6_geod_subsegment hgeo (hau.trans hus) hst.le (htv.trans hvc)
  have hsC : P s ∈ siteC d := interior_subset (cert.hV hsV)
  have htC : P t ∈ siteC d := interior_subset (cert.hV htV)
  have hDlow := cert.lower (P s) hsC (P t) htC
  have hDlen : D.internal (siteA d) (P s) (P t) ≤ D.len P s t :=
    D.internal_le_len hst.le hPst
      (fun r hr => hA r ⟨hus.trans hr.1, hr.2.trans htv⟩)
  have hatt : 0 < εatt := q6_epsatt_pos cert hsC
  have hnet : 0 < εnet := q6_epsnet_pos cert hsC
  have hshort := q6_attach_competitor cert hW hξ hsV htV
  have hshort' : ENNReal.ofReal (D'.1 (P s, P t)) ≤
      ENNReal.ofReal (2 * εatt + εnet) := by
    calc
      ENNReal.ofReal (D'.1 (P s, P t)) ≤
          ENNReal.ofReal εatt + ENNReal.ofReal εnet + ENNReal.ofReal εatt := hshort
      _ = ENNReal.ofReal (2 * εatt + εnet) := by
        rw [show (2 : ℝ) * εatt + εnet = (εatt + εnet) + εatt by ring,
          ENNReal.ofReal_add (add_nonneg hatt.le hnet.le) hatt.le,
          ENNReal.ofReal_add hatt.le hnet.le]
  have hδ : 0 < δsep / 2 := by linarith only [cert.h_pos, hsep]
  have hthresh : 0 < H⁻¹ * (δsep / 2) ^ b :=
    mul_pos (inv_pos.mpr hH) (Real.rpow_pos_of_pos hδ b)
  by_contra hnot
  have hfar : δsep / 2 ≤ ‖P s - P t‖ := le_of_not_gt hnot
  have hpow : (δsep / 2) ^ b ≤ ‖P s - P t‖ ^ b :=
    Real.rpow_le_rpow hδ.le hfar hb
  have hreal : H⁻¹ * (δsep / 2) ^ b ≤ H⁻¹ * ‖P s - P t‖ ^ b :=
    mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hH.le)
  have hlim : ENNReal.ofReal (H⁻¹ * (δsep / 2) ^ b) ≤
      ENNReal.ofReal (2 * εatt + εnet) := by
    calc
      ENNReal.ofReal (H⁻¹ * (δsep / 2) ^ b) ≤
          ENNReal.ofReal (H⁻¹ * ‖P s - P t‖ ^ b) := ENNReal.ofReal_le_ofReal hreal
      _ ≤ D.internal (siteA d) (P s) (P t) := hDlow
      _ ≤ D.len P s t := hDlen
      _ = D'.len P s t := hlenzero.symm
      _ = ENNReal.ofReal (D'.1 (P s, P t)) := hlengeo
      _ ≤ ENNReal.ofReal (2 * εatt + εnet) := hshort'
  have hstrict : ENNReal.ofReal (2 * εatt + εnet) <
      ENNReal.ofReal (H⁻¹ * (δsep / 2) ^ b) :=
    (ENNReal.ofReal_lt_ofReal_iff hthresh).2 hbudget
  exact (not_le_of_gt hstrict) hlim

/-- Every point of the thickened plateau belongs to a thickened node.  The closed-set
representation of `cthickening` avoids a separate finite-union calculation. -/
theorem q6_V_node_cover {D E : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    {x : Rd d} (hx : x ∈ cthickening h cert.U) :
    ∃ n : cert.Node, x ∈ cthickening h (cert.N n) := by
  rw [cert.hU.cthickening_eq_biUnion_closedBall cert.h_pos.le] at hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp (cert.cover hy)
  refine ⟨n, Metric.mem_cthickening_of_dist_le x y h (cert.N n) hn ?_⟩
  simpa only [mem_closedBall, dist_comm] using hxy

/-- Thickened nonadjacent nodes retain at least half of their separation. -/
theorem q6_nonadjacent_sep {D E : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hsep : 4 * h ≤ δsep) {n n' : cert.Node} (hne : n ≠ n')
    (hnot : ¬ cert.adj.Adj n n') {x y : Rd d}
    (hx : x ∈ cthickening h (cert.N n))
    (hy : y ∈ cthickening h (cert.N n')) :
    δsep / 2 ≤ dist x y := by
  rw [(cert.N_closed n).cthickening_eq_biUnion_closedBall cert.h_pos.le] at hx
  rw [(cert.N_closed n').cthickening_eq_biUnion_closedBall cert.h_pos.le] at hy
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
  obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.mp hy
  have hbase := cert.sep n n' hne hnot p hp q hq
  have htri : dist p q ≤ dist p x + dist x y + dist y q := by
    calc
      dist p q ≤ dist p y + dist y q := dist_triangle _ _ _
      _ ≤ (dist p x + dist x y) + dist y q := by
        gcongr
        exact dist_triangle _ _ _
  have hpx : dist p x ≤ h := by simpa only [mem_closedBall, dist_comm] using hxp
  have hyq' : dist y q ≤ h := by simpa only [mem_closedBall, dist_comm] using hyq
  linarith only [hbase, htri, hpx, hyq', hsep]

/-- The trigger forces the short collector segment to meet the plateau collar. -/
theorem q6_V_visited {D E D' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ btrig : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hW : IsWeylInternal ξ (-f) D D') (hξ : 0 ≤ ξ)
    (hnet : εnet ≤ ε₀) (htrig : 7 * ε₀ < btrig)
    {P : ℝ → Rd d} {a c u w : ℝ} (hgeo : IsGeodSeg D' P a c)
    (hau : a ≤ u) (huw : u ≤ w) (hwc : w ≤ c)
    (hu : P u ∈ siteC d) (hw : P w ∈ siteC d)
    (hA : ∀ t ∈ Icc u w, P t ∈ siteA d)
    (htrigger : ENNReal.ofReal btrig ≤ D.internal (siteB d) (P u) (P w)) :
    ∃ t ∈ Icc u w, P t ∈ cthickening h cert.U := by
  by_contra hnone
  push Not at hnone
  have hzero : ∀ t ∈ Icc u w, f (P t) = 0 :=
    fun t ht => q6_f_zero_off_V cert (hnone t ht)
  have hP : ContinuousOn P (Icc u w) :=
    hgeo.2.1.mono (Icc_subset_Icc hau hwc)
  have hlen : D'.len P u w = D.len P u w :=
    q6_weyl_len_zero hW huw hP hzero
  have hε : 0 ≤ ε₀ := (q6_eps0_pos cert (q6_dim_pos_of_mem_C hu)).le
  have hshort := q6_geod_collector_short cert hW hξ hnet hε hgeo hau huw hwc hu hw
  have hlow : D.internal (siteB d) (P u) (P w) ≤ D.len P u w :=
    D.internal_le_len huw hP
      (fun t ht => q6_siteA_subset_B d (hA t ht))
  have hstrict : ENNReal.ofReal (3 * ε₀) < ENNReal.ofReal btrig := by
    apply ENNReal.ofReal_lt_ofReal_iff (by linarith only [hε, htrig]) |>.2
    linarith only [hε, htrig]
  exact (not_le_of_gt hstrict) (htrigger.trans (hlow.trans (hlen ▸ hshort)))

/-- A transition between two disjoint closed parts of a visited collar creates an excursion
whose interior avoids the collar. -/
theorem q6_first_switch_gap {P : ℝ → Rd d} {u w p q : ℝ}
    {V F₁ F₂ : Set (Rd d)} (hP : ContinuousOn P (Icc u w))
    (hF₁ : IsClosed F₁) (hF₂ : IsClosed F₂)
    (hdis : Disjoint F₁ F₂)
    (hcover : ∀ r ∈ Icc u w, P r ∈ V → P r ∈ F₁ ∨ P r ∈ F₂)
    (hp : p ∈ Icc u w) (hq : q ∈ Icc u w) (hpq : p < q)
    (hpF : P p ∈ F₁) (hqF : P q ∈ F₂) :
    ∃ s t : ℝ, p ≤ s ∧ s < t ∧ t ≤ q ∧ P s ∈ F₁ ∧ P t ∈ F₂ ∧
      ∀ r ∈ Ioo s t, P r ∉ V := by
  have hpqc : ContinuousOn P (Icc p q) :=
    hP.mono (Icc_subset_Icc hp.1 hq.2)
  let t := firstVisit P p q F₂
  obtain ⟨htI, htF, _, _, _⟩ :=
    q6_visit_times hpqc hF₂ ⟨q, ⟨hpq.le, le_rfl⟩, hqF⟩
  have hpt : p < t := by
    exact htI.1.lt_of_ne (by
      intro heq
      exact (hdis.le_bot ⟨hpF, heq ▸ htF⟩).elim)
  have hptc : ContinuousOn P (Icc p t) :=
    hpqc.mono (Icc_subset_Icc le_rfl htI.2)
  let s := lastVisit P p t F₁
  obtain ⟨_, _, hsI, hsF, _⟩ :=
    q6_visit_times hptc hF₁ ⟨p, ⟨le_rfl, hpt.le⟩, hpF⟩
  have hst : s < t := by
    exact hsI.2.lt_of_ne (by
      intro heq
      exact (hdis.le_bot ⟨hsF, heq.symm ▸ htF⟩).elim)
  refine ⟨s, t, hsI.1, hst, htI.2, hsF, htF, ?_⟩
  intro r hr hrV
  have hrUW : r ∈ Icc u w := ⟨hp.1.trans (hsI.1.trans hr.1.le),
    hr.2.le.trans (htI.2.trans hq.2)⟩
  rcases hcover r hrUW hrV with hrF₁ | hrF₂
  · have hrset : r ∈ {z | z ∈ Icc p t ∧ P z ∈ F₁} :=
      ⟨⟨hsI.1.trans hr.1.le, hr.2.le⟩, hrF₁⟩
    have hbound : BddAbove {z | z ∈ Icc p t ∧ P z ∈ F₁} :=
      ⟨t, fun z hz => hz.1.2⟩
    have hrle : r ≤ s := le_csSup hbound hrset
    exact (not_le_of_gt hr.1) hrle
  · have hrset : r ∈ {z | z ∈ Icc p q ∧ P z ∈ F₂} :=
      ⟨⟨hsI.1.trans hr.1.le, hr.2.le.trans htI.2⟩,
        hrF₂⟩
    have hbound : BddBelow {z | z ∈ Icc p q ∧ P z ∈ F₂} :=
      ⟨p, fun z hz => hz.1.1⟩
    have htle : t ≤ r := csInf_le hbound hrset
    exact (not_le_of_gt hr.2) htle

end HigherDimLQGContinuity
