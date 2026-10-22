import HigherDimLQGContinuity.Forcing.Visits
import LQGMetric.Papers.DDDF.T20CCross
import HigherDimLQGMetric.Sec6.Transfer

/-!
# Collar confinement for Lemma 4.3

The first and last collector visits of a modified geodesic delimit a short segment.  A departure
from the inspection annulus would create two undiscounted collar crossings.
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

/-- Extract a downward scalar crossing with no overshoot between its endpoints. -/
theorem q6_downcross_times {g : ℝ → ℝ} {u v inner outer : ℝ}
    (huv : u ≤ v) (hg : ContinuousOn g (Icc u v))
    (hio : inner < outer) (hu : outer ≤ g u) (hv : g v ≤ inner) :
    ∃ p q : ℝ, u ≤ p ∧ p < q ∧ q ≤ v ∧ g p = outer ∧ g q = inner ∧
      ∀ t ∈ Icc p q, inner ≤ g t ∧ g t ≤ outer := by
  obtain ⟨q, hq, hqIic, hbefore⟩ := exists_first_hit (P := g) hg
    (isClosed_Iic (a := inner)) ⟨v, ⟨huv, le_rfl⟩, hv⟩
  have huq : u < q := by
    apply lt_of_le_of_ne hq.1
    intro heq
    have : g u ≤ inner := by rw [heq]; exact hqIic
    linarith only [this, hu, hio]
  have hgq : g q = inner := by
    refine le_antisymm hqIic ?_
    have hne : (𝓝[Ico u q] q).NeBot := right_nhdsWithin_Ico_neBot huq
    have hcw : ContinuousWithinAt g (Ico u q) q :=
      (hg q hq).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl hq.2))
    exact ge_of_tendsto hcw (eventually_nhdsWithin_of_forall fun t ht =>
      (not_le.1 (hbefore t ht)).le)
  obtain ⟨p, hup, hpq, hgp, hpafter⟩ :=
    LQGMetric.DDDF.T20C.last_cross (f := fun t => -g t) (a := -outer) huq.le
      (hg.mono (Icc_subset_Icc le_rfl hq.2)).neg
      (by linarith only [hu]) (by rw [hgq]; linarith only [hio])
  refine ⟨p, q, hup, hpq, hq.2, by linarith only [hgp], hgq, ?_⟩
  intro t ht
  constructor
  · rcases ht.2.eq_or_lt with heq | hlt
    · rw [heq, hgq]
    · exact (not_le.1 (hbefore t ⟨hup.trans ht.1, hlt⟩)).le
  · have := hpafter t ht
    linarith only [this]

/-- Extract the reversed crossing by applying `q6_downcross_times` to the negative function. -/
theorem q6_upcross_times {g : ℝ → ℝ} {u v inner outer : ℝ}
    (huv : u ≤ v) (hg : ContinuousOn g (Icc u v))
    (hio : inner < outer) (hu : g u ≤ inner) (hv : outer ≤ g v) :
    ∃ p q : ℝ, u ≤ p ∧ p < q ∧ q ≤ v ∧ g p = inner ∧ g q = outer ∧
      ∀ t ∈ Icc p q, inner ≤ g t ∧ g t ≤ outer := by
  obtain ⟨p, q, hup, hpq, hqv, hp, hq, hband⟩ :=
    q6_downcross_times (g := fun t => -g t) huv hg.neg
      (show -outer < -inner by linarith only [hio])
      (show -inner ≤ -g u by linarith only [hu])
      (show -g v ≤ -outer by linarith only [hv])
  refine ⟨p, q, hup, hpq, hqv, by linarith only [hp], by linarith only [hq], ?_⟩
  intro t ht
  obtain ⟨hlo, hhi⟩ := hband t ht
  constructor <;> linarith only [hlo, hhi]

/-- The collector's interior consists of the strict middle shell. -/
theorem q6_mem_interior_siteC_iff (x : Rd d) :
    x ∈ interior (siteC d) ↔ (3 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 5 / 2 := by
  have hset : siteC d = closedBall (0 : Rd d) (5 / 2) ∩
      (ball (0 : Rd d) (3 / 2))ᶜ := by
    ext y
    simp only [siteC, annCl, mem_ofPred_eq, mem_inter_iff, mem_closedBall,
      mem_compl_iff, mem_ball, dist_eq_norm, not_lt]
    exact and_comm
  rw [hset, interior_inter, interior_closedBall (0 : Rd d) (by norm_num : (5 / 2 : ℝ) ≠ 0),
    interior_compl, closure_ball (0 : Rd d) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  simp only [mem_inter_iff, mem_ball, mem_compl_iff, mem_closedBall, dist_eq_norm,
    not_le, sub_zero, and_comm]

/-- A path inside either collar is outside the support of the perturbation. -/
theorem q6_f_zero_of_collar {D E : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    {x : Rd d} (hx : ‖x‖ ≤ (3 / 2 : ℝ) ∨ (5 / 2 : ℝ) ≤ ‖x‖) : f x = 0 := by
  apply q6_f_zero_off_intC cert
  intro hmem
  obtain ⟨hlo, hhi⟩ := (q6_mem_interior_siteC_iff x).1 hmem
  rcases hx with hx | hx <;> linarith only [hx, hlo, hhi]

/-- Affine restriction of a curve to a subinterval. -/
theorem q6_reparam_collar {P : ℝ → Rd d} {a c p q : ℝ}
    (hP : ContinuousOn P (Icc a c)) (hap : a ≤ p) (hpq : p ≤ q) (hqc : q ≤ c) :
    ContinuousOn (fun t : ℝ => P (p + t * (q - p))) (Icc 0 1) ∧
      (fun t : ℝ => P (p + t * (q - p))) 0 = P p ∧
      (fun t : ℝ => P (p + t * (q - p))) 1 = P q := by
  have hmaps : MapsTo (fun t : ℝ => p + t * (q - p)) (Icc 0 1) (Icc a c) := by
    intro t ht
    constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hpq),
      mul_le_mul_of_nonneg_right ht.2 (sub_nonneg.mpr hpq)]
  refine ⟨hP.comp (by fun_prop) hmaps, by simp, by simp⟩

/-- Reversing the parameter of a path leaves its length unchanged. -/
theorem q6_len_reverse (D : ContMetric d) (Q : ℝ → Rd d) :
    D.len (fun t : ℝ => Q (1 - t)) 0 1 = D.len Q 0 1 := by
  change curveLength (fun t : ℝ => D.pt (Q (1 - t))) 0 1 =
    curveLength (D.pt ∘ Q) 0 1
  simpa only [zero_add, Function.comp_apply] using
    (curveLength_reverse (D.pt ∘ Q) (by norm_num : (0 : ℝ) ≤ 1))

/-- The certificate's collar lower bound also holds for reversed paths. -/
theorem q6_collar_lower_reverse {D E : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    {Q : ℝ → Rd d} (hQ : ContinuousOn Q (Icc 0 1))
    (hends : (‖Q 0‖ = 1 / 2 ∧ ‖Q 1‖ = 3 / 2) ∨
      (‖Q 0‖ = 7 / 2 ∧ ‖Q 1‖ = 5 / 2)) :
    ENNReal.ofReal aout ≤ D.len Q 0 1 := by
  have hmaps : MapsTo (fun t : ℝ => 1 - t) (Icc 0 1) (Icc 0 1) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hrev : ContinuousOn (fun t : ℝ => Q (1 - t)) (Icc 0 1) :=
    hQ.comp (by fun_prop) hmaps
  have hcost := cert.collar (fun t : ℝ => Q (1 - t)) hrev
  have hends' :
      (‖Q (1 - 0)‖ = 3 / 2 ∧ ‖Q (1 - 1)‖ = 1 / 2) ∨
        (‖Q (1 - 0)‖ = 5 / 2 ∧ ‖Q (1 - 1)‖ = 7 / 2) := by
    simpa only [sub_zero, sub_self] using hends.imp
      (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩)
  rw [q6_len_reverse] at hcost
  exact hcost hends'

/-- Every crossing of an undiscounted collar costs at least `aout` in the modified metric. -/
theorem q6_collar_cost {D E D' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hW : IsWeylInternal ξ (-f) D D')
    {P : ℝ → Rd d} {a c p q : ℝ} (hP : ContinuousOn P (Icc a c))
    (hap : a ≤ p) (hpq : p ≤ q) (hqc : q ≤ c)
    (hband : ∀ t ∈ Icc p q, ‖P t‖ ≤ (3 / 2 : ℝ) ∨ (5 / 2 : ℝ) ≤ ‖P t‖)
    (hends : (‖P p‖ = 3 / 2 ∧ ‖P q‖ = 1 / 2) ∨
      (‖P p‖ = 1 / 2 ∧ ‖P q‖ = 3 / 2) ∨
      (‖P p‖ = 5 / 2 ∧ ‖P q‖ = 7 / 2) ∨
      (‖P p‖ = 7 / 2 ∧ ‖P q‖ = 5 / 2)) :
    ENNReal.ofReal aout ≤ D'.len P p q := by
  let Q : ℝ → Rd d := fun t => P (p + t * (q - p))
  obtain ⟨hQc, hQ0, hQ1⟩ := q6_reparam_collar hP hap hpq hqc
  have hDlenQ : D.len Q 0 1 = D.len P p q := by
    simpa [Q] using
      S6a.len_affine_reparam D P hpq (by norm_num : (0 : ℝ) ≤ 1)
  have hDcost : ENNReal.ofReal aout ≤ D.len P p q := by
    rw [← hDlenQ]
    rcases hends with h1 | h2 | h3 | h4
    · exact cert.collar Q hQc (Or.inl (by simpa [Q] using h1))
    · exact q6_collar_lower_reverse cert hQc
        (Or.inl (by simpa [Q] using h2))
    · exact cert.collar Q hQc (Or.inr (by simpa [Q] using h3))
    · exact q6_collar_lower_reverse cert hQc
        (Or.inr (by simpa [Q] using h4))
  have hzero : D'.len P p q = D.len P p q :=
    q6_weyl_len_zero hW hpq (hP.mono (Icc_subset_Icc hap hqc))
      (fun t ht => q6_f_zero_of_collar cert (hband t ht))
  exact hzero.symm ▸ hDcost

/-- Lengths of two ordered disjoint subintervals fit inside the enclosing interval. -/
theorem q6_two_subinterval_lengths (D : ContMetric d) (P : ℝ → Rd d)
    {u v p₁ q₁ p₂ q₂ : ℝ} (hup : u ≤ p₁) (hpq : p₁ ≤ q₁)
    (hqp : q₁ ≤ p₂) (hpq' : p₂ ≤ q₂) (hqv : q₂ ≤ v) :
    D.len P p₁ q₁ + D.len P p₂ q₂ ≤ D.len P u v := by
  change curveLength (D.pt ∘ P) p₁ q₁ + curveLength (D.pt ∘ P) p₂ q₂ ≤
    curveLength (D.pt ∘ P) u v
  calc
    curveLength (D.pt ∘ P) p₁ q₁ + curveLength (D.pt ∘ P) p₂ q₂ =
        curveLength (D.pt ∘ P) p₁ q₁ + 0 + curveLength (D.pt ∘ P) p₂ q₂ := by simp
    _ ≤ curveLength (D.pt ∘ P) p₁ q₁ + curveLength (D.pt ∘ P) q₁ p₂ +
          curveLength (D.pt ∘ P) p₂ q₂ :=
      add_le_add (add_le_add le_rfl bot_le) le_rfl
    _ = curveLength (D.pt ∘ P) p₁ q₂ := by
      rw [curveLength_add _ hpq hqp, curveLength_add _ (hpq.trans hqp) hpq']
    _ ≤ curveLength (D.pt ∘ P) u v := curveLength_mono _ hup hqv

/-- The first-to-last collector part of a modified geodesic costs at most `3 ε₀`. -/
theorem q6_geod_collector_short {D E D' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hW : IsWeylInternal ξ (-f) D D') (hξ : 0 ≤ ξ)
    (hnet : εnet ≤ ε₀) (hε : 0 ≤ ε₀)
    {P : ℝ → Rd d} {a c u v : ℝ} (hgeo : IsGeodSeg D' P a c)
    (hau : a ≤ u) (huv : u ≤ v) (hvc : v ≤ c)
    (hu : P u ∈ siteC d) (hv : P v ∈ siteC d) :
    D'.len P u v ≤ ENNReal.ofReal (3 * ε₀) := by
  have hshort := q6_short_competitor cert hW hξ hu hv
  have hlen := q6_geod_subsegment hgeo hau huv hvc
  rw [hlen]
  calc
    ENNReal.ofReal (D'.1 (P u, P v)) ≤
        ENNReal.ofReal ε₀ + ENNReal.ofReal εnet + ENNReal.ofReal ε₀ := hshort
    _ ≤ ENNReal.ofReal ε₀ + ENNReal.ofReal ε₀ + ENNReal.ofReal ε₀ := by
      exact add_le_add (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hnet)) le_rfl
    _ = ENNReal.ofReal (3 * ε₀) := by
      rw [show (3 : ℝ) * ε₀ = (ε₀ + ε₀) + ε₀ by ring,
        ENNReal.ofReal_add (add_nonneg hε hε) hε,
        ENNReal.ofReal_add hε hε]

/-- If a continuous path avoids the closed network collar between its endpoints, continuity
forces the perturbation to vanish at the endpoints too. -/
theorem q6_f_zero_on_gap {D E : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    {P : ℝ → Rd d} {s t : ℝ} (hst : s < t)
    (hP : ContinuousOn P (Icc s t))
    (hgap : ∀ r ∈ Ioo s t, P r ∉ cthickening h cert.U) :
    ∀ r ∈ Icc s t, f (P r) = 0 := by
  have hzero : EqOn (fun r => f (P r)) (fun _ => (0 : ℝ)) (Ioo s t) :=
    fun r hr => q6_f_zero_off_V cert (hgap r hr)
  have hclosed : Icc s t ⊆ closure (Ioo s t) := by
    rw [closure_Ioo hst.ne]
  exact hzero.of_subset_closure (f.continuous.comp_continuousOn hP)
    continuousOn_const Ioo_subset_Icc_self hclosed

/-- An inner departure from the inspection annulus forces two undiscounted collar crossings. -/
theorem q6_two_inner_collar_cost {D E D' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hW : IsWeylInternal ξ (-f) D D') (haout : 0 ≤ aout)
    {P : ℝ → Rd d} {u v τ : ℝ} (hP : ContinuousOn P (Icc u v))
    (hτ : τ ∈ Icc u v) (hu : P u ∈ siteC d) (hv : P v ∈ siteC d)
    (hinner : ‖P τ‖ ≤ (1 / 2 : ℝ)) :
    ENNReal.ofReal (2 * aout) ≤ D'.len P u v := by
  have hnorm : ContinuousOn (fun t => ‖P t‖) (Icc u v) := hP.norm
  have huNorm : (3 / 2 : ℝ) ≤ ‖P u‖ := by
    change (3 / 2 : ℝ) ≤ ‖P u - 0‖ ∧ ‖P u - 0‖ ≤ 5 / 2 at hu
    simpa only [sub_zero] using hu.1
  have hvNorm : (3 / 2 : ℝ) ≤ ‖P v‖ := by
    change (3 / 2 : ℝ) ≤ ‖P v - 0‖ ∧ ‖P v - 0‖ ≤ 5 / 2 at hv
    simpa only [sub_zero] using hv.1
  obtain ⟨p₁, q₁, hup₁, hpq₁, hqτ, hp₁, hq₁, hband₁⟩ :=
    q6_downcross_times hτ.1
      (hnorm.mono (Icc_subset_Icc le_rfl hτ.2))
      (by norm_num : (1 / 2 : ℝ) < 3 / 2) huNorm hinner
  obtain ⟨p₂, q₂, hτp, hpq₂, hqv, hp₂, hq₂, hband₂⟩ :=
    q6_upcross_times hτ.2
      (hnorm.mono (Icc_subset_Icc hτ.1 le_rfl))
      (by norm_num : (1 / 2 : ℝ) < 3 / 2) hinner hvNorm
  have hcost₁ : ENNReal.ofReal aout ≤ D'.len P p₁ q₁ :=
    q6_collar_cost cert hW hP hup₁ hpq₁.le (hqτ.trans hτ.2)
      (fun t ht => Or.inl (hband₁ t ht).2)
      (Or.inl ⟨hp₁, hq₁⟩)
  have hcost₂ : ENNReal.ofReal aout ≤ D'.len P p₂ q₂ :=
    q6_collar_cost cert hW hP (hτ.1.trans hτp) hpq₂.le hqv
      (fun t ht => Or.inl (hband₂ t ht).2)
      (Or.inr (Or.inl ⟨hp₂, hq₂⟩))
  calc
    ENNReal.ofReal (2 * aout) = ENNReal.ofReal aout + ENNReal.ofReal aout := by
      rw [show (2 : ℝ) * aout = aout + aout by ring, ENNReal.ofReal_add haout haout]
    _ ≤ D'.len P p₁ q₁ + D'.len P p₂ q₂ := add_le_add hcost₁ hcost₂
    _ ≤ D'.len P u v := q6_two_subinterval_lengths D' P hup₁ hpq₁.le
      (hqτ.trans hτp) hpq₂.le hqv

/-- An outer departure from the inspection annulus forces two undiscounted collar crossings. -/
theorem q6_two_outer_collar_cost {D E D' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hW : IsWeylInternal ξ (-f) D D') (haout : 0 ≤ aout)
    {P : ℝ → Rd d} {u v τ : ℝ} (hP : ContinuousOn P (Icc u v))
    (hτ : τ ∈ Icc u v) (hu : P u ∈ siteC d) (hv : P v ∈ siteC d)
    (houter : (7 / 2 : ℝ) ≤ ‖P τ‖) :
    ENNReal.ofReal (2 * aout) ≤ D'.len P u v := by
  have hnorm : ContinuousOn (fun t => ‖P t‖) (Icc u v) := hP.norm
  have huNorm : ‖P u‖ ≤ (5 / 2 : ℝ) := by
    change (3 / 2 : ℝ) ≤ ‖P u - 0‖ ∧ ‖P u - 0‖ ≤ 5 / 2 at hu
    simpa only [sub_zero] using hu.2
  have hvNorm : ‖P v‖ ≤ (5 / 2 : ℝ) := by
    change (3 / 2 : ℝ) ≤ ‖P v - 0‖ ∧ ‖P v - 0‖ ≤ 5 / 2 at hv
    simpa only [sub_zero] using hv.2
  obtain ⟨p₁, q₁, hup₁, hpq₁, hqτ, hp₁, hq₁, hband₁⟩ :=
    q6_upcross_times hτ.1
      (hnorm.mono (Icc_subset_Icc le_rfl hτ.2))
      (by norm_num : (5 / 2 : ℝ) < 7 / 2) huNorm houter
  obtain ⟨p₂, q₂, hτp, hpq₂, hqv, hp₂, hq₂, hband₂⟩ :=
    q6_downcross_times hτ.2
      (hnorm.mono (Icc_subset_Icc hτ.1 le_rfl))
      (by norm_num : (5 / 2 : ℝ) < 7 / 2) houter hvNorm
  have hcost₁ : ENNReal.ofReal aout ≤ D'.len P p₁ q₁ :=
    q6_collar_cost cert hW hP hup₁ hpq₁.le (hqτ.trans hτ.2)
      (fun t ht => Or.inr (hband₁ t ht).1)
      (Or.inr (Or.inr (Or.inl ⟨hp₁, hq₁⟩)))
  have hcost₂ : ENNReal.ofReal aout ≤ D'.len P p₂ q₂ :=
    q6_collar_cost cert hW hP (hτ.1.trans hτp) hpq₂.le hqv
      (fun t ht => Or.inr (hband₂ t ht).1)
      (Or.inr (Or.inr (Or.inr ⟨hp₂, hq₂⟩)))
  calc
    ENNReal.ofReal (2 * aout) = ENNReal.ofReal aout + ENNReal.ofReal aout := by
      rw [show (2 : ℝ) * aout = aout + aout by ring, ENNReal.ofReal_add haout haout]
    _ ≤ D'.len P p₁ q₁ + D'.len P p₂ q₂ := add_le_add hcost₁ hcost₂
    _ ≤ D'.len P u v := q6_two_subinterval_lengths D' P hup₁ hpq₁.le
      (hqτ.trans hτp) hpq₂.le hqv

/-- The deterministic confinement step, with only the hypotheses actually used by this part. -/
theorem q6_confine_core {D E D' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hW : IsWeylInternal ξ (-f) D D') (hξ : 0 ≤ ξ)
    (hnet : εnet ≤ ε₀) (hcollar : 3 * ε₀ < 2 * aout)
    {P : ℝ → Rd d} {a c : ℝ} (hgeo : IsGeodSeg D' P a c)
    (ha : P a ∉ siteB d) (hc : P c ∉ siteB d)
    (hvisit : ∃ t ∈ Icc a c, P t ∈ siteC d) :
    let u := firstVisit P a c (siteC d)
    let w := lastVisit P a c (siteC d)
    a < u ∧ u ≤ w ∧ w < c ∧
      D'.len P u w = ENNReal.ofReal (D'.1 (P u, P w)) ∧
      D'.len P u w ≤ ENNReal.ofReal (3 * ε₀) ∧
      ∀ t ∈ Icc u w, P t ∈ siteA d := by
  dsimp
  obtain ⟨hau, huw, hwc, hPu, hPw⟩ :=
    q6_collector_visit_times hgeo ha hc hvisit
  have hε : 0 < ε₀ := q6_eps0_pos cert (q6_dim_pos_of_mem_C hPu)
  have haout : 0 ≤ aout := by linarith only [hε, hcollar]
  have hshort : D'.len P (firstVisit P a c (siteC d))
      (lastVisit P a c (siteC d)) ≤ ENNReal.ofReal (3 * ε₀) :=
    q6_geod_collector_short cert hW hξ hnet hε.le hgeo hau.le huw hwc.le hPu hPw
  have hstrict : D'.len P (firstVisit P a c (siteC d))
      (lastVisit P a c (siteC d)) < ENNReal.ofReal (2 * aout) :=
    hshort.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith only [hε, hcollar])).2 hcollar)
  have hPuw : ContinuousOn P
      (Icc (firstVisit P a c (siteC d)) (lastVisit P a c (siteC d))) :=
    hgeo.2.1.mono (Icc_subset_Icc hau.le hwc.le)
  refine ⟨hau, huw, hwc, q6_geod_subsegment hgeo hau.le huw hwc.le, hshort, ?_⟩
  intro τ hτ
  by_contra hnotA
  have hnorm : ¬ ((1 / 2 : ℝ) < ‖P τ‖ ∧ ‖P τ‖ < 7 / 2) := by
    change ¬ ((1 / 2 : ℝ) < ‖P τ - 0‖ ∧ ‖P τ - 0‖ < 7 / 2) at hnotA
    simpa only [sub_zero] using hnotA
  by_cases hinner : ‖P τ‖ ≤ (1 / 2 : ℝ)
  · have hcost := q6_two_inner_collar_cost cert hW haout hPuw hτ hPu hPw hinner
    exact (not_le_of_gt hstrict) hcost
  · have houter : (7 / 2 : ℝ) ≤ ‖P τ‖ := by
      by_contra hnot
      exact hnorm ⟨lt_of_not_ge hinner, lt_of_not_ge hnot⟩
    have hcost := q6_two_outer_collar_cost cert hW haout hPuw hτ hPu hPw houter
    exact (not_le_of_gt hstrict) hcost

/-- Lemma 4.3(a): confinement of the modified primary geodesic between its first and last
collector visits.  The signature carries the full certificate-side hypotheses of Part B. -/
theorem lemma43_confine (d : ℕ) {D E D' E' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ η M θ h δsep ε₀ εnet εatt btrig aout H b v d₀ Ω : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hWD : IsWeylInternal ξ (-f) D D') (_hWE : IsWeylInternal η (-f) E E')
    (hξ : 0 ≤ ξ) (_hη : 0 ≤ η) (_hd₀ : 0 < d₀)
    (_hmismatch : |η - ξ| * M ≤ Ω) (_hv : 0 < v) (_hvle : v ≤ 1 / 100)
    (_hΩ : Ω ≤ v / 100) (hcollar : 3 * ε₀ < 2 * aout)
    (hnet : εnet ≤ ε₀) (_htrig : 7 * ε₀ < btrig)
    (_hsep : 4 * h ≤ δsep)
    (_hexc : 2 * εatt + εnet < H⁻¹ * (δsep / 2) ^ b)
    (P : ℝ → Rd d) (a c : ℝ) (hgeo : IsGeodSeg D' P a c)
    (ha : P a ∉ siteB d) (hc : P c ∉ siteB d)
    (hvisit : ∃ t ∈ Icc a c, P t ∈ siteC d) :
    let u := firstVisit P a c (siteC d)
    let w := lastVisit P a c (siteC d)
    a < u ∧ u ≤ w ∧ w < c ∧
      D'.len P u w = ENNReal.ofReal (D'.1 (P u, P w)) ∧
      D'.len P u w ≤ ENNReal.ofReal (3 * ε₀) ∧
      ∀ t ∈ Icc u w, P t ∈ siteA d :=
  q6_confine_core cert hWD hξ hnet hcollar hgeo ha hc hvisit

end HigherDimLQGContinuity
