import HigherDimLQGMetric.Collapse.Lemma31

/-! # Ambient speed of weighted arc-length parametrizations -/

set_option autoImplicit false

open Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- A normalized weighted subcurve has ambient speed at most one when `w ≥ λ`. -/
theorem dist_le_time_of_weighted_cost {X : Type*} [MetricSpace X]
    {P : ℝ → X} {w : X → ℝ} {lam s t : ℝ} (hlam : 0 < lam) (hst : s ≤ t)
    (hw : ∀ z, lam ≤ w z)
    (hcost : weightedLength w P s t ≤ ENNReal.ofReal (lam * (t - s))) :
    dist (P s) (P t) ≤ t - s := by
  have hfac : ENNReal.ofReal lam ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hlam)
  have hlow : ENNReal.ofReal lam * edist (P s) (P t) ≤
      weightedLength w P s t := by
    calc
      ENNReal.ofReal lam * edist (P s) (P t)
          ≤ ENNReal.ofReal lam * curveLength P s t :=
        mul_le_mul' le_rfl (edist_le_curveLength P hst)
      _ ≤ weightedLength w P s t :=
        ofReal_mul_curveLength_le_weightedLength hst (fun r _ => hw (P r))
  have hmul : ENNReal.ofReal lam * ENNReal.ofReal (dist (P s) (P t)) ≤
      ENNReal.ofReal lam * ENNReal.ofReal (t - s) := by
    rw [← edist_dist, ← ENNReal.ofReal_mul hlam.le]
    exact hlow.trans hcost
  have hle : ENNReal.ofReal (dist (P s) (P t)) ≤ ENNReal.ofReal (t - s) :=
    (ENNReal.mul_le_mul_iff_right hfac ENNReal.ofReal_ne_top).1 hmul
  exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hst)).1 hle

/-- A curve that is 1-Lipschitz on an interval has length at most the interval duration. -/
theorem curveLength_le_time_of_unit_lipschitz {X : Type*} [MetricSpace X]
    {P : ℝ → X} {s t : ℝ} (_hst : s ≤ t)
    (hP : ∀ a ∈ Icc s t, ∀ b ∈ Icc s t, dist (P a) (P b) ≤ dist a b) :
    curveLength P s t ≤ ENNReal.ofReal (t - s) := by
  have hlip : LipschitzOnWith 1 P (Icc s t) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    simpa using hP a ha b hb
  have h := hlip.comp_eVariationOn_le (g := id) (s := Icc s t)
    (fun _ ha => ha)
  simpa [curveLength, eVariationOn_id_Icc, Function.comp_def] using h

/-- The constant extension of a weighted arc-length parametrization is 1-Lipschitz
in the original ambient metric. -/
theorem normalized_path_lipschitz {X : Type*} [MetricSpace X]
    {P : ℝ → X} {w : X → ℝ} {lam L T : ℝ}
    (hlam : 0 < lam)
    (hw : ∀ z, lam ≤ w z)
    (hparam : ∀ s t, 0 ≤ s → s ≤ t → t ≤ L →
      weightedLength w P s t = ENNReal.ofReal (lam * (t - s)))
    (hconst : ∀ t, L ≤ t → t ≤ T → P t = P L) :
    ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      dist (P s) (P t) ≤ dist s t := by
  have hordered : ∀ s t, 0 ≤ s → s ≤ t → t ≤ T →
      dist (P s) (P t) ≤ t - s := by
    intro s t hs hst ht
    by_cases htL : t ≤ L
    · exact dist_le_time_of_weighted_cost hlam hst hw
        ((hparam s t hs hst htL).le)
    by_cases hLs : L ≤ s
    · rw [hconst s hLs (hst.trans ht), hconst t (hLs.trans hst) ht]
      simp [sub_nonneg.mpr hst]
    have hsL : s ≤ L := le_of_not_ge hLs
    have hLt : L ≤ t := le_of_not_ge htL
    rw [hconst t hLt ht]
    have hspeed := dist_le_time_of_weighted_cost hlam hsL hw
      ((hparam s L hs hsL le_rfl).le)
    linarith
  intro s hs t ht
  rcases le_total (s : ℝ) t with hst | hts
  · have h := hordered s t hs.1 hst ht.2
    simpa [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)] using h
  · have h := hordered t s ht.1 hts hs.2
    simpa [dist_comm, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hts)] using h

/-- The internal distance along a 1-Lipschitz curve in `K` is bounded by elapsed time. -/
theorem internalEDist_le_time_of_unit_curve {X : Type*} [MetricSpace X]
    {K : Set X} {P : ℝ → X} {T : ℝ}
    (hPc : ContinuousOn P (Icc 0 T)) (hPK : MapsTo P (Icc 0 T) K)
    (hspeed : ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T,
      dist (P a) (P b) ≤ dist a b)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T)
    (hst : s ≤ t) :
    internalEDist K (P s) (P t) ≤ ENNReal.ofReal (t - s) := by
  have hsub : Icc s t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc hs.1 ht.2
  have hlen := curveLength_le_time_of_unit_lipschitz hst
    (fun a ha b hb => hspeed a (hsub ha) b (hsub hb))
  exact (internalEDist_le_curveLength hst (hPc.mono hsub)
    (hPK.mono_left hsub)).trans hlen

/-- A unit-Lipschitz curve in `K` that uses exactly the intrinsic endpoint distance
must be an intrinsic unit-speed geodesic. -/
theorem intrinsic_unit_speed_of_endpoint_distance {X : Type*} [MetricSpace X]
    {K : Set X} {P : ℝ → X} {T ℓ : ℝ} {u v : X}
    (hPc : ContinuousOn P (Icc 0 T)) (hPK : MapsTo P (Icc 0 T) K)
    (hspeed : ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T,
      dist (P a) (P b) ≤ dist a b)
    (hℓ0 : 0 ≤ ℓ) (hℓT : ℓ ≤ T) (hP0 : P 0 = u) (hPℓ : P ℓ = v)
    (hend : internalEDist K u v = ENNReal.ofReal ℓ) :
    ∀ s ∈ Icc (0 : ℝ) ℓ, ∀ t ∈ Icc (0 : ℝ) ℓ, s ≤ t →
      internalEDist K (P s) (P t) = ENNReal.ofReal (t - s) := by
  intro s hs t ht hst
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hℓ0.trans hℓT⟩
  have hℓT' : ℓ ∈ Icc (0 : ℝ) T := ⟨hℓ0, hℓT⟩
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans hℓT⟩
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.trans hℓT⟩
  have hleft := internalEDist_le_time_of_unit_curve hPc hPK hspeed h0T hsT hs.1
  have hmid := internalEDist_le_time_of_unit_curve hPc hPK hspeed hsT htT hst
  have hright := internalEDist_le_time_of_unit_curve hPc hPK hspeed htT hℓT' ht.2
  rw [hP0] at hleft
  rw [hPℓ] at hright
  have hmidfin : internalEDist K (P s) (P t) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmid
  have hleftfin : internalEDist K u (P s) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hleft
  have hrightfin : internalEDist K (P t) v ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hright
  have htri : internalEDist K u v ≤
      internalEDist K u (P s) + internalEDist K (P s) (P t) +
        internalEDist K (P t) v := by
    calc
      internalEDist K u v
          ≤ internalEDist K u (P s) + internalEDist K (P s) v :=
        internalEDist_triangle K u (P s) v
      _ ≤ internalEDist K u (P s) +
          (internalEDist K (P s) (P t) + internalEDist K (P t) v) :=
        add_le_add_right (internalEDist_triangle K (P s) (P t) v) _
      _ = _ := by rw [add_assoc]
  have htriReal : ℓ ≤ s + (internalEDist K (P s) (P t)).toReal + (ℓ - t) := by
    have hsumfin : internalEDist K u (P s) + internalEDist K (P s) (P t) +
        internalEDist K (P t) v ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hleftfin, hmidfin⟩,
        hrightfin⟩
    have hreal := ENNReal.toReal_mono hsumfin htri
    rw [hend, ENNReal.toReal_ofReal hℓ0,
      ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hleftfin, hmidfin⟩) hrightfin,
      ENNReal.toReal_add hleftfin hmidfin] at hreal
    have hleftReal : (internalEDist K u (P s)).toReal ≤ s := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hleft
      simpa [ENNReal.toReal_ofReal hs.1] using this
    have hrightReal : (internalEDist K (P t) v).toReal ≤ ℓ - t := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hright
      simpa [ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2)] using this
    linarith
  have hreverse : ENNReal.ofReal (t - s) ≤ internalEDist K (P s) (P t) := by
    apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hmidfin).1
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hst)]
    linarith
  exact le_antisymm hmid hreverse

/-- A positive weight on one subinterval controls its ambient displacement. -/
theorem dist_le_cost_div_of_weight_lower {X : Type*} [MetricSpace X]
    {P : ℝ → X} {w : X → ℝ} {a₀ c s t : ℝ}
    (ha₀ : 0 < a₀) (hc : 0 ≤ c) (hst : s ≤ t)
    (hw : ∀ r ∈ Icc s t, a₀ ≤ w (P r))
    (hcost : weightedLength w P s t ≤ ENNReal.ofReal c) :
    dist (P s) (P t) ≤ c / a₀ := by
  have hlow : ENNReal.ofReal a₀ * edist (P s) (P t) ≤ ENNReal.ofReal c := by
    calc
      ENNReal.ofReal a₀ * edist (P s) (P t)
          ≤ ENNReal.ofReal a₀ * curveLength P s t :=
        mul_le_mul' le_rfl (edist_le_curveLength P hst)
      _ ≤ weightedLength w P s t :=
        ofReal_mul_curveLength_le_weightedLength hst hw
      _ ≤ ENNReal.ofReal c := hcost
  have hprod : a₀ * dist (P s) (P t) ≤ c := by
    rw [edist_dist, ← ENNReal.ofReal_mul ha₀.le] at hlow
    exact (ENNReal.ofReal_le_ofReal_iff hc).1 hlow
  exact (le_div_iff₀ ha₀).2 (by nlinarith [hprod])

end HigherDimLQGMetric
