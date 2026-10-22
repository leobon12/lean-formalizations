import HigherDimLQGMetric.Config.Props
import HigherDimLQGMetric.Coord.Transfer

/-! Relations between outer and inner configuration coordinates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Filter Topology BoundedContinuousFunction unitInterval
open LQGMetric.MetricGeometry
open scoped ENNReal
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Inclusion of the inner annulus into the outer annulus. -/
def configInnerInOuter (u : configInner d) : configOuter d :=
  ⟨u.1, configInner_subset_outer u.2⟩

theorem configInnerInOuter_continuous :
    Continuous (configInnerInOuter (d := d)) := by
  exact continuous_subtype_val.subtype_mk _

/-- The source metric assigns the same path length to both annular internal
metrics along a path contained in the inner annulus. -/
theorem config_internalC_curveLength_eq (D : ContMetric d) (hD : D.IsLength)
    (hd : 2 ≤ d) (P : unitInterval →ᵇ configInner d) :
    curveLengthWith (fun u v : configOuter d =>
      ENNReal.ofReal ((internalC D hD configOuter_isOpen
        (configOuter_isPreconnected hd)) (u, v)))
      (Set.IccExtend zero_le_one (fun t => configInnerInOuter (P t))) 0 1 =
    curveLengthWith (fun u v : configInner d =>
      ENNReal.ofReal ((internalC D hD configInner_isOpen
        (configInner_isPreconnected hd)) (u, v)))
      (Set.IccExtend zero_le_one P) 0 1 := by
  let R : ℝ → Rd d := fun t => (Set.IccExtend zero_le_one P t).1
  have hRc : ContinuousOn R (Icc 0 1) :=
    (continuous_subtype_val.comp (continuous_IccExtend_iff.mpr P.continuous)).continuousOn
  have hRin : MapsTo R (Icc 0 1) (configInner d) :=
    fun t _ => (Set.IccExtend zero_le_one P t).2
  have hRout : MapsTo R (Icc 0 1) (configOuter d) :=
    fun t ht => configInner_subset_outer (hRin ht)
  have houter (u v : configOuter d) :
      ENNReal.ofReal ((internalC D hD configOuter_isOpen
        (configOuter_isPreconnected hd)) (u, v)) = D.internal (configOuter d) u.1 v.1 := by
    change ENNReal.ofReal ((D.internal (configOuter d) u.1 v.1).toReal) = _
    exact ENNReal.ofReal_toReal
      (D.internal_ne_top_of_isPreconnected hD configOuter_isOpen
        (configOuter_isPreconnected hd) u.2 v.2)
  have hinner (u v : configInner d) :
      ENNReal.ofReal ((internalC D hD configInner_isOpen
        (configInner_isPreconnected hd)) (u, v)) = D.internal (configInner d) u.1 v.1 := by
    change ENNReal.ofReal ((D.internal (configInner d) u.1 v.1).toReal) = _
    exact ENNReal.ofReal_toReal
      (D.internal_ne_top_of_isPreconnected hD configInner_isOpen
        (configInner_isPreconnected hd) u.2 v.2)
  have ho : curveLengthWith (fun u v : configOuter d =>
      ENNReal.ofReal ((internalC D hD configOuter_isOpen
        (configOuter_isPreconnected hd)) (u, v)))
      (Set.IccExtend zero_le_one (fun t => configInnerInOuter (P t))) 0 1 = D.len R 0 1 := by
    calc
      _ = curveLengthWith (fun u v : configOuter d => D.internal (configOuter d) u.1 v.1)
          (Set.IccExtend zero_le_one (fun t => configInnerInOuter (P t))) 0 1 := by
            apply curveLengthWith_congr
            intro u v _ _ _
            exact houter _ _
      _ = curveLengthWith (D.internal (configOuter d)) R 0 1 := by rfl
      _ = D.len R 0 1 := D.curveLengthWith_internal hRc hRout
  have hi : curveLengthWith (fun u v : configInner d =>
      ENNReal.ofReal ((internalC D hD configInner_isOpen
        (configInner_isPreconnected hd)) (u, v)))
      (Set.IccExtend zero_le_one P) 0 1 = D.len R 0 1 := by
    calc
      _ = curveLengthWith (fun u v : configInner d => D.internal (configInner d) u.1 v.1)
          (Set.IccExtend zero_le_one P) 0 1 := by
            apply curveLengthWith_congr
            intro u v _ _ _
            exact hinner _ _
      _ = curveLengthWith (D.internal (configInner d)) R 0 1 := by rfl
      _ = D.len R 0 1 := D.curveLengthWith_internal hRc hRin
  exact ho.trans hi.symm

theorem configOriginal_P4 (hd : 2 ≤ d) (c C : ℝ)
    {q : ConfigC d} (hq : q ∈ configOriginal hd c C)
    (P : unitInterval →ᵇ configInner d) :
    (curveLengthWith (fun u v : configOuter d => ENNReal.ofReal (q.1 (u, v)))
        (Set.IccExtend zero_le_one (fun t => configInnerInOuter (P t))) 0 1 =
      curveLengthWith (fun u v : configInner d => ENNReal.ofReal (q.2.2.1 (u, v)))
        (Set.IccExtend zero_le_one P) 0 1) ∧
    (curveLengthWith (fun u v : configOuter d => ENNReal.ofReal (q.2.1 (u, v)))
        (Set.IccExtend zero_le_one (fun t => configInnerInOuter (P t))) 0 1 =
      curveLengthWith (fun u v : configInner d => ENNReal.ofReal (q.2.2.2 (u, v)))
        (Set.IccExtend zero_le_one P) 0 1) := by
  obtain ⟨D, Dt, hD, hDt, -, rfl⟩ := hq
  constructor
  · simpa only [configC, configScaledMetric_one] using
      config_internalC_curveLength_eq D hD hd P
  · simpa only [configC, configScaledMetric_one] using
      config_internalC_curveLength_eq Dt hDt hd P

theorem configC_mem_original (hd : 2 ≤ d) {c C : ℝ}
    (D Dt : ContMetric d) (hD : D.IsLength) (hDt : Dt.IsLength)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (z : Rd d)
    (hcmp : ∀ u v : Rd d,
      c * D.1 (u, v) ≤ Dt.1 (u, v) ∧
      Dt.1 (u, v) ≤ C * D.1 (u, v)) :
    configC hd D Dt hD hDt hs hr z ∈ configOriginal hd c C := by
  let E := configScaledMetric D hs hr z
  let Et := configScaledMetric Dt hs hr z
  refine ⟨E, Et,
    configScaledMetric_isLength D hD hs hr z,
    configScaledMetric_isLength Dt hDt hs hr z, ?_, ?_⟩
  · intro u v
    dsimp [E, Et]
    simp only [configScaledMetric, ContMetric.smul_apply, ContMetric.affine_apply]
    have h := hcmp (r • u + z) (r • v + z)
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left h.1 (inv_pos.mpr hs).le]
    · nlinarith [mul_le_mul_of_nonneg_left h.2 (inv_pos.mpr hs).le]
  · simp only [E, Et, configC, configScaledMetric_one]

/-- A compact collar around a point of an open subdomain, with a positive
Euclidean gap between its core and the collar boundary. -/
theorem config_compact_collar {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    {V : Set X} (hV : IsOpen V) {z : X} (hz : z ∈ V) :
    ∃ K O : Set X, K ∈ 𝓝 z ∧ IsCompact K ∧ K ⊆ O ∧ IsOpen O ∧
      IsCompact (closure O) ∧ closure O ⊆ V ∧
      ∃ η : ℝ, 0 < η ∧ ∀ x ∈ K, ∀ y ∈ frontier O, η ≤ dist x y := by
  obtain ⟨O, hO, hzO, hOV, hOc⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton hV
      (by simpa using hz)
  have hzO' : z ∈ O := hzO (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hO.mem_nhds hzO')
  let K : Set X := Metric.closedBall z (r / 2)
  have hKO : K ⊆ O :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hK : IsCompact K := hOc.of_isClosed_subset Metric.isClosed_closedBall
    (hKO.trans subset_closure)
  have hKn : K ∈ 𝓝 z :=
    Filter.mem_of_superset (Metric.ball_mem_nhds z (by linarith))
      Metric.ball_subset_closedBall
  have hdis : Disjoint K (frontier O) := by
    rw [Set.disjoint_iff]
    intro x hx
    exact (disjoint_frontier_iff_isOpen.mpr hO).symm.le_bot ⟨hKO hx.1, hx.2⟩
  obtain ⟨η, hη, hsep⟩ := Metric.exists_pos_forall_lt_edist hK isClosed_frontier hdis
  refine ⟨K, O, hKn, hK, hKO, hO, hOc, hOV, (η : ℝ), ?_, ?_⟩
  · exact_mod_cast hη
  · intro x hx y hy
    have h := hsep x hx y hy
    rw [edist_dist] at h
    apply (ENNReal.ofReal_le_ofReal_iff dist_nonneg).1
    simpa only [ENNReal.ofReal_coe_nnreal] using h.le

/-- A coordinate metric remains a coordinate on any subspace. -/
theorem IsCoordinate.restrictTo {X : Type*} [MetricSpace X]
    {ρ : X × X → ℝ} (hρ : IsCoordinate ρ) (S : Set X) :
    IsCoordinate (fun p : S × S => ρ (p.1.1, p.2.1)) := by
  let rhoS : S × S → ℝ := fun p => ρ (p.1.1, p.2.1)
  let hrhoS : IsMetricFun rhoS := HigherDimLQGMetric.IsMetricFun.restrictTo hρ.metric S
  have hrhoSpt : Continuous (MetricFunSpace.pt rhoS hrhoS) := by
    refine Metric.continuous_iff.2 fun x ε hε => ?_
    have hc : Continuous fun y : S => rhoS (y, x) :=
      (hρ.continuous.comp
        ((continuous_subtype_val.comp continuous_id).prodMk
          (continuous_subtype_val.comp continuous_const)))
    obtain ⟨δ, hδ, hsmall⟩ := Metric.continuous_iff.1 hc x ε hε
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have := hsmall y hy
    rw [show rhoS (x, x) = 0 from hrhoS.self_eq_zero x, Real.dist_eq, sub_zero] at this
    change rhoS (y, x) < ε
    exact (le_abs_self _).trans_lt this
  have hj : LipschitzWith 1
      (fun x : MetricFunSpace rhoS hrhoS =>
        MetricFunSpace.pt ρ hρ.metric (x : S).1) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    change ρ ((x : S).1, (y : S).1) ≤ 1 * rhoS ((x : S), (y : S))
    simp [rhoS]
  have hrhoSval : Continuous (LQGMetric.metricFunSpaceVal rhoS hrhoS) :=
    (hρ.val_continuous.comp hj.continuous).subtype_mk _
  exact ⟨hrhoS, hrhoSpt, hrhoSval⟩

/-- Transport a coordinate metric across a homeomorphism. -/
theorem IsCoordinate.pullbackHomeomorph {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] {ρ : X × X → ℝ}
    (hρ : IsCoordinate ρ) (e : Y ≃ₜ X) :
    IsCoordinate (fun p : Y × Y => ρ (e p.1, e p.2)) := by
  let rhoY : Y × Y → ℝ := fun p => ρ (e p.1, e p.2)
  have hrhoY : IsMetricFun rhoY := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x; exact hρ.metric.self_eq_zero (e x)
    · intro x y h; exact e.injective (hρ.metric.eq_of_eq_zero _ _ h)
    · intro x y; exact hρ.metric.symm (e x) (e y)
    · intro x y z; exact hρ.metric.triangle (e x) (e y) (e z)
  have hpt : Continuous (MetricFunSpace.pt rhoY hrhoY) := by
    refine Metric.continuous_iff.2 fun x ε hε => ?_
    have hc : Continuous fun y : Y => rhoY (y, x) :=
      (hρ.continuous.comp (e.continuous.prodMk
        (continuous_const : Continuous (fun _ : Y => e x))))
    obtain ⟨δ, hδ, hsmall⟩ := Metric.continuous_iff.1 hc x ε hε
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have := hsmall y hy
    rw [show rhoY (x, x) = 0 from hrhoY.self_eq_zero x, Real.dist_eq, sub_zero] at this
    change rhoY (y, x) < ε
    exact (le_abs_self _).trans_lt this
  have hj : LipschitzWith 1
      (fun x : MetricFunSpace rhoY hrhoY =>
        MetricFunSpace.pt ρ hρ.metric (e (x : Y))) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    change ρ (e (x : Y), e (y : Y)) ≤ 1 * rhoY ((x : Y), (y : Y))
    simp [rhoY]
  have hval : Continuous (LQGMetric.metricFunSpaceVal rhoY hrhoY) := by
    have heq : (fun x : MetricFunSpace rhoY hrhoY =>
        e.symm (LQGMetric.metricFunSpaceVal ρ hρ.metric
          (MetricFunSpace.pt ρ hρ.metric (e (x : Y))))) =
        LQGMetric.metricFunSpaceVal rhoY hrhoY := by
      funext x
      exact e.left_inv x
    rw [← heq]
    exact e.symm.continuous.comp (hρ.val_continuous.comp hj.continuous)
  exact ⟨hrhoY, hpt, hval⟩

theorem IsLengthCoordinate.pullbackHomeomorph {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] {ρ : X × X → ℝ}
    (hρ : IsLengthCoordinate ρ) (e : Y ≃ₜ X) :
    IsLengthCoordinate (fun p : Y × Y => ρ (e p.1, e p.2)) := by
  let rhoY : Y × Y → ℝ := fun p => ρ (e p.1, e p.2)
  let hcoord := hρ.toIsCoordinate.pullbackHomeomorph e
  let hm : IsMetricFun rhoY := hcoord.metric
  refine ⟨hm, hcoord.pt_continuous, hcoord.val_continuous, ?_⟩
  intro x y ε hε
  let fx : MetricFunSpace ρ hρ.metric := MetricFunSpace.pt ρ hρ.metric (e (x : Y))
  let fy : MetricFunSpace ρ hρ.metric := MetricFunSpace.pt ρ hρ.metric (e (y : Y))
  obtain ⟨γ, hγ⟩ := hρ.length fx fy ε hε
  let f : MetricFunSpace ρ hρ.metric → MetricFunSpace rhoY hm :=
    fun w => MetricFunSpace.pt rhoY hm (e.symm
      (LQGMetric.metricFunSpaceVal ρ hρ.metric w))
  have hf : Continuous f := hcoord.pt_continuous.comp
    (e.symm.continuous.comp hρ.val_continuous)
  have hfedist (a b : MetricFunSpace ρ hρ.metric) :
      edist (f a) (f b) = 1 * edist a b := by
    rw [one_mul, edist_dist, edist_dist]
    change ENNReal.ofReal
      (ρ (e (e.symm (LQGMetric.metricFunSpaceVal ρ hρ.metric a)),
        e (e.symm (LQGMetric.metricFunSpaceVal ρ hρ.metric b)))) =
      ENNReal.ofReal (ρ (LQGMetric.metricFunSpaceVal ρ hρ.metric a,
        LQGMetric.metricFunSpaceVal ρ hρ.metric b))
    simp only [e.apply_symm_apply]
  let δ : Path x y :=
    { toFun := fun t => f (γ t)
      continuous_toFun := hf.comp γ.continuous
      source' := by
        rw [γ.source]
        change e.symm (e (x : Y)) = x
        exact e.left_inv _
      target' := by
        rw [γ.target]
        change e.symm (e (y : Y)) = y
        exact e.left_inv _ }
  refine ⟨δ, ?_⟩
  have hlen : pathLength δ = pathLength (γ.map hf) := rfl
  rw [hlen, pathLength_map_of_edist_eq hfedist hf γ, one_mul]
  rw [edist_dist]
  change pathLength γ ≤ ENNReal.ofReal (rhoY ((x : Y), (y : Y))) + ENNReal.ofReal ε
  simpa only [fx, fy, edist_dist, MetricFunSpace.dist_pt] using hγ

def configInnerOuterHomeomorph (d : ℕ) :
    configInner d ≃ₜ {u : configOuter d | u.1 ∈ configInner d} where
  toFun u := ⟨configInnerInOuter u, u.2⟩
  invFun u := ⟨u.1.1, u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := configInnerInOuter_continuous.subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem configOuter_pullback_isCoordinate (hd : 2 ≤ d) (c C : ℝ)
    (β : ConfigBounds d) {q : ConfigC d}
    (hq : q ∈ configCompactFamily hd c C β) :
    IsCoordinate (fun p : configInner d × configInner d =>
      q.1 (configInnerInOuter p.1, configInnerInOuter p.2)) := by
  have hqout := (configCompactFamily_outer_P1 hd c C β hq).1
  let V : Set (configOuter d) := {u | u.1 ∈ configInner d}
  have hres := hqout.restrictTo V
  convert hres.pullbackHomeomorph (configInnerOuterHomeomorph d) using 1
  funext p
  rfl

/-- A path contained in the inner annulus, viewed first in the outer subtype. -/
def configLiftInnerPath (Q : unitInterval →ᵇ configOuter d)
    (hQ : ∀ t, (Q t).1 ∈ configInner d) : unitInterval →ᵇ configInner d :=
  mkOfCompact ⟨fun t => ⟨(Q t).1, hQ t⟩,
    (continuous_subtype_val.comp Q.continuous).subtype_mk _⟩

theorem configLiftInnerPath_outer (Q : unitInterval →ᵇ configOuter d)
    (hQ : ∀ t, (Q t).1 ∈ configInner d) :
    (fun t => configInnerInOuter (configLiftInnerPath Q hQ t)) = Q := by
  funext t
  apply Subtype.ext
  rfl

theorem configLiftInnerPath_curveLength (f : C(configOuter d × configOuter d, ℝ))
    (Q : unitInterval →ᵇ configOuter d)
    (hQ : ∀ t, (Q t).1 ∈ configInner d) :
    curveLengthWith (fun u v : configInner d =>
      ENNReal.ofReal (f (configInnerInOuter u, configInnerInOuter v)))
      (Set.IccExtend zero_le_one (configLiftInnerPath Q hQ)) 0 1 =
    curveLengthWith (fun u v : configOuter d => ENNReal.ofReal (f (u, v)))
      (Set.IccExtend zero_le_one Q) 0 1 := by
  have heq := configLiftInnerPath_outer Q hQ
  calc
    _ = curveLengthWith (fun u v : configOuter d => ENNReal.ofReal (f (u, v)))
        (Set.IccExtend zero_le_one (fun t =>
          configInnerInOuter (configLiftInnerPath Q hQ t))) 0 1 := by rfl
    _ = _ := by rw [heq]

/-- (P4) in a projection-independent form; the two intended instances are
the two metric assignments in the configuration. -/
theorem configCompactFamily_P4_one (hd : 2 ≤ d) (c C : ℝ)
    (β : ConfigBounds d)
    (πo : ConfigC d → C(configOuter d × configOuter d, ℝ))
    (πi : ConfigC d → C(configInner d × configInner d, ℝ))
    (hπo : Continuous πo) (hπi : Continuous πi)
    (hLo : ∀ q ∈ configOriginal hd c C, IsLengthCoordinate (πo q))
    (hLi : ∀ q ∈ configOriginal hd c C, IsLengthCoordinate (πi q))
    (hBo : ∀ q ∈ configBoundSet β,
      πo q ∈ configBoundOne (configOuterExhaust d) β.outer)
    (hBi : ∀ q ∈ configBoundSet β,
      πi q ∈ configBoundOne (configInnerExhaust d) β.inner)
    (hLen : ∀ q ∈ configOriginal hd c C, ∀ P : unitInterval →ᵇ configInner d,
      curveLengthWith (fun u v : configOuter d => ENNReal.ofReal (πo q (u, v)))
        (Set.IccExtend zero_le_one (fun t => configInnerInOuter (P t))) 0 1 =
      curveLengthWith (fun u v : configInner d => ENNReal.ofReal (πi q (u, v)))
        (Set.IccExtend zero_le_one P) 0 1)
    {q : ConfigC d} (hq : q ∈ configCompactFamily hd c C β)
    (P : unitInterval →ᵇ configInner d) :
    curveLengthWith (fun u v : configOuter d => ENNReal.ofReal (πo q (u, v)))
      (Set.IccExtend zero_le_one (fun t => configInnerInOuter (P t))) 0 1 =
    curveLengthWith (fun u v : configInner d => ENNReal.ofReal (πi q (u, v)))
      (Set.IccExtend zero_le_one P) 0 1 := by
  obtain ⟨F, hF, hlim⟩ := configCompactFamily_exists_seq hd c C β hq
  let ιpair : configInner d × configInner d → configOuter d × configOuter d :=
    fun p => (configInnerInOuter p.1, configInnerInOuter p.2)
  have hιpair : Continuous ιpair :=
    configInnerInOuter_continuous.prodMap configInnerInOuter_continuous
  let Ro : ConfigC d → C(configInner d × configInner d, ℝ) :=
    fun p => (πo p).comp ⟨ιpair, hιpair⟩
  have hRo : Continuous Ro := (ContinuousMap.continuous_precomp _).comp hπo
  have hρconv : TendstoLocallyUniformly (fun n => ⇑(Ro (F n))) (⇑(Ro q)) atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp ((hRo.tendsto q).comp hlim)
  have hτconv : TendstoLocallyUniformly (fun n => ⇑(πi (F n))) (⇑(πi q)) atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp ((hπi.tendsto q).comp hlim)
  have hOuterCoord (p : ConfigC d) (hp : p ∈ configCompactFamily hd c C β) :
      IsCoordinate (πo p) :=
    (configCompactFamily_project_P1 hd c C β (configOuterExhaust d) β.outer
      πo hπo hLo hBo hp).1
  let V : Set (configOuter d) := {u | u.1 ∈ configInner d}
  have hV : IsOpen V := configInner_isOpen.preimage continuous_subtype_val
  have hRestrict (p : ConfigC d) (hp : IsCoordinate (πo p)) :
      IsCoordinate (Ro p) := by
    have hr := (hp.restrictTo V).pullbackHomeomorph
      (configInnerOuterHomeomorph d)
    convert hr using 1
    funext pair
    rfl
  have hρn (n : ℕ) : IsCoordinate (Ro (F n)) :=
    hRestrict (F n) (hLo (F n) (hF n).1).toIsCoordinate
  have hτn (n : ℕ) : IsLengthCoordinate (πi (F n)) :=
    hLi (F n) (hF n).1
  have hρlim : IsCoordinate (Ro q) := hRestrict q (hOuterCoord q hq)
  have hτlim : IsCoordinate (πi q) :=
    (configCompactFamily_project_P1 hd c C β (configInnerExhaust d) β.inner
      πi hπi hLi hBi hq).1
  have hmod : ∀ L : Set (configOuter d), IsCompact L → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ u ∈ L, ∀ v ∈ L,
        πo (F n) (u, v) < δ → dist u v < ε :=
    configBoundOne_uniformLower (configOuterExhaust d) β.outer
      (fun n => πo (F n)) (fun n => hBo (F n) (hF n).2)
  have hoconv : TendstoLocallyUniformly (fun n => ⇑(πo (F n))) (⇑(πo q)) atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp ((hπo.tendsto q).comp hlim)
  have hlocal : ∀ z : configInner d, ∃ N : Set (configInner d), N ∈ 𝓝 z ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ u ∈ N, ∀ v ∈ N,
        Ro (F n) (u, v) < δ →
          ∃ R : unitInterval →ᵇ configInner d, R 0 = u ∧ R 1 = v ∧
            curveLengthWith (fun p q => ENNReal.ofReal (Ro (F n) (p, q)))
              (Set.IccExtend zero_le_one R) 0 1 =
              ENNReal.ofReal (Ro (F n) (u, v)) := by
    intro z
    have hzV : configInnerInOuter z ∈ V := z.2
    obtain ⟨K, O, hKn, hK, hKO, hO, hOc, hOV, η, hη, hsep⟩ :=
      config_compact_collar hV hzV
    obtain ⟨m, hm⟩ := (configOuterExhaust d).exists_superset_of_isCompact hOc
    have hlower : ∀ n, ∀ u ∈ closure O, ∀ v ∈ closure O,
        β.outer.lower m (dist u v) ≤ πo (F n) (u, v) := by
      intro n u hu v hv
      exact ((hBo (F n) (hF n).2).1 m (u, v) (hm hu) (hm hv)).1
    have hP2 := lemma23 (fun n => ⇑(πo (F n))) (⇑(πo q))
      (fun n => hLo (F n) (hF n).1) hoconv hmod hKO hO hOc
      (β.outer.lower m) (β.outer.lower_mono m) (β.outer.lower_pos m)
      hlower η hη hsep
    let N : Set (configInner d) := configInnerInOuter ⁻¹' K
    have hN : N ∈ 𝓝 z := configInnerInOuter_continuous.continuousAt.preimage_mem_nhds hKn
    refine ⟨N, hN, β.outer.lower m η / 4,
      div_pos (β.outer.lower_pos m η hη) (by norm_num), ?_⟩
    intro n u hu v hv hsmall
    obtain ⟨Q, hQ, hQ0, hQ1, hQlen⟩ := hP2.1 n _ hu _ hv hsmall
    have hQinner (t : unitInterval) : (Q t).1 ∈ configInner d := hOV (hQ t)
    let R := configLiftInnerPath Q hQinner
    refine ⟨R, ?_, ?_, ?_⟩
    · apply Subtype.ext
      change (Q 0).1 = u.1
      simpa only [configInnerInOuter] using congrArg Subtype.val hQ0
    · apply Subtype.ext
      change (Q 1).1 = v.1
      simpa only [configInnerInOuter] using congrArg Subtype.val hQ1
    · calc
        _ = curveLengthWith (fun a b : configOuter d =>
              ENNReal.ofReal (πo (F n) (a, b)))
              (Set.IccExtend zero_le_one Q) 0 1 :=
            configLiftInnerPath_curveLength (πo (F n)) Q hQinner
        _ = ENNReal.ofReal (Ro (F n) (u, v)) := hQlen
  have hlen (n : ℕ) (R : unitInterval →ᵇ configInner d) :
      curveLengthWith (fun u v => ENNReal.ofReal (Ro (F n) (u, v)))
        (Set.IccExtend zero_le_one R) 0 1 =
      curveLengthWith (fun u v => ENNReal.ofReal (πi (F n) (u, v)))
        (Set.IccExtend zero_le_one R) 0 1 := by
    exact hLen (F n) (hF n).1 R
  have hresult := lemma22iii (fun n => ⇑(Ro (F n))) (fun n => ⇑(πi (F n)))
    (⇑(Ro q)) (⇑(πi q)) hρn hτn hρlim hτlim hρconv hτconv
    hlen hlocal P
  exact hresult

theorem configCompactFamily_P4 (hd : 2 ≤ d) (c C : ℝ)
    (β : ConfigBounds d) {q : ConfigC d}
    (hq : q ∈ configCompactFamily hd c C β)
    (P : unitInterval →ᵇ configInner d) :
    (curveLengthWith (fun u v : configOuter d => ENNReal.ofReal (q.1 (u, v)))
        (Set.IccExtend zero_le_one (fun t => configInnerInOuter (P t))) 0 1 =
      curveLengthWith (fun u v : configInner d => ENNReal.ofReal (q.2.2.1 (u, v)))
        (Set.IccExtend zero_le_one P) 0 1) ∧
    (curveLengthWith (fun u v : configOuter d => ENNReal.ofReal (q.2.1 (u, v)))
        (Set.IccExtend zero_le_one (fun t => configInnerInOuter (P t))) 0 1 =
      curveLengthWith (fun u v : configInner d => ENNReal.ofReal (q.2.2.2 (u, v)))
        (Set.IccExtend zero_le_one P) 0 1) := by
  constructor
  · exact configCompactFamily_P4_one hd c C β
      (fun p => p.1) (fun p => p.2.2.1)
      continuous_fst (continuous_fst.comp (continuous_snd.comp continuous_snd))
      (fun p hp => configOriginal_outer_length hd c C hp)
      (fun p hp => configOriginal_inner_length hd c C hp)
      (fun p hp => hp.1) (fun p hp => hp.2.2.1)
      (fun p hp R => (configOriginal_P4 hd c C hp R).1) hq P
  · exact configCompactFamily_P4_one hd c C β
      (fun p => p.2.1) (fun p => p.2.2.2)
      (continuous_fst.comp continuous_snd)
      (continuous_snd.comp (continuous_snd.comp continuous_snd))
      (fun p hp => configOriginal_outer_tilde_length hd c C hp)
      (fun p hp => configOriginal_inner_tilde_length hd c C hp)
      (fun p hp => hp.2.1) (fun p hp => hp.2.2.2)
      (fun p hp R => (configOriginal_P4 hd c C hp R).2) hq P

/-- The closure of the inner annulus inside the outer annulus is compact. -/
theorem configInnerInOuter_closure_compact :
    IsCompact (closure ({u : configOuter d | u.1 ∈ configInner d})) := by
  let K : Set (Rd d) := Metric.closedBall 0 4 \ Metric.ball 0 (2 / 3)
  have hK : IsCompact K := (isCompact_closedBall (0 : Rd d) 4).diff (Metric.isOpen_ball)
  have hKO : K ⊆ configOuter d := by
    intro x hx
    have hfar : 2 / 3 ≤ dist x 0 := by
      have hn : x ∉ Metric.ball 0 (2 / 3) := hx.2
      simpa [Metric.mem_ball, dist_comm, not_lt] using hn
    have hnear : dist x 0 ≤ 4 := by
      simpa [Metric.mem_closedBall, dist_comm] using hx.1
    change 1 / 2 < dist x 0 ∧ dist x 0 < 5
    constructor <;> linarith
  let f : K → configOuter d := fun x => ⟨x.1, hKO x.2⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hcompact : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hrange : IsCompact (Set.range f) := by
    simpa only [Set.image_univ] using (@isCompact_univ K _ hcompact).image hf
  have hV : ({u : configOuter d | u.1 ∈ configInner d}) ⊆ Set.range f := by
    intro u hu
    have hinner : 3 / 4 < ‖u.1 - (0 : Rd d)‖ ∧
        ‖u.1 - (0 : Rd d)‖ < 7 / 2 := hu
    have hdist : 3 / 4 < dist 0 u.1 ∧ dist 0 u.1 < 7 / 2 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hinner
    have huK : u.1 ∈ K := by
      constructor
      · rw [Metric.mem_closedBall, dist_comm]
        linarith [hdist.2]
      · rw [Metric.mem_ball, dist_comm]
        linarith [hdist.1]
    exact ⟨⟨u.1, huK⟩, Subtype.ext rfl⟩
  exact hrange.of_isClosed_subset isClosed_closure
    (closure_minimal hV hrange.isClosed)

/-- (P5): bounded inner distances along an approximating sequence produce an
outer limit path in the closed inner annulus. -/
theorem configCompactFamily_P5_one (hd : 2 ≤ d) (c C : ℝ)
    (β : ConfigBounds d)
    (πo : ConfigC d → C(configOuter d × configOuter d, ℝ))
    (πi : ConfigC d → C(configInner d × configInner d, ℝ))
    (hπo : Continuous πo)
    (hLo : ∀ q ∈ configOriginal hd c C, IsLengthCoordinate (πo q))
    (hLi : ∀ q ∈ configOriginal hd c C, IsLengthCoordinate (πi q))
    (hBo : ∀ q ∈ configBoundSet β,
      πo q ∈ configBoundOne (configOuterExhaust d) β.outer)
    (hLen : ∀ q ∈ configOriginal hd c C, ∀ P : unitInterval →ᵇ configInner d,
      curveLengthWith (fun u v : configOuter d => ENNReal.ofReal (πo q (u, v)))
        (Set.IccExtend zero_le_one (fun t => configInnerInOuter (P t))) 0 1 =
      curveLengthWith (fun u v : configInner d => ENNReal.ofReal (πi q (u, v)))
        (Set.IccExtend zero_le_one P) 0 1)
    (F : ℕ → ConfigC d)
    (hF : ∀ n, F n ∈ configOriginal hd c C ∩ configBoundSet β)
    (q : ConfigC d) (hlim : Tendsto F atTop (𝓝 q))
    (xseq yseq : ℕ → {u : configOuter d | u.1 ∈ configInner d})
    (x y : configOuter d)
    (hxlim : Tendsto (fun n => (xseq n : configOuter d)) atTop (𝓝 x))
    (hylim : Tendsto (fun n => (yseq n : configOuter d)) atTop (𝓝 y))
    (A : ℝ)
    (hbound : ∀ n, πi (F n)
      ((configInnerOuterHomeomorph d).symm (xseq n),
       (configInnerOuterHomeomorph d).symm (yseq n)) ≤ A) :
    ∃ Q : unitInterval →ᵇ configOuter d,
      (∀ t, Q t ∈ closure ({u : configOuter d | u.1 ∈ configInner d})) ∧
      Q 0 = x ∧ Q 1 = y ∧
      curveLengthWith (fun u v => ENNReal.ofReal (πo q (u, v)))
        (Set.IccExtend zero_le_one Q) 0 1 ≤ ENNReal.ofReal A := by
  let V : Set (configOuter d) := {u | u.1 ∈ configInner d}
  let e : V ≃ₜ configInner d := (configInnerOuterHomeomorph d).symm
  let ρ : ℕ → configOuter d × configOuter d → ℝ := fun n => ⇑(πo (F n))
  let τ : ℕ → V × V → ℝ := fun n p => πi (F n) (e p.1, e p.2)
  have hρ (n : ℕ) : IsCoordinate (ρ n) :=
    (hLo (F n) (hF n).1).toIsCoordinate
  have hτ (n : ℕ) : IsLengthCoordinate (τ n) :=
    (hLi (F n) (hF n).1).pullbackHomeomorph e
  have hL : IsCompact (closure V) := configInnerInOuter_closure_compact
  have hρconv : TendstoLocallyUniformly ρ (⇑(πo q)) atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp
      ((hπo.tendsto q).comp hlim)
  have hconv : TendstoUniformlyOn ρ (⇑(πo q)) atTop
      (closure V ×ˢ closure V) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (hL.prod hL)).1 hρconv.tendstoLocallyUniformlyOn
  have hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ n, ∀ u ∈ closure V, ∀ v ∈ closure V,
        ρ n (u, v) < δ → dist u v < ε :=
    configBoundOne_uniformLower (configOuterExhaust d) β.outer
      (fun n => πo (F n)) (fun n => hBo (F n) (hF n).2)
      (closure V) hL
  have hlen (n : ℕ) (P : unitInterval →ᵇ V) :
      curveLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v)))
        (Set.IccExtend zero_le_one (fun t : unitInterval => (P t : configOuter d))) 0 1 =
      curveLengthWith (fun u v => ENNReal.ofReal (τ n (u, v)))
        (Set.IccExtend zero_le_one P) 0 1 := by
    let R : unitInterval →ᵇ configInner d :=
      mkOfCompact ⟨fun t => e (P t), e.continuous.comp P.continuous⟩
    have heq (t : unitInterval) : configInnerInOuter (R t) = (P t : configOuter d) := by
      apply Subtype.ext
      rfl
    have h := hLen (F n) (hF n).1 R
    convert h using 1
    congr 1
    rfl
  exact lemma22iv V ρ (⇑(πo q)) τ hρ hτ hL hconv hmod hlen
    xseq yseq x y hxlim hylim A hbound

theorem configCompactFamily_outer_P5 (hd : 2 ≤ d) (c C : ℝ)
    (β : ConfigBounds d) (F : ℕ → ConfigC d)
    (hF : ∀ n, F n ∈ configOriginal hd c C ∩ configBoundSet β)
    (q : ConfigC d) (hlim : Tendsto F atTop (𝓝 q))
    (xseq yseq : ℕ → {u : configOuter d | u.1 ∈ configInner d})
    (x y : configOuter d)
    (hxlim : Tendsto (fun n => (xseq n : configOuter d)) atTop (𝓝 x))
    (hylim : Tendsto (fun n => (yseq n : configOuter d)) atTop (𝓝 y))
    (A : ℝ)
    (hbound : ∀ n, (F n).2.2.1
      ((configInnerOuterHomeomorph d).symm (xseq n),
       (configInnerOuterHomeomorph d).symm (yseq n)) ≤ A) :
    ∃ Q : unitInterval →ᵇ configOuter d,
      (∀ t, Q t ∈ closure ({u : configOuter d | u.1 ∈ configInner d})) ∧
      Q 0 = x ∧ Q 1 = y ∧
      curveLengthWith (fun u v => ENNReal.ofReal (q.1 (u, v)))
        (Set.IccExtend zero_le_one Q) 0 1 ≤ ENNReal.ofReal A := by
  exact configCompactFamily_P5_one hd c C β
    (fun p => p.1) (fun p => p.2.2.1) continuous_fst
    (fun p hp => configOriginal_outer_length hd c C hp)
    (fun p hp => configOriginal_inner_length hd c C hp)
    (fun p hp => hp.1)
    (fun p hp R => (configOriginal_P4 hd c C hp R).1)
    F hF q hlim xseq yseq x y hxlim hylim A hbound

theorem configCompactFamily_outer_tilde_P5 (hd : 2 ≤ d) (c C : ℝ)
    (β : ConfigBounds d) (F : ℕ → ConfigC d)
    (hF : ∀ n, F n ∈ configOriginal hd c C ∩ configBoundSet β)
    (q : ConfigC d) (hlim : Tendsto F atTop (𝓝 q))
    (xseq yseq : ℕ → {u : configOuter d | u.1 ∈ configInner d})
    (x y : configOuter d)
    (hxlim : Tendsto (fun n => (xseq n : configOuter d)) atTop (𝓝 x))
    (hylim : Tendsto (fun n => (yseq n : configOuter d)) atTop (𝓝 y))
    (A : ℝ)
    (hbound : ∀ n, (F n).2.2.2
      ((configInnerOuterHomeomorph d).symm (xseq n),
       (configInnerOuterHomeomorph d).symm (yseq n)) ≤ A) :
    ∃ Q : unitInterval →ᵇ configOuter d,
      (∀ t, Q t ∈ closure ({u : configOuter d | u.1 ∈ configInner d})) ∧
      Q 0 = x ∧ Q 1 = y ∧
      curveLengthWith (fun u v => ENNReal.ofReal (q.2.1 (u, v)))
        (Set.IccExtend zero_le_one Q) 0 1 ≤ ENNReal.ofReal A := by
  exact configCompactFamily_P5_one hd c C β
    (fun p => p.2.1) (fun p => p.2.2.2)
    (continuous_fst.comp continuous_snd)
    (fun p hp => configOriginal_outer_tilde_length hd c C hp)
    (fun p hp => configOriginal_inner_tilde_length hd c C hp)
    (fun p hp => hp.2.1)
    (fun p hp R => (configOriginal_P4 hd c C hp R).2)
    F hF q hlim xseq yseq x y hxlim hylim A hbound

end HigherDimLQGMetric
