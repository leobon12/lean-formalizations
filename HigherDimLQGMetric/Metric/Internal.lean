import HigherDimLQGMetric.Metric.ContMetric
import HigherDimLQGMetric.Metric.Partition
import LQGMetric.Metric.Geodesic

/-!
# Internal metrics of continuous metrics on `ℝ^d`

Packet M1 (Phase A, block A2). Port of LQGMetric's ℂ-typed `Metric/InternalC.lean` (LM Lemma 1.1,
GM S3.1 (a)) from `ℂ` to `Rd d` (ruling M10), plus the basic API of the frozen
`ContMetric.internal` and the "internal metric of an internal metric" identity.

For `D : ContMetric d` and `U ⊆ ℝ^d`, `D.internal U z w ∈ [0, ∞]` (frozen) is the infimum of the
`D`-lengths of paths in `U` from `z` to `w`.

* Curve form (`internal_eq_iInf_len`): the infimum of `D.len P 0 1` over curves
  `P : [0, 1] → U` continuous for the Euclidean topology; `internal_le_len` for curves on any
  `[a, b]`.
* Metric properties: `internal_self`, `internal_comm`, `internal_triangle`,
  `ofReal_le_internal` (`D ≤ D(·,·;U)`), antitone in `U` (`internal_anti`), `∞` off `U`.
* Length metrics: `internal_univ_of_isLength` (`D(·,·;ℝ^d) = D`) and the converse
  (`isLength_iff_internal_univ`), the curve form of `IsLength` (`isLength_iff_curves`),
  locality (`internal_eq_of_ball_subset`: near-minimal paths from `z` stay in a `D`-ball in `U`),
  continuity on open sets (**LM Lemma 1.1**, `continuousOn_internal`), finiteness on open
  preconnected sets (`internal_ne_top_of_isPreconnected`), geodesics of proper length metrics
  (`exists_geodesic`, BBI Cor. 2.5.20) and their confinement (`internal_eq_of_le_infEDist_frontier`,
  **GM S3.1 (b)**).
* Frontier localization (**GM S3.1 (a)**): `infEDist_frontier_le_of_internal_eq`,
  `infEDist_frontier_eq_of_internal_eq`, `internal_eq_of_lt_infEDist_frontier`.
* Internal of internal (**BBI Prop. 2.3.12**): partition sums of `D(·,·;U)` along a curve in `U`
  give its `D`-length (`curveLengthWith_internal`), and for `W ⊆ U` the internal distance of `W`
  induced by `D(·,·;U)` is `D(·,·;W)` (`internalWith_internal`); with `W = U`: `D(·,·;U)` is
  the induced length distance of itself (`internalWith_internal_self`).

Proofs as in the 2D layer (own elementary arguments; LM tex:206–216, GM tex:1197).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

namespace ContMetric

variable {d : ℕ}

/-! ### Curve form and metric properties -/

theorem internal_def (D : ContMetric d) (U : Set (Rd d)) (z w : Rd d) :
    D.internal U z w = internalEDist (D.pt '' U) (D.pt z) (D.pt w) := rfl

/-- A continuous curve `P : [a, b] → U` bounds the internal distance of its endpoints. -/
theorem internal_le_len (D : ContMetric d) {U : Set (Rd d)} {P : ℝ → Rd d} {a b : ℝ}
    (hab : a ≤ b) (hP : ContinuousOn P (Icc a b)) (hPU : MapsTo P (Icc a b) U) :
    D.internal U (P a) (P b) ≤ D.len P a b :=
  internalEDist_le_curveLength hab (D.continuous_pt.comp_continuousOn hP)
    fun t ht => ⟨P t, hPU ht, rfl⟩

/-- **Curve form** of the internal metric: the infimum of `D`-lengths of Euclidean-continuous
curves `[0, 1] → U` from `z` to `w`. -/
theorem internal_eq_iInf_len (D : ContMetric d) (U : Set (Rd d)) (z w : Rd d) :
    D.internal U z w = ⨅ (P : ℝ → Rd d) (_ : ContinuousOn P (Icc 0 1)) (_ : P 0 = z)
      (_ : P 1 = w) (_ : MapsTo P (Icc 0 1) U), D.len P 0 1 := by
  apply le_antisymm
  · refine le_iInf fun P => le_iInf fun hc => le_iInf fun h0 => le_iInf fun h1 => le_iInf fun hU =>
      ?_
    have h := D.internal_le_len zero_le_one hc hU
    rwa [h0, h1] at h
  · rw [internal_def, internalEDist_eq_iInf_curve]
    refine le_iInf fun Q => le_iInf fun hc => le_iInf fun h0 => le_iInf fun h1 => le_iInf fun hU =>
      ?_
    refine iInf_le_of_le (D.unpt ∘ Q) <| iInf_le_of_le (D.continuous_unpt.comp_continuousOn hc) <|
      iInf_le_of_le (by simp [h0]) <| iInf_le_of_le (by simp [h1]) <|
      iInf_le_of_le (fun t ht => ?_) le_rfl
    obtain ⟨x, hx, hxt⟩ := hU ht
    simp only [Function.comp_apply, ← hxt, unpt_pt]
    exact hx

theorem le_internal (D : ContMetric d) {U : Set (Rd d)} {z w : Rd d} {e : ℝ≥0∞}
    (h : ∀ P : ℝ → Rd d, ContinuousOn P (Icc 0 1) → P 0 = z → P 1 = w → MapsTo P (Icc 0 1) U →
      e ≤ D.len P 0 1) : e ≤ D.internal U z w := by
  rw [internal_eq_iInf_len]
  exact le_iInf fun P => le_iInf fun hc => le_iInf fun h0 => le_iInf fun h1 => le_iInf fun hU =>
    h P hc h0 h1 hU

theorem ofReal_le_internal (D : ContMetric d) (U : Set (Rd d)) (z w : Rd d) :
    ENNReal.ofReal (D.1 (z, w)) ≤ D.internal U z w := by
  rw [← edist_pt]; exact edist_le_internalEDist _ _ _

theorem internal_self (D : ContMetric d) {U : Set (Rd d)} {z : Rd d} (hz : z ∈ U) :
    D.internal U z z = 0 :=
  internalEDist_self ⟨z, hz, rfl⟩

theorem internal_comm (D : ContMetric d) (U : Set (Rd d)) (z w : Rd d) :
    D.internal U z w = D.internal U w z :=
  internalEDist_comm _ _ _

theorem internal_triangle (D : ContMetric d) (U : Set (Rd d)) (x y z : Rd d) :
    D.internal U x z ≤ D.internal U x y + D.internal U y z :=
  internalEDist_triangle _ _ _ _

/-- **Anti-monotonicity in the domain**: fewer paths in a smaller set. -/
theorem internal_anti (D : ContMetric d) {U V : Set (Rd d)} (hUV : U ⊆ V) (z w : Rd d) :
    D.internal V z w ≤ D.internal U z w :=
  internalEDist_anti (image_mono hUV) _ _

theorem internal_eq_top_of_notMem_right (D : ContMetric d) {U : Set (Rd d)} {z w : Rd d}
    (hw : w ∉ U) : D.internal U z w = ∞ :=
  internalEDist_eq_top_of_notMem_right fun h => hw (D.mem_image_pt.1 h)

theorem internal_eq_top_of_notMem_left (D : ContMetric d) {U : Set (Rd d)} {z w : Rd d}
    (hz : z ∉ U) : D.internal U z w = ∞ :=
  internalEDist_eq_top_of_notMem_left fun h => hz (D.mem_image_pt.1 h)

theorem internal_empty (D : ContMetric d) (z w : Rd d) : D.internal ∅ z w = ∞ :=
  D.internal_eq_top_of_notMem_right (notMem_empty w)

/-! ### Length metrics -/

/-- For a length metric, `D(·,·;ℝ^d) = D`. -/
theorem internal_univ_of_isLength (D : ContMetric d) (hD : D.IsLength) (z w : Rd d) :
    D.internal univ z w = ENNReal.ofReal (D.1 (z, w)) := by
  rw [internal_def, image_univ_of_surjective (fun x => ⟨x, rfl⟩ : Function.Surjective D.pt),
    internalEDist_univ_of_isLengthSpace hD, edist_pt]

/-- `D` is a length metric iff `D(·,·;ℝ^d) = D`. -/
theorem isLength_iff_internal_univ (D : ContMetric d) :
    D.IsLength ↔ ∀ z w : Rd d, D.internal univ z w = ENNReal.ofReal (D.1 (z, w)) := by
  refine ⟨fun hD => D.internal_univ_of_isLength hD, fun h x y ε hε => ?_⟩
  have hx := h (D.unpt x) (D.unpt y)
  rw [internal_def, image_univ_of_surjective (fun x => ⟨x, rfl⟩ : Function.Surjective D.pt),
    pt_unpt, pt_unpt, ← edist_pt, pt_unpt, pt_unpt] at hx
  have hlt : internalEDist univ x y < edist x y + ENNReal.ofReal ε := by
    rw [hx]
    exact ENNReal.lt_add_right (edist_ne_top _ _) (by simpa using hε)
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 hlt
  exact ⟨γ.1, hγ.le⟩

/-- Curve form of `IsLength`: Euclidean-continuous curves on `[0, 1]` of `D`-length at most
`D(z, w) + ε`. -/
theorem isLength_iff_curves (D : ContMetric d) :
    D.IsLength ↔ ∀ z w : Rd d, ∀ ε : ℝ, 0 < ε → ∃ P : ℝ → Rd d, ContinuousOn P (Icc 0 1) ∧
      P 0 = z ∧ P 1 = w ∧ D.len P 0 1 ≤ ENNReal.ofReal (D.1 (z, w)) + ENNReal.ofReal ε := by
  constructor
  · intro hD z w ε hε
    have hlt : D.internal univ z w < ENNReal.ofReal (D.1 (z, w)) + ENNReal.ofReal ε := by
      rw [D.internal_univ_of_isLength hD]
      exact ENNReal.lt_add_right ENNReal.ofReal_ne_top (by simpa using hε)
    rw [internal_eq_iInf_len] at hlt
    simp only [iInf_lt_iff] at hlt
    obtain ⟨P, hc, h0, h1, -, hP⟩ := hlt
    exact ⟨P, hc, h0, h1, hP.le⟩
  · intro h
    rw [isLength_iff_internal_univ]
    intro z w
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
      (D.ofReal_le_internal _ z w)
    obtain ⟨P, hc, h0, h1, hP⟩ := h z w ε (by exact_mod_cast hε)
    rw [ENNReal.ofReal_coe_nnreal] at hP
    calc D.internal univ z w = D.internal univ (P 0) (P 1) := by rw [h0, h1]
      _ ≤ D.len P 0 1 := D.internal_le_len zero_le_one hc (mapsTo_univ _ _)
      _ ≤ _ := hP

/-- **Locality** (LM tex:213–214): for a length metric, if every point `D`-closer than `r` to `z`
lies in `U` and `D(z, w) < r`, then `D(z, w; U) = D(z, w)`. -/
theorem internal_eq_of_ball_subset (D : ContMetric d) (hD : D.IsLength) {U : Set (Rd d)}
    {z w : Rd d} {r : ℝ} (hball : ∀ y, D.1 (z, y) < r → y ∈ U) (hzw : D.1 (z, w) < r) :
    D.internal U z w = ENNReal.ofReal (D.1 (z, w)) := by
  rw [internal_def, ← edist_pt]
  refine internalEDist_eq_edist_of_ball_subset hD (r := ENNReal.ofReal r) (fun x hx => ?_) ?_
  · rw [Metric.mem_eball, edist_comm, ← D.pt_unpt x, edist_pt] at hx
    refine ⟨D.unpt x, hball _ ?_, rfl⟩
    by_contra hge
    exact (ENNReal.ofReal_le_ofReal (not_lt.1 hge)).not_gt hx
  · rw [edist_pt]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (D.nonneg z w)).2 hzw

/-- **LM Lemma 1.1** (continuity): for a length metric `D` and `V` open, `D(·,·;V)` is
continuous on `V × V`. -/
theorem continuousOn_internal (D : ContMetric d) (hD : D.IsLength) {V : Set (Rd d)}
    (hV : IsOpen V) : ContinuousOn (fun p : Rd d × Rd d => D.internal V p.1 p.2) (V ×ˢ V) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let f : V → D.pt '' V := fun z => ⟨D.pt z, z, z.2, rfl⟩
  have hf : Continuous f := (D.continuous_pt.comp continuous_subtype_val).subtype_mk _
  have hc := InternalSpace.continuous_internalEDist hD (D.isOpen_image_pt hV)
  have h1 : Continuous fun p : V ×ˢ V => (⟨p.1.1, (mem_prod.1 p.2).1⟩ : V) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have h2 : Continuous fun p : V ×ˢ V => (⟨p.1.2, (mem_prod.1 p.2).2⟩ : V) :=
    (continuous_snd.comp continuous_subtype_val).subtype_mk _
  exact hc.comp ((hf.comp h1).prodMk (hf.comp h2))

/-- For a length metric, the internal metric of an open preconnected set is finite on it (the
points reachable from `z` by rectifiable paths in `U` form an open and closed subset of `U`). -/
theorem internal_ne_top_of_isPreconnected (D : ContMetric d) (hD : D.IsLength) {U : Set (Rd d)}
    (hU : IsOpen U) (hUc : IsPreconnected U) {z w : Rd d} (hz : z ∈ U) (hw : w ∈ U) :
    D.internal U z w ≠ ⊤ := by
  -- near every point of `U`, the internal distance is finite
  have hloc : ∀ y ∈ U, ∀ᶠ y' in 𝓝 y, y' ∈ U ∧ D.internal U y y' ≠ ⊤ := by
    intro y hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (D.isOpen_image_pt hU) (D.pt y) ⟨y, hy, rfl⟩
    have hballU : ∀ y', D.1 (y, y') < ε → y' ∈ U := fun y' hy' => by
      have : D.pt y' ∈ D.pt '' U := hball (by
        rw [Metric.mem_ball, dist_pt, D.apply_comm]; exact hy')
      exact D.mem_image_pt.1 this
    have hcont : Tendsto (fun y' => D.1 (y, y')) (𝓝 y) (𝓝 (D.1 (y, y))) :=
      (D.1.continuous.comp (continuous_const.prodMk continuous_id)).tendsto y
    rw [D.apply_self] at hcont
    filter_upwards [hcont (gt_mem_nhds hε)] with y' hy'
    refine ⟨hballU y' hy', ?_⟩
    rw [D.internal_eq_of_ball_subset hD hballU hy']
    exact ENNReal.ofReal_ne_top
  set A : Set (Rd d) := {y | y ∈ U ∧ D.internal U z y ≠ ⊤} with hA
  set B : Set (Rd d) := {y | y ∈ U ∧ D.internal U z y = ⊤} with hB
  have hAo : IsOpen A := by
    refine isOpen_iff_mem_nhds.2 fun y hy => ?_
    filter_upwards [hloc y hy.1] with y' hy'
    refine ⟨hy'.1, ne_top_of_le_ne_top ?_ (D.internal_triangle U z y y')⟩
    exact ENNReal.add_ne_top.2 ⟨hy.2, hy'.2⟩
  have hBo : IsOpen B := by
    refine isOpen_iff_mem_nhds.2 fun y hy => ?_
    filter_upwards [hloc y hy.1] with y' hy'
    refine ⟨hy'.1, ?_⟩
    by_contra hne
    have h1 : D.internal U y' y ≠ ⊤ := by rw [D.internal_comm]; exact hy'.2
    exact (ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hne, h1⟩)
      (D.internal_triangle U z y' y)) hy.2
  by_contra htop
  obtain ⟨y, -, hyA, hyB⟩ := hUc A B hAo hBo (fun y hy => by
      by_cases h : D.internal U z y = ⊤
      · exact Or.inr ⟨hy, h⟩
      · exact Or.inl ⟨hy, h⟩)
    ⟨z, hz, hz, by rw [D.internal_self hz]; exact ENNReal.zero_ne_top⟩ ⟨w, hw, hw, htop⟩
  exact hyA.2 hyB.2

/-! ### Geodesics of proper length metrics -/

/-- **Geodesics** (BBI Cor. 2.5.20): if `(ℝ^d, D)` is a proper length space, any `z, w` are joined
by a `D`-geodesic parametrized by `D`-length on `[0, D(z, w)]`. -/
theorem exists_geodesic (D : ContMetric d) (hD : D.IsLength) [ProperSpace D.Space] (z w : Rd d) :
    ∃ P : ℝ → Rd d, P 0 = z ∧ P (D.1 (z, w)) = w ∧
      IsGeodesicCurve (D.pt ∘ P) 0 (D.1 (z, w)) ∧ HasUnitSpeedOn (D.pt ∘ P) (Icc 0 (D.1 (z, w))) ∧
      ∀ s ∈ Icc 0 (D.1 (z, w)), ∀ t ∈ Icc 0 (D.1 (z, w)), D.1 (P s, P t) = |t - s| := by
  obtain ⟨P, h0, h1, hgeo, hu, hdist⟩ := exists_isGeodesicCurve_unitSpeed hD (D.pt z) (D.pt w)
  exact ⟨D.unpt ∘ P, h0, h1, hgeo, hu, hdist⟩

/-- In a proper length space, `D(u, v; V) = D(u, v)` when `D(u, v) ≤ D(u, ∂V)` (`u, v ∈ V` open):
the geodesic from `u` to `v` stays in `V` (**GM S3.1 (b)**). -/
theorem internal_eq_of_le_infEDist_frontier (D : ContMetric d) (hD : D.IsLength)
    [ProperSpace D.Space] {V : Set (Rd d)} (hV : IsOpen V) {u v : Rd d} (hu : u ∈ V) (hv : v ∈ V)
    (hle : edist (D.pt u) (D.pt v) ≤ Metric.infEDist (D.pt u) (D.pt '' frontier V)) :
    D.internal V u v = ENNReal.ofReal (D.1 (u, v)) := by
  rw [internal_def, ← edist_pt]
  refine internalEDist_eq_edist_of_le_infEDist hD (D.isOpen_image_pt hV) ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    ?_
  rwa [← D.image_pt_frontier]

/-! ### Frontier localization (GM S3.1 (a)) -/

/-- Key step of **GM S3.1 (a)**: if `D` and `D'` have the same internal metric on `V`, every
`D`-path from `u ∈ V` to a point outside `V` has `D`-length at least `D'(u, ∂V)`. -/
theorem infEDist_frontier_le_pathLength {D D' : ContMetric d} {V : Set (Rd d)} (hV : IsOpen V)
    {u : Rd d} (hu : u ∈ V) (heq : ∀ z ∈ V, ∀ w ∈ V, D.internal V z w = D'.internal V z w)
    {w : D.Space} (hw : D.unpt w ∉ V) (γ : Path (D.pt u) w) :
    Metric.infEDist (D'.pt u) (D'.pt '' frontier V) ≤ pathLength γ := by
  set P : ℝ → D.Space := ⇑γ.extend with hPdef
  have hA : IsClosed (D.pt '' V)ᶜ := (D.isOpen_image_pt hV).isClosed_compl
  have hPc : Continuous P := γ.continuous_extend
  have h1 : P 1 ∈ (D.pt '' V)ᶜ := by
    rw [hPdef, Path.extend_one]
    exact fun h => hw ((D.mem_image_pt (z := D.unpt w)).1 h)
  obtain ⟨s, hs, hsA, hbefore⟩ :=
    exists_first_hit hPc.continuousOn hA ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩
  have hin : ∀ t ∈ Ico 0 s, P t ∈ D.pt '' V := fun t ht => not_not.1 (hbefore t ht)
  have hP0 : P 0 = D.pt u := Path.extend_zero γ
  have hs0 : 0 < s := by
    rcases hs.1.eq_or_lt with h | h
    · exfalso
      rw [← h, hP0] at hsA
      exact hsA ⟨u, hu, rfl⟩
    · exact h
  have hbound : ∀ t ∈ Ico 0 s, edist (D'.pt u) (D'.pt (D.unpt (P t))) ≤ pathLength γ := by
    intro t ht
    have hmaps : MapsTo P (Icc 0 t) (D.pt '' V) := fun r hr => hin r ⟨hr.1, hr.2.trans_lt ht.2⟩
    have hPt : D.unpt (P t) ∈ V := D.mem_image_pt.1 (hin t ht)
    calc edist (D'.pt u) (D'.pt (D.unpt (P t))) ≤ D'.internal V u (D.unpt (P t)) :=
          edist_le_internalEDist _ _ _
      _ = D.internal V u (D.unpt (P t)) := (heq u hu _ hPt).symm
      _ ≤ curveLength P 0 t := by
          have := internalEDist_le_curveLength ht.1 hPc.continuousOn hmaps
          rw [hP0] at this
          exact this
      _ ≤ pathLength γ := curveLength_mono P le_rfl (ht.2.le.trans hs.2)
  have hg : Continuous fun t => edist (D'.pt u) (D'.pt (D.unpt (P t))) :=
    continuous_const.edist ((D'.continuous_pt.comp D.continuous_unpt).comp hPc)
  have hne : (𝓝[Ico 0 s] s).NeBot := right_nhdsWithin_Ico_neBot hs0
  have hgs : edist (D'.pt u) (D'.pt (D.unpt (P s))) ≤ pathLength γ :=
    le_of_tendsto ((hg.tendsto s).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall hbound)
  have hfr : D.unpt (P s) ∈ frontier V := by
    refine ⟨mem_closure_of_tendsto
      (((D.continuous_unpt.comp hPc).tendsto s).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun t ht => D.mem_image_pt.1 (hin t ht)), ?_⟩
    rw [hV.interior_eq]
    exact fun h => hsA (D.mem_image_pt.2 h)
  exact (Metric.infEDist_le_edist_of_mem (s := D'.pt '' frontier V) ⟨_, hfr, rfl⟩).trans hgs

/-- **GM S3.1 (a)** (GM tex:1197, 1351): if `D` is a length metric and `D(·,·;V) = D'(·,·;V)` on
the open set `V`, then `D'(u, ∂V) ≤ D(u, ∂V)` for `u ∈ V`. -/
theorem infEDist_frontier_le_of_internal_eq {D D' : ContMetric d} (hD : D.IsLength)
    {V : Set (Rd d)} (hV : IsOpen V) {u : Rd d} (hu : u ∈ V)
    (heq : ∀ z ∈ V, ∀ w ∈ V, D.internal V z w = D'.internal V z w) :
    Metric.infEDist (D'.pt u) (D'.pt '' frontier V) ≤
      Metric.infEDist (D.pt u) (D.pt '' frontier V) := by
  refine le_trans ?_ (Metric.infEDist_anti (x := D.pt u) (s := D.pt '' frontier V)
    (t := (D.pt '' V)ᶜ) ?_)
  · refine Metric.le_infEDist.2 fun w hw => ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨γ, hγ⟩ := hD (D.pt u) w ε (by exact_mod_cast hε)
    rw [ENNReal.ofReal_coe_nnreal] at hγ
    exact (infEDist_frontier_le_pathLength hV hu heq (fun h => hw (D.mem_image_pt.2 h)) γ).trans hγ
  · rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', hzz⟩
    exact hz.2 (by rw [hV.interior_eq]; exact (show z' = z from hzz) ▸ hz')

/-- **GM S3.1 (a)**, symmetric form: two length metrics with the same internal metric on the open
set `V` have the same distance from `u ∈ V` to `∂V`. -/
theorem infEDist_frontier_eq_of_internal_eq {D D' : ContMetric d} (hD : D.IsLength)
    (hD' : D'.IsLength) {V : Set (Rd d)} (hV : IsOpen V) {u : Rd d} (hu : u ∈ V)
    (heq : ∀ z ∈ V, ∀ w ∈ V, D.internal V z w = D'.internal V z w) :
    Metric.infEDist (D.pt u) (D.pt '' frontier V) =
      Metric.infEDist (D'.pt u) (D'.pt '' frontier V) :=
  le_antisymm (infEDist_frontier_le_of_internal_eq hD' hV hu fun z hz w hw => (heq z hz w hw).symm)
    (infEDist_frontier_le_of_internal_eq hD hV hu heq)

/-- Points `D`-closer to `u ∈ V` than `D(u, ∂V)` lie in `V`, and there `D(u, v) = D(u, v; V)`
(LM tex:213–214 / GM tex:1197). -/
theorem internal_eq_of_lt_infEDist_frontier {D : ContMetric d} (hD : D.IsLength)
    {V : Set (Rd d)} (hV : IsOpen V) {u v : Rd d} (hu : u ∈ V)
    (hv : edist (D.pt u) (D.pt v) < Metric.infEDist (D.pt u) (D.pt '' frontier V)) :
    v ∈ V ∧ D.internal V u v = edist (D.pt u) (D.pt v) := by
  have hfr : D.pt '' frontier V = frontier (D.pt '' V) := D.image_pt_frontier V
  rw [hfr, ← infEDist_compl_eq_infEDist_frontier hD (D.isOpen_image_pt hV) ⟨u, hu, rfl⟩] at hv
  have hball : Metric.eball (D.pt u) (Metric.infEDist (D.pt u) (D.pt '' V)ᶜ) ⊆ D.pt '' V :=
    fun x hx => by
      by_contra hxV
      rw [Metric.mem_eball, edist_comm] at hx
      exact (Metric.infEDist_le_edist_of_mem hxV).not_gt hx
  refine ⟨D.mem_image_pt.1 (hball (by rw [Metric.mem_eball, edist_comm]; exact hv)), ?_⟩
  exact internalEDist_eq_edist_of_ball_subset hD hball hv

/-! ### Internal metric of an internal metric (BBI Prop. 2.3.12) -/

/-- **BBI Prop. 2.3.12(1)**: partition sums of `D(·,·;U)` along a Euclidean-continuous curve in `U`
give its `D`-length. -/
theorem curveLengthWith_internal (D : ContMetric d) {U : Set (Rd d)} {P : ℝ → Rd d} {a b : ℝ}
    (hP : ContinuousOn P (Icc a b)) (hPU : MapsTo P (Icc a b) U) :
    curveLengthWith (D.internal U) P a b = D.len P a b := by
  apply le_antisymm
  · refine partitionSup_le fun p => ?_
    calc p.sum (fun u v => D.internal U (P u) (P v))
        ≤ ∑ i ∈ Finset.range p.n, D.len P (p.t i) (p.t (i + 1)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          obtain ⟨h1, h2, h3⟩ := p.step (Finset.mem_range.1 hi)
          have hsub : Icc (p.t i) (p.t (i + 1)) ⊆ Icc a b := Icc_subset_Icc h1 h3
          exact D.internal_le_len h2 (hP.mono hsub) (hPU.mono_left hsub)
      _ = D.len P (p.t 0) (p.t p.n) := by
          have hmono : Monotone fun i => p.t (min i p.n) := fun i j hij =>
            p.le_t (min_le_min_right p.n hij) (min_le_right _ _)
          have h := sum_curveLength_eq (D.pt ∘ P) hmono p.n
          simp only [min_self, Nat.zero_min] at h
          simp only [len]
          rw [← h]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_range] at hi
          rw [min_eq_left hi.le, min_eq_left (by omega)]
      _ = D.len P a b := by rw [p.zero, p.last]
  · rw [len, ← curveLengthWith_edist]
    exact curveLengthWith_mono fun u v _ _ _ => edist_le_internalEDist _ _ _

/-- **Internal metric of an internal metric** (LM S-int (b), BBI Prop. 2.3.12(2)): for `W ⊆ U`,
the internal distance of `W` induced by `D(·,·;U)` is `D(·,·;W)`. -/
theorem internalWith_internal (D : ContMetric d) {U W : Set (Rd d)} (hWU : W ⊆ U) (z w : Rd d) :
    internalWith (D.internal U) W z w = D.internal W z w := by
  rw [internal_eq_iInf_len]
  unfold internalWith
  refine iInf_congr fun P => iInf_congr fun hc => iInf_congr fun _ => iInf_congr fun _ =>
    iInf_congr fun hW => ?_
  exact D.curveLengthWith_internal hc (hW.mono_right hWU)

/-- `D(·,·;U)` is the length distance it induces on `U` (internal metrics are length metrics, in the
`[0, ∞]`-valued sense). -/
theorem internalWith_internal_self (D : ContMetric d) (U : Set (Rd d)) (z w : Rd d) :
    internalWith (D.internal U) U z w = D.internal U z w :=
  D.internalWith_internal subset_rfl z w

end ContMetric

end HigherDimLQGMetric
