import SupercriticalConformalCovariance.Compact.ClosedDiskBridge
import SupercriticalConformalCovariance.Tangent.DiskFunctional
import SupercriticalConformalCovariance.Tangent.LscLemmas
import SupercriticalConformalCovariance.Transport.CompactLSC
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.InternalOfInternal

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Classical
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints

/-- Closed-disk intrinsic distance, with the global diagonal set to zero. -/
def confKernel (D : LSCMetric) (c : ℂ) (R : ℝ) (p : ℂ × ℂ) : ℝ≥0∞ :=
  if p.1 = p.2 then 0 else closedBallPathInf D c R p.1 p.2

theorem confKernel_eq_intrinsic (D : LSCMetric) (c : ℂ) (R : ℝ)
    {x y : ℂ} (hx : x ∈ closedBall c R) (hy : y ∈ closedBall c R) :
    confKernel D c R (x, y) = D.internal (closedBall c R) (⟨x,hx⟩,⟨y,hy⟩) := by
  by_cases hxy : x = y
  · subst y
    simp [confKernel, (D.isExtMetric_internal (closedBall c R)).1]
  · simp [confKernel, hxy, SupercriticalConformalCovariance.Tangent.closedBallPathInf_eq_extInternal,
      SupercriticalConformalCovariance.Tangent.extInternal, hx, hy]

theorem confKernel_outside (D : LSCMetric) (c : ℂ) (R : ℝ)
    {x y : ℂ} (hxy : x ≠ y)
    (h : ¬ (x ∈ closedBall c R ∧ y ∈ closedBall c R)) :
    confKernel D c R (x, y) = ⊤ := by
  rw [confKernel, if_neg hxy, SupercriticalConformalCovariance.Tangent.closedBallPathInf_eq_extInternal]
  unfold SupercriticalConformalCovariance.Tangent.extInternal
  split_ifs with hq
  · exact False.elim (h hq)
  · rfl

/-- Lower semicontinuity survives lowering the diagonal of a nonnegative kernel to zero. -/
theorem lsc_zero_diagonal {F : ℂ × ℂ → ℝ≥0∞} (hF : LowerSemicontinuous F) :
    LowerSemicontinuous (fun p : ℂ × ℂ => if p.1 = p.2 then 0 else F p) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage] at hF ⊢
  intro a
  let O : Set (ℂ × ℂ) := {p | p.1 ≠ p.2}
  have hO : IsOpen O := (isClosed_eq continuous_fst continuous_snd).isOpen_compl
  have hset : (fun p : ℂ × ℂ => if p.1 = p.2 then (0 : ℝ≥0∞) else F p) ⁻¹' Ioi a =
      F ⁻¹' Ioi a ∩ O := by
    ext p; by_cases hp : p.1 = p.2 <;> simp [hp, O]
  rw [hset]
  exact (hF a).inter hO

theorem confKernel_lsc (D : LSCMetric) (c : ℂ) (R : ℝ) :
    LowerSemicontinuous (confKernel D c R) := by
  exact lsc_zero_diagonal (SupercriticalConformalCovariance.Compact.closed_disk_intrinsic_lsc D c R)

/-- Extend an intrinsic metric on `K` to the whole plane, isolating points outside `K`. -/
def extendMetric (K : Set ℂ) (d : K × K → ℝ≥0∞) (p : ℂ × ℂ) : ℝ≥0∞ :=
  if p.1 = p.2 then 0 else
    if h : p.1 ∈ K ∧ p.2 ∈ K then d (⟨p.1,h.1⟩,⟨p.2,h.2⟩) else ⊤

theorem extendMetric_on (K : Set ℂ) (d : K × K → ℝ≥0∞)
    (hd : IsExtMetric d) {x y : ℂ} (hx : x ∈ K) (hy : y ∈ K) :
    extendMetric K d (x,y) = d (⟨x,hx⟩,⟨y,hy⟩) := by
  by_cases hxy : x = y
  · subst y; simp [extendMetric, hd.1]
  · simp [extendMetric, hxy, hx, hy]

theorem extendMetric_off (K : Set ℂ) (d : K × K → ℝ≥0∞)
    {x y : ℂ} (hxy : x ≠ y) (h : ¬ (x ∈ K ∧ y ∈ K)) :
    extendMetric K d (x,y) = ⊤ := by
  simp [extendMetric, hxy, h]

theorem isExtMetric_extendMetric (K : Set ℂ) (d : K × K → ℝ≥0∞)
    (hd : IsExtMetric d) : IsExtMetric (extendMetric K d) := by
  refine ⟨fun x => by simp [extendMetric], fun x y hxy => ?_, fun x y => ?_,
    fun x y z => ?_⟩
  · by_contra hne
    by_cases hx : x ∈ K
    · by_cases hy : y ∈ K
      · rw [extendMetric_on K d hd hx hy] at hxy
        exact hne (congrArg Subtype.val (hd.2.1 ⟨x,hx⟩ ⟨y,hy⟩ hxy))
      · rw [extendMetric_off K d hne (by simp [hy])] at hxy
        exact ENNReal.top_ne_zero hxy
    · rw [extendMetric_off K d hne (by simp [hx])] at hxy
      exact ENNReal.top_ne_zero hxy
  · by_cases hxy : x = y
    · subst y; rfl
    by_cases hx : x ∈ K
    · by_cases hy : y ∈ K
      · rw [extendMetric_on K d hd hx hy, extendMetric_on K d hd hy hx]
        exact hd.2.2.1 ⟨x,hx⟩ ⟨y,hy⟩
      · rw [extendMetric_off K d hxy (by simp [hy]),
          extendMetric_off K d (Ne.symm hxy) (by simp [hy])]
    · rw [extendMetric_off K d hxy (by simp [hx]),
        extendMetric_off K d (Ne.symm hxy) (by simp [hx])]
  · by_cases hxz : x = z
    · subst z; simp [extendMetric]
    by_cases hx : x ∈ K
    · by_cases hy : y ∈ K
      · by_cases hz : z ∈ K
        · rw [extendMetric_on K d hd hx hz, extendMetric_on K d hd hx hy,
            extendMetric_on K d hd hy hz]
          exact hd.2.2.2 ⟨x,hx⟩ ⟨y,hy⟩ ⟨z,hz⟩
        · by_cases hyz : y = z
          · subst z; exact False.elim (hz hy)
          · rw [extendMetric_off K d hyz (by simp [hz])]
            simp
      · by_cases hxy : x = y
        · subst y; exact False.elim (hy hx)
        · rw [extendMetric_off K d hxy (by simp [hy])]
          simp
    · by_cases hxy : x = y
      · subst y
        rw [extendMetric_off K d hxz (by simp [hx])]
        simp [extendMetric]
      · rw [extendMetric_off K d hxz (by simp [hx]),
          extendMetric_off K d hxy (by simp [hx])]
        simp

theorem confKernel_eq_extendMetric (D : LSCMetric) (c : ℂ) (R : ℝ) :
    confKernel D c R = extendMetric (closedBall c R) (D.internal (closedBall c R)) := by
  funext p
  by_cases hxy : p.1 = p.2
  · simp [confKernel, extendMetric, hxy]
  · by_cases hx : p.1 ∈ closedBall c R
    · by_cases hy : p.2 ∈ closedBall c R
      · rw [confKernel_eq_intrinsic D c R hx hy,
          extendMetric_on _ _ (D.isExtMetric_internal _) hx hy]
      · rw [confKernel_outside D c R hxy (by simp [hy]),
          extendMetric_off _ _ hxy (by simp [hy])]
    · rw [confKernel_outside D c R hxy (by simp [hx]),
        extendMetric_off _ _ hxy (by simp [hx])]

theorem confKernel_isExtMetric (D : LSCMetric) (c : ℂ) (R : ℝ) :
    IsExtMetric (confKernel D c R) := by
  rw [confKernel_eq_extendMetric]
  exact isExtMetric_extendMetric _ _ (D.isExtMetric_internal _)

/-- Diagonal-corrected confined metric on the whole plane. -/
def conf (D : LSCMetric) (c : ℂ) (R : ℝ) : LSCMetric :=
  ⟨confKernel D c R, confKernel_isExtMetric D c R, confKernel_lsc D c R⟩

theorem conf_apply (D : LSCMetric) (c : ℂ) (R : ℝ) (p : ℂ × ℂ) :
    conf D c R p = confKernel D c R p := rfl

theorem conf_eq_extInternal_on (D : LSCMetric) (c : ℂ) (R : ℝ)
    {x y : ℂ} (hx : x ∈ closedBall c R) (hy : y ∈ closedBall c R) :
    conf D c R (x,y) = SupercriticalConformalCovariance.Tangent.extInternal D (closedBall c R) (x,y) := by
  rw [conf_apply, confKernel_eq_intrinsic D c R hx hy]
  simp [SupercriticalConformalCovariance.Tangent.extInternal, hx, hy]

theorem conf_eq_extInternal_eventually_local (D : LSCMetric) {R : ℕ → ℝ}
    (hR : Tendsto R atTop atTop) (B : ℝ) :
    ∀ᶠ n in atTop, ∀ p : ℂ × ℂ, ‖p.1‖ < B → ‖p.2‖ < B →
      conf D 0 (R n) p = SupercriticalConformalCovariance.Tangent.extInternal D (closedBall 0 (R n)) p := by
  filter_upwards [hR.eventually_ge_atTop B] with n hn p hp hq
  apply conf_eq_extInternal_on
  · exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using le_trans hp.le hn)
  · exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using le_trans hq.le hn)

theorem lscTendsto_conf_iff_extInternal (D : LSCMetric) {R : ℕ → ℝ}
    (hR : Tendsto R atTop atTop) (L : ℂ × ℂ → EReal) :
    LSCTendsto (fun n p => ((conf D 0 (R n) p : ℝ≥0∞) : EReal)) L ↔
    LSCTendsto (fun n p => ((SupercriticalConformalCovariance.Tangent.extInternal D (closedBall 0 (R n)) p : ℝ≥0∞) : EReal)) L := by
  have hEq : ∀ B : ℝ, ∀ᶠ n in atTop, ∀ p : ℂ × ℂ, ‖p.1‖ < B → ‖p.2‖ < B →
      ((conf D 0 (R n) p : ℝ≥0∞) : EReal) =
      ((SupercriticalConformalCovariance.Tangent.extInternal D (closedBall 0 (R n)) p : ℝ≥0∞) : EReal) := by
    intro B
    filter_upwards [conf_eq_extInternal_eventually_local D hR B] with n hn p hp hq
    exact congrArg (fun v : ℝ≥0∞ => (v : EReal)) (hn p hp hq)
  constructor
  · intro h
    exact SupercriticalConformalCovariance.Tangent.lscTendsto_of_eventually_eq_local
      (fun B => (hEq B).mono fun n hn p hp hq => (hn p hp hq).symm) h
  · intro h
    exact SupercriticalConformalCovariance.Tangent.lscTendsto_of_eventually_eq_local hEq h

theorem conf_len_eq_original_of_mem (D : LSCMetric) (c : ℂ) (R : ℝ)
    (P : ℝ → ℂ) (a b : ℝ) (hP : D.IsCurve P a b)
    (hK : ∀ t : ℝ, P t ∈ closedBall c R) :
    (conf D c R).len P a b = D.len P a b := by
  let K := closedBall c R
  let Q : ℝ → K := fun t => ⟨P t, hK t⟩
  have hPQ : D.IsCurve (fun t => (Q t : ℂ)) a b := hP
  rw [SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.len_eq_internalLen D K Q a b hPQ]
  unfold LSCMetric.len SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.internalLen
  unfold eVariationOn
  refine iSup_congr fun q => Finset.sum_congr rfl fun i _ => ?_
  change conf D c R (P (q.2.1 (i+1)), P (q.2.1 i)) =
    D.internal K (Q (q.2.1 (i+1)), Q (q.2.1 i))
  exact confKernel_eq_intrinsic D c R (hK _) (hK _)

theorem conf_isCurve_of_lipschitz (D : LSCMetric) (c : ℂ) (R : ℝ)
    (P : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hK : ∀ t : ℝ, P t ∈ closedBall c R)
    {C : NNReal} (hLip : LipschitzOnWith C (D.pt ∘ P) (Icc a b)) :
    (conf D c R).IsCurve P a b := by
  let K := closedBall c R
  let Y : Set D.Space := D.pt '' K
  let Q : ℝ → Y := fun t => ⟨D.pt (P t), ⟨P t, hK t, rfl⟩⟩
  have hLip' : LipschitzOnWith C (fun t => (Q t : D.Space)) (Icc a b) := hLip
  have hi := SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.lipschitzOnWith_internalSpace
    (X := D.Space) Y Q hLip'
  refine ⟨hab, ?_⟩
  have hc : LipschitzOnWith C ((conf D c R).pt ∘ P) (Icc a b) := by
    intro s hs t ht
    change conf D c R (P s, P t) ≤ (C : ℝ≥0∞) * edist s t
    rw [conf_apply, confKernel_eq_intrinsic D c R (hK s) (hK t),
      LSCMetric.internal_eq_internalEDist]
    exact hi hs ht
  exact hc.continuousOn

theorem conf_isLengthSpace (D : LSCMetric) (c : ℂ) (R : ℝ) :
    (conf D c R).IsLengthSpace := by
  intro x y hfin ε hε
  by_cases hxy : x = y
  · subst y
    refine ⟨fun _ => x, 0, 0, ⟨le_rfl, continuousOn_const⟩, rfl, rfl, ?_⟩
    have hzero : (conf D c R).len (fun _ => x) 0 0 = 0 := by
      unfold LSCMetric.len
      exact eVariationOn.constant_on (by
        rintro _ ⟨s, -, rfl⟩ _ ⟨t, -, rfl⟩
        simp)
    rw [hzero]
    exact bot_le
  let K := closedBall c R
  have hKxy : x ∈ K ∧ y ∈ K := by
    by_contra h
    have htop := confKernel_outside D c R hxy h
    rw [← conf_apply] at htop
    rw [htop] at hfin
    exact (lt_irrefl (⊤ : ℝ≥0∞)) hfin
  rcases hKxy with ⟨hx, hy⟩
  have hcost : conf D c R (x,y) = D.internal K (⟨x,hx⟩,⟨y,hy⟩) :=
    confKernel_eq_intrinsic D c R hx hy
  have hlt : D.internal K (⟨x,hx⟩,⟨y,hy⟩) <
      conf D c R (x,y) + ENNReal.ofReal ε := by
    have hinnerfin : D.internal K (⟨x,hx⟩,⟨y,hy⟩) ≠ ⊤ := by
      rw [← hcost]
      exact hfin.ne
    rw [hcost]
    exact ENNReal.lt_add_right hinnerfin (ENNReal.ofReal_pos.2 hε).ne'
  unfold LSCMetric.internal at hlt
  simp only [iInf_lt_iff] at hlt
  obtain ⟨P,a,b,hP,hPK,ha,hb,hlen⟩ := hlt
  let f : ℝ → D.Space := D.pt ∘ P
  have hf : ContinuousOn f (Icc a b) := hP.2
  obtain ⟨γ,hγlen,hγrange⟩ :=
    LQGMetric.MetricGeometry.exists_path_of_curve hP.1 hf
  have hγcost : LQGMetric.MetricGeometry.pathLength γ <
      conf D c R (x,y) + ENNReal.ofReal ε := by
    rw [hγlen]
    exact hlen
  have hγfin : LQGMetric.MetricGeometry.pathLength γ ≠ ⊤ :=
    (lt_of_lt_of_le hγcost le_top).ne
  obtain ⟨γ',hγ'len,hγ'range,hγ'lip⟩ :=
    LQGMetric.MetricGeometry.exists_lipschitz_path γ hγfin
  let Q : ℝ → ℂ := fun t => γ'.extend t
  have hγK : ∀ t : unitInterval, (γ t : ℂ) ∈ K := by
    intro t
    obtain ⟨s,hs,heq⟩ := hγrange (Set.mem_range_self t)
    have ht : P s ∈ K := hPK s hs
    have heq' : (γ t : ℂ) = P s := congrArg (fun v : D.Space => (v : ℂ)) heq.symm
    exact heq'.symm ▸ ht
  have hγ'K : ∀ t : unitInterval, (γ' t : ℂ) ∈ K := by
    intro t
    obtain ⟨s,heq⟩ := hγ'range (Set.mem_range_self t)
    exact heq.symm ▸ hγK s
  have hQK : ∀ t : ℝ, Q t ∈ K := by
    intro t
    obtain ⟨s,heq⟩ := γ'.extend_range.subset (Set.mem_range_self t)
    change (γ'.extend t : ℂ) ∈ K
    have heq' : (γ' s : ℂ) = (γ'.extend t : ℂ) :=
      congrArg (fun v : D.Space => (v : ℂ)) heq
    exact heq' ▸ hγ'K s
  have hQLip : LipschitzOnWith
      (LQGMetric.MetricGeometry.pathLength γ).toNNReal (D.pt ∘ Q) (Icc 0 1) := by
    intro s hs t ht
    change edist (γ'.extend s) (γ'.extend t) ≤
      ((LQGMetric.MetricGeometry.pathLength γ).toNNReal : ℝ≥0∞) * edist s t
    rw [Path.extend_apply _ hs, Path.extend_apply _ ht]
    simpa only [Subtype.edist_eq] using hγ'lip ⟨s,hs⟩ ⟨t,ht⟩
  have hQc : (conf D c R).IsCurve Q 0 1 :=
    conf_isCurve_of_lipschitz D c R Q 0 1 zero_le_one hQK hQLip
  have hQD : D.IsCurve Q 0 1 := by
    refine ⟨zero_le_one, ?_⟩
    exact γ'.continuous_extend.continuousOn
  refine ⟨Q, 0, 1, hQc, ?_, ?_, ?_⟩
  · change γ'.extend 0 = x
    rw [Path.extend_zero]
    change P a = x
    exact ha
  · change γ'.extend 1 = y
    rw [Path.extend_one]
    change P b = y
    exact hb
  · rw [conf_len_eq_original_of_mem D c R Q 0 1 hQD hQK]
    change LQGMetric.MetricGeometry.pathLength γ' ≤ _
    rw [hγ'len]
    exact hγcost.le

theorem original_le_conf (D : LSCMetric) (c : ℂ) (R : ℝ) (x y : ℂ) :
    D (x,y) ≤ conf D c R (x,y) := by
  by_cases hxy : x = y
  · subst y
    simp [conf, confKernel, D.isExtMetric.1]
  by_cases hx : x ∈ closedBall c R
  · by_cases hy : y ∈ closedBall c R
    · rw [conf_apply, confKernel_eq_intrinsic D c R hx hy]
      exact D.edist_le_internal (closedBall c R) (⟨x,hx⟩,⟨y,hy⟩)
    · rw [conf_apply, confKernel_outside D c R hxy (by simp [hy])]
      exact le_top
  · rw [conf_apply, confKernel_outside D c R hxy (by simp [hx])]
    exact le_top

theorem conf_curve_original_curve (D : LSCMetric) (c : ℂ) (R : ℝ)
    (P : ℝ → ℂ) (a b : ℝ) (hP : (conf D c R).IsCurve P a b) :
    D.IsCurve P a b := by
  let F : (conf D c R).Space → D.Space := fun x => D.pt x
  have hF : LipschitzWith 1 F := by
    intro x y
    change D (x,y) ≤ (1 : ℝ≥0∞) * conf D c R (x,y)
    simpa only [one_mul] using original_le_conf D c R x y
  exact ⟨hP.1, hF.continuous.comp_continuousOn hP.2⟩

theorem original_len_le_conf_len (D : LSCMetric) (c : ℂ) (R : ℝ)
    (P : ℝ → ℂ) (a b : ℝ) :
    D.len P a b ≤ (conf D c R).len P a b := by
  let F : (conf D c R).Space → D.Space := fun x => D.pt x
  have hF : ∀ x y, edist (F x) (F y) ≤ edist x y := fun x y =>
    original_le_conf D c R x y
  exact SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.curveLength_comp_le_of_edist_le
    F hF ((conf D c R).pt ∘ P) a b

theorem conf_euclidean_regular_of_original (D : LSCMetric) (c : ℂ) (R : ℝ)
    (hreg : ∀ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b →
      D.len P a b < ⊤ → ContinuousOn P (Icc a b))
    (P : ℝ → ℂ) (a b : ℝ) (hP : (conf D c R).IsCurve P a b)
    (hfin : (conf D c R).len P a b < ⊤) : ContinuousOn P (Icc a b) := by
  exact hreg P a b (conf_curve_original_curve D c R P a b hP)
    ((original_len_le_conf_len D c R P a b).trans_lt hfin)

theorem compact_extInternal_lsc (D : LSCMetric) (K : Set ℂ) (hK : IsCompact K) :
    LowerSemicontinuous (SupercriticalConformalCovariance.Tangent.extInternal D K) := by
  have hraw : LowerSemicontinuous (fun p : ℂ × ℂ =>
      (SupercriticalConformalCovariance.Transport.compactFun K hK D).1 p) := (SupercriticalConformalCovariance.Transport.compactFun K hK D).2
  have h := EReal.continuous_toENNReal.comp_lowerSemicontinuous hraw
    (fun _ _ hab => EReal.toENNReal_le_toENNReal hab)
  have heq : (fun p : ℂ × ℂ => EReal.toENNReal ((SupercriticalConformalCovariance.Transport.compactFun K hK D).1 p)) =
      SupercriticalConformalCovariance.Tangent.extInternal D K := by
    funext p
    by_cases hp : p.1 ∈ K ∧ p.2 ∈ K
    · obtain ⟨hx, hy⟩ := hp
      have hv := SupercriticalConformalCovariance.Transport.compactFun_on K hK D (⟨p.1,hx⟩,⟨p.2,hy⟩)
      change (SupercriticalConformalCovariance.Transport.compactFun K hK D).1 p =
        ((D.internal K (⟨p.1,hx⟩,⟨p.2,hy⟩) : ℝ≥0∞) : EReal) at hv
      rw [hv]
      simp [SupercriticalConformalCovariance.Tangent.extInternal, hx, hy]
    · rw [SupercriticalConformalCovariance.Transport.compactFun_off K hK D p hp]
      simp [SupercriticalConformalCovariance.Tangent.extInternal, hp]
  rw [← heq]
  exact h

def confCompact (D : LSCMetric) (K : Set ℂ) (hK : IsCompact K) : LSCMetric :=
  ⟨extendMetric K (D.internal K),
    isExtMetric_extendMetric K (D.internal K) (D.isExtMetric_internal K), by
      have heq : extendMetric K (D.internal K) =
          fun p : ℂ × ℂ => if p.1 = p.2 then 0 else SupercriticalConformalCovariance.Tangent.extInternal D K p := by
        funext p
        by_cases hxy : p.1 = p.2
        · simp [extendMetric, hxy]
        by_cases hp : p.1 ∈ K ∧ p.2 ∈ K
        · rcases hp with ⟨hx,hy⟩
          simp [extendMetric, hxy, SupercriticalConformalCovariance.Tangent.extInternal, hx, hy]
        · simp [extendMetric, hxy, SupercriticalConformalCovariance.Tangent.extInternal, hp]
      rw [heq]
      exact lsc_zero_diagonal (compact_extInternal_lsc D K hK)⟩

theorem confCompact_on (D : LSCMetric) (K : Set ℂ) (hK : IsCompact K)
    {x y : ℂ} (hx : x ∈ K) (hy : y ∈ K) :
    confCompact D K hK (x,y) = D.internal K (⟨x,hx⟩,⟨y,hy⟩) :=
  extendMetric_on K (D.internal K) (D.isExtMetric_internal K) hx hy
