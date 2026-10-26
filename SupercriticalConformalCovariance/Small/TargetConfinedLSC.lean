import SupercriticalConformalCovariance.Transport.CompactLSC
import SupercriticalConformalCovariance.Tangent.DiskFunctional
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.InternalOfInternal
import SupercriticalConformalCovariance.Small.ConfinedLSC

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Classical
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness

def pullInner (D : LSCMetric) (L K : Set ℂ) (j : C(K,L)) (p : K × K) : ℝ≥0∞ :=
  D.internal L (j p.1, j p.2)

theorem pullInner_isExtMetric (D : LSCMetric) (L K : Set ℂ) (j : C(K,L))
    (hj : Function.Injective j) : IsExtMetric (pullInner D L K j) := by
  let h := D.isExtMetric_internal L
  refine ⟨fun x => h.1 (j x), fun x y hxy => hj (h.2.1 (j x) (j y) hxy),
    fun x y => h.2.2.1 (j x) (j y), fun x y z => h.2.2.2 (j x) (j y) (j z)⟩

theorem pullInner_lsc (D : LSCMetric) (L K : Set ℂ) (hK : IsCompact K)
    (hL : IsCompact L) (j : C(K,L)) :
    LowerSemicontinuous (fun p : ℂ × ℂ =>
      EReal.toENNReal ((SupercriticalConformalCovariance.Transport.compactPullFun K L hK hL j D).1 p)) := by
  exact EReal.continuous_toENNReal.comp_lowerSemicontinuous
    (SupercriticalConformalCovariance.Transport.compactPullFun K L hK hL j D).2
    (fun _ _ hab => EReal.toENNReal_le_toENNReal hab)

def confPullCompact (D : LSCMetric) (L K : Set ℂ) (hK : IsCompact K)
    (hL : IsCompact L) (j : C(K,L)) (hj : Function.Injective j) : LSCMetric :=
  ⟨extendMetric K (pullInner D L K j),
    isExtMetric_extendMetric K (pullInner D L K j) (pullInner_isExtMetric D L K j hj), by
      have heq : extendMetric K (pullInner D L K j) =
          fun p : ℂ × ℂ => if p.1 = p.2 then 0 else
            EReal.toENNReal ((SupercriticalConformalCovariance.Transport.compactPullFun K L hK hL j D).1 p) := by
        funext p
        by_cases hxy : p.1 = p.2
        · simp [extendMetric, hxy]
        by_cases hp : p.1 ∈ K ∧ p.2 ∈ K
        · rcases hp with ⟨hx,hy⟩
          have hv := SupercriticalConformalCovariance.Transport.compactPullFun_on K L hK hL j D
            (⟨p.1,hx⟩,⟨p.2,hy⟩)
          simp [extendMetric, hxy, pullInner, hx, hy, hv]
        · have hv := SupercriticalConformalCovariance.Transport.compactPullFun_off K L hK hL j D p hp
          simp [extendMetric, hxy, hp, hv]
      rw [heq]
      exact lsc_zero_diagonal (pullInner_lsc D L K hK hL j)⟩

theorem confPullCompact_on (D : LSCMetric) (L K : Set ℂ) (hK : IsCompact K)
    (hL : IsCompact L) (j : C(K,L)) (hj : Function.Injective j)
    {x y : ℂ} (hx : x ∈ K) (hy : y ∈ K) :
    confPullCompact D L K hK hL j hj (x,y) =
      D.internal L (j ⟨x,hx⟩, j ⟨y,hy⟩) :=
  extendMetric_on K (pullInner D L K j)
    (pullInner_isExtMetric D L K j hj) hx hy


theorem confPullCompact_isLengthSpace (D : LSCMetric) (L K : Set ℂ)
    (hK : IsCompact K) (hL : IsCompact L) (j : C(K,L))
    (hj : Function.Injective j) (jInv : C(L,K))
    (hjInv : ∀ y : L, j (jInv y) = y) :
    (confPullCompact D L K hK hL j hj).IsLengthSpace := by
  let E := confPullCompact D L K hK hL j hj
  intro x y hfin ε hε
  by_cases hxy : x = y
  · subst y
    refine ⟨fun _ => x, 0, 0, ⟨le_rfl, continuousOn_const⟩, rfl, rfl, ?_⟩
    have hzero : E.len (fun _ => x) 0 0 = 0 := by
      unfold LSCMetric.len
      exact eVariationOn.constant_on (by
        rintro _ ⟨s, -, rfl⟩ _ ⟨t, -, rfl⟩
        simp)
    rw [hzero]
    exact bot_le
  have hKxy : x ∈ K ∧ y ∈ K := by
    by_contra h
    have htop := extendMetric_off K (pullInner D L K j) hxy h
    change E (x,y) = ⊤ at htop
    rw [htop] at hfin
    exact (lt_irrefl (⊤ : ℝ≥0∞)) hfin
  rcases hKxy with ⟨hx, hy⟩
  let xK : K := ⟨x,hx⟩
  let yK : K := ⟨y,hy⟩
  have hcost : E (x,y) = D.internal L (j xK, j yK) :=
    confPullCompact_on D L K hK hL j hj hx hy
  have hlt : D.internal L (j xK, j yK) < E (x,y) + ENNReal.ofReal ε := by
    have hinnerfin : D.internal L (j xK, j yK) ≠ ⊤ := by
      rw [← hcost]
      exact hfin.ne
    rw [hcost]
    exact ENNReal.lt_add_right hinnerfin (ENNReal.ofReal_pos.2 hε).ne'
  unfold LSCMetric.internal at hlt
  simp only [iInf_lt_iff] at hlt
  obtain ⟨P,a,b,hP,hPL,ha,hb,hlen⟩ := hlt
  let f : ℝ → D.Space := D.pt ∘ P
  have hf : ContinuousOn f (Icc a b) := hP.2
  obtain ⟨γ,hγlen,hγrange⟩ :=
    LQGMetric.MetricGeometry.exists_path_of_curve hP.1 hf
  have hγcost : LQGMetric.MetricGeometry.pathLength γ < E (x,y) + ENNReal.ofReal ε := by
    rw [hγlen]
    exact hlen
  have hγfin : LQGMetric.MetricGeometry.pathLength γ ≠ ⊤ :=
    (lt_of_lt_of_le hγcost le_top).ne
  obtain ⟨γ',hγ'len,hγ'range,hγ'lip⟩ :=
    LQGMetric.MetricGeometry.exists_lipschitz_path γ hγfin
  have hγL : ∀ t : unitInterval, (γ t : ℂ) ∈ L := by
    intro t
    obtain ⟨s,hs,heq⟩ := hγrange (Set.mem_range_self t)
    have ht : P s ∈ L := hPL s hs
    have heq' : (γ t : ℂ) = P s := congrArg (fun v : D.Space => (v : ℂ)) heq.symm
    exact heq'.symm ▸ ht
  have hγ'L : ∀ t : unitInterval, (γ' t : ℂ) ∈ L := by
    intro t
    obtain ⟨s,heq⟩ := hγ'range (Set.mem_range_self t)
    exact heq.symm ▸ hγL s
  have hQL : ∀ t : ℝ, (γ'.extend t : ℂ) ∈ L := by
    intro t
    obtain ⟨s,heq⟩ := γ'.extend_range.subset (Set.mem_range_self t)
    have heq' : (γ' s : ℂ) = (γ'.extend t : ℂ) :=
      congrArg (fun v : D.Space => (v : ℂ)) heq
    exact heq' ▸ hγ'L s
  let Q : ℝ → L := fun t => ⟨(γ'.extend t : ℂ), hQL t⟩
  let P' : ℝ → ℂ := fun t => (jInv (Q t) : ℂ)
  have hP'K : ∀ t : ℝ, P' t ∈ K := fun t => (jInv (Q t)).2
  have hjP' : ∀ t : ℝ, j ⟨P' t, hP'K t⟩ = Q t := by
    intro t
    exact hjInv (Q t)
  have hQLip : LipschitzOnWith
      (LQGMetric.MetricGeometry.pathLength γ).toNNReal (D.pt ∘ fun t => (Q t : ℂ)) (Icc 0 1) := by
    intro s hs t ht
    change edist (γ'.extend s) (γ'.extend t) ≤
      ((LQGMetric.MetricGeometry.pathLength γ).toNNReal : ℝ≥0∞) * edist s t
    rw [Path.extend_apply _ hs, Path.extend_apply _ ht]
    simpa only [Subtype.edist_eq] using hγ'lip ⟨s,hs⟩ ⟨t,ht⟩
  have hEcurve : E.IsCurve P' 0 1 := by
    let Y : Set D.Space := D.pt '' L
    let Q' : ℝ → Y := fun t => ⟨D.pt (Q t), ⟨(Q t : ℂ), (Q t).2, rfl⟩⟩
    have hLip' : LipschitzOnWith
        (LQGMetric.MetricGeometry.pathLength γ).toNNReal
        (fun t => (Q' t : D.Space)) (Icc 0 1) := hQLip
    have hi := SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.lipschitzOnWith_internalSpace
      (X := D.Space) Y Q' hLip'
    refine ⟨zero_le_one, ?_⟩
    have hc : LipschitzOnWith (LQGMetric.MetricGeometry.pathLength γ).toNNReal
        (E.pt ∘ P') (Icc 0 1) := by
      intro s hs t ht
      change E (P' s, P' t) ≤ _
      rw [confPullCompact_on D L K hK hL j hj (hP'K s) (hP'K t),
        hjP' s, hjP' t]
      rw [LSCMetric.internal_eq_internalEDist]
      exact hi hs ht
    exact hc.continuousOn
  have hDcurve : D.IsCurve (fun t => (Q t : ℂ)) 0 1 := by
    refine ⟨zero_le_one, ?_⟩
    exact γ'.continuous_extend.continuousOn
  have hlenEq : E.len P' 0 1 = D.len (fun t => (Q t : ℂ)) 0 1 := by
    have hbase := SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.len_eq_internalLen
      D L Q 0 1 hDcurve
    rw [hbase]
    unfold LSCMetric.len SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.internalLen
    unfold eVariationOn
    refine iSup_congr fun q => Finset.sum_congr rfl fun i _ => ?_
    change E (P' (q.2.1 (i+1)), P' (q.2.1 i)) =
      D.internal L (Q (q.2.1 (i+1)), Q (q.2.1 i))
    rw [confPullCompact_on D L K hK hL j hj (hP'K _) (hP'K _)]
    rw [hjP', hjP']
  refine ⟨P', 0, 1, hEcurve, ?_, ?_, ?_⟩
  · change (jInv (Q 0) : ℂ) = x
    rw [show Q 0 = j xK from by
      apply Subtype.ext
      change γ'.extend 0 = (j xK : ℂ)
      rw [Path.extend_zero]
      change P a = (j xK : ℂ)
      exact ha]
    exact congrArg Subtype.val (hj (hjInv (j xK)))
  · change (jInv (Q 1) : ℂ) = y
    rw [show Q 1 = j yK from by
      apply Subtype.ext
      change γ'.extend 1 = (j yK : ℂ)
      rw [Path.extend_one]
      change P b = (j yK : ℂ)
      exact hb]
    exact congrArg Subtype.val (hj (hjInv (j yK)))
  · rw [hlenEq]
    change LQGMetric.MetricGeometry.pathLength γ' ≤ _
    rw [hγ'len]
    exact hγcost.le
