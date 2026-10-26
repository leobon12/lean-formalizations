import SupercriticalConformalCovariance.Small.TargetConfinedLSC
import SupercriticalConformalCovariance.Small.ConfinedMeasurable
import SupercriticalConformalCovariance.Tangent.CompactPull
import SupercriticalConformalCovariance.Tangent.DiskFunctional
import SupercriticalConformalCovariance.Compact.ClosedDiskBridge
import SupercriticalLQGUniqueness.B2.LscTop.Limits

/-!
# Diagonal-corrected confined metrics (the Lemma 3.3 proof, for the Proposition 4.3 proof's consumption form)

the Proposition 4.3 proof consumes confined metrics as global `LSCMetric`s with the diagonal set to zero:
`conf K e (x, y) = 0` if `x = y`, `e_K(x, y)` if `x ≠ y` and `x, y ∈ K`, `∞` otherwise. The
The metric helper proofs below adapt the Proposition 4.3 construction. The exported
`confDisk` and `confPull` constructors abbreviate the actual constructors of the Proposition 4.3 proof;
`SupercriticalConformalCovariance.Conf` is the shared interface for consumers.

* `lscTendsto_of_eqOn_offDiag`: epigraph convergence is unchanged when the functions are modified on the
  diagonal (to `0`), provided the limit vanishes on the diagonal.
* `confDisk M R`, `confPull M L K j`: the diagonal-corrected internal metric of a closed disk, and the
  diagonal-corrected pull-back of a compact internal metric, as `LSCMetric`s; both are Borel functions of
  the metric `M`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalConformalCovariance.Tangent

open SupercriticalLQGUniqueness (LSCMetric LSCFun LSCTendsto IsExtMetric lowerSemicontinuous_iff_seq)
open SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints (closedBallPathInf
  closedBallPathInf_joint_lsc)

/-! ## The diagonal does not matter in the limit -/

/-- **Zeroing the diagonal.** If `G n` agrees with `F n` off the diagonal, `G n` vanishes on the
diagonal, and the limit `L` vanishes on the diagonal, then `F n → L` implies `G n → L`
(values in `[0, ∞]`). -/
theorem lscTendsto_of_eqOn_offDiag {F G : ℕ → ℂ × ℂ → ℝ≥0∞} {L : ℂ × ℂ → ℝ≥0∞}
    (hL0 : ∀ x, L (x, x) = 0) (hG0 : ∀ n x, G n (x, x) = 0)
    (hGF : ∀ n q, q.1 ≠ q.2 → G n q = F n q)
    (h : LSCTendsto (fun n q => (F n q : EReal)) (fun q => (L q : EReal))) :
    LSCTendsto (fun n q => (G n q : EReal)) (fun q => (L q : EReal)) := by
  have hoff : ∀ {p : ℕ → ℂ × ℂ} {q : ℂ × ℂ}, Tendsto p atTop (𝓝 q) → q.1 ≠ q.2 →
      ∀ᶠ n in atTop, (p n).1 ≠ (p n).2 := fun {p q} hp hq =>
    hp ((isClosed_eq continuous_fst continuous_snd).isOpen_compl.mem_nhds hq)
  refine ⟨fun p q hp => ?_, fun q => ?_⟩
  · by_cases hq : q.1 = q.2
    · have hLq : L q = 0 := by
        obtain ⟨x, y⟩ := q; simp only at hq; subst hq; exact hL0 x
      show (L q : EReal) ≤ _
      rw [hLq, EReal.coe_ennreal_zero]
      exact le_liminf_of_le (by isBoundedDefault)
        (Eventually.of_forall fun n => EReal.coe_ennreal_nonneg _)
    · have heq : (fun n => (G n (p n) : EReal)) =ᶠ[atTop] fun n => (F n (p n) : EReal) := by
        filter_upwards [hoff hp hq] with n hn
        rw [hGF n (p n) hn]
      rw [liminf_congr heq]
      exact h.1 p q hp
  · by_cases hq : q.1 = q.2
    · refine ⟨fun _ => q, tendsto_const_nhds, ?_⟩
      obtain ⟨x, y⟩ := q
      simp only at hq
      subst hq
      show Tendsto (fun n => (G n (x, x) : EReal)) atTop (𝓝 (L (x, x) : EReal))
      simp only [hG0, hL0]
      exact tendsto_const_nhds
    · obtain ⟨p, hp, hFp⟩ := h.2 q
      refine ⟨p, hp, hFp.congr' ?_⟩
      filter_upwards [hoff hp hq] with n hn
      rw [hGF n (p n) hn]

/-! ## `extendMetric` (copy of the Proposition 4.3 proof's construction) -/

/-- Extend a metric on `K` to the plane: `0` on the diagonal, `∞` off `K × K`. -/
def extendMetric (K : Set ℂ) (d : K × K → ℝ≥0∞) (p : ℂ × ℂ) : ℝ≥0∞ :=
  open Classical in
  if p.1 = p.2 then 0 else if h : p.1 ∈ K ∧ p.2 ∈ K then d (⟨p.1, h.1⟩, ⟨p.2, h.2⟩) else ⊤

theorem extendMetric_on (K : Set ℂ) (d : K × K → ℝ≥0∞) (hd : IsExtMetric d) {x y : ℂ}
    (hx : x ∈ K) (hy : y ∈ K) : extendMetric K d (x, y) = d (⟨x, hx⟩, ⟨y, hy⟩) := by
  by_cases hxy : x = y
  · subst y; simp [extendMetric, hd.1]
  · simp [extendMetric, hxy, hx, hy]

theorem extendMetric_off (K : Set ℂ) (d : K × K → ℝ≥0∞) {x y : ℂ} (hxy : x ≠ y)
    (h : ¬ (x ∈ K ∧ y ∈ K)) : extendMetric K d (x, y) = ⊤ := by
  simp [extendMetric, hxy, h]

theorem isExtMetric_extendMetric (K : Set ℂ) (d : K × K → ℝ≥0∞) (hd : IsExtMetric d) :
    IsExtMetric (extendMetric K d) := by
  refine ⟨fun x => by simp [extendMetric], fun x y hxy => ?_, fun x y => ?_, fun x y z => ?_⟩
  · by_contra hne
    by_cases hx : x ∈ K
    · by_cases hy : y ∈ K
      · rw [extendMetric_on K d hd hx hy] at hxy
        exact hne (congrArg Subtype.val (hd.2.1 ⟨x, hx⟩ ⟨y, hy⟩ hxy))
      · rw [extendMetric_off K d hne (by simp [hy])] at hxy
        exact ENNReal.top_ne_zero hxy
    · rw [extendMetric_off K d hne (by simp [hx])] at hxy
      exact ENNReal.top_ne_zero hxy
  · by_cases hxy : x = y
    · subst y; rfl
    by_cases hx : x ∈ K
    · by_cases hy : y ∈ K
      · rw [extendMetric_on K d hd hx hy, extendMetric_on K d hd hy hx]
        exact hd.2.2.1 ⟨x, hx⟩ ⟨y, hy⟩
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
          exact hd.2.2.2 ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
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
      · rw [extendMetric_off K d hxz (by simp [hx]), extendMetric_off K d hxy (by simp [hx])]
        simp

/-- Lowering the diagonal of a jointly lower semicontinuous kernel to zero keeps it lower
semicontinuous. -/
theorem lsc_zero_diagonal_joint {X : Type*} [TopologicalSpace X] {F : X × (ℂ × ℂ) → ℝ≥0∞}
    (hF : LowerSemicontinuous F) :
    LowerSemicontinuous (fun p : X × (ℂ × ℂ) => if p.2.1 = p.2.2 then 0 else F p) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage] at hF ⊢
  intro a
  have hO : IsOpen {p : X × (ℂ × ℂ) | p.2.1 ≠ p.2.2} :=
    (isClosed_eq (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd)).isOpen_compl
  have hset : (fun p : X × (ℂ × ℂ) => if p.2.1 = p.2.2 then (0 : ℝ≥0∞) else F p) ⁻¹' Ioi a =
      F ⁻¹' Ioi a ∩ {p | p.2.1 ≠ p.2.2} := by
    ext p; by_cases hp : p.2.1 = p.2.2 <;> simp [hp]
  rw [hset]
  exact (hF a).inter hO

theorem lsc_zero_diagonal {F : ℂ × ℂ → ℝ≥0∞} (hF : LowerSemicontinuous F) :
    LowerSemicontinuous (fun p : ℂ × ℂ => if p.1 = p.2 then 0 else F p) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage] at hF ⊢
  intro a
  have hO : IsOpen {p : ℂ × ℂ | p.1 ≠ p.2} :=
    (isClosed_eq continuous_fst continuous_snd).isOpen_compl
  have hset : (fun p : ℂ × ℂ => if p.1 = p.2 then (0 : ℝ≥0∞) else F p) ⁻¹' Ioi a =
      F ⁻¹' Ioi a ∩ {p | p.1 ≠ p.2} := by
    ext p; by_cases hp : p.1 = p.2 <;> simp [hp]
  rw [hset]
  exact (hF a).inter hO

/-! ## The closed-disk version (for `d_n`) -/

theorem extendMetric_internal_eq (M : LSCMetric) (K : Set ℂ) (p : ℂ × ℂ) :
    extendMetric K (M.internal K) p = if p.1 = p.2 then 0 else extInternal M K p := by
  unfold extendMetric extInternal
  rfl

/-- The diagonal-corrected internal metric of `B̄_R(0)`, as an `LSCMetric`. -/
abbrev confDisk (M : LSCMetric) (R : ℝ) : LSCMetric := SupercriticalConformalCovariance.Small.conf M 0 R

theorem confDisk_apply (M : LSCMetric) (R : ℝ) (p : ℂ × ℂ) :
    confDisk M R p = if p.1 = p.2 then 0 else extInternal M (closedBall 0 R) p := by
  change SupercriticalConformalCovariance.Small.confKernel M 0 R p = _
  rw [SupercriticalConformalCovariance.Small.confKernel_eq_extendMetric]
  exact extendMetric_internal_eq M _ p

theorem measurable_confDisk (R : ℝ) : Measurable fun M : LSCMetric => confDisk M R := by
  letI : MeasurableSpace LSCFun := borel LSCFun
  haveI : BorelSpace LSCFun := ⟨rfl⟩
  have := SupercriticalLQGUniqueness.B2.LscTop.borelSpace_LSCMetric
  rw [SupercriticalLQGUniqueness.B2.LscTop.measurable_iff_toLSCFun]
  have hc : Continuous fun p : LSCMetric × (ℂ × ℂ) => (p.1, ((0 : ℂ), (R, p.2))) :=
    continuous_fst.prodMk (continuous_const.prodMk (continuous_const.prodMk continuous_snd))
  have hj : LowerSemicontinuous fun p : LSCMetric × (ℂ × ℂ) =>
      closedBallPathInf p.1 0 R p.2.1 p.2.2 := by
    change LowerSemicontinuous
      ((fun p : LSCMetric × (ℂ × (ℝ × (ℂ × ℂ))) =>
        closedBallPathInf p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∘
        fun p : LSCMetric × (ℂ × ℂ) => (p.1, ((0 : ℂ), (R, p.2))))
    exact closedBallPathInf_joint_lsc.comp hc
  have hk : LowerSemicontinuous fun p : LSCMetric × (ℂ × ℂ) =>
      (((if p.2.1 = p.2.2 then 0 else closedBallPathInf p.1 0 R p.2.1 p.2.2 : ℝ≥0∞)) : EReal) :=
    continuous_coe_ennreal_ereal.comp_lowerSemicontinuous (lsc_zero_diagonal_joint hj)
      EReal.coe_ennreal_strictMono.monotone
  have hm := SupercriticalConformalCovariance.Lemma31.measurable_lscSection (fun M q =>
    (((if q.1 = q.2 then 0 else closedBallPathInf M 0 R q.1 q.2 : ℝ≥0∞)) : EReal)) hk
  have e : (fun M : LSCMetric => (confDisk M R).toLSCFun) = SupercriticalConformalCovariance.Lemma31.lscSection (fun M q =>
      (((if q.1 = q.2 then 0 else closedBallPathInf M 0 R q.1 q.2 : ℝ≥0∞)) : EReal)) hk := by
    funext M
    apply Subtype.ext
    funext p
    show ((confDisk M R p : ℝ≥0∞) : EReal) =
      ((if p.1 = p.2 then 0 else closedBallPathInf M 0 R p.1 p.2 : ℝ≥0∞) : EReal)
    rw [confDisk_apply, closedBallPathInf_eq_extInternal]
  rw [e]
  exact hm

/-! ## The pulled-back compact version (for `e_n`) -/

/-- The pull-back of the internal metric of `L` to `K` along `j`. -/
def pullInner (M : LSCMetric) (L K : Set ℂ) (j : C(K, L)) (p : K × K) : ℝ≥0∞ :=
  M.internal L (j p.1, j p.2)

theorem pullInner_isExtMetric (M : LSCMetric) (L K : Set ℂ) (j : C(K, L))
    (hj : Function.Injective j) : IsExtMetric (pullInner M L K j) := by
  have h := M.isExtMetric_internal L
  exact ⟨fun x => h.1 (j x), fun x y hxy => hj (h.2.1 (j x) (j y) hxy),
    fun x y => h.2.2.1 (j x) (j y), fun x y z => h.2.2.2 (j x) (j y) (j z)⟩

theorem extendMetric_pullInner_eq (M : LSCMetric) (L K : Set ℂ) (hK : IsCompact K)
    (hL : IsCompact L) (j : C(K, L)) (p : ℂ × ℂ) :
    extendMetric K (pullInner M L K j) p =
      if p.1 = p.2 then 0 else EReal.toENNReal ((compactPullFun K L hK hL j M).1 p) := by
  by_cases hxy : p.1 = p.2
  · simp [extendMetric, hxy]
  by_cases hp : p.1 ∈ K ∧ p.2 ∈ K
  · obtain ⟨hx, hy⟩ := hp
    have hv := compactPullFun_on K L hK hL j M (⟨p.1, hx⟩, ⟨p.2, hy⟩)
    simp [extendMetric, hxy, pullInner, hx, hy, hv]
  · have hv := compactPullFun_off K L hK hL j M p hp
    simp [extendMetric, hxy, hp, hv]

/-- The diagonal-corrected pulled-back compact internal metric, as an `LSCMetric`. -/
abbrev confPull (M : LSCMetric) (L K : Set ℂ) (hK : IsCompact K) (hL : IsCompact L)
    (j : C(K, L)) (hj : Function.Injective j) : LSCMetric :=
  SupercriticalConformalCovariance.Small.confPullCompact M L K hK hL j hj

theorem confPull_apply (M : LSCMetric) (L K : Set ℂ) (hK : IsCompact K) (hL : IsCompact L)
    (j : C(K, L)) (hj : Function.Injective j) (p : ℂ × ℂ) :
    confPull M L K hK hL j hj p = extendMetric K (pullInner M L K j) p := rfl

theorem measurable_confPull (L K : Set ℂ) (hK : IsCompact K) (hL : IsCompact L) (j : C(K, L))
    (hj : Function.Injective j) : Measurable fun M : LSCMetric => confPull M L K hK hL j hj := by
  letI : MeasurableSpace LSCFun := borel LSCFun
  haveI : BorelSpace LSCFun := ⟨rfl⟩
  have := SupercriticalLQGUniqueness.B2.LscTop.borelSpace_LSCMetric
  rw [SupercriticalLQGUniqueness.B2.LscTop.measurable_iff_toLSCFun]
  have hj' : LowerSemicontinuous fun p : LSCMetric × (ℂ × ℂ) =>
      EReal.toENNReal ((compactPullFun K L hK hL j p.1).1 p.2) :=
    EReal.continuous_toENNReal.comp_lowerSemicontinuous (compactPullFun_joint_lsc K L hK hL j)
      (fun _ _ hab => EReal.toENNReal_le_toENNReal hab)
  have hk : LowerSemicontinuous fun p : LSCMetric × (ℂ × ℂ) =>
      (((if p.2.1 = p.2.2 then 0 else EReal.toENNReal ((compactPullFun K L hK hL j p.1).1 p.2) :
        ℝ≥0∞)) : EReal) :=
    continuous_coe_ennreal_ereal.comp_lowerSemicontinuous (lsc_zero_diagonal_joint hj')
      EReal.coe_ennreal_strictMono.monotone
  have hm := SupercriticalConformalCovariance.Lemma31.measurable_lscSection (fun M q =>
    (((if q.1 = q.2 then 0 else EReal.toENNReal ((compactPullFun K L hK hL j M).1 q) :
      ℝ≥0∞)) : EReal)) hk
  have e : (fun M : LSCMetric => (confPull M L K hK hL j hj).toLSCFun) =
      SupercriticalConformalCovariance.Lemma31.lscSection (fun M q =>
        (((if q.1 = q.2 then 0 else EReal.toENNReal ((compactPullFun K L hK hL j M).1 q) :
          ℝ≥0∞)) : EReal)) hk := by
    funext M
    apply Subtype.ext
    funext p
    show ((confPull M L K hK hL j hj p : ℝ≥0∞) : EReal) = _
    rw [confPull_apply, extendMetric_pullInner_eq M L K hK hL j p]
    rfl
  rw [e]
  exact hm

end SupercriticalConformalCovariance.Tangent
