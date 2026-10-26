import SupercriticalConformalCovariance.Transport.ConfinedFieldFactor
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.JointCompact

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory TopologicalSpace Set Classical
open scoped ENNReal
open SupercriticalLQGUniqueness
namespace SupercriticalConformalCovariance.Transport

private theorem lsc_extend_top {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {e : α → β} (he : Topology.IsClosedEmbedding e) {f : α → EReal}
    (hf : LowerSemicontinuous f) :
    LowerSemicontinuous (fun b : β => ⨅ a : α, if e a = b then f a else ⊤) := by
  let F : β → EReal := fun b => ⨅ a : α, if e a = b then f a else ⊤
  have hon : ∀ a, F (e a) = f a := by
    intro a
    apply le_antisymm
    · exact iInf_le_of_le a (by simp [F])
    · refine le_iInf fun a' => ?_
      by_cases h : e a' = e a
      · have heq := he.injective h
        subst a'
        simp [F]
      · simp [h]
  have hoff : ∀ b, b ∉ range e → F b = ⊤ := by
    intro b hb
    simp only [F]
    have h : ∀ a : α, e a ≠ b := fun a ha => hb ⟨a, ha⟩
    simp [h]
  apply lowerSemicontinuous_iff_isClosed_preimage.2
  intro t
  by_cases ht : t = ⊤
  · subst t
    simp
  have hpre : F ⁻¹' Iic t = e '' (f ⁻¹' Iic t) := by
    ext b
    constructor
    · intro hb
      by_cases hr : b ∈ range e
      · rcases hr with ⟨a, rfl⟩
        exact ⟨a, by simpa [hon a] using hb, rfl⟩
      · have htop := hoff b hr
        have hle : (⊤ : EReal) ≤ t := by simpa [hoff b hr] using hb
        exact (ht (top_le_iff.mp hle)).elim
    · rintro ⟨a, ha, rfl⟩
      simpa [hon] using ha
  rw [hpre]
  exact he.isClosedMap _ (hf.isClosed_preimage t)

private def compactJoint (K : Set ℂ) (p : LSCMetric × (ℂ × ℂ)) : EReal :=
  ⨅ a : LSCMetric × (K × K),
    if (a.1, ((a.2.1 : ℂ), (a.2.2 : ℂ))) = p then
      ((a.1.internal K a.2 : ℝ≥0∞) : EReal) else ⊤

private theorem compactJoint_lsc (K : Set ℂ) (hK : IsCompact K) :
    LowerSemicontinuous (compactJoint K) := by
  let e : LSCMetric × (K × K) → LSCMetric × (ℂ × ℂ) :=
    fun a => (a.1, ((a.2.1 : ℂ), (a.2.2 : ℂ)))
  have he : Topology.IsClosedEmbedding e := by
    change Topology.IsClosedEmbedding
      (Prod.map id (Prod.map (Subtype.val : K → ℂ) (Subtype.val : K → ℂ)))
    exact Topology.IsClosedEmbedding.id.prodMap
      (hK.isClosed.isClosedEmbedding_subtypeVal.prodMap
        hK.isClosed.isClosedEmbedding_subtypeVal)
  have hf : LowerSemicontinuous (fun a : LSCMetric × (K × K) =>
      ((a.1.internal K a.2 : ℝ≥0∞) : EReal)) :=
    continuous_coe_ennreal_ereal.comp_lowerSemicontinuous
      (Uniqueness.Toolkit.MovingEndpoints.internal_compact_joint_lsc hK)
      EReal.coe_ennreal_strictMono.monotone
  convert lsc_extend_top he hf using 1
  funext p
  simp only [compactJoint, e]
  refine iInf_congr fun a => ?_
  by_cases h : (a.1, ((a.2.1 : ℂ), (a.2.2 : ℂ))) = p <;> simp [h]

/-- The compact internal metric, extended by infinity off the compact endpoint carrier. -/
def compactFun (K : Set ℂ) (hK : IsCompact K) (D : LSCMetric) : LSCFun :=
  ⟨fun q => compactJoint K (D, q),
    (compactJoint_lsc K hK).comp (continuous_const.prodMk continuous_id)⟩


/-- Evaluation on the compact carrier is exactly the internal metric. -/
theorem compactFun_on (K : Set ℂ) (hK : IsCompact K) (D : LSCMetric)
    (q : K × K) :
    (compactFun K hK D).1 ((q.1 : ℂ), (q.2 : ℂ)) = ((D.internal K q : ℝ≥0∞) : EReal) := by
  have he : Function.Injective
      (fun a : LSCMetric × (K × K) => (a.1, ((a.2.1 : ℂ), (a.2.2 : ℂ)))) := by
    intro a b hab
    have h₁ : a.1 = b.1 := congrArg (fun p : LSCMetric × (ℂ × ℂ) => p.1) hab
    have h₂ : ((a.2.1 : ℂ), (a.2.2 : ℂ)) =
        ((b.2.1 : ℂ), (b.2.2 : ℂ)) :=
      congrArg (fun p : LSCMetric × (ℂ × ℂ) => p.2) hab
    apply Prod.ext
    · exact h₁
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst h₂
      · apply Subtype.ext
        exact congrArg Prod.snd h₂
  unfold compactFun compactJoint
  apply le_antisymm
  · exact iInf_le_of_le (D, q) (by simp)
  · refine le_iInf fun a => ?_
    by_cases ha : (a.1, ((a.2.1 : ℂ), (a.2.2 : ℂ))) =
        (D, ((q.1 : ℂ), (q.2 : ℂ)))
    · have hae : a = (D, q) := he ha
      subst a
      simp
    · simp [ha]

/-- Evaluation outside the compact carrier is infinite. -/
theorem compactFun_off (K : Set ℂ) (hK : IsCompact K) (D : LSCMetric)
    (q : ℂ × ℂ) (hq : ¬ (q.1 ∈ K ∧ q.2 ∈ K)) :
    (compactFun K hK D).1 q = ⊤ := by
  unfold compactFun compactJoint
  have he : ∀ a : LSCMetric × (K × K),
      (a.1, ((a.2.1 : ℂ), (a.2.2 : ℂ))) ≠ (D, q) := by
    intro a ha
    have hqeq := congrArg Prod.snd ha
    have hx : (a.2.1 : ℂ) = q.1 := congrArg Prod.fst hqeq
    have hy : (a.2.2 : ℂ) = q.2 := congrArg Prod.snd hqeq
    exact hq ⟨hx ▸ a.2.1.2, hy ▸ a.2.2.2⟩
  simp [he]

/-- The lower-semicontinuous function topology admits Borel maps with jointly lsc evaluation. -/
theorem measurable_lscFun_of_joint_lsc [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (T : LSCMetric → LSCFun)
    (hjoint : LowerSemicontinuous (fun p : LSCMetric × (ℂ × ℂ) => (T p.1).1 p.2)) :
    Measurable T := by
  have hcomp : ∀ H : Set (ℂ × ℂ), IsCompact H →
      Measurable (fun D : LSCMetric => ⨅ q ∈ H, (T D).1 q) := by
    intro H hH
    exact (compact_inf_joint_lsc hjoint hH).measurable
  apply SupercriticalLQGUniqueness.B2.PfeAxioms.measurable_lscFun_of_tests
  · intro O hO r
    have heq : {D : LSCMetric | ∃ q ∈ O, (T D).1 q < (((r : ℝ) : EReal))} =
        (fun D => ⨅ q ∈ O, (T D).1 q) ⁻¹' Iio (((r : ℝ) : EReal)) := by
      ext D
      simp only [mem_ofPred_eq, mem_preimage, mem_Iio, iInf_lt_iff, exists_prop]
    rw [heq]
    have hm : Measurable (fun D : LSCMetric => ⨅ q ∈ O, (T D).1 q) := by
      simp_rw [SupercriticalLQGUniqueness.B2.PfeAxioms.iInf_open_eq_iInf_ballFamily
        (u := fun q => (T _).1 q) hO]
      refine Measurable.iInf fun j => ?_
      by_cases hj : SupercriticalLQGUniqueness.B2.PfeAxioms.ballFamily j ⊆ O
      · simp only [hj, iInf_pos]
        exact hcomp _ (SupercriticalLQGUniqueness.B2.PfeAxioms.isCompact_ballFamily j)
      · simp only [hj, iInf_false]
        exact measurable_const
    exact hm measurableSet_Iio
  · intro H hH r
    have heq : {D : LSCMetric | ∀ q ∈ H, (((r : ℝ) : EReal)) < (T D).1 q} =
        (fun D => ⨅ q ∈ H, (T D).1 q) ⁻¹' Ioi (((r : ℝ) : EReal)) := by
      ext D
      simp only [mem_ofPred_eq, mem_preimage, mem_Ioi]
      exact SupercriticalLQGUniqueness.B2.PfeAxioms.forall_lt_iff_lt_iInf
        (T D).2 hH _ (EReal.coe_ne_top _)
    rw [heq]
    exact hcomp H hH measurableSet_Ioi

/-- Borel measurability of the compact internal metric as an `LSCFun`. -/
theorem measurable_compactFun [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (K : Set ℂ) (hK : IsCompact K) : Measurable (compactFun K hK) :=
  measurable_lscFun_of_joint_lsc _ (compactJoint_lsc K hK)


private def compactPullJoint (K L : Set ℂ) (hL : IsCompact L) (j : C(K, L))
    (p : LSCMetric × (ℂ × ℂ)) : EReal :=
  ⨅ a : LSCMetric × (K × K),
    if (a.1, ((a.2.1 : ℂ), (a.2.2 : ℂ))) = p then
      (compactFun L hL a.1).1 ((j a.2.1 : ℂ), (j a.2.2 : ℂ)) else ⊤

private theorem compactPullJoint_lsc (K L : Set ℂ) (hK : IsCompact K)
    (hL : IsCompact L) (j : C(K, L)) :
    LowerSemicontinuous (compactPullJoint K L hL j) := by
  let e : LSCMetric × (K × K) → LSCMetric × (ℂ × ℂ) :=
    fun a => (a.1, ((a.2.1 : ℂ), (a.2.2 : ℂ)))
  have he : Topology.IsClosedEmbedding e := by
    change Topology.IsClosedEmbedding
      (Prod.map id (Prod.map (Subtype.val : K → ℂ) (Subtype.val : K → ℂ)))
    exact Topology.IsClosedEmbedding.id.prodMap
      (hK.isClosed.isClosedEmbedding_subtypeVal.prodMap
        hK.isClosed.isClosedEmbedding_subtypeVal)
  have hj : Continuous (fun x : K => (j x : ℂ)) :=
    continuous_subtype_val.comp j.continuous
  have hc : Continuous (fun a : LSCMetric × (K × K) =>
      (a.1, ((j a.2.1 : ℂ), (j a.2.2 : ℂ)))) := by
    exact continuous_fst.prodMk
      ((hj.comp (continuous_fst.comp continuous_snd)).prodMk
        (hj.comp (continuous_snd.comp continuous_snd)))
  have hf : LowerSemicontinuous (fun a : LSCMetric × (K × K) =>
      (compactFun L hL a.1).1 ((j a.2.1 : ℂ), (j a.2.2 : ℂ))) :=
    (compactJoint_lsc L hL).comp hc
  convert lsc_extend_top he hf using 1
  funext p
  simp only [compactPullJoint, e]
  refine iInf_congr fun a => ?_
  by_cases h : (a.1, ((a.2.1 : ℂ), (a.2.2 : ℂ))) = p <;> simp [h]

/-- Compact target internal metric transported to source compact coordinates, infinite outside. -/
def compactPullFun (K L : Set ℂ) (hK : IsCompact K) (hL : IsCompact L)
    (j : C(K, L)) (D : LSCMetric) : LSCFun :=
  ⟨fun q => compactPullJoint K L hL j (D, q),
    (compactPullJoint_lsc K L hK hL j).comp (continuous_const.prodMk continuous_id)⟩

/-- Borel measurability of transported compact confinement. -/
theorem measurable_compactPullFun [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (K L : Set ℂ) (hK : IsCompact K) (hL : IsCompact L) (j : C(K, L)) :
    Measurable (compactPullFun K L hK hL j) :=
  measurable_lscFun_of_joint_lsc _ (compactPullJoint_lsc K L hK hL j)

/-- Exact value of transported confinement on the source carrier. -/
theorem compactPullFun_on (K L : Set ℂ) (hK : IsCompact K) (hL : IsCompact L)
    (j : C(K, L)) (D : LSCMetric) (q : K × K) :
    (compactPullFun K L hK hL j D).1 ((q.1 : ℂ), (q.2 : ℂ)) =
      ((D.internal L (j q.1, j q.2) : ℝ≥0∞) : EReal) := by
  have he : Function.Injective
      (fun a : LSCMetric × (K × K) => (a.1, ((a.2.1 : ℂ), (a.2.2 : ℂ)))) := by
    intro a b hab
    have h₁ : a.1 = b.1 := congrArg (fun p : LSCMetric × (ℂ × ℂ) => p.1) hab
    have h₂ : ((a.2.1 : ℂ), (a.2.2 : ℂ)) =
        ((b.2.1 : ℂ), (b.2.2 : ℂ)) :=
      congrArg (fun p : LSCMetric × (ℂ × ℂ) => p.2) hab
    apply Prod.ext
    · exact h₁
    · apply Prod.ext
      · apply Subtype.ext; exact congrArg Prod.fst h₂
      · apply Subtype.ext; exact congrArg Prod.snd h₂
  unfold compactPullFun compactPullJoint
  rw [← compactFun_on L hL D (j q.1, j q.2)]
  apply le_antisymm
  · exact iInf_le_of_le (D, q) (by simp)
  · refine le_iInf fun a => ?_
    by_cases ha : (a.1, ((a.2.1 : ℂ), (a.2.2 : ℂ))) =
        (D, ((q.1 : ℂ), (q.2 : ℂ)))
    · have hae : a = (D, q) := he ha
      subst a
      simp
    · simp [ha]

/-- Transported confinement is infinite outside the source carrier. -/
theorem compactPullFun_off (K L : Set ℂ) (hK : IsCompact K) (hL : IsCompact L)
    (j : C(K, L)) (D : LSCMetric) (q : ℂ × ℂ)
    (hq : ¬ (q.1 ∈ K ∧ q.2 ∈ K)) :
    (compactPullFun K L hK hL j D).1 q = ⊤ := by
  unfold compactPullFun compactPullJoint
  have he : ∀ a : LSCMetric × (K × K),
      (a.1, ((a.2.1 : ℂ), (a.2.2 : ℂ))) ≠ (D, q) := by
    intro a ha
    have hqeq := congrArg Prod.snd ha
    have hx : (a.2.1 : ℂ) = q.1 := congrArg Prod.fst hqeq
    have hy : (a.2.2 : ℂ) = q.2 := congrArg Prod.snd hqeq
    exact hq ⟨hx ▸ a.2.1.2, hy ▸ a.2.2.2⟩
  simp [he]

/-- Joint lower semicontinuity of transported compact confinement, exported for Lemma 3.3. -/
theorem compactPullFun_joint_lsc (K L : Set ℂ) (hK : IsCompact K) (hL : IsCompact L)
    (j : C(K, L)) :
    LowerSemicontinuous (fun p : LSCMetric × (ℂ × ℂ) => (compactPullFun K L hK hL j p.1).1 p.2) :=
  compactPullJoint_lsc K L hK hL j

end SupercriticalConformalCovariance.Transport
