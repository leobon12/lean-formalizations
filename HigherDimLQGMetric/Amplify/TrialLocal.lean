import HigherDimLQGMetric.Amplify.TrialMeas
import HigherDimLQGMetric.Events.EventInvariant
import HigherDimLQGMetric.WNSplit.Local

/-!
# Shell locality of the fine-field trial event

The normalized trial inequalities use only the two internal metrics on the outer and
inner annuli. The countable shell code from the event layer then supplies locality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

theorem amplify_scale_ofReal (s t : ℝ) (hs : 0 < s) :
    ENNReal.ofReal s⁻¹ * ENNReal.ofReal (t * s) = ENNReal.ofReal t := by
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ s⁻¹)]
  congr 1
  field_simp

theorem amplify_scale_lower_iff {s t : ℝ} (hs : 0 < s) {x : ℝ≥0∞} :
    ENNReal.ofReal (t * s) ≤ x ↔
      ENNReal.ofReal t ≤ ENNReal.ofReal s⁻¹ * x := by
  constructor
  · intro h
    calc
      ENNReal.ofReal t = ENNReal.ofReal s⁻¹ * ENNReal.ofReal (t * s) :=
        (amplify_scale_ofReal s t hs).symm
      _ ≤ ENNReal.ofReal s⁻¹ * x := by gcongr
  · exact unscale_lower hs

theorem amplify_scale_upper_iff {s t : ℝ} (hs : 0 < s) {x : ℝ≥0∞} :
    x ≤ ENNReal.ofReal (t * s) ↔
      ENNReal.ofReal s⁻¹ * x ≤ ENNReal.ofReal t := by
  constructor
  · intro h
    calc
      ENNReal.ofReal s⁻¹ * x ≤ ENNReal.ofReal s⁻¹ * ENNReal.ofReal (t * s) := by gcongr
      _ = ENNReal.ofReal t := amplify_scale_ofReal s t hs
  · exact unscale_le hs

theorem amplify_scale_lower_strict_iff {s t : ℝ} (hs : 0 < s) {x : ℝ≥0∞} :
    ENNReal.ofReal (t * s) < x ↔
      ENNReal.ofReal t < ENNReal.ofReal s⁻¹ * x := by
  constructor
  · intro h
    have hpos : ENNReal.ofReal s⁻¹ ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr hs)).ne'
    have hfin : ENNReal.ofReal s⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
    calc
      ENNReal.ofReal t = ENNReal.ofReal s⁻¹ * ENNReal.ofReal (t * s) :=
        (amplify_scale_ofReal s t hs).symm
      _ < ENNReal.ofReal s⁻¹ * x := by
        simpa only [mul_comm] using ENNReal.mul_lt_mul_left hpos hfin h
  · exact unscale_lower_strict hs

def amplify_normSetDist (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (g : DistRd d) (s : ℝ) (w : Rd d) (V K L : Set (Rd d)) : ℝ≥0∞ :=
  ⨅ u ∈ K, ⨅ v ∈ L, normInt ξ Q D g s w V u v

theorem amplify_normSetDist_eq (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (g : DistRd d) {s : ℝ} (hs : 0 < s) (w : Rd d) (V K L : Set (Rd d)) :
    amplify_normSetDist ξ Q D g s w V K L =
      ENNReal.ofReal ((sNorm ξ Q g s w)⁻¹) * setDistIn (D g) V K L := by
  unfold amplify_normSetDist normInt setDistIn
  simp only [ENNReal.mul_iInf_of_ne
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (sNorm_pos ξ Q g hs w))).ne'
    ENNReal.ofReal_ne_top]

def amplify_normTrial (D Dt : DistRd d → ContMetric d)
    (ξ Q cs c1 ℓ δ s : ℝ) (w : Rd d) (g : DistRd d) : Prop :=
  let J := ann w (s / 2) (5 * s)
  let O := ann w (3 * s / 4) (3 * s)
  let K := annCl w s (2 * s)
  ENNReal.ofReal (Real.exp (-ξ * δ) * (4 * max 1 cs⁻¹ * ℓ)) <
      amplify_normSetDist ξ Q D g s w J K
        (Metric.sphere w (3 * s / 4) ∪ Metric.sphere w (3 * s)) ∧
    ∃ P : ℝ → Rd d, ContinuousOn P (Icc 0 1) ∧
      (∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ K) ∧
      ENNReal.ofReal (Real.exp (-ξ * δ) * (ℓ / (2 * c1))) ≤
        normInt ξ Q D g s w O (P 0) (P 1) ∧
      curveLengthWith (normInt ξ Q Dt g s w O) P 0 1 ≤
        ENNReal.ofReal (Real.exp (ξ * δ) * ℓ) ∧
      curveLengthWith (normInt ξ Q Dt g s w O) P 0 1 ≤
        ENNReal.ofReal (Real.exp (2 * ξ * δ) * c1) *
          normInt ξ Q D g s w O (P 0) (P 1)

theorem amplify_normTrial_iff
    (D Dt : DistRd d → ContMetric d) (ξ Q cs c1 ℓ δ : ℝ)
    {s : ℝ} (hs : 0 < s) (w : Rd d) (g : DistRd d) :
    g ∈ TrialEvent D Dt ξ Q cs c1 ℓ δ s w ↔
      amplify_normTrial D Dt ξ Q cs c1 ℓ δ s w g := by
  let J := ann w (s / 2) (5 * s)
  let O := ann w (3 * s / 4) (3 * s)
  let K := annCl w s (2 * s)
  let norm := sNorm ξ Q g s w
  have hnorm : 0 < norm := sNorm_pos ξ Q g hs w
  have hKO : K ⊆ O := by
    intro x hx
    dsimp [K, O, ann, annCl] at hx ⊢
    constructor <;> linarith
  have hdist := amplify_normSetDist_eq ξ Q D g hs w J K
    (Metric.sphere w (3 * s / 4) ∪ Metric.sphere w (3 * s))
  change
    (ENNReal.ofReal (Real.exp (-ξ * δ) * (4 * max 1 cs⁻¹ * ℓ) * norm) <
        setDistIn (D g) J K (Metric.sphere w (3 * s / 4) ∪ Metric.sphere w (3 * s)) ∧
      ∃ P : ℝ → Rd d, ContinuousOn P (Icc 0 1) ∧
        (∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ K) ∧
        ENNReal.ofReal (Real.exp (-ξ * δ) * (ℓ / (2 * c1)) * norm) ≤
          (D g).internal O (P 0) (P 1) ∧
        (Dt g).len P 0 1 ≤ ENNReal.ofReal (Real.exp (ξ * δ) * ℓ * norm) ∧
        (Dt g).len P 0 1 ≤ ENNReal.ofReal (Real.exp (2 * ξ * δ) * c1) *
          (D g).internal O (P 0) (P 1)) ↔
    (ENNReal.ofReal (Real.exp (-ξ * δ) * (4 * max 1 cs⁻¹ * ℓ)) <
        amplify_normSetDist ξ Q D g s w J K
          (Metric.sphere w (3 * s / 4) ∪ Metric.sphere w (3 * s)) ∧
      ∃ P : ℝ → Rd d, ContinuousOn P (Icc 0 1) ∧
        (∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ K) ∧
        ENNReal.ofReal (Real.exp (-ξ * δ) * (ℓ / (2 * c1))) ≤
          normInt ξ Q D g s w O (P 0) (P 1) ∧
        curveLengthWith (normInt ξ Q Dt g s w O) P 0 1 ≤
          ENNReal.ofReal (Real.exp (ξ * δ) * ℓ) ∧
        curveLengthWith (normInt ξ Q Dt g s w O) P 0 1 ≤
          ENNReal.ofReal (Real.exp (2 * ξ * δ) * c1) *
            normInt ξ Q D g s w O (P 0) (P 1))
  rw [hdist]
  simp only [amplify_scale_lower_strict_iff hnorm]
  constructor
  · rintro ⟨hc, P, hPc, hPK, hlow, hhigh, hratio⟩
    have hPO : MapsTo P (Icc 0 1) O := fun t ht => hKO (hPK t ht)
    have hlen : curveLengthWith (normInt ξ Q Dt g s w O) P 0 1 =
        ENNReal.ofReal norm⁻¹ * (Dt g).len P 0 1 := by
      unfold normInt
      rw [curveLengthWith_const_mul, (Dt g).curveLengthWith_internal hPc hPO]
    refine ⟨hc, P, hPc, hPK, ?_, ?_, ?_⟩
    · exact (amplify_scale_lower_iff hnorm).1 hlow
    · rw [hlen]
      exact (amplify_scale_upper_iff hnorm).1 hhigh
    · rw [hlen, normInt]
      calc
        ENNReal.ofReal norm⁻¹ * (Dt g).len P 0 1 ≤
            ENNReal.ofReal norm⁻¹ * (ENNReal.ofReal (Real.exp (2 * ξ * δ) * c1) *
              (D g).internal O (P 0) (P 1)) := by gcongr
        _ = _ := by ac_rfl
  · rintro ⟨hc, P, hPc, hPK, hlow, hhigh, hratio⟩
    have hPO : MapsTo P (Icc 0 1) O := fun t ht => hKO (hPK t ht)
    have hlen : curveLengthWith (normInt ξ Q Dt g s w O) P 0 1 =
        ENNReal.ofReal norm⁻¹ * (Dt g).len P 0 1 := by
      unfold normInt
      rw [curveLengthWith_const_mul, (Dt g).curveLengthWith_internal hPc hPO]
    refine ⟨hc, P, hPc, hPK, ?_, ?_, ?_⟩
    · exact (amplify_scale_lower_iff hnorm).2 hlow
    · exact (amplify_scale_upper_iff hnorm).2 (hlen ▸ hhigh)
    · have hs0 : ENNReal.ofReal norm⁻¹ ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (inv_pos.mpr hnorm)).ne'
      have hsT : ENNReal.ofReal norm⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
      apply (ENNReal.mul_le_mul_iff_right hs0 hsT).1
      simpa only [hlen, normInt, mul_left_comm] using hratio

theorem amplify_trial_saturated
    (D Dt : DistRd d → ContMetric d) (ξ Q cs c1 ℓ δ : ℝ)
    {s : ℝ} (hs : 0 < s) (w : Rd d) (g₁ g₂ : DistRd d)
    (hDJ : ∀ u ∈ ann w (s / 2) (5 * s), ∀ v ∈ ann w (s / 2) (5 * s),
      normInt ξ Q D g₁ s w (ann w (s / 2) (5 * s)) u v =
        normInt ξ Q D g₂ s w (ann w (s / 2) (5 * s)) u v)
    (hDO : ∀ u ∈ ann w (3 * s / 4) (3 * s), ∀ v ∈ ann w (3 * s / 4) (3 * s),
      normInt ξ Q D g₁ s w (ann w (3 * s / 4) (3 * s)) u v =
        normInt ξ Q D g₂ s w (ann w (3 * s / 4) (3 * s)) u v)
    (hDtO : ∀ u ∈ ann w (3 * s / 4) (3 * s), ∀ v ∈ ann w (3 * s / 4) (3 * s),
      normInt ξ Q Dt g₁ s w (ann w (3 * s / 4) (3 * s)) u v =
        normInt ξ Q Dt g₂ s w (ann w (3 * s / 4) (3 * s)) u v)
    (hmem : g₁ ∈ TrialEvent D Dt ξ Q cs c1 ℓ δ s w) :
    g₂ ∈ TrialEvent D Dt ξ Q cs c1 ℓ δ s w := by
  have eJ := normInt_eq_all_of_eq_on D ξ Q hs w (ann w (s / 2) (5 * s))
    g₁ g₂ hDJ
  have eO := normInt_eq_all_of_eq_on D ξ Q hs w (ann w (3 * s / 4) (3 * s))
    g₁ g₂ hDO
  have eDtO := normInt_eq_all_of_eq_on Dt ξ Q hs w (ann w (3 * s / 4) (3 * s))
    g₁ g₂ hDtO
  rw [amplify_normTrial_iff D Dt ξ Q cs c1 ℓ δ hs w] at hmem ⊢
  unfold amplify_normTrial at hmem ⊢
  simp only [amplify_normSetDist, eJ, eO, eDtO] at hmem ⊢
  exact hmem

/-- Shell locality of the trial for a whole-space LGF. The fine-field consumer
needs the `IsLGFPlusCont` extension proved separately. -/
theorem amplify_aeEventIn_trialEvent_lgf
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hd : 2 ≤ d) (cs c1 ℓ δ : ℝ) {s : ℝ} (hs : 0 < s) (w : Rd d) :
    AEEventIn P (fieldSigma0 h (ann w (s / 2) (5 * s)))
      (h ⁻¹' TrialEvent D Dt ξ Q cs c1 ℓ δ s w) := by
  have hmap := hh.map_id
  have hE : NullMeasurableSet
      (TrialEvent D Dt ξ Q cs c1 ℓ δ s w) (P.map h) :=
    amplify_nullMeasurableSet_trialEvent (P.map h) id hmap.isLGFPlusCont
      hD hDt cs c1 ℓ δ s w
  refine aeEventIn_of_normInternal_shell P h hh hD hDt hd w hs
    (TrialEvent D Dt ξ Q cs c1 ℓ δ s w) hE ?_
  intro g₁ g₂ _ _ _ _ hDJ _ hDO hDtO hmem
  exact amplify_trial_saturated D Dt ξ Q cs c1 ℓ δ hs w g₁ g₂
    hDJ hDO hDtO hmem

end HigherDimLQGMetric
