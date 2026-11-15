/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NdClockL

/-!
# F2b′'s canonical driver below the clock, read from the completed line filtration

Packet PROVE-AUX61-NOJUMP (round 21, D34, components B–D). SB2(1)'s `read` field for F2b′: below the clock at `t`,
the canonical driver `segDrv` of the relative stage curve is measurable for the completed line filtration at `t`
(**`measurable_segDrv_line`**). Deterministic part:

* `segDrv_congr_prefix`: the canonical driver at capacity `s` only sees the prefix images at capacities `≤ s`;
* `prefix_eq`, `exists_Btime`: the prefix image at capacity `s' <` clock at `t` is the image of the canonical values on
  `[0, T]` for a B-time `T < min t L` of capacity `s'`;
* **`segDrv_canon_congr`**: hence it only sees the canonical values before `min t L`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nd

open Restart Exist Exist.Staged Exist.StagedLaw Lv Ms Mf WalkSide LocalSets Sec7.PocketTraversal Sec7.Lemma71C Lk
  LuM Nc Dv

/-- **The canonical driver at capacity `s` only sees the prefix images at capacities `≤ s`.** -/
theorem segDrv_congr_prefix {γ γ' : ℝ → ℂ} {s : ℝ}
    (h : ∀ s' ≤ s, γ '' Icc 0 (capInv γ s') = γ' '' Icc 0 (capInv γ' s')) : segDrv γ s = segDrv γ' s := by
  have hG : ∀ s' ≤ s, segG γ s' = segG γ' s' := fun s' hs' => by
    funext z; unfold segG; rw [h s' hs']
  unfold segDrv segQuot
  congr 1
  funext N
  congr 1
  funext k
  rw [hG s le_rfl, hG (s - 1 / ((k : ℝ) + 1)) (by linarith [show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity])]

variable {L : ℝ≥0∞}

theorem uOf_rTime (hL : L ≠ 0) {v : ℝ} (hv : 0 ≤ v) : uOf L (rTime L v) = v := by
  have hb : BeforeL L (rTime L v) := by
    refine ⟨rTime_nonneg hL hv, ?_⟩
    by_cases h : L = ⊤
    · exact Or.inl h
    · right; unfold rTime; rw [if_neg h]; exact clockOf_lt (ENNReal.toReal_pos hL h) hv
  exact (strictMonoOn_rTime hL).injOn (mem_Ici.2 (uOf_nonneg hb)) (mem_Ici.2 hv) (rTime_uOf hb)

theorem beforeL_of_toNNReal_lt {T : ℝ} (hT0 : 0 ≤ T) (hT : ((T.toNNReal : ℝ≥0) : ℝ≥0∞) < L) : BeforeL L T := by
  have := beforeL_of_lt hT
  rwa [Real.coe_toNNReal _ hT0] at this

variable {X : Set ℂ} {x₀ : ℝ} {p : ℝ≥0 → ℂ}

/-- The prefix image at capacity `s'` is the image of the canonical values up to a B-time of capacity `s'`. -/
theorem prefix_eq (hd : IsDrivenCurve (canonCurve X x₀ p L)) (hL : L ≠ 0) {T : ℝ} (hT : BeforeL L T) {s' : ℝ}
    (hTc : capClock (fun r : ℝ => canonVal X x₀ p L r.toNNReal) T = s') :
    canonCurve X x₀ p L '' Icc 0 (capInv (canonCurve X x₀ p L) s') = canonVal X x₀ p L '' Icc 0 T.toNNReal := by
  rw [← hTc, capClock_liftR_canonVal hL hT, hd.capInv_eq (uOf_nonneg hT), image_canonCurve_Icc hL (uOf_nonneg hT),
    cTime_uOf hT]

/-- **A B-time of capacity `s'` below the clock at `t`**, before `min t L`. -/
theorem exists_Btime (hd : IsDrivenCurve (canonCurve X x₀ p L)) (hL : L ≠ 0) {s' : ℝ} (hs' : 0 ≤ s') (t : ℝ≥0)
    (hlt : ENNReal.ofReal s' < Vc.clockOf (canonVal X x₀ p L) 0 L t) :
    ∃ T : ℝ, BeforeL L T ∧ ((T.toNNReal : ℝ≥0) : ℝ≥0∞) < min (t : ℝ≥0∞) L ∧
      capClock (fun r : ℝ => canonVal X x₀ p L r.toNNReal) T = s' := by
  have hcl := clockOf_canonVal hd hL t
  have hlife : ENNReal.ofReal s' < capLife (canonCurve X x₀ p L) := by
    refine lt_of_lt_of_le hlt ?_
    rw [hcl]
    split_ifs with ht
    · exact (hd.ofReal_capClock_lt (uOf_nonneg (beforeL_of_lt ht))).le
    · exact le_rfl
  obtain ⟨hv0, hv⟩ := hd.capInv_spec hs' hlife
  set v := capInv (canonCurve X x₀ p L) s' with hvdef
  have hTb : BeforeL L (rTime L v) := by
    refine ⟨rTime_nonneg hL hv0, ?_⟩
    by_cases h : L = ⊤
    · exact Or.inl h
    · right; unfold rTime; rw [if_neg h]; exact clockOf_lt (ENNReal.toReal_pos hL h) hv0
  refine ⟨rTime L v, hTb, ?_, ?_⟩
  · have hcT : (rTime L v).toNNReal = cTime L v := rfl
    rw [hcT]
    refine lt_min ?_ ?_
    · by_cases ht : (t : ℝ≥0∞) < L
      · rw [hcl, if_pos ht] at hlt
        have h1 : s' < capClock (canonCurve X x₀ p L) (uOf L t) :=
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs').1 hlt
        rw [← hv] at h1
        have h2 : v < uOf L t := (hd.strictMonoOn_capClock.lt_iff_lt (mem_Ici.2 hv0)
          (mem_Ici.2 (uOf_nonneg (beforeL_of_lt ht)))).1 h1
        have h3 : rTime L v < rTime L (uOf L t) :=
          strictMonoOn_rTime hL (mem_Ici.2 hv0) (mem_Ici.2 (uOf_nonneg (beforeL_of_lt ht))) h2
        rw [rTime_uOf (beforeL_of_lt ht)] at h3
        have : (cTime L v : ℝ) < t := by rw [coe_cTime hL hv0]; exact h3
        exact_mod_cast this
      · rw [not_lt] at ht
        refine lt_of_lt_of_le ?_ ht
        rcases hTb.2 with h | h
        · rw [h]; exact ENNReal.coe_lt_top
        · have hfin : L ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top ht
          rw [← ENNReal.ofReal_coe_nnreal, coe_cTime hL hv0]
          exact (ENNReal.ofReal_lt_iff_lt_toReal (rTime_nonneg hL hv0) hfin).2 h
    · by_cases hfin : L = ⊤
      · rw [hfin]; exact ENNReal.coe_lt_top
      · have h := hTb.2.resolve_left hfin
        rw [← ENNReal.ofReal_coe_nnreal, coe_cTime hL hv0]
        exact (ENNReal.ofReal_lt_iff_lt_toReal (rTime_nonneg hL hv0) hfin).2 h
  · rw [capClock_liftR_canonVal hL hTb, uOf_rTime hL hv0, hv]

/-- **Below the clock at `t`, the canonical driver only sees the canonical values before `min t L`.** -/
theorem segDrv_canon_congr {X' : Set ℂ} (hX : fillH X = fillH X') {p' : ℝ≥0 → ℂ} {L' : ℝ≥0∞}
    (hd : IsDrivenCurve (canonCurve X x₀ p L)) (hd' : IsDrivenCurve (canonCurve X' x₀ p' L')) (hL : L ≠ 0)
    (t : ℝ≥0) (hmin : min (t : ℝ≥0∞) L = min (t : ℝ≥0∞) L')
    (hp : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ min (t : ℝ≥0∞) L → p s = p' s) {r : ℝ}
    (hr : ENNReal.ofReal r < Vc.clockOf (canonVal X x₀ p L) 0 L t) :
    segDrv (canonCurve X x₀ p L) r = segDrv (canonCurve X' x₀ p' L') r := by
  have hloc : ∀ s : ℝ≥0, (s : ℝ≥0∞) < min (t : ℝ≥0∞) L → canonVal X x₀ p L s = canonVal X' x₀ p' L' s :=
    fun s hs => canonVal_congr_lt hX x₀ (min_le_right _ _) (hmin ▸ min_le_right _ _) hp hs
  refine segDrv_congr_prefix fun s' hs' => ?_
  rcases le_or_gt s' 0 with h0 | h0
  · rw [hd.capInv_of_nonpos h0, hd'.capInv_of_nonpos h0, Icc_self, image_singleton, image_singleton, hd.zero,
      hd'.zero]
  · have hlt' : ENNReal.ofReal s' < Vc.clockOf (canonVal X x₀ p L) 0 L t :=
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hs') hr
    obtain ⟨T, hT, hTlt, hTc⟩ := exists_Btime hd hL h0.le t hlt'
    have hT' : BeforeL L' T := beforeL_of_toNNReal_lt hT.1 (lt_of_lt_of_le (hmin ▸ hTlt) (min_le_right _ _))
    have heq : ∀ q : ℝ≥0, q ≤ T.toNNReal → canonVal X x₀ p L q = canonVal X' x₀ p' L' q := fun q hq =>
      hloc q (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hq) hTlt)
    have hTc' : capClock (fun r : ℝ => canonVal X' x₀ p' L' r.toNNReal) T = s' := by
      rw [← hTc]; exact (Vc.capClock_congr heq).symm
    rw [prefix_eq hd hL hT hTc, prefix_eq hd' (fun h => by rw [h] at hT'; exact absurd hT'.2 (by simp; linarith
      [hT.1])) hT' hTc']
    exact image_congr fun q hq => heq q hq.2


section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}

theorem StageObj.a_le_capLife (S : StageObj P κ b jumps E u l k ℓ) {ω : Ω} (hω : ω ∈ S.Eg) (t : ℝ≥0) :
    S.a t ω ≤ capLife (S.ρM ω) := by
  rw [S.a_eq hω]
  split_ifs with ht
  · exact ((S.driven_ρM ω).ofReal_capClock_lt (uOf_nonneg (beforeL_of_lt ht))).le
  · exact le_rfl

/-- **The canonical driver below the clock at `t` is measurable for the completed line filtration at `t`.** -/
theorem measurable_segDrv_line (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (S : StageObj P κ b jumps E u l k ℓ) (t r : ℝ≥0) :
    Measurable[mΩ ⊓ aeSigma (lineSigmaT κ b jumps E u l k ℓ t) P]
      ((S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω}).indicator fun ω => segDrv (S.ρM ω) r) := by
  classical
  have hm := fun s hs => S.measurable_ρM hb s hs
  have e : ((S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω}).indicator fun ω => segDrv (S.ρM ω) r) =
      (S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω}).indicator (Supp8.GB6.CoordB.drivenDriver S.ρM r) := by
    funext ω
    by_cases hω : ω ∈ S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω}
    · rw [indicator_of_mem hω, indicator_of_mem hω,
        Supp8.GB6.CoordB.drivenDriver_eq (lt_of_lt_of_le hω.2 (StageObj.a_le_capLife S hω.1 t))]
      rfl
    · rw [indicator_of_notMem hω, indicator_of_notMem hω]
  have hmeas : Measurable ((S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω}).indicator fun ω => segDrv (S.ρM ω) r) := by
    rw [e]
    exact (Supp8.GB6.CoordB.measurable_drivenDriver S.driven_ρM hm r).indicator
      (S.hEg.1.inter (measurableSet_lt measurable_const (S.measurable_a hb t)))
  refine measurable_inf_aeSigma_of_frozen (lineSigmaT_le (u := u) (k := k) hb hE hER hlθ hℓ hwℓ t) hmeas ?_
  filter_upwards [ae_ae_frozenData hb hE hER hlθ hℓ hwℓ S t] with ω₀ hfr
  filter_upwards [hfr] with ω ⟨e1, e2, e3, e4, e5⟩
  by_cases hω₀ : ω₀ ∈ S.Eg
  · have hω : ω ∈ S.Eg := e1.2 hω₀
    have ha := StageObj.a_eq_of_frozen hℓ hwℓ S hω hω₀ t e2 e3 e4 e5
    by_cases hr : (r : ℝ≥0∞) < S.a t ω₀
    · have hm1 : ω ∈ S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω} := ⟨hω, by rw [mem_ofPred_eq, ha]; exact hr⟩
      have hm0 : ω₀ ∈ S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω} := ⟨hω₀, hr⟩
      rw [indicator_of_mem hm1, indicator_of_mem hm0, S.ρM_eq hω, S.ρM_eq hω₀]
      have G := S.good ω hω
      have G₀ := S.good ω₀ hω₀
      obtain ⟨-, hmin, hp⟩ := piece_eq_of_frozen hℓ hwℓ G G₀ t e4 e5
      have hd := G.driven
      unfold bRel at hd ⊢
      rw [e3] at hd ⊢
      refine segDrv_canon_congr (by rw [e2]) hd G₀.driven G.pos t hmin hp ?_
      rw [ENNReal.ofReal_coe_nnreal]
      have := hm1.2
      rw [mem_ofPred_eq, S.a_of_mem hω] at this
      unfold bLift at this
      rwa [e3] at this
    · have hm1 : ω ∉ S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω} := fun h' => hr (by rw [← ha]; exact h'.2)
      have hm0 : ω₀ ∉ S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω} := fun h' => hr h'.2
      rw [indicator_of_notMem hm1, indicator_of_notMem hm0]
  · have hm1 : ω ∉ S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω} := fun h' => hω₀ (e1.1 h'.1)
    have hm0 : ω₀ ∉ S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω} := fun h' => hω₀ h'.1
    rw [indicator_of_notMem hm1, indicator_of_notMem hm0]

end

end InteractingSLE.Theorem14.SB.Nd
