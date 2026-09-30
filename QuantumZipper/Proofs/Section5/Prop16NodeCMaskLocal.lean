import QuantumZipper.Proofs.Section5.Prop16NodeCMaskSplit
import QuantumZipper.Proofs.Section5.Prop16LocGoodBasic
import QuantumZipper.Proofs.GFF.K3.MixedRiesz
import QuantumZipper.Proofs.GFF.CircleMeanValue

/-!
# Proposition 1.6, node C′ (masked): the masked coordinates only read admissible circles

Deterministic locality for `Prop16FixedLawMaskStmt` (step (b) of task P16-NODEC-MASK):

* `palmCanonMask_congr`: if two fields agree on the dyadic folded circles inside an open `W ⊇ D ∪
  (a,b)` (`Prop16Area.G.CircAgree`), their masked canonical zoom coordinates at `t` agree. The
  local area measure on `D − t` only reads circles inside `D` (`isVagueLimitOn_of_circAgree` and
  uniqueness of local vague limits, `LocalRule.qAreaMeasureOn_eq`), so the scales agree; a kept
  coordinate reads the field on a measure carried by `t + closedBall 0 (s · reach) ∩ Hbar`, which
  lies in `D ∪ (a,b)` because `s · reach < gap(t)` (`PalmKeep`).
* `admCoords`: the dyadic circle coordinates of a field with the non-admissible ones (for the
  mixed GFF, `IsAdmissibleDual D (mixedSpace D S)`) replaced by `0`; and
  `circAgree_reconstruct_admCoords`: every dyadic folded circle inside the open set `W` with
  `W ∩ Hbar = D ∪ (a,b)` is admissible (M4, `isAdmissibleDual_foldedCircle_of_local`, with a
  radius margin from compactness), so the reconstruction of `admCoords x` agrees with `x` there.

Source: Sheffield, arXiv:1012.4797, proof of Prop. 1.6 (p. 25): the zoom only reads the field
in `D` near the boundary point. The locality bookkeeping is an own elementary argument (built on
the locality lemmas of `Prop16LocalAgree.lean` / `Prop16LocalRule.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open TV Factorization

/-! ## 1. Locality of the masked coordinates -/

theorem ae_fc_mem_closedBall_zero_nc (d : ℂ) (r : ℝ) :
    ∀ᵐ u ∂foldedCircle d r, u ∈ closedBall (0 : ℂ) (‖d‖ + |r|) ∩ Hbar := by
  have h1 : ∀ᵐ u ∂foldedCircle d r, u ∈ closedBall (0 : ℂ) (‖d‖ + |r|) := by
    unfold foldedCircle
    refine (ae_map_iff measurable_foldH.aemeasurable measurableSet_closedBall).2 ?_
    filter_upwards [CircleMV.ae_circleUnif d r] with u hu
    show dist (foldH u) 0 ≤ _
    rw [dist_zero_right, CircleFubini.norm_foldH']
    calc ‖u‖ = ‖d + (u - d)‖ := by ring_nf
      _ ≤ ‖d‖ + ‖u - d‖ := norm_add_le _ _
      _ = ‖d‖ + |r| := by rw [hu]
  filter_upwards [h1, RegClosure.fc_ae_mem_Hbar d r] with u hu1 hu2
  exact ⟨hu1, hu2⟩

theorem circAgree_symm_nc {W : Set ℂ} {x x' : FieldSample} (h : Prop16Area.G.CircAgree W x x') :
    Prop16Area.G.CircAgree W x' x := fun n k z hz hW => (h n k z hz hW).symm

/-- Local area measures only read the circles inside `W`. -/
theorem qAreaMeasureOn_eq_of_circAgree {γ : ℝ} {W U : Set ℂ} (hWo : IsOpen W) {y y' : FieldSample}
    (h : Prop16Area.G.CircAgree W y y') (hUo : IsOpen U) (hUH : U ⊆ H) (hUW : U ⊆ W) :
    qAreaMeasureOn γ y U = qAreaMeasureOn γ y' U := by
  by_cases hg : ∃ m, IsVagueLimitOn U (areaApprox γ y') m
  · obtain ⟨m, hm⟩ := hg
    rw [LocalRule.qAreaMeasureOn_eq hUo hm,
      LocalRule.qAreaMeasureOn_eq hUo (Prop16Area.G.isVagueLimitOn_of_circAgree hWo h hUH hUW hm)]
  · have hg' : ¬ ∃ m, IsVagueLimitOn U (areaApprox γ y) m := fun ⟨m, hm⟩ =>
      hg ⟨m, Prop16Area.G.isVagueLimitOn_of_circAgree hWo (circAgree_symm_nc h) hUH hUW hm⟩
    rw [Prop16Area.Meas.qAreaMeasureOn_of_not hg, Prop16Area.Meas.qAreaMeasureOn_of_not hg']

theorem scaleParamOn_eq_of_circAgree {γ : ℝ} {W U : Set ℂ} (hWo : IsOpen W) {y y' : FieldSample}
    (h : Prop16Area.G.CircAgree W y y') (hUo : IsOpen U) (hUH : U ⊆ H) (hUW : U ⊆ W) :
    scaleParamOn γ y U = scaleParamOn γ y' U := by
  unfold scaleParamOn
  rw [qAreaMeasureOn_eq_of_circAgree hWo h hUo hUH hUW]

/-- Agreement near the zoom point is inherited by the unperturbed zoomed fields. -/
theorem circAgree_zoomFree_nc {W : Set ℂ} (hWo : IsOpen W) {x x' : FieldSample}
    (h : Prop16Area.G.CircAgree W x x') (γ C k t : ℝ) :
    Prop16Area.G.CircAgree ((fun z => z + (t : ℂ)) ⁻¹' W) (addConst (zoomField γ C x t) k)
      (addConst (zoomField γ C x' t) k) :=
  (Prop16Area.G.fcAgree_addConst (Prop16Area.G.fcAgree_addConst
    (Prop16Area.G.fcAgree_translate hWo h t) (C / γ)) k).circAgree

theorem zoomDomain_subset_H {D : Set ℂ} (hDH : D ⊆ H) (t : ℝ) : zoomDomain D t ⊆ H :=
  fun z hz => by
    have : 0 < (z + (t : ℂ)).im := hDH hz
    show 0 < z.im
    simpa using this

/-- **Locality of the masked zoom coordinates.** -/
theorem palmCanonMask_congr {γ C : ℝ} {D : Set ℂ} {a b : ℝ} {h0 : ℂ → ℝ} {W : Set ℂ}
    (hWo : IsOpen W) (hDo : IsOpen D) (hDH : D ⊆ H) (hVW : D ∪ realSet (Ioo a b) ⊆ W)
    {Ω Ω' : Type} (X : Ω → FieldSample) (X' : Ω' → FieldSample) (ω : Ω) (ω' : Ω') (t : ℝ)
    (h : Prop16Area.G.CircAgree W (X ω) (X' ω')) :
    palmCanonMask γ C D a b h0 X (ω, t) = palmCanonMask γ C D a b h0 X' (ω', t) := by
  classical
  set Wt := (fun z => z + (t : ℂ)) ⁻¹' W with hWt
  have hWto : IsOpen Wt := hWo.preimage (continuous_id.add continuous_const)
  have hy : Prop16Area.G.CircAgree Wt (zoomFree γ C h0 X (ω, t)) (zoomFree γ C h0 X' (ω', t)) :=
    circAgree_zoomFree_nc hWo h γ C (h0 t) t
  have hUo : IsOpen (zoomDomain D t) := hDo.preimage (continuous_id.add continuous_const)
  have hUW : zoomDomain D t ⊆ Wt := fun z hz => hVW (Or.inl hz)
  have hs : palmScale γ C D h0 X (ω, t) = palmScale γ C D h0 X' (ω', t) :=
    scaleParamOn_eq_of_circAgree hWto hy hUo (zoomDomain_subset_H hDH t) hUW
  have e : ∀ {Ω₁ : Type} (X₁ : Ω₁ → FieldSample) (ω₁ : Ω₁) (i : ℕ),
      palmCanonCoords γ C D h0 X₁ (ω₁, t) i =
        evalReg (zoomFree γ C h0 X₁ (ω₁, t))
          ((foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)).map
            fun z => ((palmScale γ C D h0 X₁ (ω₁, t) : ℝ) : ℂ) * z) +
        Qc γ * ∫ z, Real.log ‖deriv (fun z => ((palmScale γ C D h0 X₁ (ω₁, t) : ℝ) : ℂ) * z) z‖
          ∂(foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)) :=
    fun _ _ _ => rfl
  have hm : ∀ {Ω₁ : Type} (X₁ : Ω₁ → FieldSample) (ω₁ : Ω₁),
      palmCanonMask γ C D a b h0 X₁ (ω₁, t) = maskCoords D a b (palmScale γ C D h0 X₁ (ω₁, t)) t
        (palmCanonCoords γ C D h0 X₁ (ω₁, t)) := fun _ _ => rfl
  rw [hm X, hm X', hs]
  funext i
  simp only [maskCoords]
  split_ifs with hk
  · set s := palmScale γ C D h0 X' (ω', t) with hsdef
    obtain ⟨hs0, hsg⟩ := hk
    have hr0 : 0 ≤ coordReach i := add_nonneg (norm_nonneg _) (radius_pos _).le
    have hsr : s * coordReach i < palmGap D a b t := by
      have : 0 ≤ s * coordReach i := mul_nonneg hs0.le hr0
      linarith
    rw [e X, e X', hs]
    set K := closedBall (0 : ℂ) (s * coordReach i) ∩ Hbar with hK
    have hKW : K ⊆ Wt := by
      rintro u ⟨hu1, hu2⟩
      show u + (t : ℂ) ∈ W
      refine hVW ?_
      by_contra hno
      have hmem : u + (t : ℂ) ∈ palmOutside D a b := by
        refine ⟨?_, hno⟩
        show (0 : ℝ) ≤ (u + (t : ℂ)).im
        have : (0 : ℝ) ≤ u.im := hu2
        simpa using this
      have h1 := infDist_le_dist_of_mem (x := (t : ℂ)) hmem
      have h2 : dist (t : ℂ) (u + (t : ℂ)) = ‖u‖ := by
        rw [dist_eq_norm]; simp [norm_neg]
      rw [mem_closedBall, dist_zero_right] at hu1
      have : palmGap D a b t ≤ s * coordReach i := by
        unfold palmGap; linarith
      linarith
    have hae : ∀ᵐ u ∂((foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)).map
        fun z => ((s : ℝ) : ℂ) * z), u ∈ K ∩ Hbar := by
      refine (ae_map_iff (by fun_prop : Measurable fun z : ℂ => (s : ℂ) * z).aemeasurable
          ((measurableSet_closedBall.inter isClosed_Hbar.measurableSet).inter
            isClosed_Hbar.measurableSet)).2 ?_
      filter_upwards [ae_fc_mem_closedBall_zero_nc (dyadicIndex i).1 (radius (dyadicIndex i).2)]
        with u hu
      have hH : (s : ℂ) * u ∈ Hbar := RegClosure.mapsTo_mul_pos hs0 hu.2
      refine ⟨⟨?_, hH⟩, hH⟩
      have := hu.1
      rw [mem_closedBall, dist_zero_right] at this ⊢
      rw [abs_of_pos (radius_pos _)] at this
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      exact mul_le_mul_of_nonneg_left this hs0.le
    rw [Prop16Area.G.evalReg_eq_of_circAgree hWto hy
      ((isCompact_closedBall _ _).inter_right isClosed_Hbar) hKW hae]
  · rfl

/-! ## 2. Admissible coordinates -/

/-- The `i`-th dyadic folded circle is admissible for the mixed GFF on `D`, free on `S`. -/
def AdmIdx (D S : Set ℂ) (i : ℕ) : Prop :=
  IsAdmissibleDual D (mixedSpace D S) (foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2))

open Classical in
/-- The dyadic circle coordinates of `x`, with the non-admissible ones replaced by `0`. -/
def admCoords (D S : Set ℂ) (x : FieldSample) : ℕ → ℝ :=
  fun i => if AdmIdx D S i then coords x i else 0

/-- A compact margin: a closed half-ball inside an open set is inside it with a larger radius. -/
theorem exists_closedBall_margin {W : Set ℂ} (hWo : IsOpen W) {c : ℂ} (hc : c ∈ Hbar) {r : ℝ}
    (hr : 0 ≤ r) (hW : closedBall c r ∩ Hbar ⊆ W) :
    ∃ R > r, closedBall c R ∩ Hbar ⊆ W := by
  obtain ⟨δ, hδ, hδW⟩ := ((isCompact_closedBall c r).inter_right isClosed_Hbar).exists_cthickening_subset_open
    hWo hW
  refine ⟨r + δ, by linarith, fun p hp => hδW ?_⟩
  obtain ⟨hp1, hp2⟩ := hp
  rw [mem_closedBall, dist_eq_norm] at hp1
  by_cases hpr : ‖p - c‖ ≤ r
  · exact self_subset_cthickening _ ⟨by rwa [mem_closedBall, dist_eq_norm], hp2⟩
  · push_neg at hpr
    have hn : 0 < ‖p - c‖ := lt_of_le_of_lt hr hpr
    set τ : ℝ := r / ‖p - c‖ with hτ
    have hτ0 : 0 ≤ τ := div_nonneg hr hn.le
    have hτ1 : τ ≤ 1 := (div_le_one hn).2 hpr.le
    set q : ℂ := c + (τ : ℂ) * (p - c) with hq
    have hqK : q ∈ closedBall c r ∩ Hbar := by
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall, dist_eq_norm, hq, add_sub_cancel_left, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg hτ0, hτ, div_mul_cancel₀ _ hn.ne']
      · have e : q.im = (1 - τ) * c.im + τ * p.im := by
          simp only [hq, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.sub_im, Complex.sub_re, zero_mul, add_zero]
          ring
        show 0 ≤ q.im
        rw [e]
        have : (0 : ℝ) ≤ c.im := hc
        have : (0 : ℝ) ≤ p.im := hp2
        have : 0 ≤ 1 - τ := by linarith
        positivity
    refine mem_cthickening_of_dist_le p q δ _ hqK ?_
    have e : p - q = ((1 - τ : ℝ) : ℂ) * (p - c) := by
      rw [hq]; push_cast; ring
    rw [dist_eq_norm, e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith),
      sub_mul, one_mul, hτ, div_mul_cancel₀ _ hn.ne']
    linarith

/-- Every dyadic folded circle inside `W` (`W ∩ Hbar = D ∪ (a,b)`) is admissible. -/
theorem admissible_of_mem_W {D : Set ℂ} {c d a b : ℝ} (hgeo : K3.Prop16Geometry D c d)
    (hca : c ≤ a) (hbd : b ≤ d) {W : Set ℂ} (hWo : IsOpen W)
    (hWV : W ∩ Hbar = D ∪ realSet (Ioo a b)) {z : ℂ} (hz : z ∈ Hbar) {r : ℝ} (hr : 0 < r)
    (hW : closedBall z r ∩ Hbar ⊆ W) :
    IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) (foldedCircle z r) := by
  obtain ⟨hDo, -, hb, hDH, -, hfr, -⟩ := hgeo
  obtain ⟨R0, hR0, hR0W⟩ := exists_closedBall_margin hWo hz hr.le hW
  have hsub : realSet (Ioo a b) ⊆ realSet (Icc c d) := by
    rintro w ⟨u, hu, rfl⟩
    exact ⟨u, ⟨by linarith [hu.1], by linarith [hu.2]⟩, rfl⟩
  have hS : realSet (Icc c d) ⊆ {w : ℂ | w.im = 0} := by
    rintro w ⟨u, -, rfl⟩
    simp
  have hin : closedBall z R0 ∩ Hbar ⊆ D ∪ realSet (Ioo a b) := fun w hw =>
    hWV ▸ ⟨hR0W hw, hw.2⟩
  have hclH : closure D ⊆ Hbar := closure_minimal (hDH.trans H_subset_Hbar) isClosed_Hbar
  have hloc : K3.LocalBall D (realSet (Icc c d)) z R0 := by
    refine ⟨hz, lt_trans hr hR0, hDH, fun w hw => ?_, fun w hw => ?_⟩
    · rcases hin hw with h | h
      · exact subset_closure h
      · have : w ∈ frontier D ∩ {z : ℂ | z.im = 0} := hfr ▸ hsub h
        exact frontier_subset_closure this.1
    · have hwH : w ∈ Hbar := hclH (frontier_subset_closure hw.2)
      rcases hin ⟨hw.1, hwH⟩ with h | h
      · exact absurd h (fun h' => by
          rw [hDo.frontier_eq] at hw
          exact hw.2.2 h')
      · exact hsub h
  exact K3.isAdmissibleDual_foldedCircle_of_local hDo hDH hb hS hloc hr hR0

/-- The reconstruction from the admissible coordinates agrees with the field inside `W`. -/
theorem circAgree_reconstruct_admCoords {D : Set ℂ} {c d a b : ℝ}
    (hgeo : K3.Prop16Geometry D c d) (hca : c ≤ a) (hbd : b ≤ d) {W : Set ℂ} (hWo : IsOpen W)
    (hWV : W ∩ Hbar = D ∪ realSet (Ioo a b)) (x : FieldSample) :
    Prop16Area.G.CircAgree W x (reconstruct (admCoords D (realSet (Icc c d)) x)) := by
  classical
  intro n k z hz hW
  have hex : ∃ i, foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2) =
      foldedCircle (dyadicRoundC n z) (radius k) := by
    obtain ⟨i, hi⟩ := dyadicIndex_surj n k z
    exact ⟨i, by rw [hi]⟩
  have hadm := admissible_of_mem_W hgeo hca hbd hWo hWV (CircleCont.dyadicRoundC_mem_Hbar hz n)
    (radius_pos k) hW
  unfold reconstruct
  rw [dif_pos hex]
  have hj := Nat.find_spec hex
  have hA : AdmIdx D (realSet (Icc c d)) (Nat.find hex) := by
    unfold AdmIdx; rw [hj]; exact hadm
  simp only [admCoords, hA, if_true, coords, hj]

end Prop16Asm

end QuantumZipper
