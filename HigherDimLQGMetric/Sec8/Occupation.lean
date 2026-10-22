import HigherDimLQGMetric.Sec8.Geod

/-!
# Occupation length and weighted losses

An infimum-weighted partition contributes only on intervals on which the
weight is strictly positive everywhere. If that positivity forces the path
to lie inside a collector, the whole weighted length is bounded by `occLen`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Filter Topology Metric
open LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- A nonnegative weight at most one which vanishes off a collector has
weighted length bounded by the occupation length of that collector. -/
theorem sec8_weightedLength_le_occLen (D : ContMetric d) (P : ℝ → Rd d)
    (V : Set (Rd d)) (w : D.Space → ℝ)
    (hw1 : ∀ τ ∈ Icc (0 : ℝ) 1, w (D.pt (P τ)) ≤ 1)
    (hwV : ∀ τ ∈ Icc (0 : ℝ) 1, 0 < w (D.pt (P τ)) → P τ ∈ V) :
    weightedLength w (D.pt ∘ P) 0 1 ≤ occLen D P V := by
  classical
  unfold weightedLength
  refine partitionSup_le fun p => ?_
  let term : ℕ → ℝ≥0∞ := fun i =>
    infAlong w (D.pt ∘ P) (p.t i) (p.t (i + 1)) *
      D.len P (p.t i) (p.t (i + 1))
  let S : Finset ℕ := (Finset.range p.n).filter fun i => 0 < term i
  let endpoint : ℕ → ℝ × ℝ := fun i => (p.t i, p.t (i + 1))
  let I : Finset (ℝ × ℝ) := S.image endpoint
  have hSpos (i : ℕ) (hi : i ∈ S) : 0 < term i := (Finset.mem_filter.mp hi).2
  have hSrange (i : ℕ) (hi : i ∈ S) : i < p.n :=
    Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have hSwidth (i : ℕ) (hi : i ∈ S) : p.t i < p.t (i + 1) := by
    have hs := (p.step (hSrange i hi)).2.1
    apply lt_of_le_of_ne hs
    intro heq
    have hzero : term i = 0 := by
      dsimp [term]
      rw [heq, ContMetric.len_def, curveLength_self, mul_zero]
    exact (ne_of_gt (hSpos i hi)) hzero
  have hSinf (i : ℕ) (hi : i ∈ S) :
      0 < infAlong w (D.pt ∘ P) (p.t i) (p.t (i + 1)) := by
    by_contra hnot
    have hz : infAlong w (D.pt ∘ P) (p.t i) (p.t (i + 1)) = 0 :=
      le_antisymm (le_of_not_gt hnot) bot_le
    have : term i = 0 := by simp [term, hz]
    exact (ne_of_gt (hSpos i hi)) this
  have hIinj : Set.InjOn endpoint S := by
    intro i hi j hj heq
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hle : p.t (i + 1) ≤ p.t j :=
        p.le_t (by omega) (hSrange j hj).le
      have hfirst : p.t i = p.t j := congrArg Prod.fst heq
      exact False.elim ((not_le_of_gt (hSwidth i hi)) (hfirst ▸ hle))
    · rfl
    · have hle : p.t (j + 1) ≤ p.t i :=
        p.le_t (by omega) (hSrange i hi).le
      have hfirst : p.t i = p.t j := congrArg Prod.fst heq
      exact False.elim ((not_le_of_gt (hSwidth j hj)) (hfirst.symm ▸ hle))
  have hIpair : (I : Set (ℝ × ℝ)).PairwiseDisjoint
      (fun pair => Ioo pair.1 pair.2) := by
    intro a ha b hb hab
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    have hij : i ≠ j := fun heq => hab (by rw [heq])
    apply Set.disjoint_left.mpr
    intro t hit hjt
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hle : p.t (i + 1) ≤ p.t j :=
        p.le_t (by omega) (hSrange j hj).le
      exact (not_lt_of_ge hle) (hjt.1.trans hit.2)
    · have hle : p.t (j + 1) ≤ p.t i :=
        p.le_t (by omega) (hSrange i hi).le
      exact (not_lt_of_ge hle) (hit.1.trans hjt.2)
  have hIadm : ∀ pair ∈ I, 0 ≤ pair.1 ∧ pair.1 ≤ pair.2 ∧ pair.2 ≤ 1 ∧
      ∀ τ ∈ Icc pair.1 pair.2, P τ ∈ V := by
    intro pair hpair
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hpair
    have hstep := p.step (hSrange i hi)
    refine ⟨hstep.1, hstep.2.1, hstep.2.2, ?_⟩
    intro τ hτ
    have h01 : τ ∈ Icc (0 : ℝ) 1 := ⟨hstep.1.trans hτ.1, hτ.2.trans hstep.2.2⟩
    have hwt : 0 < w (D.pt (P τ)) := by
      have h := (hSinf i hi).trans_le (infAlong_le (P := D.pt ∘ P) hτ)
      exact ENNReal.ofReal_pos.mp h
    exact hwV τ h01 hwt
  have hterm_le_len (i : ℕ) (hi : i ∈ S) :
      term i ≤ D.len P (p.t i) (p.t (i + 1)) := by
    have hstep := p.step (hSrange i hi)
    have hInf : infAlong w (D.pt ∘ P) (p.t i) (p.t (i + 1)) ≤ 1 := by
      calc
        infAlong w (D.pt ∘ P) (p.t i) (p.t (i + 1)) ≤
            ENNReal.ofReal (w (D.pt (P (p.t i)))) := infAlong_le ⟨le_rfl, hstep.2.1⟩
        _ ≤ 1 := by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal
            (hw1 (p.t i) ⟨hstep.1, hstep.2.1.trans hstep.2.2⟩)
    dsimp [term]
    calc
      infAlong w (D.pt ∘ P) (p.t i) (p.t (i + 1)) *
          D.len P (p.t i) (p.t (i + 1)) ≤
        1 * D.len P (p.t i) (p.t (i + 1)) := by gcongr
      _ = D.len P (p.t i) (p.t (i + 1)) := one_mul _
  have hsum : p.sum (fun u v => infAlong w (D.pt ∘ P) u v *
      curveLength (D.pt ∘ P) u v) ≤ ∑ i ∈ S, D.len P (p.t i) (p.t (i + 1)) := by
    change ∑ i ∈ Finset.range p.n, term i ≤ _
    calc
      ∑ i ∈ Finset.range p.n, term i ≤
          ∑ i ∈ Finset.range p.n, if i ∈ S then D.len P (p.t i) (p.t (i + 1)) else 0 := by
            apply Finset.sum_le_sum
            intro i hi
            by_cases his : i ∈ S
            · simp only [his, ↓reduceIte]
              exact hterm_le_len i his
            · simp only [his, ↓reduceIte]
              have hnot : ¬ 0 < term i := by
                intro hpos
                exact his (Finset.mem_filter.mpr ⟨hi, hpos⟩)
              have hz : term i = 0 :=
                le_antisymm (le_of_not_gt hnot) bot_le
              exact hz.le
      _ = ∑ i ∈ S, D.len P (p.t i) (p.t (i + 1)) := by
        have hfilter : (Finset.range p.n).filter (fun i => i ∈ S) = S := by
          ext i
          simp only [Finset.mem_filter]
          constructor
          · exact And.right
          · intro hi
            exact ⟨(Finset.mem_filter.mp hi).1, hi⟩
        rw [Finset.sum_ite]
        simp only [Finset.sum_const_zero, add_zero, hfilter]
  have hsumI : (∑ i ∈ S, D.len P (p.t i) (p.t (i + 1))) =
      ∑ pair ∈ I, D.len P pair.1 pair.2 := by
    change (∑ i ∈ S, D.len P (endpoint i).1 (endpoint i).2) =
      ∑ pair ∈ S.image endpoint, D.len P pair.1 pair.2
    rw [Finset.sum_image]
    exact fun i hi j hj hij => hIinj hi hj hij
  calc
    p.sum (fun u v => infAlong w (D.pt ∘ P) u v *
      curveLength (D.pt ∘ P) u v) ≤ _ := hsum
    _ = ∑ pair ∈ I, D.len P pair.1 pair.2 := hsumI
    _ ≤ occLen D P V := by
      unfold occLen
      exact le_iSup_of_le I (le_iSup_of_le hIpair (le_iSup_of_le hIadm le_rfl))

/-- Weighted length is additive in two continuous nonnegative weights along
a continuous curve of finite length. -/
theorem sec8_weightedLength_add_weight {X : Type*} [EMetricSpace X]
    (Q : ℝ → X) {a b : ℝ} (hab : a ≤ b)
    (hQ : ContinuousOn Q (Icc a b)) (hL : curveLength Q a b ≠ ⊤)
    (w v : X → ℝ) (hw : Continuous w) (hv : Continuous v)
    (hw0 : ∀ x, 0 ≤ w x) (hv0 : ∀ x, 0 ≤ v x) :
    weightedLength (fun x => w x + v x) Q a b =
      weightedLength w Q a b + weightedLength v Q a b := by
  let ℓ := (curveLength Q a b).toReal
  let R := lengthParam Q a b
  have hprops := lengthParam_props (Q := Q) hab hQ hL (S := univ)
    (mapsTo_univ _ _)
  have hu : HasUnitSpeedOn R (Icc 0 ℓ) := hprops.1
  have hc : ContinuousOn R (Icc 0 ℓ) := hprops.2.1
  have hwc : ContinuousOn (fun t => w (R t)) (Icc 0 ℓ) :=
    hw.continuousOn.comp hc (mapsTo_univ _ _)
  have hvc : ContinuousOn (fun t => v (R t)) (Icc 0 ℓ) :=
    hv.continuousOn.comp hc (mapsTo_univ _ _)
  have hsumc : ContinuousOn (fun t => w (R t) + v (R t)) (Icc 0 ℓ) :=
    hwc.add hvc
  rw [weightedLength_eq_lengthParam hab hQ hL,
    weightedLength_eq_lengthParam hab hQ hL,
    weightedLength_eq_lengthParam hab hQ hL]
  rw [weightedLength_of_hasUnitSpeedOn ENNReal.toReal_nonneg hu hsumc,
    weightedLength_of_hasUnitSpeedOn ENNReal.toReal_nonneg hu hwc,
    weightedLength_of_hasUnitSpeedOn ENNReal.toReal_nonneg hu hvc]
  have hpoint : (fun t : ℝ => ENNReal.ofReal (w (R t) + v (R t))) =
      (fun t => ENNReal.ofReal (w (R t)) + ENNReal.ofReal (v (R t))) := by
    funext t
    exact ENNReal.ofReal_add (hw0 _) (hv0 _)
  rw [hpoint]
  have hwm : AEMeasurable (fun t : ℝ => ENNReal.ofReal (w (R t)))
      (volume.restrict (Icc 0 ℓ)) :=
    (ENNReal.continuous_ofReal.comp_continuousOn hwc).aemeasurable measurableSet_Icc
  exact lintegral_add_left' hwm _

/-- Constant-one weighted length equals ordinary curve length. -/
theorem sec8_weightedLength_one {X : Type*} [PseudoEMetricSpace X]
    (Q : ℝ → X) {a b : ℝ} (hab : a ≤ b) :
    weightedLength (fun _ : X => (1 : ℝ)) Q a b = curveLength Q a b := by
  apply le_antisymm
  · simpa using (weightedLength_le_ofReal_mul_curveLength (P := Q) (a := a)
      (b := b) (M := 1) (fun _ _ => le_rfl))
  · simpa using (ofReal_mul_curveLength_le_weightedLength (P := Q) (a := a)
      (b := b) (w := fun _ : X => (1 : ℝ)) hab (fun _ _ => le_rfl))

/-- The length lost by a nonnegative Weyl discount supported in an open
collector is bounded by the base-metric occupation length there. -/
theorem sec8_length_loss_le_occLen (D E : ContMetric d)
    (ξ : ℝ) (hξ : 0 < ξ) (F : C(Rd d, ℝ))
    (hF0 : ∀ x, 0 ≤ F x) (V : Set (Rd d))
    (hFV : ∀ x, 0 < F x → x ∈ V)
    (hE : IsWeylOf ξ (-F) D E)
    (P : ℝ → Rd d) (hP : IsGeod E P) :
    D.len P 0 1 ≤ E.len P 0 1 + occLen D P V := by
  let w : D.Space → ℝ := D.weylWeight ξ (-F)
  let loss : D.Space → ℝ := fun x => 1 - w x
  have hwc : Continuous w := D.continuous_weylWeight ξ (-F)
  have hlc : Continuous loss := continuous_const.sub hwc
  have hw0 : ∀ x, 0 ≤ w x := fun x => (D.weylWeight_pos ξ (-F) x).le
  have hw1 : ∀ x, w x ≤ 1 := by
    intro x
    change Real.exp (ξ * (-F (D.unpt x))) ≤ 1
    apply Real.exp_le_one_iff.mpr
    have h := hF0 (D.unpt x)
    nlinarith [mul_nonneg hξ.le h]
  have hl0 : ∀ x, 0 ≤ loss x := fun x => sub_nonneg.mpr (hw1 x)
  have hEfin : E.len P 0 1 ≠ ⊤ := by
    rw [hP.2]
    exact ENNReal.ofReal_ne_top
  have hDfin : D.len P 0 1 ≠ ⊤ :=
    (curveLength_weyl_ne_top_iff hE zero_le_one hP.1).mp hEfin
  have hPc : ContinuousOn (D.pt ∘ P) (Icc 0 1) :=
    D.continuous_pt.comp_continuousOn hP.1
  have hOcc : weightedLength loss (D.pt ∘ P) 0 1 ≤ occLen D P V := by
    apply sec8_weightedLength_le_occLen D P V loss
    · intro τ hτ
      dsimp [loss]
      linarith [hw0 (D.pt (P τ))]
    · intro τ hτ hpos
      have hexp : Real.exp (ξ * (-F (P τ))) < 1 := by
        simpa only [loss, w, ContMetric.weylWeight_pt,
          ContinuousMap.neg_apply, sub_pos] using hpos
      have hmul : ξ * (-F (P τ)) < 0 := Real.exp_lt_one_iff.mp hexp
      have hFpos : 0 < F (P τ) := by
        nlinarith [hξ]
      exact hFV _ hFpos
  have hadd := sec8_weightedLength_add_weight (D.pt ∘ P) zero_le_one hPc hDfin
    w loss hwc hlc hw0 hl0
  have hsum : (fun x : D.Space => w x + loss x) = fun _ => (1 : ℝ) := by
    funext x
    dsimp [loss]
    ring
  calc
    D.len P 0 1 = weightedLength (fun x : D.Space => w x + loss x)
        (D.pt ∘ P) 0 1 := by
          rw [hsum, sec8_weightedLength_one _ zero_le_one]
          rfl
    _ = weightedLength w (D.pt ∘ P) 0 1 +
        weightedLength loss (D.pt ∘ P) 0 1 := hadd
    _ = E.len P 0 1 + weightedLength loss (D.pt ∘ P) 0 1 := by
      rw [E.len_def, curveLength_eq_weightedLength_of_weyl hE hP.1]
    _ ≤ E.len P 0 1 + occLen D P V := add_le_add_right hOcc _

/-- Elementary subadditivity of the discount loss for nonnegative inputs. -/
theorem sec8_one_sub_exp_neg_sum_le_sum {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) :
    1 - Real.exp (-(∑ i ∈ S, a i)) ≤
      ∑ i ∈ S, (1 - Real.exp (-a i)) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      have hai : 0 ≤ a i := ha i (Finset.mem_insert_self _ _)
      have haS : ∀ j ∈ S, 0 ≤ a j := fun j hj =>
        ha j (Finset.mem_insert_of_mem hj)
      have hind := ih haS
      have heA : Real.exp (-a i) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr hai)
      have heB : Real.exp (-(∑ j ∈ S, a j)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        exact neg_nonpos.mpr (Finset.sum_nonneg haS)
      rw [Finset.sum_insert hi, Finset.sum_insert hi, neg_add_rev, Real.exp_add]
      nlinarith [mul_nonneg (sub_nonneg.mpr heA) (sub_nonneg.mpr heB)]

/-- Finite additivity of weighted length in continuous nonnegative weights
along a finite-length curve. -/
theorem sec8_weightedLength_finset_sum {X ι : Type*} [EMetricSpace X]
    [DecidableEq ι] (Q : ℝ → X) {a b : ℝ} (hab : a ≤ b)
    (hQ : ContinuousOn Q (Icc a b)) (hL : curveLength Q a b ≠ ⊤)
    (S : Finset ι) (w : ι → X → ℝ)
    (hwc : ∀ i ∈ S, Continuous (w i))
    (hw0 : ∀ i ∈ S, ∀ x, 0 ≤ w i x) :
    weightedLength (fun x => ∑ i ∈ S, w i x) Q a b =
      ∑ i ∈ S, weightedLength (w i) Q a b := by
  induction S using Finset.induction_on with
  | empty =>
      have hzero : weightedLength (fun _ : X => (0 : ℝ)) Q a b = 0 := by
        apply le_antisymm
        · have h := weightedLength_le_ofReal_mul_curveLength (P := Q)
            (a := a) (b := b) (w := fun _ : X => (0 : ℝ))
            (M := 0) (fun _ _ => le_rfl)
          simpa using h
        · exact bot_le
      simpa using hzero
  | @insert i S hi ih =>
      have hiC : Continuous (w i) := hwc i (Finset.mem_insert_self _ _)
      have hi0 : ∀ x, 0 ≤ w i x := hw0 i (Finset.mem_insert_self _ _)
      have hSc : ∀ j ∈ S, Continuous (w j) := fun j hj =>
        hwc j (Finset.mem_insert_of_mem hj)
      have hS0 : ∀ j ∈ S, ∀ x, 0 ≤ w j x := fun j hj =>
        hw0 j (Finset.mem_insert_of_mem hj)
      have hSumC : Continuous (fun x => ∑ j ∈ S, w j x) :=
        continuous_finsetSum _ fun j hj => hSc j hj
      have hSum0 : ∀ x, 0 ≤ ∑ j ∈ S, w j x := fun x =>
        Finset.sum_nonneg fun j hj => hS0 j hj x
      simp only [Finset.sum_insert hi]
      rw [sec8_weightedLength_add_weight Q hab hQ hL (w i)
        (fun x => ∑ j ∈ S, w j x) hiC hSumC hi0 hSum0,
        ih hSc hS0]

/-- The exact weighted-loss identity underlying the integrated occupation
estimate. -/
theorem sec8_length_eq_weyl_plus_loss (D E : ContMetric d)
    (ξ : ℝ) (F : C(Rd d, ℝ)) (hF0 : ∀ x, 0 ≤ F x)
    (hE : IsWeylOf ξ (-F) D E) (P : ℝ → Rd d) (hP : IsGeod E P)
    (hξ : 0 < ξ) :
    D.len P 0 1 = E.len P 0 1 +
      weightedLength (fun x : D.Space => 1 - D.weylWeight ξ (-F) x)
        (D.pt ∘ P) 0 1 := by
  let w : D.Space → ℝ := D.weylWeight ξ (-F)
  let loss : D.Space → ℝ := fun x => 1 - w x
  have hwc : Continuous w := D.continuous_weylWeight ξ (-F)
  have hlc : Continuous loss := continuous_const.sub hwc
  have hw0 : ∀ x, 0 ≤ w x := fun x => (D.weylWeight_pos ξ (-F) x).le
  have hw1 : ∀ x, w x ≤ 1 := by
    intro x
    change Real.exp (ξ * (-F (D.unpt x))) ≤ 1
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hξ.le (hF0 (D.unpt x))]
  have hl0 : ∀ x, 0 ≤ loss x := fun x => sub_nonneg.mpr (hw1 x)
  have hEfin : E.len P 0 1 ≠ ⊤ := by
    rw [hP.2]
    exact ENNReal.ofReal_ne_top
  have hDfin : D.len P 0 1 ≠ ⊤ :=
    (curveLength_weyl_ne_top_iff hE zero_le_one hP.1).mp hEfin
  have hPc : ContinuousOn (D.pt ∘ P) (Icc 0 1) :=
    D.continuous_pt.comp_continuousOn hP.1
  have hadd := sec8_weightedLength_add_weight (D.pt ∘ P) zero_le_one hPc hDfin
    w loss hwc hlc hw0 hl0
  have hsum : (fun x : D.Space => w x + loss x) = fun _ => (1 : ℝ) := by
    funext x
    dsimp [loss]
    ring
  calc
    D.len P 0 1 = weightedLength (fun x : D.Space => w x + loss x)
        (D.pt ∘ P) 0 1 := by
          rw [hsum, sec8_weightedLength_one _ zero_le_one]
          rfl
    _ = weightedLength w (D.pt ∘ P) 0 1 +
        weightedLength loss (D.pt ∘ P) 0 1 := hadd
    _ = E.len P 0 1 + weightedLength loss (D.pt ∘ P) 0 1 := by
      rw [E.len_def, curveLength_eq_weightedLength_of_weyl hE hP.1]

end HigherDimLQGMetric
