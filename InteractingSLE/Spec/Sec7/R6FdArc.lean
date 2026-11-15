/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FdLand
import InteractingSLE.Spec.Sec7.SideAncOrient
import InteractingSLE.Spec.Sec7.PocketReverseFields

/-!
# Wall points of a bounded change pocket in its Jordan coordinate

Packet PROVE-R6-FACE3. Deterministic planar facts for a bounded change pocket `C = cfPocket R L r` (counterflow
chart, `0 ∉ closure (changePocket R L r)`) with a Jordan coordinate `ψ` (`x₀ ↦ ∞`, `y₀ ↦ 0`) under the flow-chart
orientation, and a nested bounded change pocket `U` sharing one wall with `C`. Write `ℓ_M(θ)` (`wallPt M θ`) for the
counterflow-chart point of the wall `M` at the disc parameter `θ ∈ (0, 1]`.

* `mem_Icc_left_of_mem_closure` / `_right_`: a wall point in `closure C` has its parameter in `C`'s arc interval
  (the other wall meets it only at the two corners: contact gaps);
* `left_arc_facts` / `right_arc_facts`: `θ ↦ ψ(ℓ_L(θ))` is real, continuous and **strictly decreasing** on
  `(leftLo, leftHi]` (from `+∞` to `0`); `s ↦ ψ(ℓ_R(s))` is real, continuous and **strictly increasing** on
  `(rightLo, rightHi]` (from `−∞` to `0`);
* `extension_psi_eq`: the continuous inverse extension `E₀` of `ψ⁻¹` inverts `ψ` on `closure C ∖ {x₀}`;
* `exists_left_param_of_between` / `_right_`: a real value between the coordinates of a point of `U`'s open shared arc
  and of a later wall point beyond `U`'s outgoing corner is the coordinate of a point of `U`'s open shared arc;
* `nonCorner_of_left_open` / `_right_open`: a point of `U`'s open shared arc is a non-corner point of `∂U`
  (`R6Fc.IsNonCornerLanding`'s three conjuncts).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Function
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal

namespace InteractingSLE.Sec7.R6Fd

open WangWu PocketCoord Lemma71I PocketJordan PocketWordAssembly

variable {R L R' L' : ℝ≥0 → ℂ} {r r' : ℝ≥0}

/-! ### Wall points -/

/-- The counterflow-chart point of the wall `M` at the disc parameter `θ`. -/
abbrev wallPt (M : ℝ≥0 → ℂ) (θ : ℝ) : ℂ := cfPt (toDisc (Lemma71I.realPath M) θ)

theorem toDisc_ne_neg_one {M : ℝ≥0 → ℂ} (hM : IsSimpleProper M) {θ : ℝ} (hθ : θ ∈ Ioc (0 : ℝ) 1) :
    toDisc (Lemma71I.realPath M) θ ≠ -1 := fun he => by
  have hc := hM.isProperArc.isDiscCrosscut_toDisc
  have := hc.inj ⟨hθ.1.le, hθ.2⟩ ⟨le_rfl, zero_le_one⟩ (he.trans hc.zero.symm)
  linarith [hθ.1]

theorem wallPt_injOn {M : ℝ≥0 → ℂ} (hM : IsSimpleProper M) : InjOn (wallPt M) (Ioc (0 : ℝ) 1) :=
  fun _ hθ _ hθ' he => hM.isProperArc.isDiscCrosscut_toDisc.inj ⟨hθ.1.le, hθ.2⟩ ⟨hθ'.1.le, hθ'.2⟩
    (injOn_cfPt (toDisc_ne_neg_one hM hθ) (toDisc_ne_neg_one hM hθ') he)

theorem continuousOn_wallPt {M : ℝ≥0 → ℂ} (hM : IsSimpleProper M) : ContinuousOn (wallPt M) (Ioc (0 : ℝ) 1) :=
  continuousOn_cfPt.comp (hM.isProperArc.isDiscCrosscut_toDisc.cont.mono Ioc_subset_Icc_self)
    fun _ hθ => toDisc_ne_neg_one hM hθ

/-- A wall point of either wall is not in the counterflow-chart pocket. -/
theorem wallPt_notMem {M : ℝ≥0 → ℂ} (h : IsChangeConfigInc R L r) (hM : M = R ∨ M = L) {θ : ℝ}
    (hθ : θ ∈ Ioc (0 : ℝ) 1) : wallPt M θ ∉ cfPocket R L r := by
  have hMs : IsSimpleProper M := by rcases hM with rfl | rfl; exacts [h.right, h.left]
  rcases hθ.2.lt_or_eq with hθ1 | hθ1
  · obtain ⟨e, -⟩ := PocketJordan.cfPt_toDisc_of_mem hMs ⟨hθ.1, hθ1⟩
    rintro ⟨w, hw, hwe⟩
    have hwe' : wallPt M θ = negInv (M (arcTime θ).toNNReal) := e
    rw [hwe'] at hwe
    have hw' : w = M (arcTime θ).toNNReal := by
      have := congrArg negInv hwe
      rwa [WangWu.negInv_negInv, WangWu.negInv_negInv] at this
    have hmem : w ∈ range R ∪ range L := by
      rcases hM with rfl | rfl
      · exact Or.inl ⟨_, hw'.symm⟩
      · exact Or.inr ⟨_, hw'.symm⟩
    exact (h.changePocket_subset hw).2 hmem
  · intro hm
    have h0 : wallPt M θ = 0 := by
      show cfPt (toDisc (Lemma71I.realPath M) θ) = 0
      rw [hθ1, toDisc_one, cfPt_one]
    have := PocketJordan.image_negInv_subset_H h.changePocket_subset_H hm
    rw [h0] at this
    exact lt_irrefl _ (show (0 : ℂ).im > 0 from this)

/-! ### The arc intervals -/

/-- **A left-wall point in the closed pocket has its parameter in the left arc interval.** -/
theorem mem_Icc_left_of_mem_closure (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    {θ : ℝ} (hθ : θ ∈ Ioc (0 : ℝ) 1) (hm : wallPt L θ ∈ closure (cfPocket R L r)) :
    θ ∈ Icc (leftLo R L r) (leftHi R L r) := by
  have hC := h.isCfPocket h0
  have hfr : wallPt L θ ∈ frontier (cfPocket R L r) :=
    ⟨hm, by rw [hC.isOpen.interior_eq]; exact wallPt_notMem h (Or.inr rfl) hθ⟩
  obtain ⟨hu, hv, huv, ha, hb, hab, hLa, hLb⟩ := h.changeCorner_props
  have hg := h.changeCorners.1
  have hu0 := h.rightLo_pos h0
  have ha0 := h.leftLo_pos h0
  have hcL := h.isDiscCrosscut_left
  rw [hC.frontier_eq] at hfr
  rcases hfr with ⟨v, hv1, hve⟩ | ⟨v, hv1, hve⟩
  · have hs := (IsChangeConfigInc.affine_mem huv).1 hv1
    have hs01 : rightLo R L r + v * (rightHi R L r - rightLo R L r) ∈ Ioc (0 : ℝ) 1 :=
      ⟨hu0.trans_le hs.1, hs.2.trans hv.2⟩
    have he : toDisc (Lemma71I.realPath R) (rightLo R L r + v * (rightHi R L r - rightLo R L r)) =
        toDisc (Lemma71I.realPath L) θ :=
      injOn_cfPt (toDisc_ne_neg_one h.right hs01) (toDisc_ne_neg_one h.left hθ) hve
    have hcs : rightLo R L r + v * (rightHi R L r - rightLo R L r) ∈
        Sec7.pocketContactSet (toDisc (Lemma71I.realPath R)) (toDisc (Lemma71I.realPath L)) :=
      ⟨⟨hs01.1.le, hs01.2⟩, θ, ⟨hθ.1.le, hθ.2⟩, he.symm⟩
    have hend : rightLo R L r + v * (rightHi R L r - rightLo R L r) = rightLo R L r ∨
        rightLo R L r + v * (rightHi R L r - rightLo R L r) = rightHi R L r := by
      by_contra hne
      push Not at hne
      exact hg.2.2.2 _ ⟨lt_of_le_of_ne hs.1 (Ne.symm hne.1), lt_of_le_of_ne hs.2 hne.2⟩ hcs
    rcases hend with he' | he'
    · have hθe : toDisc (Lemma71I.realPath L) θ = toDisc (Lemma71I.realPath L) (leftLo R L r) := by
        rw [← he, he', hLa]; rfl
      rw [hcL.inj ⟨hθ.1.le, hθ.2⟩ ha hθe]
      exact ⟨le_rfl, hab.le⟩
    · have hθe : toDisc (Lemma71I.realPath L) θ = toDisc (Lemma71I.realPath L) (leftHi R L r) := by
        rw [← he, he', hLb]; rfl
      rw [hcL.inj ⟨hθ.1.le, hθ.2⟩ hb hθe]
      exact ⟨hab.le, le_rfl⟩
  · have hs := (IsChangeConfigInc.affine_mem hab).1 hv1
    have hs01 : leftLo R L r + v * (leftHi R L r - leftLo R L r) ∈ Ioc (0 : ℝ) 1 :=
      ⟨ha0.trans_le hs.1, hs.2.trans hb.2⟩
    rw [← wallPt_injOn h.left hs01 hθ hve]
    exact hs

/-- **A right-wall point in the closed pocket has its parameter in the right arc interval.** -/
theorem mem_Icc_right_of_mem_closure (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) (hm : wallPt R s ∈ closure (cfPocket R L r)) :
    s ∈ Icc (rightLo R L r) (rightHi R L r) := by
  have hC := h.isCfPocket h0
  have hfr : wallPt R s ∈ frontier (cfPocket R L r) :=
    ⟨hm, by rw [hC.isOpen.interior_eq]; exact wallPt_notMem h (Or.inl rfl) hs⟩
  obtain ⟨hu, hv, huv, ha, hb, hab, hLa, hLb⟩ := h.changeCorner_props
  have hgL := h.changeCorners.2.2.2.1
  have hu0 := h.rightLo_pos h0
  have ha0 := h.leftLo_pos h0
  have hcR := h.isDiscCrosscut_right
  rw [hC.frontier_eq] at hfr
  rcases hfr with ⟨v, hv1, hve⟩ | ⟨v, hv1, hve⟩
  · have hs' := (IsChangeConfigInc.affine_mem huv).1 hv1
    have hs01 : rightLo R L r + v * (rightHi R L r - rightLo R L r) ∈ Ioc (0 : ℝ) 1 :=
      ⟨hu0.trans_le hs'.1, hs'.2.trans hv.2⟩
    rw [← wallPt_injOn h.right hs01 hs hve]
    exact hs'
  · have ht := (IsChangeConfigInc.affine_mem hab).1 hv1
    have ht01 : leftLo R L r + v * (leftHi R L r - leftLo R L r) ∈ Ioc (0 : ℝ) 1 :=
      ⟨ha0.trans_le ht.1, ht.2.trans hb.2⟩
    have he : toDisc (Lemma71I.realPath L) (leftLo R L r + v * (leftHi R L r - leftLo R L r)) =
        toDisc (Lemma71I.realPath R) s :=
      injOn_cfPt (toDisc_ne_neg_one h.left ht01) (toDisc_ne_neg_one h.right hs) hve
    have hcs : leftLo R L r + v * (leftHi R L r - leftLo R L r) ∈
        Sec7.pocketContactSet (toDisc (Lemma71I.realPath L)) (toDisc (Lemma71I.realPath R)) :=
      ⟨⟨ht01.1.le, ht01.2⟩, s, ⟨hs.1.le, hs.2⟩, he.symm⟩
    have hend : leftLo R L r + v * (leftHi R L r - leftLo R L r) = leftLo R L r ∨
        leftLo R L r + v * (leftHi R L r - leftLo R L r) = leftHi R L r := by
      by_contra hne
      push Not at hne
      exact hgL.2.2.2 _ ⟨lt_of_le_of_ne ht.1 (Ne.symm hne.1), lt_of_le_of_ne ht.2 hne.2⟩ hcs
    rcases hend with he' | he'
    · have hse : toDisc (Lemma71I.realPath R) s = toDisc (Lemma71I.realPath R) (rightLo R L r) := by
        rw [← he, he', hLa]; rfl
      rw [hcR.inj ⟨hs.1.le, hs.2⟩ hu hse]
      exact ⟨le_rfl, huv.le⟩
    · have hse : toDisc (Lemma71I.realPath R) s = toDisc (Lemma71I.realPath R) (rightHi R L r) := by
        rw [← he, he', hLb]; rfl
      rw [hcR.inj ⟨hs.1.le, hs.2⟩ hv hse]
      exact ⟨huv.le, le_rfl⟩

/-! ### The coordinate along one wall -/

/-- A left-wall point with parameter in the left arc interval is a point of the left arc. -/
theorem exists_cfArcL_eq {θ : ℝ} (hlh : leftLo R L r < leftHi R L r)
    (hθ : θ ∈ Icc (leftLo R L r) (leftHi R L r)) : ∃ v ∈ Icc (0 : ℝ) 1, cfArcL R L r v = wallPt L θ := by
  have hd : 0 < leftHi R L r - leftLo R L r := sub_pos.2 hlh
  refine ⟨(θ - leftLo R L r) / (leftHi R L r - leftLo R L r),
    ⟨div_nonneg (by linarith [hθ.1]) hd.le, (div_le_one hd).2 (by linarith [hθ.2])⟩, ?_⟩
  have he : leftLo R L r + (θ - leftLo R L r) / (leftHi R L r - leftLo R L r) * (leftHi R L r - leftLo R L r) =
      θ := by field_simp; ring
  show cfPt (toDisc (Lemma71I.realPath L) (leftLo R L r + _ * (leftHi R L r - leftLo R L r))) = _
  rw [he]

/-- A right-wall point with parameter in the right arc interval is a point of the right arc. -/
theorem exists_cfArcR_eq {s : ℝ} (hlh : rightLo R L r < rightHi R L r)
    (hs : s ∈ Icc (rightLo R L r) (rightHi R L r)) : ∃ v ∈ Icc (0 : ℝ) 1, cfArcR R L r v = wallPt R s := by
  have hd : 0 < rightHi R L r - rightLo R L r := sub_pos.2 hlh
  refine ⟨(s - rightLo R L r) / (rightHi R L r - rightLo R L r),
    ⟨div_nonneg (by linarith [hs.1]) hd.le, (div_le_one hd).2 (by linarith [hs.2])⟩, ?_⟩
  have he : rightLo R L r + (s - rightLo R L r) / (rightHi R L r - rightLo R L r) *
      (rightHi R L r - rightLo R L r) = s := by field_simp; ring
  show cfPt (toDisc (Lemma71I.realPath R) (rightLo R L r + _ * (rightHi R L r - rightLo R L r))) = _
  rw [he]

/-- **The coordinate along the left arc**: real, continuous and strictly decreasing on `(leftLo, leftHi]`. -/
theorem left_arc_facts (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hor : PocketMarks.IsFlowChartOriented R L r) {ψ : ℂ → ℂ} (hψ : IsCfJordan R L r ψ) :
    (∀ θ ∈ Ioc (leftLo R L r) (leftHi R L r),
      wallPt L θ ∈ closure (cfPocket R L r) \ {cfPt (openPt R L r)} ∧ (ψ (wallPt L θ)).im = 0) ∧
    ContinuousOn (fun θ => ψ (wallPt L θ)) (Ioc (leftLo R L r) (leftHi R L r)) ∧
    StrictAntiOn (fun θ => (ψ (wallPt L θ)).re) (Ioc (leftLo R L r) (leftHi R L r)) := by
  obtain ⟨-, -, -, ha, hb, hab, hLa, hLb⟩ := h.changeCorner_props
  have ha0 := h.leftLo_pos h0
  have hC := h.isCfPocket h0
  have hI : Ioc (leftLo R L r) (leftHi R L r) ⊆ Ioc 0 1 := fun θ hθ => ⟨ha0.trans hθ.1, hθ.2.trans hb.2⟩
  have hx₀ : cfPt (openPt R L r) = wallPt L (leftLo R L r) := by
    show cfPt _ = cfPt (toDisc (Lemma71I.realPath L) (leftLo R L r)); rw [hLa]
  have hy₀ : cfPt (closePt R L r) = wallPt L (leftHi R L r) := by
    show cfPt _ = cfPt (toDisc (Lemma71I.realPath L) (leftHi R L r)); rw [hLb]
  have hpt : ∀ θ ∈ Ioc (leftLo R L r) (leftHi R L r),
      wallPt L θ ∈ frontier (cfPocket R L r) ∧ wallPt L θ ≠ cfPt (openPt R L r) := by
    intro θ hθ
    obtain ⟨v, hv, hve⟩ := exists_cfArcL_eq hab ⟨hθ.1.le, hθ.2⟩
    refine ⟨?_, ?_⟩
    · rw [hC.frontier_eq]; exact Or.inr ⟨v, hv, hve⟩
    · rw [hx₀]
      intro he
      exact hθ.1.ne' (wallPt_injOn h.left (hI hθ) ⟨ha0, hab.le.trans hb.2⟩ he)
  have hfacts : ∀ θ ∈ Ioc (leftLo R L r) (leftHi R L r),
      wallPt L θ ∈ closure (cfPocket R L r) \ {cfPt (openPt R L r)} ∧ (ψ (wallPt L θ)).im = 0 := fun θ hθ =>
    ⟨⟨frontier_subset_closure (hpt θ hθ).1, (hpt θ hθ).2⟩, hψ.2.2.2.2.1 _ ⟨(hpt θ hθ).1, (hpt θ hθ).2⟩⟩
  have hcont : ContinuousOn (fun θ => ψ (wallPt L θ)) (Ioc (leftLo R L r) (leftHi R L r)) :=
    hψ.1.comp ((continuousOn_wallPt h.left).mono hI) fun θ hθ => (hfacts θ hθ).1
  have hinj : InjOn (fun θ => (ψ (wallPt L θ)).re) (Ioc (leftLo R L r) (leftHi R L r)) := by
    intro θ hθ θ' hθ' he
    have : ψ (wallPt L θ) = ψ (wallPt L θ') := Complex.ext he (by rw [(hfacts θ hθ).2, (hfacts θ' hθ').2])
    exact wallPt_injOn h.left (hI hθ) (hI hθ') (hψ.2.1 (hfacts θ hθ).1 (hfacts θ' hθ').1 this)
  have hpos : ∀ θ ∈ Ioo (leftLo R L r) (leftHi R L r), 0 < (ψ (wallPt L θ)).re :=
    (SideAnc.jordan_sides h h0 hor hψ).2
  have hhi : (ψ (wallPt L (leftHi R L r))).re = 0 := by rw [← hy₀, hψ.2.2.2.2.2.1]; rfl
  refine ⟨hfacts, hcont, fun θ₁ h₁ θ₂ h₂ h12 => ?_⟩
  rcases h₂.2.lt_or_eq with h₂hi | h₂hi
  · by_contra hle
    push Not at hle
    have hθ₁pos := hpos θ₁ ⟨h₁.1, h12.trans h₂hi⟩
    have hcI : ContinuousOn (fun θ => (ψ (wallPt L θ)).re) (Icc θ₂ (leftHi R L r)) :=
      (Complex.continuous_re.comp_continuousOn hcont).mono fun θ hθ => ⟨h₂.1.trans_le hθ.1, hθ.2⟩
    obtain ⟨θ₃, hθ₃, he⟩ := intermediate_value_Icc' h₂.2 hcI ⟨by rw [hhi]; exact hθ₁pos.le, hle⟩
    have := hinj ⟨h₂.1.trans_le hθ₃.1, hθ₃.2⟩ h₁ he
    linarith [hθ₃.1]
  · show (ψ (wallPt L θ₂)).re < (ψ (wallPt L θ₁)).re
    rw [h₂hi, hhi]
    exact hpos θ₁ ⟨h₁.1, h₂hi ▸ h12⟩

/-- **The coordinate along the right arc**: real, continuous and strictly increasing on `(rightLo, rightHi]`. -/
theorem right_arc_facts (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hor : PocketMarks.IsFlowChartOriented R L r) {ψ : ℂ → ℂ} (hψ : IsCfJordan R L r ψ) :
    (∀ s ∈ Ioc (rightLo R L r) (rightHi R L r),
      wallPt R s ∈ closure (cfPocket R L r) \ {cfPt (openPt R L r)} ∧ (ψ (wallPt R s)).im = 0) ∧
    ContinuousOn (fun s => ψ (wallPt R s)) (Ioc (rightLo R L r) (rightHi R L r)) ∧
    StrictMonoOn (fun s => (ψ (wallPt R s)).re) (Ioc (rightLo R L r) (rightHi R L r)) := by
  obtain ⟨hu, hv, huv, -, -, -, -, -⟩ := h.changeCorner_props
  have hu0 := h.rightLo_pos h0
  have hC := h.isCfPocket h0
  have hI : Ioc (rightLo R L r) (rightHi R L r) ⊆ Ioc 0 1 := fun θ hθ => ⟨hu0.trans hθ.1, hθ.2.trans hv.2⟩
  have hx₀ : cfPt (openPt R L r) = wallPt R (rightLo R L r) := rfl
  have hy₀ : cfPt (closePt R L r) = wallPt R (rightHi R L r) := rfl
  have hpt : ∀ s ∈ Ioc (rightLo R L r) (rightHi R L r),
      wallPt R s ∈ frontier (cfPocket R L r) ∧ wallPt R s ≠ cfPt (openPt R L r) := by
    intro s hs
    obtain ⟨w, hw, hwe⟩ := exists_cfArcR_eq huv ⟨hs.1.le, hs.2⟩
    refine ⟨?_, ?_⟩
    · rw [hC.frontier_eq]; exact Or.inl ⟨w, hw, hwe⟩
    · rw [hx₀]
      intro he
      exact hs.1.ne' (wallPt_injOn h.right (hI hs) ⟨hu0, huv.le.trans hv.2⟩ he)
  have hfacts : ∀ s ∈ Ioc (rightLo R L r) (rightHi R L r),
      wallPt R s ∈ closure (cfPocket R L r) \ {cfPt (openPt R L r)} ∧ (ψ (wallPt R s)).im = 0 := fun s hs =>
    ⟨⟨frontier_subset_closure (hpt s hs).1, (hpt s hs).2⟩, hψ.2.2.2.2.1 _ ⟨(hpt s hs).1, (hpt s hs).2⟩⟩
  have hcont : ContinuousOn (fun s => ψ (wallPt R s)) (Ioc (rightLo R L r) (rightHi R L r)) :=
    hψ.1.comp ((continuousOn_wallPt h.right).mono hI) fun s hs => (hfacts s hs).1
  have hinj : InjOn (fun s => (ψ (wallPt R s)).re) (Ioc (rightLo R L r) (rightHi R L r)) := by
    intro s hs s' hs' he
    have : ψ (wallPt R s) = ψ (wallPt R s') := Complex.ext he (by rw [(hfacts s hs).2, (hfacts s' hs').2])
    exact wallPt_injOn h.right (hI hs) (hI hs') (hψ.2.1 (hfacts s hs).1 (hfacts s' hs').1 this)
  have hneg : ∀ s ∈ Ioo (rightLo R L r) (rightHi R L r), (ψ (wallPt R s)).re < 0 :=
    (SideAnc.jordan_sides h h0 hor hψ).1
  have hhi : (ψ (wallPt R (rightHi R L r))).re = 0 := by rw [← hy₀, hψ.2.2.2.2.2.1]; rfl
  refine ⟨hfacts, hcont, fun s₁ h₁ s₂ h₂ h12 => ?_⟩
  rcases h₂.2.lt_or_eq with h₂hi | h₂hi
  · by_contra hle
    push Not at hle
    have hs₁neg := hneg s₁ ⟨h₁.1, h12.trans h₂hi⟩
    have hcI : ContinuousOn (fun s => (ψ (wallPt R s)).re) (Icc s₂ (rightHi R L r)) :=
      (Complex.continuous_re.comp_continuousOn hcont).mono fun s hs => ⟨h₂.1.trans_le hs.1, hs.2⟩
    obtain ⟨s₃, hs₃, he⟩ := intermediate_value_Icc h₂.2 hcI ⟨hle, by rw [hhi]; exact hs₁neg.le⟩
    have := hinj ⟨h₂.1.trans_le hs₃.1, hs₃.2⟩ h₁ he
    linarith [hs₃.1]
  · show (ψ (wallPt R s₁)).re < (ψ (wallPt R s₂)).re
    rw [h₂hi, hhi]
    exact hneg s₁ ⟨h₁.1, h₂hi ▸ h12⟩

/-! ### The inverse extension inverts the Jordan coordinate -/

/-- **The continuous inverse extension inverts the Jordan coordinate on `closure C ∖ {x₀}`.** -/
theorem extension_psi_eq {C : Set ℂ} {x₀ y₀ : ℂ} {ψ E₀ : ℂ → ℂ} (hψ : Sec6.IsJordanCoord C x₀ y₀ ψ) (hx₀ : x₀ ∉ C)
    (hE₀ : EqOn E₀ (invFunOn ψ C) H) (hE₀c : ContinuousOn E₀ Hbar) {p : ℂ} (hp : p ∈ closure C \ {x₀}) :
    E₀ (ψ p) = p := by
  have hb : (𝓝[C] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hp.1
  have hCsub : C ⊆ closure C \ {x₀} := fun z hz => ⟨subset_closure hz, fun he => hx₀ (he ▸ hz)⟩
  have hψH : ∀ z ∈ C, ψ z ∈ H := fun z hz => hψ.2.2.2.1.2.mapsTo hz
  have h1 : Tendsto ψ (𝓝[C] p) (𝓝[Hbar] (ψ p)) :=
    tendsto_nhdsWithin_iff.2 ⟨((hψ.1 p hp).mono hCsub).tendsto,
      eventually_nhdsWithin_of_forall fun z hz => QuantumZipper.H_subset_Hbar (hψH z hz)⟩
  have h2 : Tendsto (fun z => E₀ (ψ z)) (𝓝[C] p) (𝓝 (E₀ (ψ p))) :=
    (hE₀c (ψ p) (hψ.2.2.1 hp)).tendsto.comp h1
  have h3 : Tendsto (fun z => E₀ (ψ z)) (𝓝[C] p) (𝓝 p) := by
    refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
    refine eventually_nhdsWithin_of_forall fun z hz => ?_
    show z = E₀ (ψ z)
    rw [hE₀ (hψH z hz)]
    exact (hψ.2.2.2.1.2.injOn.leftInvOn_invFunOn hz).symm
  exact tendsto_nhds_unique h2 h3

/-! ### The landing between two wall points -/

/-- A point of the nested pocket's left arc lies in the closed outer pocket. -/
theorem wallPt_left_mem_closure (hU : IsChangeConfigInc R' L r') (hU0 : (0 : ℂ) ∉ closure (changePocket R' L r'))
    (hsub : cfPocket R' L r' ⊆ cfPocket R L r) {θ : ℝ} (hθ : θ ∈ Icc (leftLo R' L r') (leftHi R' L r')) :
    wallPt L θ ∈ closure (cfPocket R L r) := by
  obtain ⟨-, -, -, -, -, hab', -, -⟩ := hU.changeCorner_props
  obtain ⟨v, hv, hve⟩ := exists_cfArcL_eq hab' hθ
  refine closure_mono hsub (frontier_subset_closure ?_)
  rw [(hU.isCfPocket hU0).frontier_eq]
  exact Or.inr ⟨v, hv, hve⟩

/-- A point of the nested pocket's right arc lies in the closed outer pocket. -/
theorem wallPt_right_mem_closure (hU : IsChangeConfigInc R L' r') (hU0 : (0 : ℂ) ∉ closure (changePocket R L' r'))
    (hsub : cfPocket R L' r' ⊆ cfPocket R L r) {s : ℝ} (hs : s ∈ Icc (rightLo R L' r') (rightHi R L' r')) :
    wallPt R s ∈ closure (cfPocket R L r) := by
  obtain ⟨-, -, huv', -, -, -, -, -⟩ := hU.changeCorner_props
  obtain ⟨v, hv, hve⟩ := exists_cfArcR_eq huv' hs
  refine closure_mono hsub (frontier_subset_closure ?_)
  rw [(hU.isCfPocket hU0).frontier_eq]
  exact Or.inl ⟨v, hv, hve⟩

/-- **Shared left wall: a value between two wall coordinates is the coordinate of a point of the open shared arc.**
`θ₁` is a point of `U`'s open left arc with coordinate `≤ b`; `θ₂` a left-wall point of `closure C` beyond `U`'s
outgoing corner (`θ₂ > leftLo U`) with coordinate `≥ b`. -/
theorem exists_left_param_of_between (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hor : PocketMarks.IsFlowChartOriented R L r) {ψ : ℂ → ℂ} (hψ : IsCfJordan R L r ψ)
    (hU : IsChangeConfigInc R' L r') (hU0 : (0 : ℂ) ∉ closure (changePocket R' L r'))
    (hsub : cfPocket R' L r' ⊆ cfPocket R L r) {b θ₁ θ₂ : ℝ}
    (h₁ : θ₁ ∈ Ioo (leftLo R' L r') (leftHi R' L r')) (h₁x : wallPt L θ₁ ≠ cfPt (openPt R L r))
    (hb₁ : (ψ (wallPt L θ₁)).re ≤ b) (h₂ : θ₂ ∈ Ioc (leftLo R' L r') 1)
    (h₂C : wallPt L θ₂ ∈ closure (cfPocket R L r)) (h₂x : wallPt L θ₂ ≠ cfPt (openPt R L r))
    (hb₂ : b ≤ (ψ (wallPt L θ₂)).re) :
    ∃ θ ∈ Ioo (leftLo R' L r') (leftHi R' L r'), θ₂ ≤ θ ∧ ψ (wallPt L θ) = (b : ℂ) := by
  obtain ⟨-, -, -, ha, hb, -, hLa, -⟩ := h.changeCorner_props
  obtain ⟨-, -, -, ha', hb', -, -, -⟩ := hU.changeCorner_props
  have hx₀ : cfPt (openPt R L r) = wallPt L (leftLo R L r) := by
    show cfPt _ = cfPt (toDisc (Lemma71I.realPath L) (leftLo R L r)); rw [hLa]
  have ha0 := h.leftLo_pos h0
  have hIC : ∀ θ, θ ∈ Ioc (0 : ℝ) 1 → wallPt L θ ∈ closure (cfPocket R L r) → wallPt L θ ≠ cfPt (openPt R L r) →
      θ ∈ Ioc (leftLo R L r) (leftHi R L r) := fun θ hθ hm hx => by
    have hI := mem_Icc_left_of_mem_closure h h0 hθ hm
    refine ⟨lt_of_le_of_ne hI.1 fun he => hx ?_, hI.2⟩
    rw [hx₀, he]
  have h₁01 : θ₁ ∈ Ioc (0 : ℝ) 1 := ⟨ha'.1.trans_lt h₁.1, h₁.2.le.trans hb'.2⟩
  have h₂01 : θ₂ ∈ Ioc (0 : ℝ) 1 := ⟨ha'.1.trans_lt h₂.1, h₂.2⟩
  have h₁C := hIC θ₁ h₁01 (wallPt_left_mem_closure hU hU0 hsub ⟨h₁.1.le, h₁.2.le⟩) h₁x
  have h₂C' := hIC θ₂ h₂01 h₂C h₂x
  obtain ⟨hfacts, hcont, hanti⟩ := left_arc_facts h h0 hor hψ
  have h21 : θ₂ ≤ θ₁ := by
    by_contra hlt
    push Not at hlt
    have := hanti h₁C h₂C' hlt
    linarith
  have hcI : ContinuousOn (fun θ => (ψ (wallPt L θ)).re) (Icc θ₂ θ₁) :=
    (Complex.continuous_re.comp_continuousOn hcont).mono fun θ hθ => ⟨h₂C'.1.trans_le hθ.1, hθ.2.trans h₁C.2⟩
  obtain ⟨θ, hθ, he⟩ := intermediate_value_Icc' h21 hcI ⟨hb₁, hb₂⟩
  have hθC : θ ∈ Ioc (leftLo R L r) (leftHi R L r) := ⟨h₂C'.1.trans_le hθ.1, hθ.2.trans h₁C.2⟩
  refine ⟨θ, ⟨h₂.1.trans_le hθ.1, hθ.2.trans_lt h₁.2⟩, hθ.1, Complex.ext ?_ ?_⟩
  · rw [Complex.ofReal_re]; exact he
  · rw [Complex.ofReal_im]; exact (hfacts θ hθC).2

/-- **Shared right wall: a value between two wall coordinates is the coordinate of a point of the open shared arc.**
`s₁` is a point of `U`'s open right arc with coordinate `≥ b`; `s₂` a right-wall point of `closure C` beyond `U`'s
outgoing corner (`s₂ > rightLo U`) with coordinate `≤ b`. -/
theorem exists_right_param_of_between (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hor : PocketMarks.IsFlowChartOriented R L r) {ψ : ℂ → ℂ} (hψ : IsCfJordan R L r ψ)
    (hU : IsChangeConfigInc R L' r') (hU0 : (0 : ℂ) ∉ closure (changePocket R L' r'))
    (hsub : cfPocket R L' r' ⊆ cfPocket R L r) {b s₁ s₂ : ℝ}
    (h₁ : s₁ ∈ Ioo (rightLo R L' r') (rightHi R L' r')) (h₁x : wallPt R s₁ ≠ cfPt (openPt R L r))
    (hb₁ : b ≤ (ψ (wallPt R s₁)).re) (h₂ : s₂ ∈ Ioc (rightLo R L' r') 1)
    (h₂C : wallPt R s₂ ∈ closure (cfPocket R L r)) (h₂x : wallPt R s₂ ≠ cfPt (openPt R L r))
    (hb₂ : (ψ (wallPt R s₂)).re ≤ b) :
    ∃ s ∈ Ioo (rightLo R L' r') (rightHi R L' r'), s₂ ≤ s ∧ ψ (wallPt R s) = (b : ℂ) := by
  obtain ⟨-, hv, -, -, -, -, -, -⟩ := h.changeCorner_props
  obtain ⟨hu', hv', -, -, -, -, -, -⟩ := hU.changeCorner_props
  have hu0 := h.rightLo_pos h0
  have hIC : ∀ s, s ∈ Ioc (0 : ℝ) 1 → wallPt R s ∈ closure (cfPocket R L r) → wallPt R s ≠ cfPt (openPt R L r) →
      s ∈ Ioc (rightLo R L r) (rightHi R L r) := fun s hs hm hx => by
    have hI := mem_Icc_right_of_mem_closure h h0 hs hm
    refine ⟨lt_of_le_of_ne hI.1 fun he => hx ?_, hI.2⟩
    rw [← he]; rfl
  have h₁01 : s₁ ∈ Ioc (0 : ℝ) 1 := ⟨hu'.1.trans_lt h₁.1, h₁.2.le.trans hv'.2⟩
  have h₂01 : s₂ ∈ Ioc (0 : ℝ) 1 := ⟨hu'.1.trans_lt h₂.1, h₂.2⟩
  have h₁C := hIC s₁ h₁01 (wallPt_right_mem_closure hU hU0 hsub ⟨h₁.1.le, h₁.2.le⟩) h₁x
  have h₂C' := hIC s₂ h₂01 h₂C h₂x
  obtain ⟨hfacts, hcont, hmono⟩ := right_arc_facts h h0 hor hψ
  have h21 : s₂ ≤ s₁ := by
    by_contra hlt
    push Not at hlt
    have := hmono h₁C h₂C' hlt
    linarith
  have hcI : ContinuousOn (fun s => (ψ (wallPt R s)).re) (Icc s₂ s₁) :=
    (Complex.continuous_re.comp_continuousOn hcont).mono fun s hs => ⟨h₂C'.1.trans_le hs.1, hs.2.trans h₁C.2⟩
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc h21 hcI ⟨hb₂, hb₁⟩
  have hsC : s ∈ Ioc (rightLo R L r) (rightHi R L r) := ⟨h₂C'.1.trans_le hs.1, hs.2.trans h₁C.2⟩
  refine ⟨s, ⟨h₂.1.trans_le hs.1, hs.2.trans_lt h₁.2⟩, hs.1, Complex.ext ?_ ?_⟩
  · rw [Complex.ofReal_re]; exact he
  · rw [Complex.ofReal_im]; exact (hfacts s hsC).2

/-! ### Points of the open shared arc are non-corner points of `∂U` -/

/-- **A point of `U`'s open left arc (shared with `C`) is a non-corner point of `∂U`.** -/
theorem nonCorner_of_left_open (h : IsChangeConfigInc R L r) (hU : IsChangeConfigInc R' L r')
    (hU0 : (0 : ℂ) ∉ closure (changePocket R' L r')) {θ : ℝ} (hθ : θ ∈ Ioo (leftLo R' L r') (leftHi R' L r')) :
    wallPt L θ ∈ frontier (cfPocket R' L r') ∧
      wallPt L θ ∉ closure (frontier (cfPocket R' L r') ∩ cfPocket R L r) ∧ wallPt L θ ≠ cfPt (openPt R' L r') := by
  have hUc := hU.isCfPocket hU0
  obtain ⟨-, -, -, -, hb', hab', -, -⟩ := hU.changeCorner_props
  have ha0' := hU.leftLo_pos hU0
  obtain ⟨v, hv, hve⟩ := PocketMarks.exists_affine_eq hθ
  have hpt : cfArcL R' L r' v = wallPt L θ := by
    show cfPt (toDisc (Lemma71I.realPath L) (leftLo R' L r' + v * (leftHi R' L r' - leftLo R' L r'))) = _
    rw [hve]
  have hnotR : ∀ w ∈ Icc (0 : ℝ) 1, cfArcR R' L r' w ≠ wallPt L θ := by
    intro w hw he
    rw [← hpt] at he
    rcases hw.1.lt_or_eq with hw0 | hw0
    · rcases hw.2.lt_or_eq with hw1 | hw1
      · exact hUc.sides w ⟨hw0, hw1⟩ v hv he
      · rw [hw1, ← hUc.seed] at he
        have := hUc.inj₂ ⟨zero_le_one, le_rfl⟩ ⟨hv.1.le, hv.2.le⟩ he
        linarith [hv.2]
    · rw [← hw0, ← hUc.junction] at he
      have := hUc.inj₂ ⟨le_rfl, zero_le_one⟩ ⟨hv.1.le, hv.2.le⟩ he
      linarith [hv.1]
  have hfrU : frontier (cfPocket R' L r') ∩ cfPocket R L r ⊆ cfArcR R' L r' '' Icc 0 1 := by
    rintro z ⟨hz, hzC⟩
    rw [hUc.frontier_eq] at hz
    rcases hz with hz | ⟨w, hw, rfl⟩
    · exact hz
    · exfalso
      have hm := (IsChangeConfigInc.affine_mem hab').1 hw
      exact wallPt_notMem h (Or.inr rfl) ⟨ha0'.trans_le hm.1, hm.2.trans hb'.2⟩ hzC
  have hcl : IsClosed (cfArcR R' L r' '' Icc 0 1) := (isCompact_Icc.image_of_continuousOn hUc.cont₁).isClosed
  refine ⟨?_, fun hm => ?_, fun he => ?_⟩
  · rw [hUc.frontier_eq]; exact Or.inr ⟨v, Ioo_subset_Icc_self hv, hpt⟩
  · obtain ⟨w, hw, hwe⟩ := hcl.closure_subset_iff.2 hfrU hm
    exact hnotR w hw hwe
  · exact hnotR 0 ⟨le_rfl, zero_le_one⟩ (by
      show cfPt (toDisc (Lemma71I.realPath R') (rightLo R' L r' + 0 * (rightHi R' L r' - rightLo R' L r'))) = _
      rw [zero_mul, add_zero, he]; rfl)

/-- **A point of `U`'s open right arc (shared with `C`) is a non-corner point of `∂U`.** -/
theorem nonCorner_of_right_open (h : IsChangeConfigInc R L r) (hU : IsChangeConfigInc R L' r')
    (hU0 : (0 : ℂ) ∉ closure (changePocket R L' r')) {s : ℝ} (hs : s ∈ Ioo (rightLo R L' r') (rightHi R L' r')) :
    wallPt R s ∈ frontier (cfPocket R L' r') ∧
      wallPt R s ∉ closure (frontier (cfPocket R L' r') ∩ cfPocket R L r) ∧ wallPt R s ≠ cfPt (openPt R L' r') := by
  have hUc := hU.isCfPocket hU0
  obtain ⟨-, hv', huv', -, -, -, -, -⟩ := hU.changeCorner_props
  have hu0' := hU.rightLo_pos hU0
  obtain ⟨v, hv, hve⟩ := PocketMarks.exists_affine_eq hs
  have hpt : cfArcR R L' r' v = wallPt R s := by
    show cfPt (toDisc (Lemma71I.realPath R) (rightLo R L' r' + v * (rightHi R L' r' - rightLo R L' r'))) = _
    rw [hve]
  have hnotL : ∀ w ∈ Icc (0 : ℝ) 1, cfArcL R L' r' w ≠ wallPt R s := by
    intro w hw he
    rw [← hpt] at he
    rcases hw.1.lt_or_eq with hw0 | hw0
    · rcases hw.2.lt_or_eq with hw1 | hw1
      · exact hUc.sides v hv w ⟨hw0, hw1⟩ he.symm
      · rw [hw1, hUc.seed] at he
        have := hUc.inj₁ ⟨zero_le_one, le_rfl⟩ ⟨hv.1.le, hv.2.le⟩ he
        linarith [hv.2]
    · rw [← hw0, hUc.junction] at he
      have := hUc.inj₁ ⟨le_rfl, zero_le_one⟩ ⟨hv.1.le, hv.2.le⟩ he
      linarith [hv.1]
  have hfrU : frontier (cfPocket R L' r') ∩ cfPocket R L r ⊆ cfArcL R L' r' '' Icc 0 1 := by
    rintro z ⟨hz, hzC⟩
    rw [hUc.frontier_eq] at hz
    rcases hz with ⟨w, hw, rfl⟩ | hz
    · exfalso
      have hm := (IsChangeConfigInc.affine_mem huv').1 hw
      exact wallPt_notMem h (Or.inl rfl) ⟨hu0'.trans_le hm.1, hm.2.trans hv'.2⟩ hzC
    · exact hz
  have hcl : IsClosed (cfArcL R L' r' '' Icc 0 1) := (isCompact_Icc.image_of_continuousOn hUc.cont₂).isClosed
  refine ⟨?_, fun hm => ?_, fun he => ?_⟩
  · rw [hUc.frontier_eq]; exact Or.inl ⟨v, Ioo_subset_Icc_self hv, hpt⟩
  · obtain ⟨w, hw, hwe⟩ := hcl.closure_subset_iff.2 hfrU hm
    exact hnotL w hw hwe
  · have h0 : cfArcR R L' r' 0 = wallPt R s := by
      show cfPt (toDisc (Lemma71I.realPath R) (rightLo R L' r' + 0 * (rightHi R L' r' - rightLo R L' r'))) = _
      rw [zero_mul, add_zero, he]; rfl
    rw [← hpt] at h0
    have := hUc.inj₁ ⟨le_rfl, zero_le_one⟩ ⟨hv.1.le, hv.2.le⟩ h0
    linarith [hv.1]

end InteractingSLE.Sec7.R6Fd
