/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FdArc
import InteractingSLE.Spec.Sec7.PocketSeedOpen

/-!
# Wall points of a change pocket opening at the flow seed in its Jordan coordinate

Packet PROVE-R6-FACE3. The analogues of `R6FdArc` for an outer pocket `C = cfPocket R L r` opening at the flow seed
(`rightLo = leftLo = 0`; `C` is unbounded in the counterflow chart, its Jordan coordinate `ψ` is
`Sec6.IsJordanCoordInf` with `y₀ ↦ 0` and `ψ → ∞` at `∞`):

* `le_leftHi_of_mem_closureInf` / `le_rightHi_of_mem_closureInf`: a wall point in `closure C` has its parameter
  at most the closing corner's;
* `left_arc_factsInf` / `right_arc_factsInf`: `θ ↦ ψ(ℓ_L(θ))` is real, continuous, strictly decreasing on
  `(0, leftHi]`; `s ↦ ψ(ℓ_R(s))` real, continuous, strictly increasing on `(0, rightHi]`;
* `extension_psi_eqInf`: the inverse extension inverts `ψ` on `closure C`;
* `exists_left_param_of_betweenInf` / `exists_right_param_of_betweenInf`: the IVT step for a bounded nested pocket.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Function
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal

namespace InteractingSLE.Sec7.R6Fd

open WangWu PocketCoord Lemma71I PocketJordan PocketWordAssembly PocketSeedOpen

variable {R L R' L' : ℝ≥0 → ℂ} {r r' : ℝ≥0}

/-- A parameter in `(0, hi]` is `hi / (1 + v)` for some `v ≥ 0`. -/
theorem exists_div_one_add_eq {hi θ : ℝ} (hθ : θ ∈ Ioc 0 hi) : ∃ v ∈ Ici (0 : ℝ), hi / (1 + v) = θ := by
  have hθ0 := hθ.1
  refine ⟨hi / θ - 1, mem_Ici.2 (by rw [sub_nonneg, le_div_iff₀ hθ0, one_mul]; exact hθ.2), ?_⟩
  rw [add_sub_cancel, div_div_cancel₀ (hθ0.trans_le hθ.2).ne']

/-- `hi / (1 + v)` lies in `(0, hi]` for `v ≥ 0` and `hi > 0`. -/
theorem div_one_add_mem {hi v : ℝ} (hhi : 0 < hi) (hv : v ∈ Ici (0 : ℝ)) : hi / (1 + v) ∈ Ioc 0 hi := by
  have h1 : 0 < 1 + v := by linarith [mem_Ici.1 hv]
  exact ⟨div_pos hhi h1, div_le_self hhi.le (by linarith [mem_Ici.1 hv])⟩

/-! ### The arc intervals -/

/-- **A left-wall point in the closed pocket opening at the flow seed has parameter `≤ leftHi`.** -/
theorem le_leftHi_of_mem_closureInf (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    {θ : ℝ} (hθ : θ ∈ Ioc (0 : ℝ) 1) (hm : wallPt L θ ∈ closure (cfPocket R L r)) : θ ≤ leftHi R L r := by
  have hC := h.isCfPocketInf h0
  have hfr : wallPt L θ ∈ frontier (cfPocket R L r) :=
    ⟨hm, by rw [hC.isOpen.interior_eq]; exact wallPt_notMem h (Or.inr rfl) hθ⟩
  obtain ⟨hu, hv, huv, ha, hb, hab, hLa, hLb⟩ := h.changeCorner_props
  have ha0 := h.leftLo_eq_zero_of_rightLo_eq_zero h0
  have hg := h.changeCorners.1
  have hhiR : 0 < rightHi R L r := h0 ▸ huv
  have hhiL : 0 < leftHi R L r := ha0 ▸ hab
  have hcL := h.isDiscCrosscut_left
  rw [hC.frontier_eq] at hfr
  rcases hfr with ⟨v, hv1, hve⟩ | ⟨v, hv1, hve⟩
  · have hs := div_one_add_mem hhiR hv1
    have hs01 : rightHi R L r / (1 + v) ∈ Ioc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans hv.2⟩
    have he : toDisc (Lemma71I.realPath R) (rightHi R L r / (1 + v)) = toDisc (Lemma71I.realPath L) θ :=
      injOn_cfPt (toDisc_ne_neg_one h.right hs01) (toDisc_ne_neg_one h.left hθ) hve
    have hcs : rightHi R L r / (1 + v) ∈ Sec7.pocketContactSet (toDisc (Lemma71I.realPath R))
        (toDisc (Lemma71I.realPath L)) := ⟨⟨hs01.1.le, hs01.2⟩, θ, ⟨hθ.1.le, hθ.2⟩, he.symm⟩
    have hend : rightHi R L r / (1 + v) = rightHi R L r := by
      by_contra hne
      exact hg.2.2.2 _ ⟨by rw [h0]; exact hs.1, lt_of_le_of_ne hs.2 hne⟩ hcs
    have hθe : toDisc (Lemma71I.realPath L) θ = toDisc (Lemma71I.realPath L) (leftHi R L r) := by
      rw [← he, hend, hLb]; rfl
    rw [hcL.inj ⟨hθ.1.le, hθ.2⟩ hb hθe]
  · have hs := div_one_add_mem hhiL hv1
    have hs01 : leftHi R L r / (1 + v) ∈ Ioc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans hb.2⟩
    rw [← wallPt_injOn h.left hs01 hθ hve]
    exact hs.2

/-- **A right-wall point in the closed pocket opening at the flow seed has parameter `≤ rightHi`.** -/
theorem le_rightHi_of_mem_closureInf (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) (hm : wallPt R s ∈ closure (cfPocket R L r)) : s ≤ rightHi R L r := by
  have hC := h.isCfPocketInf h0
  have hfr : wallPt R s ∈ frontier (cfPocket R L r) :=
    ⟨hm, by rw [hC.isOpen.interior_eq]; exact wallPt_notMem h (Or.inl rfl) hs⟩
  obtain ⟨hu, hv, huv, ha, hb, hab, hLa, hLb⟩ := h.changeCorner_props
  have ha0 := h.leftLo_eq_zero_of_rightLo_eq_zero h0
  have hgL := h.changeCorners.2.2.2.1
  have hhiR : 0 < rightHi R L r := h0 ▸ huv
  have hhiL : 0 < leftHi R L r := ha0 ▸ hab
  have hcR := h.isDiscCrosscut_right
  rw [hC.frontier_eq] at hfr
  rcases hfr with ⟨v, hv1, hve⟩ | ⟨v, hv1, hve⟩
  · have hs' := div_one_add_mem hhiR hv1
    have hs01 : rightHi R L r / (1 + v) ∈ Ioc (0 : ℝ) 1 := ⟨hs'.1, hs'.2.trans hv.2⟩
    rw [← wallPt_injOn h.right hs01 hs hve]
    exact hs'.2
  · have ht := div_one_add_mem hhiL hv1
    have ht01 : leftHi R L r / (1 + v) ∈ Ioc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hb.2⟩
    have he : toDisc (Lemma71I.realPath L) (leftHi R L r / (1 + v)) = toDisc (Lemma71I.realPath R) s :=
      injOn_cfPt (toDisc_ne_neg_one h.left ht01) (toDisc_ne_neg_one h.right hs) hve
    have hcs : leftHi R L r / (1 + v) ∈ Sec7.pocketContactSet (toDisc (Lemma71I.realPath L))
        (toDisc (Lemma71I.realPath R)) := ⟨⟨ht01.1.le, ht01.2⟩, s, ⟨hs.1.le, hs.2⟩, he.symm⟩
    have hend : leftHi R L r / (1 + v) = leftHi R L r := by
      by_contra hne
      exact hgL.2.2.2 _ ⟨by rw [ha0]; exact ht.1, lt_of_le_of_ne ht.2 hne⟩ hcs
    have hse : toDisc (Lemma71I.realPath R) s = toDisc (Lemma71I.realPath R) (rightHi R L r) := by
      rw [← he, hend, hLb]; rfl
    rw [hcR.inj ⟨hs.1.le, hs.2⟩ hv hse]

/-! ### The coordinate along one wall -/

/-- **The coordinate along the left arc** (pocket opening at the flow seed): real, continuous and strictly
decreasing on `(0, leftHi]`. -/
theorem left_arc_factsInf (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hor : PocketMarks.IsFlowChartOriented R L r) {ψ : ℂ → ℂ} (hψ : IsCfJordanInf R L r ψ) :
    (∀ θ ∈ Ioc 0 (leftHi R L r), wallPt L θ ∈ closure (cfPocket R L r) ∧ (ψ (wallPt L θ)).im = 0) ∧
    ContinuousOn (fun θ => ψ (wallPt L θ)) (Ioc 0 (leftHi R L r)) ∧
    StrictAntiOn (fun θ => (ψ (wallPt L θ)).re) (Ioc 0 (leftHi R L r)) := by
  obtain ⟨-, -, -, -, hb, hab, -, hLb⟩ := h.changeCorner_props
  have ha0 := h.leftLo_eq_zero_of_rightLo_eq_zero h0
  have hhiL : 0 < leftHi R L r := ha0 ▸ hab
  have hC := h.isCfPocketInf h0
  have hI : Ioc 0 (leftHi R L r) ⊆ Ioc 0 1 := fun θ hθ => ⟨hθ.1, hθ.2.trans hb.2⟩
  have hy₀ : cfPt (closePt R L r) = wallPt L (leftHi R L r) := by
    show cfPt _ = cfPt (toDisc (Lemma71I.realPath L) (leftHi R L r)); rw [hLb]
  have hfr : ∀ θ ∈ Ioc 0 (leftHi R L r), wallPt L θ ∈ frontier (cfPocket R L r) := by
    intro θ hθ
    obtain ⟨v, hv, hve⟩ := exists_div_one_add_eq hθ
    rw [hC.frontier_eq]
    exact Or.inr ⟨v, hv, by rw [← hve]; rfl⟩
  have hfacts : ∀ θ ∈ Ioc 0 (leftHi R L r), wallPt L θ ∈ closure (cfPocket R L r) ∧ (ψ (wallPt L θ)).im = 0 :=
    fun θ hθ => ⟨frontier_subset_closure (hfr θ hθ), hψ.2.2.2.2.1 _ (hfr θ hθ)⟩
  have hcont : ContinuousOn (fun θ => ψ (wallPt L θ)) (Ioc 0 (leftHi R L r)) :=
    hψ.1.comp ((continuousOn_wallPt h.left).mono hI) fun θ hθ => (hfacts θ hθ).1
  have hinj : InjOn (fun θ => (ψ (wallPt L θ)).re) (Ioc 0 (leftHi R L r)) := by
    intro θ hθ θ' hθ' he
    have : ψ (wallPt L θ) = ψ (wallPt L θ') := Complex.ext he (by rw [(hfacts θ hθ).2, (hfacts θ' hθ').2])
    exact wallPt_injOn h.left (hI hθ) (hI hθ') (hψ.2.1 (hfacts θ hθ).1 (hfacts θ' hθ').1 this)
  have hpos : ∀ θ ∈ Ioo 0 (leftHi R L r), 0 < (ψ (wallPt L θ)).re := fun θ hθ =>
    (SideAnc.jordanInf_sides h h0 hor hψ).2 θ (by rw [ha0]; exact hθ)
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

/-- **The coordinate along the right arc** (pocket opening at the flow seed): real, continuous and strictly
increasing on `(0, rightHi]`. -/
theorem right_arc_factsInf (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hor : PocketMarks.IsFlowChartOriented R L r) {ψ : ℂ → ℂ} (hψ : IsCfJordanInf R L r ψ) :
    (∀ s ∈ Ioc 0 (rightHi R L r), wallPt R s ∈ closure (cfPocket R L r) ∧ (ψ (wallPt R s)).im = 0) ∧
    ContinuousOn (fun s => ψ (wallPt R s)) (Ioc 0 (rightHi R L r)) ∧
    StrictMonoOn (fun s => (ψ (wallPt R s)).re) (Ioc 0 (rightHi R L r)) := by
  obtain ⟨-, hv, huv, -, -, -, -, -⟩ := h.changeCorner_props
  have hhiR : 0 < rightHi R L r := h0 ▸ huv
  have hC := h.isCfPocketInf h0
  have hI : Ioc 0 (rightHi R L r) ⊆ Ioc 0 1 := fun θ hθ => ⟨hθ.1, hθ.2.trans hv.2⟩
  have hy₀ : cfPt (closePt R L r) = wallPt R (rightHi R L r) := rfl
  have hfr : ∀ s ∈ Ioc 0 (rightHi R L r), wallPt R s ∈ frontier (cfPocket R L r) := by
    intro s hs
    obtain ⟨v, hv', hve⟩ := exists_div_one_add_eq hs
    rw [hC.frontier_eq]
    exact Or.inl ⟨v, hv', by rw [← hve]; rfl⟩
  have hfacts : ∀ s ∈ Ioc 0 (rightHi R L r), wallPt R s ∈ closure (cfPocket R L r) ∧ (ψ (wallPt R s)).im = 0 :=
    fun s hs => ⟨frontier_subset_closure (hfr s hs), hψ.2.2.2.2.1 _ (hfr s hs)⟩
  have hcont : ContinuousOn (fun s => ψ (wallPt R s)) (Ioc 0 (rightHi R L r)) :=
    hψ.1.comp ((continuousOn_wallPt h.right).mono hI) fun s hs => (hfacts s hs).1
  have hinj : InjOn (fun s => (ψ (wallPt R s)).re) (Ioc 0 (rightHi R L r)) := by
    intro s hs s' hs' he
    have : ψ (wallPt R s) = ψ (wallPt R s') := Complex.ext he (by rw [(hfacts s hs).2, (hfacts s' hs').2])
    exact wallPt_injOn h.right (hI hs) (hI hs') (hψ.2.1 (hfacts s hs).1 (hfacts s' hs').1 this)
  have hneg : ∀ s ∈ Ioo 0 (rightHi R L r), (ψ (wallPt R s)).re < 0 := fun s hs =>
    (SideAnc.jordanInf_sides h h0 hor hψ).1 s (by rw [h0]; exact hs)
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

/-- **The continuous inverse extension inverts a Jordan coordinate at infinity on `closure C`.** -/
theorem extension_psi_eqInf {C : Set ℂ} {y₀ : ℂ} {ψ E₀ : ℂ → ℂ} (hψ : Sec6.IsJordanCoordInf C y₀ ψ)
    (hE₀ : EqOn E₀ (invFunOn ψ C) H) (hE₀c : ContinuousOn E₀ Hbar) {p : ℂ} (hp : p ∈ closure C) :
    E₀ (ψ p) = p := by
  have hb : (𝓝[C] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hp
  have hψH : ∀ z ∈ C, ψ z ∈ H := fun z hz => hψ.2.2.2.1.2.mapsTo hz
  have h1 : Tendsto ψ (𝓝[C] p) (𝓝[Hbar] (ψ p)) :=
    tendsto_nhdsWithin_iff.2 ⟨((hψ.1 p hp).mono subset_closure).tendsto,
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

/-- **Shared left wall, outer pocket opening at the flow seed**: the IVT step of `exists_left_param_of_between`. -/
theorem exists_left_param_of_betweenInf (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hor : PocketMarks.IsFlowChartOriented R L r) {ψ : ℂ → ℂ} (hψ : IsCfJordanInf R L r ψ)
    (hU : IsChangeConfigInc R' L r') (hU0 : (0 : ℂ) ∉ closure (changePocket R' L r'))
    (hsub : cfPocket R' L r' ⊆ cfPocket R L r) {b θ₁ θ₂ : ℝ}
    (h₁ : θ₁ ∈ Ioo (leftLo R' L r') (leftHi R' L r')) (hb₁ : (ψ (wallPt L θ₁)).re ≤ b)
    (h₂ : θ₂ ∈ Ioc (leftLo R' L r') 1) (h₂C : wallPt L θ₂ ∈ closure (cfPocket R L r))
    (hb₂ : b ≤ (ψ (wallPt L θ₂)).re) :
    ∃ θ ∈ Ioo (leftLo R' L r') (leftHi R' L r'), θ₂ ≤ θ ∧ ψ (wallPt L θ) = (b : ℂ) := by
  obtain ⟨-, -, -, ha', hb', -, -, -⟩ := hU.changeCorner_props
  have h₁01 : θ₁ ∈ Ioc (0 : ℝ) 1 := ⟨ha'.1.trans_lt h₁.1, h₁.2.le.trans hb'.2⟩
  have h₂01 : θ₂ ∈ Ioc (0 : ℝ) 1 := ⟨ha'.1.trans_lt h₂.1, h₂.2⟩
  have h₁C : θ₁ ∈ Ioc 0 (leftHi R L r) :=
    ⟨h₁01.1, le_leftHi_of_mem_closureInf h h0 h₁01 (wallPt_left_mem_closure hU hU0 hsub ⟨h₁.1.le, h₁.2.le⟩)⟩
  have h₂C' : θ₂ ∈ Ioc 0 (leftHi R L r) := ⟨h₂01.1, le_leftHi_of_mem_closureInf h h0 h₂01 h₂C⟩
  obtain ⟨hfacts, hcont, hanti⟩ := left_arc_factsInf h h0 hor hψ
  have h21 : θ₂ ≤ θ₁ := by
    by_contra hlt
    push Not at hlt
    have := hanti h₁C h₂C' hlt
    linarith
  have hcI : ContinuousOn (fun θ => (ψ (wallPt L θ)).re) (Icc θ₂ θ₁) :=
    (Complex.continuous_re.comp_continuousOn hcont).mono fun θ hθ => ⟨h₂C'.1.trans_le hθ.1, hθ.2.trans h₁C.2⟩
  obtain ⟨θ, hθ, he⟩ := intermediate_value_Icc' h21 hcI ⟨hb₁, hb₂⟩
  have hθC : θ ∈ Ioc 0 (leftHi R L r) := ⟨h₂C'.1.trans_le hθ.1, hθ.2.trans h₁C.2⟩
  refine ⟨θ, ⟨h₂.1.trans_le hθ.1, hθ.2.trans_lt h₁.2⟩, hθ.1, Complex.ext ?_ ?_⟩
  · rw [Complex.ofReal_re]; exact he
  · rw [Complex.ofReal_im]; exact (hfacts θ hθC).2

/-- **Shared right wall, outer pocket opening at the flow seed**: the IVT step of `exists_right_param_of_between`. -/
theorem exists_right_param_of_betweenInf (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hor : PocketMarks.IsFlowChartOriented R L r) {ψ : ℂ → ℂ} (hψ : IsCfJordanInf R L r ψ)
    (hU : IsChangeConfigInc R L' r') (hU0 : (0 : ℂ) ∉ closure (changePocket R L' r'))
    (hsub : cfPocket R L' r' ⊆ cfPocket R L r) {b s₁ s₂ : ℝ}
    (h₁ : s₁ ∈ Ioo (rightLo R L' r') (rightHi R L' r')) (hb₁ : b ≤ (ψ (wallPt R s₁)).re)
    (h₂ : s₂ ∈ Ioc (rightLo R L' r') 1) (h₂C : wallPt R s₂ ∈ closure (cfPocket R L r))
    (hb₂ : (ψ (wallPt R s₂)).re ≤ b) :
    ∃ s ∈ Ioo (rightLo R L' r') (rightHi R L' r'), s₂ ≤ s ∧ ψ (wallPt R s) = (b : ℂ) := by
  obtain ⟨hu', hv', -, -, -, -, -, -⟩ := hU.changeCorner_props
  have h₁01 : s₁ ∈ Ioc (0 : ℝ) 1 := ⟨hu'.1.trans_lt h₁.1, h₁.2.le.trans hv'.2⟩
  have h₂01 : s₂ ∈ Ioc (0 : ℝ) 1 := ⟨hu'.1.trans_lt h₂.1, h₂.2⟩
  have h₁C : s₁ ∈ Ioc 0 (rightHi R L r) :=
    ⟨h₁01.1, le_rightHi_of_mem_closureInf h h0 h₁01 (wallPt_right_mem_closure hU hU0 hsub ⟨h₁.1.le, h₁.2.le⟩)⟩
  have h₂C' : s₂ ∈ Ioc 0 (rightHi R L r) := ⟨h₂01.1, le_rightHi_of_mem_closureInf h h0 h₂01 h₂C⟩
  obtain ⟨hfacts, hcont, hmono⟩ := right_arc_factsInf h h0 hor hψ
  have h21 : s₂ ≤ s₁ := by
    by_contra hlt
    push Not at hlt
    have := hmono h₁C h₂C' hlt
    linarith
  have hcI : ContinuousOn (fun s => (ψ (wallPt R s)).re) (Icc s₂ s₁) :=
    (Complex.continuous_re.comp_continuousOn hcont).mono fun s hs => ⟨h₂C'.1.trans_le hs.1, hs.2.trans h₁C.2⟩
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc h21 hcI ⟨hb₂, hb₁⟩
  have hsC : s ∈ Ioc 0 (rightHi R L r) := ⟨h₂C'.1.trans_le hs.1, hs.2.trans h₁C.2⟩
  refine ⟨s, ⟨h₂.1.trans_le hs.1, hs.2.trans_lt h₁.2⟩, hs.1, Complex.ext ?_ ?_⟩
  · rw [Complex.ofReal_re]; exact he
  · rw [Complex.ofReal_im]; exact (hfacts s hsC).2

end InteractingSLE.Sec7.R6Fd
