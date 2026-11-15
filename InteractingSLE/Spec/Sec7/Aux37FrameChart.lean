/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37AssemblyBridge
import InteractingSLE.Spec.Sec7.Aux119LiftRandom
import InteractingSLE.Spec.Sec7.PocketLeftFrontier

/-!
# Aux. lemma 37's witness frame: the flow chart and its collar bands

Packet PROVE-STRIPSYS40. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L104–L136,
pp. 198–200): "use the accessible `C`-side collar of the whole incoming segment".

* **`exists_isFlowChart_of_cfAvoid`** (frame field (F0)): a flow chart of the change pocket exists and the pocket lies
  on the left of the right wall, from the left frontier `β` (`L r = β r`), the visit of the right wall and the
  counterflow's avoidance of the open left side of `β` (pathwise; the measurable construction
  `Aux119Lift.exists_measurable_flowChart_branch` read on a one-point space).
* **`exists_band`**: for a conformal chart whose inverse has a limit inside an open set `O` at every point of a compact
  real set `K`, a whole band `{w ∈ ℍ : Re w ∈ K, Im w < δ}` is mapped into `O`.
* `IsFlowChart.tendsto_right`, `IsFlowChart.tendsto_left`: the chart inverse lands at the wall point `R(arcTime σ)`
  (resp. `L(arcTime σ)`) at the chart value of the disc parameter `σ` of the open right (left) arc, which is real.

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Function Complex
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open InteractingSLE.WangWu (negInv)
open scoped NNReal Real

namespace InteractingSLE.Sec7.Aux37Frame

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketOrientFact PocketWordAssembly PocketSeedOpen
  PocketLeftFrontier Aux119Bdry

variable {R L β : ℝ≥0 → ℂ} {r : ℝ≥0} {η : ℝ → ℂ}

/-! ### (F0) the flow chart and the pocket's side -/

section Chart

/-- **(F0): a flow chart of the change pocket, with the pocket on the left of the right wall** (pathwise), from the
left frontier `β` through the change point (`L r = β r`), the visit of every right-wall point by the counterflow, and
the counterflow's avoidance (read in `ℍ`, at rational times) of the open left side of `β`. -/
theorem exists_isFlowChart_of_cfAvoid (h : IsChangeConfigInc R L r) (hβ : IsSimpleProper β) (hLβ : L r = β r)
    (hvis : IsWallVisited R η) (hη : ContinuousOn η (Ici 0))
    (hav : ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η q) ∉ leftSideOf (range β)) :
    (∃ (Ψ : ℂ → ℂ) (c : Chart), IsFlowChart R L r Ψ c) ∧ changePocket R L r ⊆ leftSideOf (range R) := by
  have hor := isFlowChartOriented_of_cfAvoid h hβ hLβ hvis hη hav
  have hopen := Sec5.Cond44Ref.isOpen_leftSideOf_arcRange hβ.isProperArc
  rw [arcRange_realPath] at hopen
  have hd : Disjoint (range R) (leftSideOf (range β)) :=
    disjoint_range_of_isWallVisited hvis h.right.2.2.1 fun t ht => cfAvoid_of_rat hopen hη hav ht
  refine ⟨?_, h.changePocket_subset_leftSideOf (h.mem_leftSideOf_of_leftFrontier hβ hLβ hd)⟩
  obtain ⟨-, c, -, -, -, -, -, -, -, -, hflow, -⟩ :=
    Aux119Lift.exists_measurable_flowChart_branch (Ω := Unit) (R := fun _ => R) (L := fun _ => L) (r := r)
      (G := univ) (fun _ => measurable_const) (fun _ => measurable_const) MeasurableSet.univ (fun _ _ => h)
      (fun _ _ => hor)
  obtain ⟨Ψ, hΨ⟩ := hflow () trivial
  exact ⟨Ψ, c (), hΨ⟩

end Chart

/-! ### Collar bands of a conformal chart -/

section Band

/-- `|w − Re w| = |Im w|`. -/
theorem dist_re (w : ℂ) : dist w (w.re : ℂ) = |w.im| := by
  rw [Complex.dist_eq_re_im]
  simp only [ofReal_re, ofReal_im, sub_self, sub_zero]
  rw [show (0 : ℝ) ^ 2 + w.im ^ 2 = w.im ^ 2 by ring, Real.sqrt_sq_eq_abs]

/-- **A collar band of a conformal chart**: if at every point `q` of a compact real set `K` the chart inverse has a
limit inside an open set `O`, then for some `δ > 0` the inverse maps the whole band `{w ∈ ℍ : Re w ∈ K, Im w < δ}` into
`O`. -/
theorem exists_band {c : Chart} {K : Set ℝ} (hK : IsCompact K) {O : Set ℂ} (hO : IsOpen O)
    (hlim : ∀ q ∈ K, ∃ p ∈ O, Tendsto c.2.1 (𝓝[H] (q : ℂ)) (𝓝 p)) :
    ∃ δ > 0, ∀ w ∈ H, w.re ∈ K → w.im < δ → c.2.1 w ∈ O := by
  set U : Set ℂ := interior {w | w ∈ H → c.2.1 w ∈ O} with hU
  have hK' : IsCompact ((fun x : ℝ => (x : ℂ)) '' K) := hK.image continuous_ofReal
  have hKU : (fun x : ℝ => (x : ℂ)) '' K ⊆ U := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨p, hp, hl⟩ := hlim q hq
    have hmem : c.2.1 ⁻¹' O ∈ 𝓝[H] (q : ℂ) := hl (hO.mem_nhds hp)
    obtain ⟨t, htO, hqt, hts⟩ := mem_nhdsWithin.1 hmem
    exact interior_mono (fun w hw hwH => hts ⟨hw, hwH⟩) (mem_interior_iff_mem_nhds.2 (htO.mem_nhds hqt))
  obtain ⟨δ, hδ, hth⟩ := hK'.exists_thickening_subset_open isOpen_interior hKU
  refine ⟨δ, hδ, fun w hw hre him => ?_⟩
  have hwt : w ∈ thickening δ ((fun x : ℝ => (x : ℂ)) '' K) := by
    rw [mem_thickening_iff]
    refine ⟨(w.re : ℂ), ⟨w.re, hre, rfl⟩, ?_⟩
    rw [dist_re, abs_of_pos (show (0 : ℝ) < w.im from hw)]
    exact him
  exact interior_subset (hth hwt) hw

/-- The band `{w ∈ ℍ : Re w ∈ [a, b], Im w < δ}` is convex. -/
theorem convex_band (a b δ : ℝ) : Convex ℝ {w : ℂ | w ∈ H ∧ w.re ∈ Icc a b ∧ w.im < δ} := by
  intro w hw w' hw' s t hs ht hst
  obtain ⟨hwH, ⟨hwa, hwb⟩, hwδ⟩ := hw
  obtain ⟨hw'H, ⟨hw'a, hw'b⟩, hw'δ⟩ := hw'
  have hre : (s • w + t • w').re = s * w.re + t * w'.re := by simp
  have him : (s • w + t • w').im = s * w.im + t * w'.im := by simp
  have hwH' : (0 : ℝ) < w.im := hwH
  have hw'H' : (0 : ℝ) < w'.im := hw'H
  have hcomb : ∀ x y m : ℝ, m ≤ x → m ≤ y → m ≤ s * x + t * y := fun x y m hx hy => by
    have e : s * m + t * m = m := by rw [← add_mul, hst, one_mul]
    have := add_le_add (mul_le_mul_of_nonneg_left hx hs) (mul_le_mul_of_nonneg_left hy ht)
    linarith
  have hcomb' : ∀ x y m : ℝ, x ≤ m → y ≤ m → s * x + t * y ≤ m := fun x y m hx hy => by
    have e : s * m + t * m = m := by rw [← add_mul, hst, one_mul]
    have := add_le_add (mul_le_mul_of_nonneg_left hx hs) (mul_le_mul_of_nonneg_left hy ht)
    linarith
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · show (0 : ℝ) < (s • w + t • w').im
    rw [him]
    exact (lt_min hwH' hw'H').trans_le (hcomb _ _ _ (min_le_left _ _) (min_le_right _ _))
  · rw [hre]; exact hcomb _ _ _ hwa hw'a
  · rw [hre]; exact hcomb' _ _ _ hwb hw'b
  · rw [him]
    rcases lt_or_ge w.im w'.im with h | h
    · exact (hcomb' _ _ _ h.le le_rfl).trans_lt hw'δ
    · exact (hcomb' _ _ _ le_rfl h).trans_lt hwδ

end Band

/-! ### The chart values of the open arcs -/

section Arcs

variable {Ψ : ℂ → ℂ} {c : Chart}

/-- **The chart at an open right-arc point**: the disc point `toDisc (realPath R) σ`, `σ ∈ (rightLo, rightHi)`, has a
real positive chart value, and the chart inverse lands at the wall point `R(arcTime σ)` there. -/
theorem IsFlowChart.tendsto_right (hF : IsFlowChart R L r Ψ c) {σ : ℝ} (hσ : σ ∈ Ioo (rightLo R L r) (rightHi R L r)) :
    (Ψ (toDisc (realPath R) σ)).im = 0 ∧ 0 < (Ψ (toDisc (realPath R) σ)).re ∧
      Tendsto c.2.1 (𝓝[H] ((Ψ (toDisc (realPath R) σ)).re : ℂ)) (𝓝 (R (arcTime σ).toNNReal)) := by
  have h := hF.config
  obtain ⟨hu, hv, huv, -, -, -, -, -⟩ := h.changeCorner_props
  have hp : toDisc (realPath R) σ ∈ frontier (cayley '' changePocket R L r) := by
    rw [frontier_eq h]; exact Or.inl ⟨σ, ⟨hσ.1.le, hσ.2.le⟩, rfl⟩
  have hpq : toDisc (realPath R) σ ≠ closePt R L r := fun he =>
    hσ.2.ne (h.isDiscCrosscut_right.inj ⟨hu.1.trans hσ.1.le, hσ.2.le.trans hv.2⟩ hv he)
  have him := hF.unif.im_eq_zero (isOpen_cayley h) (closePt_notMem h) hp hpq
  have hre := hF.orient Ψ hF.unif σ hσ
  have hq : ((Ψ (toDisc (realPath R) σ)).re : ℂ) = Ψ (toDisc (realPath R) σ) := Complex.ext (by simp) (by simp [him])
  have hqH : ((Ψ (toDisc (realPath R) σ)).re : ℂ) ∈ Hbar := by
    show (0 : ℝ) ≤ ((Ψ (toDisc (realPath R) σ)).re : ℂ).im
    simp
  obtain ⟨z, hz, hΨz, hl⟩ := hF.exists_tendsto hqH
  have hpK : toDisc (realPath R) σ ∈ closure (cayley '' changePocket R L r) \ {closePt R L r} :=
    ⟨frontier_subset_closure hp, hpq⟩
  have hzp : z = toDisc (realPath R) σ := hF.unif.inj hz hpK (hΨz.trans hq)
  refine ⟨him, hre, ?_⟩
  rw [hzp, cayleyInv_toDisc h.right (hσ.2.trans_le hv.2)] at hl
  exact hl

/-- **The chart at an open left-arc point**: the disc point `toDisc (realPath L) σ`, `σ ∈ (leftLo, leftHi)`, has a real
negative chart value, and the chart inverse lands at the wall point `L(arcTime σ)` there. -/
theorem IsFlowChart.tendsto_left (hF : IsFlowChart R L r Ψ c) {σ : ℝ} (hσ : σ ∈ Ioo (leftLo R L r) (leftHi R L r)) :
    (Ψ (toDisc (realPath L) σ)).im = 0 ∧ (Ψ (toDisc (realPath L) σ)).re < 0 ∧
      Tendsto c.2.1 (𝓝[H] ((Ψ (toDisc (realPath L) σ)).re : ℂ)) (𝓝 (L (arcTime σ).toNNReal)) := by
  have h := hF.config
  obtain ⟨-, -, -, ha, hb, -, -, hLb⟩ := h.changeCorner_props
  have hp : toDisc (realPath L) σ ∈ frontier (cayley '' changePocket R L r) := by
    rw [frontier_eq h]; exact Or.inr ⟨σ, ⟨hσ.1.le, hσ.2.le⟩, rfl⟩
  have hpq : toDisc (realPath L) σ ≠ closePt R L r := fun he =>
    hσ.2.ne (h.isDiscCrosscut_left.inj ⟨ha.1.trans hσ.1.le, hσ.2.le.trans hb.2⟩ hb (he.trans hLb.symm))
  have him := hF.unif.im_eq_zero (isOpen_cayley h) (closePt_notMem h) hp hpq
  have hre := h.re_neg_left_of_re_pos hF.unif (hF.orient Ψ hF.unif) σ hσ
  have hq : ((Ψ (toDisc (realPath L) σ)).re : ℂ) = Ψ (toDisc (realPath L) σ) := Complex.ext (by simp) (by simp [him])
  have hqH : ((Ψ (toDisc (realPath L) σ)).re : ℂ) ∈ Hbar := by
    show (0 : ℝ) ≤ ((Ψ (toDisc (realPath L) σ)).re : ℂ).im
    simp
  obtain ⟨z, hz, hΨz, hl⟩ := hF.exists_tendsto hqH
  have hpK : toDisc (realPath L) σ ∈ closure (cayley '' changePocket R L r) \ {closePt R L r} :=
    ⟨frontier_subset_closure hp, hpq⟩
  have hzp : z = toDisc (realPath L) σ := hF.unif.inj hz hpK (hΨz.trans hq)
  refine ⟨him, hre, ?_⟩
  rw [hzp, cayleyInv_toDisc h.left (hσ.2.trans_le hb.2)] at hl
  exact hl

end Arcs

end InteractingSLE.Sec7.Aux37Frame
