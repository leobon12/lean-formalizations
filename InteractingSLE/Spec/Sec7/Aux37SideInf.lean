/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37SideAssembly

/-!
# Aux. lemma 37's witness frame in the pocket at the flow seed: generic frame fields and the reparametrized arcs

Packet PROVE-STRIPSYS42. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L104–L136,
pp. 198–200), the case `σ = T(x₀) = ∞` (the pocket's junction is the counterflow's target, `rightLo = 0`).

* **`witness_fields_visit`**: the frame fields (F2)–(F4) of `Aux37Frame.witness_fields`, from the visit data
  `IsArcVisit` instead of a bounded reverse-contained pocket (so they apply to both pocket shapes);
* `cfArcRInf_eq`, `cfArcLInf_eq`: at `rightLo = 0` the arms at infinity are the arcs reparametrized by
  `s = 1/(1 + v)`: `cfArcRInf v = cfArcR (1/(1 + v))`;
* **`isArcVisit_of_witnessInf`**: a rational witness at infinity (last-visit attachment, `u(r) < v < v₁ < v₂ < u(s)`)
  gives the visit data of the reparametrized arc at `(1/(1+v₂), 1/(1+v₁), 1/(1+v))`;
* `land_ne_zero_of_rightLo_eq_zero`, `isArcChart_rightInf`, `isArcChart_leftInf`: the reparametrized arcs as arc
  charts (`land c q = 0` only at the opening contact `q = 0`);
* `frontier_cfPocketInf_mem`: the frontier of the pocket at infinity in `ℍ` lies on the walls.

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Function Complex
open QuantumZipper (H Hbar fwdHull fwdMap)
open QuantumZipper.CA (cayley cayleyInv)
open InteractingSLE.WangWu (negInv)
open scoped NNReal Real

namespace InteractingSLE.Sec7.Aux37Side

open WangWu Lemma71I PocketCoord PocketJordan Aux119Bdry Lemma71O Aux37Frame StripPocketPath

/-! ### The frame fields from the visit data -/

section Fields

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {A : ℝ → ℂ}

/-- **The frame fields (F2), (F3), (F4) at a witness point, from the visit data** (as `Aux37Frame.witness_fields`, for
`x ∈ (v, v₂)`; generic in the pocket shape). -/
theorem witness_fields_visit {r₀ s₀ a₀ v v₂ : ℝ} (hV : IsArcVisit W η C A r₀ s₀ a₀ v v₂) (hCo : IsOpen C) {P : Set ℂ}
    (hCP : C = negInv '' P) (hPH : P ⊆ H) {X Y : ℝ≥0 → ℂ} (hX : IsSimpleProper X) (hY : IsSimpleProper Y)
    {Wu : Set ℂ} (hWu : Wu ⊆ range X ∪ range Y) (hPW : Disjoint P Wu)
    (hfr : ∀ y ∈ frontier C, y ∈ H → negInv y ∈ Wu) {lo hi : ℝ} (hlo : 0 ≤ lo) (hlh : lo < hi) (hhi : hi ≤ 1)
    (hAX : ∀ u ∈ Ioo (0 : ℝ) 1, negInv (A u) = X (arcTime (lo + u * (hi - lo))).toNNReal)
    {c : Chart} (hc : c.IsConformal) (hcP : MapsTo c.2.1 H P) {f : ℝ → ℝ}
    (hfc : ContinuousOn f (Ioo 0 1)) (hfi : InjOn f (Ioo 0 1))
    (hlim : ∀ u ∈ Ioo (0 : ℝ) 1, Tendsto c.2.1 (𝓝[H] (f u : ℂ)) (𝓝 (X (arcTime (lo + u * (hi - lo))).toNNReal)))
    {x : ℝ} (hx : x ∈ Ioo v v₂) (hY₀ : negInv (A x) ∉ range Y) :
    (∃ ε > 0, negInv '' fwdHull W r₀ ∩ ball (negInv (A x)) ε = ∅) ∧ negInv (A x) ∈ negInv '' fwdHull W s₀ ∧
      (∃ ε > 0, Wu ∩ ball (negInv (A x)) ε ⊆ negInv '' fwdHull W s₀) ∧
      (map c.2.1 (𝓝[H] (f x : ℂ))).NeBot ∧ map c.2.1 (𝓝[H] (f x : ℂ)) ≤ 𝓝[P] (negInv (A x)) ∧
      map c.2.1 (𝓝[H] (f x : ℂ)) ≤ 𝓝[H \ (negInv '' fwdHull W s₀ ∪ Wu)] (negInv (A x)) ∧
      ∃ z ∈ H \ (negInv '' fwdHull W s₀ ∪ Wu),
        connectedComponentIn (H \ (negInv '' fwdHull W s₀ ∪ Wu)) z =
          connectedComponentIn (H \ (negInv '' fwdHull W r₀ ∪ Wu)) z ∧
        ∀ᶠ w in map c.2.1 (𝓝[H] (f x : ℂ)), w ∈ connectedComponentIn (H \ (negInv '' fwdHull W s₀ ∪ Wu)) z := by
  have hη := hV.trace
  have hW := hV.continuous_W
  have hr₀ : 0 ≤ r₀ := hV.nonneg
  have hs₀ : 0 ≤ s₀ := hr₀.trans hV.lt.le
  have ha₀v := hV.a₀_lt
  have ha₀ := hV.pos
  have hv₂1 := hV.lt_one
  have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hxV : x ∈ Icc a₀ v₂ := ⟨by linarith [hx.1], hx.2.le⟩
  have hAxr : A x ∈ H \ fwdHull W r₀ := hV.unvis_r x hxV
  have hAxH : A x ∈ H := hAxr.1
  have hhull_s : ∀ u ∈ Icc v v₂, negInv (A u) ∈ negInv '' fwdHull W s₀ := fun u hu => by
    refine mem_negInv_image.2 ?_
    rw [negInv_negInv]
    by_contra hK
    exact Sec6.notMem_domain_of_mem_trace hη hs₀ (hV.vis_s u hu)
      ⟨(hV.unvis_r u ⟨by linarith [hu.1], hu.2⟩).1, hK⟩
  have hdom : ∀ {t : ℝ}, ∀ u, A u ∈ H \ fwdHull W t → negInv (A u) ∈ H \ negInv '' fwdHull W t := fun u hu =>
    ⟨negInv_mem_H hu.1, fun hK => hu.2 (by rw [mem_negInv_image, negInv_negInv] at hK; exact hK)⟩
  -- (F2), (F3a)
  have hF2 : ∃ ε > 0, negInv '' fwdHull W r₀ ∩ ball (negInv (A x)) ε = ∅ := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (WangWu.isOpen_H_diff_negInv_fwdHull hW hr₀) _ (hdom x hAxr)
    exact ⟨ε, hε, eq_empty_of_forall_notMem fun z hz => (hball hz.2).2 hz.1⟩
  have hF3a := hhull_s x ⟨hx.1.le, hx.2.le⟩
  -- (F3b): the walls near `z₀`
  have hF3b : ∃ ε > 0, Wu ∩ ball (negInv (A x)) ε ⊆ negInv '' fwdHull W s₀ := by
    set σx := lo + x * (hi - lo) with hσx
    have hσxI := affine_mem_Ioo hlh hxI
    have hσx1 : σx < 1 := hσxI.2.trans_le hhi
    set t₀ : ℝ≥0 := (arcTime σx).toNNReal with ht₀
    have ht₀r : (t₀ : ℝ) = arcTime σx := Real.coe_toNNReal _ (arcTime_nonneg ⟨(hlo.trans hσxI.1.le), hσx1⟩)
    have hz₀ : negInv (A x) = X t₀ := hAX x hxI
    have hlo' : lo + v * (hi - lo) < σx := by
      have := mul_lt_mul_of_pos_right hx.1 (sub_pos.2 hlh); linarith
    have hhi' : σx < lo + v₂ * (hi - lo) := by
      have := mul_lt_mul_of_pos_right hx.2 (sub_pos.2 hlh); linarith
    have hdc : ContinuousAt WangWu.discTime (t₀ : ℝ) := by
      have h1 : (1 : ℝ) + t₀ ≠ 0 := by positivity
      exact continuousAt_id.div (continuousAt_const.add continuousAt_id) h1
    have hdt₀ : WangWu.discTime (t₀ : ℝ) = σx := by rw [ht₀r, WangWu.discTime_arcTime hσx1]
    have hnb : Ioo (lo + v * (hi - lo)) (lo + v₂ * (hi - lo)) ∈ 𝓝 (WangWu.discTime (t₀ : ℝ)) := by
      rw [hdt₀]; exact Ioo_mem_nhds hlo' hhi'
    obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhds_iff.1 (hdc hnb)
    obtain ⟨ε₂, hε₂, hR⟩ := exists_ball_range hX t₀ hδ
    obtain ⟨ε₁, hε₁, hYb⟩ := Metric.isOpen_iff.1 (Lemma71Pin.IsSimpleProper.isClosed_range hY).isOpen_compl _ hY₀
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun z ⟨hzW, hzb⟩ => ?_⟩
    rcases hWu hzW with ⟨t, rfl⟩ | hzY
    · have htd : dist t t₀ < δ := hR t (by rw [← hz₀]; exact ball_subset_ball (min_le_right _ _) hzb)
      have hσ := hδb (show (t : ℝ) ∈ ball (t₀ : ℝ) δ from htd)
      set u := (WangWu.discTime t - lo) / (hi - lo) with hu
      have hul : lo + u * (hi - lo) = WangWu.discTime t := by
        rw [hu]; field_simp [(sub_pos.2 hlh).ne']; ring
      have hvu : v < u := by
        rw [hu, lt_div_iff₀ (sub_pos.2 hlh)]; linarith [hσ.1]
      have huv : u < v₂ := by
        rw [hu, div_lt_iff₀ (sub_pos.2 hlh)]; linarith [hσ.2]
      have huI : u ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith⟩
      have hXt : X t = negInv (A u) := by
        rw [hAX u huI, hul, WangWu.arcTime_discTime t.coe_nonneg, Real.toNNReal_coe]
      rw [hXt]
      exact hhull_s u ⟨hvu.le, huv.le⟩
    · exact absurd hzY (hYb (ball_subset_ball (min_le_left _ _) hzb))
  -- (F4): the collar
  have hIcc : Icc a₀ v₂ ⊆ Ioo (0 : ℝ) 1 := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
  obtain ⟨hev, z, hzE, hcomp, hevc⟩ := collar_of_band (σ₁ := a₀) (σ₀ := x) (σ₂ := v₂) hc hcP hPW
    (image_mono (WangWu.fwdHull_mono hV.lt.le)) (WangWu.isOpen_H_diff_negInv_fwdHull hW hr₀)
    (WangWu.isOpen_H_diff_negInv_fwdHull hW hs₀)
    (fun z hz => component_subset_pocket (by rw [← hCP]; exact hCo) (by rw [← hCP]; exact hfr) hz)
    (fun S hS hSP hSs => disjoint_of_avoid hη hr₀ hV.lt.le hPH (fun t ht => by rw [← hCP]; exact hV.avoid t ht) hS
      hSP hSs)
    (by linarith [hx.1]) hx.2 (hfc.mono hIcc) (hfi.mono hIcc) (p := fun u => X (arcTime (lo + u * (hi - lo))).toNNReal)
    (fun u hu => hlim u (hIcc hu))
    (fun u hu => by
      show X (arcTime (lo + u * (hi - lo))).toNNReal ∈ _
      rw [← hAX u (hIcc hu)]
      exact hdom u (hV.unvis_r u hu))
    (by
      show X (arcTime (lo + a₀ * (hi - lo))).toNNReal ∈ _
      rw [← hAX _ (hIcc ⟨le_rfl, by linarith [hV.v_lt]⟩)]
      exact hdom _ hV.unvis_s)
  have hxl := hlim x hxI
  rw [← hAX x hxI] at hxl
  have hne : (𝓝[H] (f x : ℂ)).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.1 ?_
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    show (0 : ℝ) ≤ ((f x : ℝ) : ℂ).im
    simp
  refine ⟨hF2, hF3a, hF3b, Filter.map_neBot, le_inf hxl (tendsto_principal.2
    (eventually_nhdsWithin_of_forall fun w hw => hcP hw)), le_inf hxl (tendsto_principal.2 hev), z, hzE, hcomp,
    hevc⟩

end Fields

/-! ### The arms at infinity as reparametrized arcs -/

section Reparam

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

theorem one_div_one_add_eq (s : ℝ) : 1 / (1 + (1 / s - 1)) = s := by
  rw [add_sub_cancel, one_div_one_div]

/-- At `rightLo = 0` the right arm at infinity is the right arc reparametrized by `s = 1/(1 + v)`. -/
theorem cfArcRInf_eq (h0 : rightLo R L r = 0) (v : ℝ) : cfArcRInf R L r v = cfArcR R L r (1 / (1 + v)) := by
  simp only [cfArcRInf, cfArcR, h0, sub_zero, zero_add, one_div, inv_mul_eq_div]

/-- At `rightLo = 0` the left arm at infinity is the left arc reparametrized by `s = 1/(1 + v)`. -/
theorem cfArcLInf_eq (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) (v : ℝ) :
    cfArcLInf R L r v = cfArcL R L r (1 / (1 + v)) := by
  simp only [cfArcLInf, cfArcL, h.leftLo_eq_zero_of_rightLo_eq_zero h0, sub_zero, zero_add, one_div, inv_mul_eq_div]

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ A Ã : ℝ → ℂ} {τ : ℝ}

/-- **The visit data of a witness at infinity**, for the arc `Ã` with `A v = Ã(1/(1 + v))` (`v ≥ 0`): the last-visit
witness `u(r₀) < v < v₁ < v₂ < u(s₀)` becomes the first-visit-type data at `1/(1+v₂) < 1/(1+v₁) < 1/(1+v)`, with
`a₀ = 1/(2 + u(s₀))`. -/
theorem isArcVisit_of_witnessInf (hP : Sec6.IsReversePocketInf W η C α₁ α₂ τ) (hA : A = α₁ ∨ A = α₂)
    (hÃ : ∀ v ∈ Ici (0 : ℝ), A v = Ã (1 / (1 + v))) {r₀ s₀ v v₁ v₂ : ℝ}
    (hw : Aux37Attach.IsAttachWitnessInf η C A τ r₀ s₀ v v₁ v₂) :
    IsArcVisit W η C Ã r₀ s₀ (1 / (1 + (Sec6.lastVisit (fun t => η '' Icc 0 t) A s₀ + 1))) (1 / (1 + v₂))
      (1 / (1 + v)) ∧ 1 / (1 + v₂) < 1 / (1 + v₁) ∧ 1 / (1 + v₁) < 1 / (1 + v) := by
  obtain ⟨hτr, hrs, havoid, hur, hvv₁, hv₁v₂, hv₂s⟩ := hw
  obtain ⟨hL0, -, -, hDr⟩ := hP.chart hτr hA
  obtain ⟨hL1, hVs, -, hDs⟩ := hP.chart (hτr.trans hrs.le) hA
  obtain ⟨-, -, -, -, -, hrev, -⟩ := hP.arm hA
  set L₀ := Sec6.lastVisit (fun t => η '' Icc 0 t) A r₀ with hL₀
  set L₁ := Sec6.lastVisit (fun t => η '' Icc 0 t) A s₀ with hL₁
  have hv0 : 0 < v := hL0.trans_lt hur
  -- the inverse parameter
  have hinv : ∀ s, 0 < s → s ≤ 1 → Ã s = A (1 / s - 1) := fun s hs hs1 => by
    have h1 : 0 ≤ 1 / s - 1 := by
      have : 1 ≤ 1 / s := by rw [le_div_iff₀ hs, one_mul]; exact hs1
      linarith
    rw [hÃ _ h1, one_div_one_add_eq]
  have hmono : ∀ a b : ℝ, 0 ≤ a → a < b → 1 / (1 + b) < 1 / (1 + a) := fun a b ha hab =>
    one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have ha₀v₂ : 1 / (1 + (L₁ + 1)) < 1 / (1 + v₂) := hmono v₂ (L₁ + 1) (by linarith) (by linarith)
  have hv₂v : 1 / (1 + v₂) < 1 / (1 + v) := hmono v v₂ hv0.le (by linarith)
  have hv1 : 1 / (1 + v) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hpar : ∀ s ∈ Icc (1 / (1 + (L₁ + 1))) (1 / (1 + v)), 0 < s ∧ v ≤ 1 / s - 1 ∧ 1 / s - 1 ≤ L₁ + 1 := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs.1
    refine ⟨hs0, ?_, ?_⟩
    · have h1 : 1 + v ≤ 1 / s := by
        rw [le_div_iff₀ hs0]
        have := hs.2
        rwa [le_div_iff₀ (by linarith), mul_comm] at this
      linarith
    · have h1 : 1 / s ≤ 1 + (L₁ + 1) := by
        rw [div_le_iff₀ hs0]
        have := hs.1
        rwa [div_le_iff₀ (by linarith), mul_comm] at this
      linarith
  have hAeq : ∀ s ∈ Icc (1 / (1 + (L₁ + 1))) (1 / (1 + v)), Ã s = A (1 / s - 1) := fun s hs =>
    hinv s (hpar s hs).1 (hs.2.trans hv1.le)
  have ha₀mem : 1 / (1 + (L₁ + 1)) ∈ Icc (1 / (1 + (L₁ + 1))) (1 / (1 + v)) :=
    ⟨le_rfl, (ha₀v₂.trans hv₂v).le⟩
  refine ⟨⟨hP.trace, hP.continuous_W, hP.W_zero, hP.nonneg.trans hτr, hrs, havoid, by positivity, ha₀v₂, hv₂v, hv1,
    fun s hs => ?_, ?_, fun s hs => ?_, fun t s hs s' hs' hss' h => ?_⟩,
    hmono _ _ (by linarith) hv₁v₂, hmono _ _ (by linarith) hvv₁⟩
  · rw [hAeq s hs]
    exact hDr _ (show L₀ < 1 / s - 1 by linarith [(hpar s hs).2.1])
  · rw [hAeq _ ha₀mem, one_div_one_div, add_sub_cancel_left]
    exact hDs _ (show L₁ < L₁ + 1 by linarith)
  · have hs' : s ∈ Icc (1 / (1 + (L₁ + 1))) (1 / (1 + v)) := ⟨ha₀v₂.le.trans hs.1, hs.2⟩
    rw [hAeq s hs']
    refine hVs _ ⟨hv0.le.trans (hpar s hs').2.1, ?_⟩
    have h1 : 1 / s ≤ 1 + v₂ := by
      rw [div_le_iff₀ (hpar s hs').1]
      have := hs.1
      rwa [div_le_iff₀ (by linarith), mul_comm] at this
    linarith
  · rw [hAeq s hs] at h
    rw [hAeq s' hs']
    refine hrev t _ (mem_Ici.2 (by linarith [(hpar s' hs').2.1])) _ (mem_Ici.2 (by linarith [(hpar s hs).2.1])) ?_ h
    have : 1 / s' ≤ 1 / s := one_div_le_one_div_of_le (hpar s hs).1 hss'
    linarith

end Reparam

/-! ### The pocket at the flow seed: landing points and frontier -/

section Seed

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ψ : ℂ → ℂ} {c : Chart}

/-- At `rightLo = 0` the opening contact is `cayley 0 = −1`. -/
theorem openPt_eq_of_rightLo_eq_zero (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) :
    openPt R L r = -1 := by
  simp [openPt, h0, toDisc, arcTime, realPath, h.right.2.2.1, WangWu.cayley_zero]

/-- **At `rightLo = 0` the flow chart lands at `0` only at the opening contact.** -/
theorem land_ne_zero_of_rightLo_eq_zero (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hF : IsFlowChart R L r Ψ c) {q : ℂ} (hq : q ∈ Hbar) (hq0 : q ≠ 0) : land c q ≠ 0 := by
  obtain ⟨z, hz, hΨz, -⟩ := hF.exists_tendsto hq
  intro hl
  rw [hF.land_eq hq hz hΨz] at hl
  have hzm : z = -1 := by rw [← QuantumZipper.CA.cayley_cayleyInv (hF.ne_one hz), hl, WangWu.cayley_zero]
  have : Ψ z = 0 := by rw [hzm, ← openPt_eq_of_rightLo_eq_zero h h0]; exact hF.unif.zero
  exact hq0 (hΨz ▸ this)

/-- **The frontier in `ℍ` of the pocket at infinity lies on the walls.** -/
theorem frontier_cfPocketInf_mem (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) {W : ℝ → ℝ} {η : ℝ → ℂ}
    {τ : ℝ} (hP : Sec6.IsReversePocketInf W η (cfPocket R L r) (cfArcRInf R L r) (cfArcLInf R L r) τ) :
    ∀ y ∈ frontier (cfPocket R L r), y ∈ H → negInv y ∈ (range L ∪ range R) ∩ H := by
  obtain ⟨-, hv, huv, -, hb, hab, -, -⟩ := h.changeCorner_props
  have ha0 := h.leftLo_eq_zero_of_rightLo_eq_zero h0
  have key : ∀ (X : ℝ≥0 → ℂ), IsSimpleProper X → ∀ {hi : ℝ}, 0 < hi → hi ≤ 1 → ∀ v ∈ Ici (0 : ℝ),
      cfPt (toDisc (realPath X) (hi / (1 + v))) ∈ H →
        negInv (cfPt (toDisc (realPath X) (hi / (1 + v)))) ∈ range X ∩ H := by
    intro X hX hi hhi0 hhi1 v hv hy
    have hσ0 : 0 < hi / (1 + v) := div_pos hhi0 (by linarith [mem_Ici.1 hv])
    have hσ1 : hi / (1 + v) ≤ 1 := (div_le_iff₀ (by linarith [mem_Ici.1 hv])).2 (by linarith [mem_Ici.1 hv])
    rcases eq_or_lt_of_le hσ1 with he | hlt
    · rw [he] at hy
      simp only [toDisc, lt_irrefl, ↓reduceIte, cfPt_one] at hy
      have h0H : (0 : ℝ) < (0 : ℂ).im := hy
      simp at h0H
    · obtain ⟨e, hpos⟩ := cfPt_toDisc_of_mem hX ⟨hσ0, hlt⟩
      rw [e, negInv_negInv]
      exact ⟨⟨_, rfl⟩, hX.2.2.2.1 _ hpos⟩
  intro y hy hyH
  rw [hP.frontier_eq] at hy
  rcases hy with ⟨v, hv', rfl⟩ | ⟨v, hv', rfl⟩
  · obtain ⟨h1, h2⟩ := key R h.right (by linarith) hv.2 v hv' hyH
    exact ⟨Or.inr h1, h2⟩
  · obtain ⟨h1, h2⟩ := key L h.left (by linarith) hb.2 v hv' hyH
    exact ⟨Or.inl h1, h2⟩

end Seed

end InteractingSLE.Sec7.Aux37Side
