import QuantumZipper.Proofs.Zipper.E6MeasNode

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5b (D75): the abstract E6 core for an arbitrary unzipping map

Task R5b of `handoff/FOLLOW-PAPER-13.md`. Verbatim copies of `E6.e6_loc_pt` (E6.lean),
`E6.e6_loc_pt_nm` and `E6.e6_core_rel_nm` (E6MeasCore.lean) and of `E6.e6_concrete_rich_nm`
(E6MeasNode.lean) in which the unzipping map `zipLenDown γ ℓ₁` is replaced by an arbitrary map
`Z : Cfg → Cfg` (the proofs never unfold it). Instantiated with `Z = zipLenDownArc γ ℓ₁` in
`LocLenE6NodeMain.lean`. Sheffield arXiv:1012.4797, §5.4, proof of Thm 1.8, pp. 70–72
(stationarity of the quantum wedge under `Z^LEN`); own bookkeeping as for the originals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper.LocLen

open E6 PalmShift B2 E1 D3Plus

section Core

variable {Ω : Type*} [MeasurableSpace Ω] {Ω' : Type*} [MeasurableSpace Ω']
  {L : Type*} [MeasurableSpace L]

/-- `E6.LocalAbs` (E6.lean:62) for an arbitrary unzipping map `Z`. -/
def LocalAbsZ (Z : Cfg → Cfg) (P' : Measure Ω') (c' : Ω' → Cfg) (loc : ℕ → Cfg → L)
    (Reg : Set Cfg) : Prop :=
  ∀ R : ℕ, ∀ ε : ℝ≥0∞, 0 < ε → ∃ R' : ℕ, ∃ F : L → L, ∃ A : Set L,
    Measurable F ∧ MeasurableSet A ∧ P' {ω' | loc R' (c' ω') ∉ A} ≤ ε ∧
    ∀ y ∈ Reg, loc R' y ∈ A → loc R (Z y) = F (loc R' y)

omit [MeasurableSpace L] in
/-- Pointwise locality bounds (both directions). -/
lemma e6_loc_ptZ {Z : Cfg → Cfg} {loc : ℕ → Cfg → L} {R R' : ℕ} {F : L → L} {A : Set L}
    {Reg : Set Cfg} (hA : ∀ y ∈ Reg, loc R' y ∈ A → loc R (Z y) = F (loc R' y))
    {Γ : L → ℝ≥0∞} (hΓ1 : ∀ y, Γ y ≤ 1) {y w : Cfg} (hy : y ∈ Reg)
    (hw : loc R w = loc R (Z y)) :
    Γ (loc R w) ≤ Γ (F (loc R' y)) + Aᶜ.indicator 1 (loc R' y) ∧
      Γ (F (loc R' y)) ≤ Γ (loc R w) + Aᶜ.indicator 1 (loc R' y) := by
  by_cases h : loc R' y ∈ A
  · rw [hw, hA y hy h]; exact ⟨le_self_add, le_self_add⟩
  · rw [indicator_of_mem (show loc R' y ∈ Aᶜ from h)]
    exact ⟨(hΓ1 _).trans (le_add_left le_rfl), (hΓ1 _).trans (le_add_left le_rfl)⟩

omit [MeasurableSpace L] in
/-- Pointwise locality bounds with the error merged (`Φ₀ = 1_A · Γ ∘ F`, `Ψ = min(Γ∘F + 1_{Aᶜ}, 1)`). -/
lemma e6_loc_pt_nmZ {Z : Cfg → Cfg} {loc : ℕ → Cfg → L} {R R' : ℕ} {F : L → L} {A : Set L}
    {Reg : Set Cfg} (hA : ∀ y ∈ Reg, loc R' y ∈ A → loc R (Z y) = F (loc R' y))
    {Γ : L → ℝ≥0∞} (hΓ1 : ∀ y, Γ y ≤ 1) {y w : Cfg} (hy : y ∈ Reg)
    (hw : loc R w = loc R (Z y)) :
    Γ (loc R w) ≤ A.indicator (fun l => Γ (F l)) (loc R' y) + Aᶜ.indicator 1 (loc R' y) ∧
      A.indicator (fun l => Γ (F l)) (loc R' y) ≤ Γ (loc R w) ∧
      Γ (loc R w) ≤ min (Γ (F (loc R' y)) + Aᶜ.indicator 1 (loc R' y)) 1 := by
  by_cases h : loc R' y ∈ A
  · have hnc : loc R' y ∉ Aᶜ := fun h' => h' h
    rw [indicator_of_mem h, indicator_of_notMem hnc, hw, hA y hy h, add_zero]
    exact ⟨le_rfl, le_rfl, le_min le_rfl (hΓ1 _)⟩
  · have hc : loc R' y ∈ Aᶜ := h
    rw [indicator_of_notMem h, indicator_of_mem hc, zero_add]
    refine ⟨hΓ1 _, zero_le, le_min ((hΓ1 _).trans ?_) (hΓ1 _)⟩
    simp

/-- **`e6_core_rel` without Palm-side measurability.** -/
theorem e6_core_rel_nmZ (Rel : Cfg → Cfg → Prop) (Z : Cfg → Cfg) (ℓ₁ δ : ℝ) (hℓ₁ : 0 < ℓ₁) (hδ : 0 < δ)
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Kernel Ω ℝ) [IsSFiniteKernel ν]
    (hit : Ω → Set ℝ) (z : Ω → ℝ) (zc : ℝ → Ω → ℝ → Cfg)
    (P' : Measure Ω') [IsProbabilityMeasure P'] (c' : Ω' → Cfg)
    (loc : ℕ → Cfg → L) (Reg : Set Cfg)
    (hatom : ∀ᵐ ω ∂P, ∀ x, ν ω {x} = 0)
    (hpos : ∀ᵐ ω ∂P, ∀ x y, x < y → 0 < ν ω (Ioo x y))
    (hfin : ∀ᵐ ω ∂P, ∀ u v, ν ω (Icc u v) ≠ ∞)
    (hmass : ∫⁻ ω, ν ω (Icc (-δ) 0) ∂P ≠ ∞)
    (hpm : 0 < pmass P ν δ hit)
    (hhit : ∀ᵐ ω ∂P, ∀ x ≤ 0, x ∈ hit ω ↔ z ω < x)
    (hc'm : ∀ R, Measurable fun ω' => loc R (c' ω'))
    (hlocEq : ∀ R a b, Rel a b → loc R a = loc R b)
    (hReg' : ∀ᵐ ω' ∂P', c' ω' ∈ Reg)
    (hRegZ : ∀ᵐ ω ∂P, ∀ C x, x ∈ hit ω → zc C ω x ∈ Reg)
    (hId : ∀ᵐ ω ∂P, ∀ C x y, x ∈ Icc (-δ) 0 → y ∈ hit ω → -δ - 1 < y → y ≤ x →
      ν ω (Icc y x) = ENNReal.ofReal (ℓ₁ * Real.exp (-C / 2)) →
      Rel (zc C ω x) (Z (zc C ω y)))
    (hLoc : LocalAbsZ Z P' c' loc Reg)
    (hE5 : E5Abs P ν δ hit zc P' c' loc) :
    ∀ R : ℕ, ∀ Γ : L → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
      ∫⁻ ω', Γ (loc R (Z (c' ω'))) ∂P' = ∫⁻ ω', Γ (loc R (c' ω')) ∂P' := by
  intro R Γ hΓ hΓ1
  set pm := pmass P ν δ hit with hpmdef
  set a := ∫⁻ ω', Γ (loc R (Z (c' ω'))) ∂P'
  set b := ∫⁻ ω', Γ (loc R (c' ω')) ∂P'
  have hpmt : pm ≠ ∞ :=
    ne_top_of_le_ne_top hmass (lintegral_mono fun ω => measure_mono fun x hx => hx.1)
  have key : ∀ t : ℝ≥0∞, 0 < t → pm * a ≤ pm * b + t ∧ pm * b ≤ pm * a + t := by
    intro t ht
    set u := t / 8
    have hu : 0 < u := ENNReal.div_pos_iff.mpr ⟨ht.ne', by norm_num⟩
    have h8 : t = u + u + u + u + u + u + u + u := by
      have : (8 : ℝ≥0∞) * u = t := ENNReal.mul_div_cancel (by norm_num) (by norm_num)
      rw [← this]; ring
    have he : 0 < u / pm := ENNReal.div_pos_iff.mpr ⟨hu.ne', hpmt⟩
    have hpe : pm * (u / pm) = u := ENNReal.mul_div_cancel hpm.ne' hpmt
    obtain ⟨R', F, A, hF, hA, hPA, hloc⟩ := hLoc R (u / pm) he
    set Φ : L → ℝ≥0∞ := fun l => Γ (F l)
    set Ind : L → ℝ≥0∞ := Aᶜ.indicator 1
    set Φ₀ : L → ℝ≥0∞ := A.indicator Φ
    set Ψ : L → ℝ≥0∞ := fun l => min (Φ l + Ind l) 1
    have hΦ : Measurable Φ := hΓ.comp hF
    have hInd : Measurable Ind := measurable_one.indicator hA.compl
    have hΦ₀ : Measurable Φ₀ := hΦ.indicator hA
    have hΨ : Measurable Ψ := (hΦ.add hInd).min measurable_const
    have hΦ₀1 : ∀ l, Φ₀ l ≤ 1 := fun l => by
      simp only [Φ₀, indicator]; split_ifs
      · exact hΓ1 _
      · exact zero_le
    have hΨ1 : ∀ l, Ψ l ≤ 1 := fun l => min_le_right _ _
    -- choice of the zoom `C`
    obtain ⟨ℓs, hℓs, hD⟩ := e6_D_small P ν δ hpos hmass hu
    have hlim : Tendsto (fun C : ℝ => ℓ₁ * Real.exp (-C / 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun C : ℝ => -C / 2) atTop atBot := by
        refine (tendsto_neg_atTop_atBot.comp
          (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))).congr fun C => ?_
        simp [Function.comp, neg_div]
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul ℓ₁
    have hl0 : Tendsto (fun C : ℝ => ENNReal.ofReal (ℓ₁ * Real.exp (-C / 2))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hlim
    have hl4 : Tendsto (fun C : ℝ => ENNReal.ofReal (4 * (ℓ₁ * Real.exp (-C / 2)))) atTop
        (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal (hlim.const_mul 4)
    have hev := (hE5 R u hu).and ((hE5 R' u hu).and ((hl0.eventually (gt_mem_nhds hu)).and
      ((hl4.eventually (gt_mem_nhds hu)).and
        (hl0.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < ℓs by exact_mod_cast hℓs))))))
    obtain ⟨C, hE5R, hE5R', hc0, hc4, hcs⟩ := hev.exists
    set ℓ : ℝ≥0 := (ℓ₁ * Real.exp (-C / 2)).toNNReal with hℓdef
    have hℓr : (ℓ : ℝ) = ℓ₁ * Real.exp (-C / 2) := Real.coe_toNNReal _ (by positivity)
    have hℓe : (ℓ : ℝ≥0∞) = ENNReal.ofReal (ℓ₁ * Real.exp (-C / 2)) := rfl
    have hℓu : (ℓ : ℝ≥0∞) ≤ u := hℓe ▸ hc0.le
    have h4u : ENNReal.ofReal (4 * ℓ) ≤ u := by rw [hℓr]; exact hc4.le
    have hcu : ENNReal.ofReal (2 * ℓ * ((1 : ℝ≥0) : ℝ)) ≤ u := by
      refine (ENNReal.ofReal_le_ofReal ?_).trans h4u
      have := ℓ.coe_nonneg
      push_cast; linarith
    have hDu : tailD P ν δ ℓ ≤ u := by
      refine (tailD_mono P ν δ ?_).trans hD
      have : (ℓ : ℝ≥0∞) ≤ ℓs := hℓe ▸ hcs.le
      exact_mod_cast this
    -- the `P_*` side
    have hcm : Measurable fun ω' => loc R' (c' ω') := hc'm R'
    have hv : ∫⁻ ω', Ind (loc R' (c' ω')) ∂P' ≤ u / pm := by
      have : (fun ω' => Ind (loc R' (c' ω'))) =
          ((fun ω' => loc R' (c' ω')) ⁻¹' Aᶜ).indicator 1 := by
        funext ω'; simp only [Ind, indicator, mem_preimage]; rfl
      rw [this, lintegral_indicator_one (hcm hA.compl)]
      exact hPA
    have hpv : pm * ∫⁻ ω', Ind (loc R' (c' ω')) ∂P' ≤ u := hpe ▸ mul_le_mul_right hv pm
    have hP1 : a ≤ ∫⁻ ω', Φ₀ (loc R' (c' ω')) ∂P' + ∫⁻ ω', Ind (loc R' (c' ω')) ∂P' := by
      rw [← lintegral_add_left (show Measurable fun ω' => Φ₀ (loc R' (c' ω')) from hΦ₀.comp hcm)]
      refine lintegral_mono_ae (hReg'.mono fun ω' hω' => ?_)
      exact (e6_loc_pt_nmZ hloc hΓ1 hω' rfl).1
    have hP2 : ∫⁻ ω', Ψ (loc R' (c' ω')) ∂P' ≤
        a + ∫⁻ ω', Ind (loc R' (c' ω')) ∂P' + ∫⁻ ω', Ind (loc R' (c' ω')) ∂P' := by
      have hIm : Measurable fun ω' => Ind (loc R' (c' ω')) := hInd.comp hcm
      calc ∫⁻ ω', Ψ (loc R' (c' ω')) ∂P'
          ≤ ∫⁻ ω', (Γ (loc R (Z (c' ω'))) + Ind (loc R' (c' ω')) +
              Ind (loc R' (c' ω'))) ∂P' := by
            refine lintegral_mono_ae (hReg'.mono fun ω' hω' => ?_)
            refine (min_le_left _ _).trans (add_le_add ?_ le_rfl)
            exact (e6_loc_ptZ hloc hΓ1 hω' rfl).2
        _ = _ := by rw [lintegral_add_right _ hIm, lintegral_add_right _ hIm]
    -- the Palm side, per `ω`
    have hgood := hatom.and (hpos.and (hfin.and (hhit.and (hRegZ.and hId))))
    have hbdir := e6_int_bound_nm P ν δ hit ℓ (ENNReal.ofReal (2 * ℓ * ((1 : ℝ≥0) : ℝ)))
      (fun ω x => Γ (loc R (zc C ω x))) (fun ω x => Ψ (loc R' (zc C ω x))) (by
        filter_upwards [hgood] with ω ⟨h1, h2, h3, h4, h5, h6⟩
        exact e6_omega_b_nm hδ h1 h2 h3 ℓ (hit ω) (z ω) h4 (fun x => hΓ1 _) (fun x => hΨ1 _)
          (fun x hx y hy hy1 hyx hlen => (e6_loc_pt_nmZ hloc hΓ1 (h5 C y hy)
            (hlocEq R _ _ (h6 C x y hx hy hy1 hyx hlen))).2.2))
    have hadir := e6_int_bound_nm P ν δ hit ℓ (ENNReal.ofReal (2 * ℓ * ((1 : ℝ≥0) : ℝ)))
      (fun ω x => Φ₀ (loc R' (zc C ω x))) (fun ω x => Γ (loc R (zc C ω x))) (by
        filter_upwards [hgood] with ω ⟨h1, h2, h3, h4, h5, h6⟩
        exact e6_omega_a_nm hδ h1 h2 h3 ℓ (hit ω) (z ω) h4 (fun x => hΦ₀1 _)
          (fun x hx y hy hy1 hyx hlen => (e6_loc_pt_nmZ hloc hΓ1 (h5 C y hy)
            (hlocEq R _ _ (h6 C x y hx hy hy1 hyx hlen))).2.1))
    change palmZ P ν δ hit (zc C) (fun y => Γ (loc R y)) ≤
      palmZ P ν δ hit (zc C) (fun y => Ψ (loc R' y)) + _ + _ at hbdir
    change palmZ P ν δ hit (zc C) (fun y => Φ₀ (loc R' y)) ≤
      palmZ P ν δ hit (zc C) (fun y => Γ (loc R y)) + _ + _ at hadir
    obtain ⟨hΓa, hΓb⟩ := hE5R Γ hΓ hΓ1
    have hΨa := (hE5R' Ψ hΨ hΨ1).1
    have hΦ₀b := (hE5R' Φ₀ hΦ₀ hΦ₀1).2
    have hsix : u + u + u + u + u + u + u ≤ t := by rw [h8]; exact le_self_add
    constructor
    · calc pm * a
          ≤ pm * (∫⁻ ω', Φ₀ (loc R' (c' ω')) ∂P' + ∫⁻ ω', Ind (loc R' (c' ω')) ∂P') :=
            mul_le_mul_right hP1 pm
        _ = pm * ∫⁻ ω', Φ₀ (loc R' (c' ω')) ∂P' + pm * ∫⁻ ω', Ind (loc R' (c' ω')) ∂P' :=
            mul_add _ _ _
        _ ≤ (palmZ P ν δ hit (zc C) (fun y => Φ₀ (loc R' y)) + u) + u := add_le_add hΦ₀b hpv
        _ ≤ (((pm * b + u) + u + (u + u)) + u) + u := by
            refine add_le_add (add_le_add (hadir.trans ?_) le_rfl) le_rfl
            exact add_le_add (add_le_add hΓa hcu) (add_le_add hℓu hDu)
        _ = pm * b + (u + u + u + u + u + u) := by ring
        _ ≤ pm * b + t := add_le_add le_rfl (le_self_add.trans hsix)
    · calc pm * b
          ≤ palmZ P ν δ hit (zc C) (fun y => Γ (loc R y)) + u := hΓb
        _ ≤ ((pm * ∫⁻ ω', Ψ (loc R' (c' ω')) ∂P' + u) + u + (u + u)) + u := by
            refine add_le_add (hbdir.trans ?_) le_rfl
            exact add_le_add (add_le_add hΨa hcu) (add_le_add hℓu hDu)
        _ ≤ (((pm * a + u + u) + u) + u + (u + u)) + u := by
            refine add_le_add (add_le_add (add_le_add (add_le_add ?_ le_rfl) le_rfl)
              le_rfl) le_rfl
            calc pm * ∫⁻ ω', Ψ (loc R' (c' ω')) ∂P'
                ≤ pm * (a + ∫⁻ ω', Ind (loc R' (c' ω')) ∂P' +
                    ∫⁻ ω', Ind (loc R' (c' ω')) ∂P') := mul_le_mul_right hP2 pm
              _ = pm * a + pm * ∫⁻ ω', Ind (loc R' (c' ω')) ∂P' +
                    pm * ∫⁻ ω', Ind (loc R' (c' ω')) ∂P' := by ring
              _ ≤ pm * a + u + u := add_le_add (add_le_add le_rfl hpv) hpv
        _ = pm * a + (u + u + u + u + u + u + u) := by ring
        _ ≤ pm * a + t := add_le_add le_rfl hsix
  have hcancel : ∀ {X Y : ℝ≥0∞}, (∀ t : ℝ≥0∞, 0 < t → pm * X ≤ pm * Y + t) → X ≤ Y := by
    intro X Y h
    refine (ENNReal.mul_le_mul_iff_right hpm.ne' hpmt).mp ?_
    exact ENNReal.le_of_forall_pos_le_add fun ε hε _ => h ε (by exact_mod_cast hε)
  exact le_antisymm (hcancel fun t ht => (key t ht).1) (hcancel fun t ht => (key t ht).2)

end Core

section Concrete

variable {Ω : Type} [MeasurableSpace Ω] {Ω' : Type} [MeasurableSpace Ω']

/-- Copy of `E6.e6_concrete_rich_nm` (E6MeasNode.lean:34) for an arbitrary unzipping map `Z`. -/
theorem e6_concrete_rich_nmZ (hE5 : E5StmtRich) (Z : Cfg → Cfg)
    (κ T : ℝ) (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (X : Ω → FieldSample) (ϖ : Measure ℂ) (hS : E5.Setup κ T P B X ϖ)
    (P' : Measure Ω') [IsProbabilityMeasure P'] (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ)
    (hY : IsQuantumWedge (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) Y P')
    (hB' : IsBrownianReal B' P') (hYB : IndepFun Y (pathOf B') P')
    (δ : ℝ) (hδ : 0 < δ) (hTδ : 4 * δ ^ 2 / (4 - κ) ≤ T) (ℓ₁ : ℝ) (hℓ₁ : 0 < ℓ₁)
    (Reg : Set Cfg)
    (hc'm : ∀ R, AEMeasurable (fun ω' => locRich R (Y ω', drive κ B' ω')) P')
    (hReg' : ∀ᵐ ω' ∂P', (Y ω', drive κ B' ω') ∈ Reg)
    (hRegZ : ∀ᵐ ω ∂P, ∀ C x, realHitTime (Vr κ T B ω) x < ENNReal.ofReal T →
      zcC κ T B X ϖ C ω x ∈ Reg)
    (hIdLoc : ∀ᵐ ω ∂P, ∀ C x y, x ∈ Icc (-δ) 0 →
      realHitTime (Vr κ T B ω) y < ENNReal.ofReal T → -δ - 1 < y → y ≤ x →
      nuPalm κ T B X ϖ ω (Icc y x) = ENNReal.ofReal (ℓ₁ * Real.exp (-C / 2)) →
      ∀ R, locRich R (zcC κ T B X ϖ C ω x) =
        locRich R (Z (zcC κ T B X ϖ C ω y)))
    (hLoc : LocalAbsZ Z P' (fun ω' => (Y ω', drive κ B' ω')) locRich Reg) :
    ∀ R : ℕ, ∀ Γ : FullData → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
      ∫⁻ ω', Γ (locRich R (Z (Y ω', drive κ B' ω'))) ∂P' =
        ∫⁻ ω', Γ (locRich R (Y ω', drive κ B' ω')) ∂P' := by
  obtain ⟨c'', hcc, hc''m⟩ := exists_modif_measurable_locRich hc'm
  have hint : ∀ f : Cfg → ℝ≥0∞,
      ∫⁻ ω', f (c'' ω') ∂P' = ∫⁻ ω', f (Y ω', drive κ B' ω') ∂P' := fun f =>
    lintegral_congr_ae (hcc.mono fun ω' h => by simp only [h])
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := hS
  have hReg := RevCouplingReg.revCouplingBoundaryMeasureRegular
  obtain ⟨K₁, hK₁⟩ := NuMeas.exists_kernel_nuPalm hReg hκ hκ4 hT hB hX hind hϖ
  have hAF := ae_nuPalm_atom_fin hReg hκ hκ4 hT hB hX hind ϖ
  obtain ⟨K, hKs, hKK⟩ := exists_sfinite_version (P := P) K₁ (by
    filter_upwards [hK₁, hAF] with ω h1 h2; rw [h1]; exact h2.2)
  have hK : ∀ᵐ ω ∂P, K ω = nuPalm κ T B X ϖ ω := by
    filter_upwards [hK₁, hKK] with ω h1 h2; rw [h2, h1]
  set hit : Ω → Set ℝ := fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}
  have hzm := B5.ae_zeroMinus_Vr_facts RS.rohdeSchrammSimple hκ hκ4.le hT P B hB
  have hpos := E3.ae_nuPalm_Ioo_pos hReg hκ hκ4 hT hB hX hind ϖ
  have hZ := EWire.zfin hκ hκ4 hT hδ hB hX hind hϖ (P := P)
  have hE3 := EWire.e3_pos hκ hκ4 hT hB hX hind hϖ hδ hTδ (P := P)
  have hpmK : pmass P K δ hit = ∫⁻ ω, nuPalm κ T B X ϖ ω
      {x | x ∈ Icc (-δ) 0 ∧ realHitTime (Vr κ T B ω) x < ENNReal.ofReal T} ∂P :=
    lintegral_congr_ae (hK.mono fun ω h => by dsimp only; rw [h]; rfl)
  have hpalm : ∀ C (f : Cfg → ℝ≥0∞), palmZ P K δ hit (zcC κ T B X ϖ C) f =
      ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}.indicator
        (fun x => f (zcC κ T B X ϖ C ω x)) x ∂nuPalm κ T B X ϖ ω ∂P := fun C f =>
    lintegral_congr_ae (hK.mono fun ω h => by dsimp only; rw [h])
  have hE5A : E5Abs P K δ hit (zcC κ T B X ϖ) P' c'' locRich := by
    intro R η hη
    have h := hE5 κ T P B X ϖ P' Y B' hReg ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ hY hB' hYB δ hδ R η hη
    filter_upwards [h] with C hC Γ hΓ hΓ1
    have := hC Γ hΓ hΓ1
    rw [hpalm, hpmK, hint (fun y => Γ (locRich R y))]
    exact this
  have hLoc'' : LocalAbsZ Z P' c'' locRich Reg := by
    intro R ε hε
    obtain ⟨R', F, A, hF, hA, hPA, hloc⟩ := hLoc R ε hε
    refine ⟨R', F, A, hF, hA, le_of_eq_of_le (measure_congr ?_) hPA, hloc⟩
    filter_upwards [hcc] with ω' h
    show (locRich R' (c'' ω') ∉ A) = (locRich R' (Y ω', drive κ B' ω') ∉ A)
    rw [h]
  have hReg'' : ∀ᵐ ω' ∂P', c'' ω' ∈ Reg := by
    filter_upwards [hcc, hReg'] with ω' h1 h2; rw [h1]; exact h2
  intro R Γ hΓ hΓ1
  have key := e6_core_rel_nmZ (fun a b => ∀ R, locRich R a = locRich R b) Z ℓ₁ δ
    hℓ₁ hδ P K hit (fun ω => zeroMinus (Vr κ T B ω) T) (zcC κ T B X ϖ) P' c'' locRich
    Reg ?_ ?_ ?_ ?_ ?_ ?_ hc''m (fun R a b h => h R) hReg'' hRegZ ?_ hLoc'' hE5A
    R Γ hΓ hΓ1
  · rw [← hint (fun y => Γ (locRich R y)),
      ← hint (fun y => Γ (locRich R (Z y)))]
    exact key
  · filter_upwards [hK, hAF] with ω h1 h2; rw [h1]; exact h2.1
  · filter_upwards [hK, hpos] with ω h1 h2; rw [h1]; exact h2
  · filter_upwards [hK, hAF] with ω h1 h2; rw [h1]; exact h2.2
  · rw [lintegral_congr_ae (hK.mono fun ω h => by rw [h])]; exact hZ.2.2.ne
  · rw [hpmK]; exact hE3
  · filter_upwards [hzm] with ω h; exact h.2.2.2.2.2
  · filter_upwards [hK, hIdLoc] with ω h1 h2; rw [h1]; exact h2
end Concrete

end QuantumZipper.LocLen
