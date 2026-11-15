/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1InEndDetBase
import InteractingSLE.Spec.Sec5.Lemma57Visit

/-!
# BW1's endpoint, deterministic half: PROVED

Packet PROVE-BW1-INPUTS. **`bw1EndpointDetStatement : BW1EndpointDetStatement`** (p. 614–615, "The endpoint and all
relative stopping times", pathwise). With `f` the boundary extension of the state chart's inverse `f_ζ⁻¹`
(`GW1P.HasProperBdryExt`), the relative tips of `wr` are `f(−1/Γ(s))` (when `Γ(s) ≠ 0`) and the physical tips of `w'`
are `−1/γ(u)` (when `γ(u) ≠ 0`); the clock identifies them on `[0, L)`.

* If `L < ∞`: let `w₀ = Γ(L)`. As `s ↑ L` the clock tends to the contact time `T`; the physical tips tend to a point
  `p_T` of the retained piece `α([0, ζ])` (to `0` if `T = ∞`, by transience; to the contact point if `T < ∞`).
  If `w₀ ≠ 0`, then `f(−1/w₀) = p_T` is in the piece, so `−1/w₀` is a real point of the filled base
  (`mem_base_of_mem_trace`), hence `w₀` lies in one of the closed protected tails `[jR, ∞)`, `(−∞, jL]` — excluded.
  If `w₀ = 0`, the relative tips `f(−1/Γ(s))` are eventually defined and blow up (`‖f(p) − p‖ ≤ C`), while the
  physical tips stay bounded — a contradiction.
* So `L = ∞`; by relative transience `−1/Γ(s) → 0` and the relative tips tend to `f(0) = q` (the tip of the piece),
  while the physical tips tend to `p_T`; `p_T = 0` is impossible (`q ≠ 0`), so `T < ∞` and the tip at `T` is `q`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.BW1In

open Exist Exist.StagedLaw Exist.Staged Supp8.GB6 BW1Life

/-- **The physical tips at the clock times converge to a point of the retained set**: to `0` if the contact time is
infinite (transience), to the contact point if it is finite. -/
theorem phys_limit {γ : ℝ≥0 → ℂ} (hγc : Continuous γ) (hγtr : Tendsto (fun s => ‖γ s‖) atTop atTop) {A : Set ℂ}
    (h0A : (0 : ℂ) ∈ A) {T : ℝ≥0∞} (hT1 : ∀ T₀ : ℝ≥0, T = T₀ → γ T₀ ≠ 0 ∧ -(γ T₀)⁻¹ ∈ A)
    {ℓ : ℝ≥0 → ℝ≥0} {F : Filter ℝ≥0} (hℓtop : T = ⊤ → Tendsto ℓ F atTop)
    (hℓfin : ∀ T₀ : ℝ≥0, T = T₀ → Tendsto ℓ F (𝓝 T₀)) :
    ∃ pT ∈ A, (∀ᶠ s in F, γ (ℓ s) ≠ 0) ∧ Tendsto (fun s => -(γ (ℓ s))⁻¹) F (𝓝 pT) ∧ (T = ⊤ → pT = 0) ∧
      ∀ T₀ : ℝ≥0, T = T₀ → pT = -(γ T₀)⁻¹ := by
  rcases eq_or_ne T ⊤ with hT | hT
  · have hn : Tendsto (fun s => ‖γ (ℓ s)‖) F atTop := hγtr.comp (hℓtop hT)
    refine ⟨0, h0A, ?_, ?_, fun _ => rfl, fun T₀ hT₀ => absurd (hT.symm.trans hT₀) ENNReal.top_ne_coe⟩
    · filter_upwards [hn.eventually_gt_atTop 0] with s hs
      exact norm_pos_iff.1 hs
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      have h := tendsto_inv_atTop_zero.comp hn
      refine h.congr fun s => ?_
      simp [norm_neg, norm_inv]
  · obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℝ≥0, T = T₀ := ⟨T.toNNReal, (ENNReal.coe_toNNReal hT).symm⟩
    subst hT₀
    obtain ⟨hne, hmem⟩ := hT1 T₀ rfl
    have hc : Tendsto (fun s => γ (ℓ s)) F (𝓝 (γ T₀)) := (hγc.tendsto T₀).comp (hℓfin T₀ rfl)
    refine ⟨-(γ T₀)⁻¹, hmem, hc.eventually_ne hne, (hc.inv₀ hne).neg,
      fun h => absurd h ENNReal.coe_ne_top, fun T₁ hT₁ => ?_⟩
    rw [ENNReal.coe_injective hT₁]

/-- **BW1's endpoint, deterministic half, PROVED** (p. 614–615, pathwise). -/
theorem bw1EndpointDetStatement : BW1EndpointDetStatement := by
  intro κ b jumps θ t gw2 rest D r w' wr γ Γ L ℓ hκ hκ4 hb hP hNR hthr hw'c hw'0 hγ hγtr hwrc hwr0 hΓ hΓtr hRt hLt
    hmono hcont himg htip
  have hrun : ExplState.run κ b jumps (bwSpec gw2 θ t rest) D 1 =
      ExplState.launch (ExplState.init 0) 0 (D 0) θ t := BW1Prop.run_one_eq_launch κ b jumps gw2 θ t rest D
  rw [hrun] at hthr htip
  rw [hrun]
  have hle := BW1Prop.le_of_endsAtThresholdSide hthr
  have hfin := BW1Prop.ne_top_of_endsAtThresholdSide hthr
  have hmin : min t (D 0).2 = (D 0).2 := min_eq_right hle
  obtain ⟨α, hα₀, -⟩ := hP.2.2
  have hα : IsGeneratingTrace (D 0).1 (D 0).2 α := by rw [hmin] at hα₀; exact hα₀
  have hWα : ContinuousOn (D 0).1 {s : ℝ≥0 | (s : ℝ≥0∞) ≤ (D 0).2} := by
    have h := hP.2.1; rw [hmin] at h; exact h
  obtain ⟨-, -, hUc, hU0, hchart, hq, hq0, αr, hαr, hαeq, -, -⟩ :=
    BW1Prop.bw1_piece_geometry hP hα₀ (hNR α hα) hthr
  set ζ : ℝ≥0 := (D 0).2.toNNReal with hζdef
  set U : ℝ → ℝ := BW1Prop.pieceDrv (D 0) with hUdef
  set q : ℝ := BW1.statePoint (ExplState.launch (ExplState.init 0) 0 (D 0) θ t) with hqdef
  set c : Chart := BW1.stateChart (ExplState.launch (ExplState.init 0) 0 (D 0) θ t) with hcdef
  -- the boundary extension `f` of the chart's inverse
  have hS : min t (D 0).2 ≠ ⊤ := by rw [hmin]; exact hfin
  obtain ⟨f, C, hf₀, hC⟩ := (GW1P.hasProperBdryExt_recenter_id 0).loewner_stopped hP hS
  have hceq : c = (Chart.id.recenter 0).loewner
      (fun r : ℝ => (D 0).1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (min t (D 0).2)).toNNReal)
      (((min t (D 0).2).toNNReal : ℝ≥0) : ℝ) := chart_launch (ExplState.init 0) 0 (D 0) θ t hS
  have hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p)) := by rw [hceq]; exact hf₀
  have hfF : ∀ p ∈ Hbar, Tendsto (fwdMapInv U ζ) (𝓝[H] p) (𝓝 (f p)) := by
    have e : c.2.1 = fwdMapInv U ζ := hchart
    rw [← e]; exact hf
  have hfcont : ContinuousOn f Hbar := GW1P.continuousOn_of_tendsto hf
  have hUnn : ∀ x : ℝ, U (x.toNNReal : ℝ) = U x := fun x => by
    simp only [hUdef, BW1Prop.pieceDrv, Real.toNNReal_coe]
  have h0H : (0 : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (0 : ℂ).im by simp
  have hαζ : αr ζ = α ζ := by rw [hαeq ζ ⟨NNReal.coe_nonneg ζ, le_rfl⟩, Real.toNNReal_coe]
  have hf0 : f 0 = (q : ℂ) := by
    have := GW1P.neBot_nhdsWithin_H h0H
    have h2 := tendsto_nhds_unique (hfF 0 h0H) (hαr.tendsto_fwdMapInv_tip hUc hU0 (NNReal.coe_nonneg ζ))
    rw [h2, hαζ, hq]
  -- the retained piece
  set A : Set ℂ := α '' Icc 0 ζ with hAdef
  have hζe : ((ζ : ℝ≥0) : ℝ≥0∞) = (D 0).2 := ENNReal.coe_toNNReal hfin
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn (hα.2.1.mono fun s hs => by
    show (s : ℝ≥0∞) ≤ (D 0).2
    rw [← hζe]; exact ENNReal.coe_le_coe.2 hs.2)
  have h0A : (0 : ℂ) ∈ A := ⟨0, ⟨le_rfl, zero_le⟩, hα.1⟩
  have hAr : A = (fun s : ℝ≥0 => αr s) '' Icc 0 ζ := by
    refine image_congr fun s hs => ?_
    rw [hαeq s ⟨s.2, NNReal.coe_le_coe.2 hs.2⟩, Real.toNNReal_coe]
  -- the contact time
  have hγc := Sec5.continuous_of_isGeneratingTrace_top hγ
  have hΓc := Sec5.continuous_of_isGeneratingTrace_top hΓ
  set T := firstTipTime infinitySourceChart w' (SB.prefixPhysSet κ b jumps (bwSpec gw2 θ t rest) D 1) with hTdef
  have hTeq : T = firstContactTime (fun s => sphereInv (γ s : OnePoint ℂ)) ((fun z : ℂ => (z : OnePoint ℂ)) '' A) := by
    rw [hTdef, BW1Prop.firstTipTime_prefixPhysSet_eq hle hfin hα hWα hP.1 hγ hw'c hw'0, hAdef, image_image]
  have hT1 : ∀ T₀ : ℝ≥0, T = T₀ → γ T₀ ≠ 0 ∧ -(γ T₀)⁻¹ ∈ A := fun T₀ hT₀ =>
    contact_of_firstContactTime_eq hγc hAc (by rw [← hTeq]; exact hT₀)
  -- the tips
  have hphys := GW4Leaf.tipAt_infinitySourceChart_iff hγ hw'c hw'0
  have hrel : ∀ (s : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt wr s z ↔ Γ s ≠ 0 ∧ z = f (-(Γ s)⁻¹) :=
    fun s z => ⟨fun h => GW4Leaf.tipAt_trans_imp hf hC hΓ hwrc hwr0 h, fun ⟨hne, he⟩ => by
      rw [he]; exact GW2aPiece.tipAt_trans_of_ne_zero hf hΓ hwrc hwr0 hne⟩
  have hcomb : ∀ s : ℝ≥0, (s : ℝ≥0∞) < L →
      (Γ s ≠ 0 ↔ γ (ℓ s) ≠ 0) ∧ (Γ s ≠ 0 → -(γ (ℓ s))⁻¹ = f (-(Γ s)⁻¹)) := by
    intro s hs
    have hiff := htip s hs
    exact ⟨⟨fun hne => ((hphys _ _).1 ((hiff _).1 ((hrel s _).2 ⟨hne, rfl⟩))).1,
      fun hne => ((hrel s _).1 ((hiff _).2 ((hphys _ _).2 ⟨hne, rfl⟩))).1⟩,
      fun hne => ((hphys _ _).1 ((hiff _).1 ((hrel s _).2 ⟨hne, rfl⟩))).2.symm⟩
  -- the protected tails exclude every image of a relative trace point in the piece
  have hΓH : ∀ u, Γ u ∈ Hbar := fun u => Sec7.IsGeneratingTrace.mem_Hbar hΓ hwrc.continuousOn hwr0 le_top
  have hnot : ∀ u, Γ u ≠ 0 → f (-(Γ u)⁻¹) ∉ A := by
    intro u hu hmem
    rw [hAr] at hmem
    obtain ⟨him, hbL, hbR⟩ := mem_base_of_mem_trace hUc hU0 hUnn hαr hfF (GW4Traverse.negInv_mem_Hbar (hΓH u)) hmem
    obtain ⟨x, hx⟩ : ∃ x : ℝ, -(Γ u)⁻¹ = (x : ℂ) := ⟨(-(Γ u)⁻¹).re, Complex.ext rfl (by simp [him])⟩
    rw [hx, Complex.ofReal_re] at hbL hbR
    have hΓx : Γ u = ((-x⁻¹ : ℝ) : ℂ) := by
      have h1 : (Γ u)⁻¹ = -(x : ℂ) := by linear_combination -hx
      rw [← inv_inv (Γ u), h1]
      push_cast
      ring
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, inv_zero, neg_zero, Complex.ofReal_zero] at hΓx
      exact hu hΓx
    have hΓim : (Γ u).im = 0 := by rw [hΓx, Complex.ofReal_im]
    have hΓre : (Γ u).re = -x⁻¹ := by rw [hΓx, Complex.ofReal_re]
    rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · have hbL0 : baseL U ζ < 0 := lt_of_le_of_lt hbL hneg
      have h1 := hRt hbL0 u
      rw [rightGap_pos_iff] at h1
      refine h1 ⟨hΓim, ?_⟩
      rw [hΓre]
      unfold junctionR
      have := (inv_le_inv_of_neg hneg hbL0).2 hbL
      linarith
    · have hbR0 : 0 < baseR U ζ := lt_of_lt_of_le hpos hbR
      have h1 := hLt hbR0 u
      rw [leftGap_pos_iff] at h1
      refine h1 ⟨hΓim, ?_⟩
      rw [hΓre]
      unfold junctionL
      have := inv_anti₀ hpos hbR
      linarith
  rcases eq_or_ne L ⊤ with hL | hL
  · -- infinite relative lifetime: relative transience gives the tip `q`
    subst hL
    obtain ⟨hℓtop, hℓfin⟩ := tendsto_clock (F := atTop) hmono himg
      (Eventually.of_forall fun s => ENNReal.coe_lt_top) (fun s₀ _ => eventually_gt_atTop s₀)
    obtain ⟨pT, -, -, hγlim, hp0, hpT⟩ := phys_limit hγc hγtr h0A hT1 hℓtop hℓfin
    have hΓne : ∀ᶠ s in atTop, Γ s ≠ 0 := (hΓtr.eventually_gt_atTop 0).mono fun s hs => norm_pos_iff.1 hs
    have hinv : Tendsto (fun s => -(Γ s)⁻¹) atTop (𝓝[Hbar] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun s => GW4Traverse.negInv_mem_Hbar (hΓH s)⟩
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact (tendsto_inv_atTop_zero.comp hΓtr).congr fun s => by simp [norm_neg, norm_inv]
    have hrelLim : Tendsto (fun s => f (-(Γ s)⁻¹)) atTop (𝓝 (q : ℂ)) := by
      rw [← hf0]; exact (hfcont 0 h0H).tendsto.comp hinv
    have hEq : (fun s => -(γ (ℓ s))⁻¹) =ᶠ[atTop] fun s => f (-(Γ s)⁻¹) := by
      filter_upwards [hΓne] with s hs
      exact (hcomb s ENNReal.coe_lt_top).2 hs
    have hpq : pT = (q : ℂ) := tendsto_nhds_unique (hγlim.congr' hEq) hrelLim
    rcases eq_or_ne T ⊤ with hT | hT
    · exfalso
      rw [hp0 hT] at hpq
      exact hq0 (Complex.ofReal_eq_zero.1 hpq.symm)
    · obtain ⟨T₀, hT₀'⟩ : ∃ T₀ : ℝ≥0, T = T₀ := ⟨T.toNNReal, (ENNReal.coe_toNNReal hT).symm⟩
      obtain ⟨hne, -⟩ := hT1 T₀ hT₀'
      refine ⟨rfl, by rw [hT₀']; exact ENNReal.coe_lt_top, ?_⟩
      rw [hT₀', ENNReal.toNNReal_coe]
      exact (hphys T₀ _).2 ⟨hne, by rw [← hpq, hpT T₀ hT₀']⟩
  · -- finite relative lifetime: impossible
    exfalso
    obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ≥0, L = L₀ := ⟨L.toNNReal, (ENNReal.coe_toNNReal hL).symm⟩
    subst hL₀
    rcases eq_or_ne L₀ 0 with hL0 | hL0
    · subst hL0
      have hempty : {s : ℝ≥0 | (s : ℝ≥0∞) < ((0 : ℝ≥0) : ℝ≥0∞)} = ∅ := by
        ext s; simp only [ENNReal.coe_zero, mem_ofPred_eq, not_lt_zero, mem_empty_iff_false]
      rw [hempty, image_empty] at himg
      have hT0 : T = 0 := by
        by_contra hne
        have h0 : (0 : ℝ≥0) ∈ ({u : ℝ≥0 | (u : ℝ≥0∞) < T} : Set ℝ≥0) := by
          show ((0 : ℝ≥0) : ℝ≥0∞) < T
          rw [ENNReal.coe_zero]; exact pos_iff_ne_zero.2 hne
        rw [← himg] at h0
        exact h0
      obtain ⟨hne, -⟩ := hT1 0 (by rw [hT0, ENNReal.coe_zero])
      exact hne hγ.1
    have hL0' : 0 < L₀ := pos_iff_ne_zero.2 hL0
    have : (𝓝[<] L₀).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hL0'⟩
    have hFI : ∀ᶠ s in 𝓝[<] L₀, s ∈ {s : ℝ≥0 | (s : ℝ≥0∞) < L₀} := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact ENNReal.coe_lt_coe.2 hs
    have hF : ∀ s₀ ∈ {s : ℝ≥0 | (s : ℝ≥0∞) < L₀}, ∀ᶠ s in 𝓝[<] L₀, s₀ < s := fun s₀ hs₀ =>
      Filter.mem_of_superset (Ioo_mem_nhdsLT (ENNReal.coe_lt_coe.1 hs₀)) fun s hs => hs.1
    obtain ⟨hℓtop, hℓfin⟩ := tendsto_clock hmono himg hFI hF
    obtain ⟨pT, hpTA, hγne, hγlim, -, -⟩ := phys_limit hγc hγtr h0A hT1 hℓtop hℓfin
    have hΓlim : Tendsto Γ (𝓝[<] L₀) (𝓝 (Γ L₀)) := (hΓc.tendsto L₀).mono_left nhdsWithin_le_nhds
    have hEq : ∀ᶠ s in 𝓝[<] L₀, Γ s ≠ 0 ∧ -(γ (ℓ s))⁻¹ = f (-(Γ s)⁻¹) := by
      filter_upwards [hγne, hFI] with s hs hsI
      have h := hcomb s hsI
      have hΓs := h.1.2 hs
      exact ⟨hΓs, h.2 hΓs⟩
    rcases eq_or_ne (Γ L₀) 0 with hw0 | hw0
    · -- the relative tips blow up while the physical tips stay bounded
      rw [hw0] at hΓlim
      set M : ℝ := ‖pT‖ + 1 with hMdef
      have hbdd : ∀ᶠ s in 𝓝[<] L₀, ‖-(γ (ℓ s))⁻¹‖ < M :=
        ((continuous_norm.tendsto pT).comp hγlim).eventually (gt_mem_nhds (by linarith))
      have hK : (0 : ℝ) < M + |C| + 1 := by positivity
      have hsmall : ∀ᶠ s in 𝓝[<] L₀, ‖Γ s‖ < (M + |C| + 1)⁻¹ := by
        have h := (continuous_norm.tendsto (0 : ℂ)).comp hΓlim
        rw [norm_zero] at h
        exact h.eventually (gt_mem_nhds (inv_pos.2 hK))
      obtain ⟨s, ⟨hne, heq⟩, hb, hsm⟩ := (hEq.and (hbdd.and hsmall)).exists
      have hpH := GW4Traverse.negInv_mem_Hbar (hΓH s)
      have hCs := hC _ hpH
      have h1 : ‖-(Γ s)⁻¹‖ = ‖Γ s‖⁻¹ := by rw [norm_neg, norm_inv]
      have h2 : ‖-(Γ s)⁻¹‖ - C ≤ ‖f (-(Γ s)⁻¹)‖ := by
        have := norm_sub_norm_le (-(Γ s)⁻¹) (f (-(Γ s)⁻¹))
        rw [norm_sub_rev] at this
        linarith
      rw [← heq] at h2
      have h3 : M + |C| + 1 < ‖Γ s‖⁻¹ := (lt_inv_comm₀ (norm_pos_iff.2 hne) hK).1 hsm
      have := le_abs_self C
      linarith
    · -- the endpoint would be an image of a relative point in the piece, on a protected tail
      have hpH : -(Γ L₀)⁻¹ ∈ Hbar := GW4Traverse.negInv_mem_Hbar (hΓH L₀)
      have hinvlim : Tendsto (fun s => -(Γ s)⁻¹) (𝓝[<] L₀) (𝓝[Hbar] (-(Γ L₀)⁻¹)) :=
        tendsto_nhdsWithin_iff.2 ⟨(hΓlim.inv₀ hw0).neg,
          Eventually.of_forall fun s => GW4Traverse.negInv_mem_Hbar (hΓH s)⟩
      have hflim : Tendsto (fun s => f (-(Γ s)⁻¹)) (𝓝[<] L₀) (𝓝 (f (-(Γ L₀)⁻¹))) :=
        (hfcont _ hpH).tendsto.comp hinvlim
      have hpT : pT = f (-(Γ L₀)⁻¹) :=
        tendsto_nhds_unique (hγlim.congr' (hEq.mono fun s h => h.2)) hflim
      exact hnot L₀ hw0 (hpT ▸ hpTA)

end InteractingSLE.Theorem14.BW1In
