/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsComp

/-!
# Central prefix matches with a controlled prefix time

Packet PROVE-WALK-WORDS2. `WalkWords.exists_isPiecePhysicalMatch_right` / `_left` (PROVE-WALK-WORDS) give, at a
positive (negative) real point whose landing `p` is a fresh point of the right (left) walk in `ℍ`, a recorded prefix
`(pre, pc, τ)` through `p` with the complete prefix match for every reference hull containing the prefix's hull; the
prefix time `τ` is any rational time in a window after the own time of `p`. For the exit data `BeforeExit` of a bounded
component the prefix must stop before the component's closing contact, so here the window is also shrunk inside a
prescribed open set `U ∋ p`, and the conclusion records a **fresh point of the same piece after the prefix, inside
`U`** (on the walk, off the prefix set): `exists_controlledMatch_right` / `_left`. The proofs are those of
PROVE-WALK-WORDS with the smaller window; the added point is the piece at a rational time between `τ` and the end
of the window (fresh: off the old set by simplicity, off the prefix by injectivity of the piece).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.WalkWd

open WalkBdry WalkWords

/-- **The prefix match of a chart landing on the right walk, with the prefix stopped inside `U`** (see the module
docstring). -/
theorem exists_controlledMatch_right {sR sL : ExplState}
    (hdR : ∀ (pre post : List Piece) (pc : Piece), sR.1 = pre ++ pc :: post →
      ∃ (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ), PieceData pc (⋃ p ∈ pre, p.1.tipSet p.2.1 p.2.2) f W α)
    (hfrontR : ∀ (pre post : List Piece) (pc : Piece), sR.1 = pre ++ pc :: post →
      (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2 → frontier ((prefixChart pc 0).dom : Set ℂ) ∩ H ⊆ prefixSet pre pc 0)
    {C : Set ℂ} (hCR : Disjoint C (wsetOf sR)) {c : Chart} (hc : c.IsConformal) (hcC : MapsTo c.2.1 H C)
    (hlandR : ∀ x : ℝ, 0 < x → ∃ z : ℂ, Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 z) ∧ (z ∈ ordOf sR ∨ z.im = 0))
    {x₀ : ℝ} {p : ℂ} (hx₀ : 0 < x₀) (hp : Tendsto c.2.1 (𝓝[H] (x₀ : ℂ)) (𝓝 p)) (hpH : p ∈ H)
    {U : Set ℂ} (hU : IsOpen U) (hpU : p ∈ U)
    (hpR : p ∈ ordOf sR) (hpF : p ∉ pieceEnds sR.1) (hpL : p ∉ closure (wsetOf sL))
    (horient : ∀ pc ∈ sR.1, ∀ (x x' : ℝ) (t t' : ℝ≥0) (z z' : ℂ), 0 < x → x < x' →
      Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 z) → Tendsto c.2.1 (𝓝[H] (x' : ℂ)) (𝓝 z') →
      (t : ℝ≥0∞) ≤ pc.2.2 → (t' : ℝ≥0∞) ≤ pc.2.2 → pc.1.tipAt pc.2.1 t z → pc.1.tipAt pc.2.1 t' z' → t < t') :
    ∃ (pre post : List Piece) (pc : Piece) (τ : ℚ≥0), sR.1 = pre ++ pc :: post ∧
      (((τ : ℝ≥0)) : ℝ≥0∞) < pc.2.2 ∧
      (∃ z ∈ U, z ∈ wsetOf sR ∧ z ∉ prefixSet pre pc τ) ∧ ∀ {d : Chart} (B : WalkIntCanon.HullModel d)
        (A : WalkIntCanon.HullModel (prefixChart pc τ)), A.hull ⊆ B.hull →
        WalkIntFiber.IsPiecePhysicalMatch sR sL true c B x₀ := by
  classical
  -- the piece through `p`
  obtain ⟨pc, hpc, hppc⟩ := mem_iUnion₂.1 hpR
  obtain ⟨pre, post, hs⟩ := List.append_of_mem hpc
  obtain ⟨f, V, α, d⟩ := hdR _ _ _ hs
  set g : ℝ≥0 → ℂ := fun t => f (α t) with hgdef
  rw [d.tipSet_eq] at hppc
  obtain ⟨t₀, ht₀D, ht₀e⟩ := hppc
  replace ht₀e : g t₀ = p := ht₀e
  have hcl : ∀ p' ∈ sR.1, IsClosed (p'.1.tipSet p'.2.1 p'.2.2) := fun p' hp' => by
    obtain ⟨a', b', h'⟩ := List.append_of_mem hp'
    obtain ⟨_, _, _, d'⟩ := hdR _ _ _ h'
    exact d'.isClosed_tipSet
  have hpost : ∀ p' ∈ post, ∀ z ∈ p'.1.tipSet p'.2.1 p'.2.2, z ∈ pc.1.tipSet pc.2.1 pc.2.2 →
      p'.1.tipAt p'.2.1 0 z := by
    intro p' hp' z hz hzpc
    obtain ⟨m, post', hpost⟩ := List.append_of_mem hp'
    have hdec : sR.1 = (pre ++ pc :: m) ++ p' :: post' := by rw [hs, hpost]; simp
    obtain ⟨_, _, _, d'⟩ := hdR _ _ _ hdec
    exact d'.tipAt_zero_of_mem (fun w hw => mem_iUnion₂.2 ⟨pc, by simp, hw⟩) hz hzpc
  have hno : ∀ p' ∈ post, ¬ p'.1.tipAt p'.2.1 0 (g t₀) := fun p' hp' h => hpF
    ⟨p', by rw [hs]; simp [hp'], Or.inl (by rw [← ht₀e]; exact h)⟩
  -- `p` is an interior fresh point of the piece
  have hend : 0 < t₀ ∧ (t₀ : ℝ≥0∞) < pc.2.2 := by
    refine ⟨?_, lt_of_le_of_ne ht₀D fun h => hpF ⟨pc, hpc, Or.inr ⟨t₀, h.symm, ?_⟩⟩⟩
    · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t₀) with h0 | h0
      · refine absurd ⟨pc, hpc, Or.inl ?_⟩ hpF
        rw [← ht₀e, ← h0]; exact d.tipAt (by simp)
      · exact h0
    · rw [← ht₀e]; exact d.tipAt ht₀D
  have hstart : ¬ pc.1.tipAt pc.2.1 0 (g t₀) := fun h => hpF ⟨pc, hpc, Or.inl (by rw [← ht₀e]; exact h)⟩
  have hgdom : g t₀ ∈ pc.1.2.1 '' H :=
    d.mem_image_of_frontier (hfrontR _ _ _ hs
    (lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hend.1) ht₀D)) hend.1 ht₀D (by show g t₀ ∈ H; rw [ht₀e]; exact hpH) hstart
  have hα₀ : α t₀ ∈ H := d.mem_H_of_mem_image ht₀D hgdom
  -- the fresh window, the prefix time and the model
  obtain ⟨ε, hε, hwin⟩ := d.exists_window ht₀D d.conf.isOpen_image hgdom
  obtain ⟨εU, hεU, hwinU⟩ := d.exists_window ht₀D hU (by show g t₀ ∈ U; rw [ht₀e]; exact hpU)
  set δ' : ℝ := min (min ε εU) (t₀ : ℝ) with hδ'def
  have hδ' : 0 < δ' := lt_min (lt_min hε hεU) (by exact_mod_cast hend.1)
  have hδ'1 : δ' ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hδ'U : δ' ≤ εU := (min_le_left _ _).trans (min_le_right _ _)
  have hδ'2 : δ' ≤ t₀ := min_le_right _ _
  obtain ⟨τ, hτ1, hτ2, hτS⟩ := exists_nnrat_window hend.2 hδ'
  set s₀ : ℝ := (t₀ : ℝ) - δ' / 2 with hs₀
  have hs₀0 : 0 ≤ s₀ := by rw [hs₀]; linarith
  have hs₀t : s₀ < t₀ := by rw [hs₀]; linarith
  have hHw : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ pc.2.2 → s₀ < t → (t : ℝ) ≤ (τ : ℝ≥0) → α t ∈ H := by
    intro t ht h1 h2
    refine d.mem_H_of_mem_image ht (hwin t ht ?_)
    rw [abs_lt]; constructor <;> linarith
  obtain ⟨W', η, T', hτT, hWc, hW0, hη, hpcT, hag, hηα⟩ := d.exists_model hτS
  have hηt : ∀ t : ℝ≥0, (t : ℝ) ≤ T' → η t = α t := fun t ht => by
    rw [hηα t ⟨t.coe_nonneg, ht⟩, Real.toNNReal_coe]
  have htS : ∀ t : ℝ≥0, (t : ℝ) ≤ (τ : ℝ≥0) → (t : ℝ≥0∞) ≤ pc.2.2 := fun t ht =>
    le_trans (ENNReal.coe_le_coe.2 (by exact_mod_cast ht)) hτS.le
  have hinj : InjOn η (Icc 0 ((τ : ℝ≥0) : ℝ)) := by
    intro r₁ hr₁ r₂ hr₂ he
    rw [hηα r₁ ⟨hr₁.1, hr₁.2.trans hτT.le⟩, hηα r₂ ⟨hr₂.1, hr₂.2.trans hτT.le⟩] at he
    have hd1 := htS r₁.toNNReal (by rw [Real.coe_toNNReal _ hr₁.1]; exact hr₁.2)
    have hd2 := htS r₂.toNNReal (by rw [Real.coe_toNNReal _ hr₂.1]; exact hr₂.2)
    have h := congrArg (fun t : ℝ≥0 => (t : ℝ)) (d.inj hd1 hd2 (show f (α _) = f (α _) by rw [he]))
    simp only [Real.coe_toNNReal _ hr₁.1, Real.coe_toNNReal _ hr₂.1] at h
    exact h
  have hfresh : ∀ s ∈ Ioc s₀ ((τ : ℝ≥0) : ℝ), η s ∈ H := by
    intro s hs
    have hs0 : 0 ≤ s := hs₀0.trans hs.1.le
    have hs' : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs0
    rw [hηα s ⟨hs0, hs.2.trans hτT.le⟩]
    exact hHw _ (htS _ (by rw [hs']; exact hs.2)) (by rw [hs']; exact hs.1) (by rw [hs']; exact hs.2)
  have hp' : pc.1.2.1 (η t₀) = p := by
    rw [hηt t₀ (hτ1.le.trans hτT.le), ← d.eq_of_mem_H hα₀]; exact ht₀e
  -- the walk near `p`, the left walk away from `p`, the prefix domain near `p`
  obtain ⟨ρw, hρw, hwalk⟩ := exists_ball_walk_window hs d hcl hpost hend.1 ht₀D hno
    (lo := s₀) (hi := ((τ : ℝ≥0) : ℝ)) hs₀t hτ1
  have hcp : f (α t₀) = p := ht₀e
  rw [hcp] at hwalk
  obtain ⟨ρL, hρL, hρLL⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl p hpL
  obtain ⟨ρd, hρd, hball⟩ := exists_ball_mem_loewner_image d.conf hη hWc hW0 hs₀0 hs₀t hτ1.le hinj hfresh
  rw [hp'] at hball
  -- the left side point and its landing
  have hFresh' : ∀ s ∈ Icc (t₀ : ℝ) ((τ : ℝ≥0) : ℝ), η s ∈ H := fun s hs =>
    hfresh s ⟨hs₀t.trans_le hs.1, hs.2⟩
  have hag' : EqOn (pieceDrv pc) W' (Icc 0 ((τ : ℝ≥0) : ℝ)) := hag.mono (Icc_subset_Icc_right hτT.le)
  obtain ⟨y, hyside, hFy, -⟩ := WalkNorm.exists_isLeftSidePt_of_cut (pc := pc) (τ := (τ : ℝ≥0)) hη hWc hW0
    hag' t₀.coe_nonneg hτ1 hinj hFresh'
  have hlandy : Tendsto (prefixChart pc (τ : ℝ≥0)).2.1 (𝓝[H] (y : ℂ)) (𝓝 p) := by
    rw [← hp']
    exact WalkNorm.tendsto_prefixChart_inv_of_eq hη hWc hW0 d.conf hτT hpcT hag'
      (hFresh' t₀ ⟨le_rfl, hτ1.le⟩) hFy
  -- the landings of `c` near `x₀`
  set Λ : ℝ → ℂ := fun x => if h : 0 < x then Classical.choose (hlandR x h) else 0 with hΛdef
  have hΛ : ∀ x : ℝ, 0 < x → Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (Λ x)) ∧ (Λ x ∈ ordOf sR ∨ (Λ x).im = 0) :=
    fun x hx => by
      have e : Λ x = Classical.choose (hlandR x hx) := by simp only [hΛdef, hx, ↓reduceDIte]
      rw [e]; exact Classical.choose_spec (hlandR x hx)
  have hρ₁ : 0 < min ρw (min ρL (min ρd p.im)) := lt_min hρw (lt_min hρL (lt_min hρd hpH))
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := exists_landing_ball hp hρ₁
  set δ : ℝ := min δ₁ x₀ with hδdef
  have hδ : 0 < δ := lt_min hδ₁ hx₀
  have hrep : ∀ x : ℝ, |x - x₀| < δ → 0 < x ∧ ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ pc.2.2 ∧ s₀ < t ∧
      (t : ℝ) < (τ : ℝ≥0) ∧ Λ x = g t ∧ α t ∈ H := by
    intro x hx
    have hx0 : 0 < x := by
      have := (abs_lt.1 hx).1; have : δ ≤ x₀ := min_le_right _ _; linarith
    refine ⟨hx0, ?_⟩
    obtain ⟨hl, hor⟩ := hΛ x hx0
    have hb := hδ₁b x (lt_of_lt_of_le hx (min_le_left _ _)) _ hl
    have hΛH : (Λ x).im ≠ 0 := by
      intro h0
      rw [mem_ball, dist_eq_norm] at hb
      have h1 := Complex.abs_im_le_norm (Λ x - p)
      rw [sub_im, h0, zero_sub, abs_neg] at h1
      have h2 : min ρw (min ρL (min ρd p.im)) ≤ p.im :=
        (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
      have h3 : (0 : ℝ) < p.im := hpH
      rw [abs_of_pos h3] at h1
      linarith
    obtain ⟨t, htD, ht1, ht2, hte⟩ := hwalk (Λ x) ⟨hor.resolve_right hΛH, ball_subset_ball (min_le_left _ _) hb⟩
    exact ⟨t, htD, ht1, ht2, hte, hHw t htD ht1 ht2.le⟩
  have : (𝓝[H] (x₀ : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ ((x₀ : ℂ)).im by simp)
  have hΛ₀ : Λ x₀ = p := tendsto_nhds_unique (hΛ x₀ hx₀).1 hp
  -- the transition
  have hinvEq : (prefixChart pc (τ : ℝ≥0)).2.1 = (pc.1.loewner W' (τ : ℝ≥0)).2.1 :=
    funext (prefixChart_inv_eq_loewner hWc hpcT hag hτT)
  obtain ⟨δd, hδd, hδdb⟩ := Metric.tendsto_nhdsWithin_nhds.1 hp ρd hρd
  obtain ⟨δt, hδt, hdomt, -, hlimt⟩ :=
    exists_prefix_transition_of_later (Λ := fun z : ℂ => Λ z.re) (x₀ := x₀) hc d.conf hη
    hWc hW0 hpcT hag hτT t₀.coe_nonneg hτ1 hinj hFresh' hyside.1 hFy
    ⟨δ, hδ, fun x hx => (hΛ x (hrep x (abs_sub_lt_iff.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩)).1).1⟩
    ⟨δ, hδ, fun x hx => by
      obtain ⟨-, t, htD, ht1, ht2, hte, hαt⟩ := hrep x (abs_sub_lt_iff.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      refine ⟨t, ⟨t.coe_nonneg, ht2.le⟩, by rw [hηt t (ht2.le.trans hτT.le)]; exact hαt, ?_⟩
      show Λ x = _
      rw [hηt t (ht2.le.trans hτT.le), hte]
      exact d.eq_of_mem_H hαt⟩
    ⟨δd, hδd, fun z hz => by
      have hwC : c.2.1 z ∈ C := hcC hz.1
      have hwb : c.2.1 z ∈ ball p ρd := hδdb hz.1 (by rw [← mem_ball]; exact hz.2)
      rw [hinvEq]
      refine hball _ hwb fun ⟨v, ⟨s', hs', hsv⟩, hvw⟩ => ?_
      have hsH := hfresh s' hs'
      have hmem : pc.1.2.1 (η s') ∈ wsetOf sR :=
        mem_wsetOf_of_model hs d.conf hη hWc hW0 hpcT hag (hs₀0.trans hs'.1.le) (hs'.2.trans_lt hτT)
          (le_trans (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs'.2)) hτS.le) hsH
      rw [hsv, hvw] at hmem
      exact Set.disjoint_left.1 hCR hwC hmem⟩
    (by show Λ x₀ = _; rw [hΛ₀, hp'])
    ⟨δ, hδ, fun x hx => by
      obtain ⟨-, t, htD, ht1, ht2, hte, hαt⟩ := hrep x (abs_sub_lt_iff.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      have hlt : t₀ < t := horient pc hpc x₀ x t₀ t p (Λ x) hx₀ hx.1 hp (hΛ x (hx₀.trans hx.1)).1 ht₀D htD
        (by rw [← ht₀e]; exact d.tipAt ht₀D) (by rw [hte]; exact d.tipAt htD)
      refine ⟨t, ⟨by exact_mod_cast hlt, ht2⟩, ?_⟩
      show Λ x = _
      rw [hηt t (ht2.le.trans hτT.le), hte]
      exact d.eq_of_mem_H hαt⟩
  -- a fresh point of the piece just after the prefix, inside `U`
  have hzU : ∃ z ∈ U, z ∈ wsetOf sR ∧ z ∉ prefixSet pre pc ((τ : ℚ≥0) : ℝ≥0) := by
    obtain ⟨τ₂, h21, h22, h23⟩ := exists_nnrat_window hτS (δ := (t₀ : ℝ) + δ' - ((τ : ℝ≥0) : ℝ)) (by linarith)
    have hτ₂S : (((τ₂ : ℝ≥0)) : ℝ≥0∞) ≤ pc.2.2 := h23.le
    have hd2 : |((τ₂ : ℝ≥0) : ℝ) - t₀| < δ' := by rw [abs_lt]; constructor <;> linarith
    have hτ₂pos : 0 < (τ₂ : ℝ≥0) := by
      rw [← NNReal.coe_pos]; linarith [(show (0 : ℝ) < t₀ by exact_mod_cast hend.1)]
    have hαH : α τ₂ ∈ H := d.mem_H_of_mem_image hτ₂S (hwin _ hτ₂S (lt_of_lt_of_le hd2 hδ'1))
    have hgH : g τ₂ ∈ H := by
      show f (α τ₂) ∈ H
      rw [d.eq_of_mem_H hαH]
      exact d.conf.2.1 hαH
    refine ⟨g τ₂, hwinU _ hτ₂S (lt_of_lt_of_le hd2 hδ'U), ⟨mem_iUnion₂.2 ⟨pc, hpc, ?_⟩, hgH⟩, ?_⟩
    · rw [d.tipSet_eq]; exact ⟨τ₂, hτ₂S, rfl⟩
    · rintro ⟨hz | hz, -⟩
      · exact d.avoid _ hτ₂pos hτ₂S hz
      · obtain ⟨t, ht, htip⟩ := hz
        have htS' : (t : ℝ≥0∞) ≤ pc.2.2 := ht.trans hτS.le
        have he : g t = g τ₂ := Chart.tipAt_unique (d.tipAt htS') htip
        have htt := d.inj htS' hτ₂S he
        have hle : (t : ℝ) ≤ ((τ : ℝ≥0) : ℝ) := by exact_mod_cast ENNReal.coe_le_coe.1 ht
        rw [htt] at hle
        linarith
  refine ⟨pre, post, pc, τ, hs, hτS, hzU, ?_⟩
  intro d' B A hAB
  refine ⟨pre, post, pc, τ, y, p, min ρw ρL, δt, A, hs, hτS, ?_, hlandy, Or.inl ⟨hpR, hpH⟩,
    lt_min hρw hρL, ?_, ?_, hAB, hδt, hdomt, hlimt⟩
  · exact hyside
  · rintro z ⟨⟨hzO, hzH⟩, hzb⟩
    obtain ⟨t, htD, -, ht2, rfl⟩ := hwalk _ ⟨hzO, ball_subset_ball (min_le_left _ _) hzb⟩
    exact ⟨Or.inr ⟨t, ENNReal.coe_le_coe.2 (by exact_mod_cast ht2.le), d.tipAt htD⟩, hzH⟩
  · rintro z ⟨hzL, hzb⟩
    exact absurd (subset_closure hzL) (hρLL (ball_subset_ball (min_le_right _ _) hzb))

/-- **The prefix match of a chart landing on the left walk, with the prefix stopped inside `U`** (mirror). -/
theorem exists_controlledMatch_left {sR sL : ExplState}
    (hdL : ∀ (pre post : List Piece) (pc : Piece), sL.1 = pre ++ pc :: post →
      ∃ (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ), PieceData pc (⋃ p ∈ pre, p.1.tipSet p.2.1 p.2.2) f W α)
    (hfrontL : ∀ (pre post : List Piece) (pc : Piece), sL.1 = pre ++ pc :: post →
      (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2 → frontier ((prefixChart pc 0).dom : Set ℂ) ∩ H ⊆ prefixSet pre pc 0)
    {C : Set ℂ} (hCL : Disjoint C (wsetOf sL)) {c : Chart} (hc : c.IsConformal) (hcC : MapsTo c.2.1 H C)
    (hlandL : ∀ x : ℝ, x < 0 → ∃ z : ℂ, Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 z) ∧ (z ∈ ordOf sL ∨ z.im = 0))
    {x₀ : ℝ} {p : ℂ} (hx₀ : x₀ < 0) (hp : Tendsto c.2.1 (𝓝[H] (x₀ : ℂ)) (𝓝 p)) (hpH : p ∈ H)
    {U : Set ℂ} (hU : IsOpen U) (hpU : p ∈ U)
    (hpL : p ∈ ordOf sL) (hpF : p ∉ pieceEnds sL.1) (hpR : p ∉ closure (wsetOf sR))
    (horient : ∀ pc ∈ sL.1, ∀ (x x' : ℝ) (t t' : ℝ≥0) (z z' : ℂ), x < x' → x' < 0 →
      Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 z) → Tendsto c.2.1 (𝓝[H] (x' : ℂ)) (𝓝 z') →
      (t : ℝ≥0∞) ≤ pc.2.2 → (t' : ℝ≥0∞) ≤ pc.2.2 → pc.1.tipAt pc.2.1 t z → pc.1.tipAt pc.2.1 t' z' → t' < t) :
    ∃ (pre post : List Piece) (pc : Piece) (τ : ℚ≥0), sL.1 = pre ++ pc :: post ∧
      (((τ : ℝ≥0)) : ℝ≥0∞) < pc.2.2 ∧
      (∃ z ∈ U, z ∈ wsetOf sL ∧ z ∉ prefixSet pre pc τ) ∧ ∀ {d : Chart} (B : WalkIntCanon.HullModel d)
        (A : WalkIntCanon.HullModel (prefixChart pc τ)), A.hull ⊆ B.hull →
        WalkIntFiber.IsPiecePhysicalMatch sL sR false c B x₀ := by
  classical
  -- the piece through `p`
  obtain ⟨pc, hpc, hppc⟩ := mem_iUnion₂.1 hpL
  obtain ⟨pre, post, hs⟩ := List.append_of_mem hpc
  obtain ⟨f, V, α, d⟩ := hdL _ _ _ hs
  set g : ℝ≥0 → ℂ := fun t => f (α t) with hgdef
  rw [d.tipSet_eq] at hppc
  obtain ⟨t₀, ht₀D, ht₀e⟩ := hppc
  replace ht₀e : g t₀ = p := ht₀e
  have hcl : ∀ p' ∈ sL.1, IsClosed (p'.1.tipSet p'.2.1 p'.2.2) := fun p' hp' => by
    obtain ⟨a', b', h'⟩ := List.append_of_mem hp'
    obtain ⟨_, _, _, d'⟩ := hdL _ _ _ h'
    exact d'.isClosed_tipSet
  have hpost : ∀ p' ∈ post, ∀ z ∈ p'.1.tipSet p'.2.1 p'.2.2, z ∈ pc.1.tipSet pc.2.1 pc.2.2 →
      p'.1.tipAt p'.2.1 0 z := by
    intro p' hp' z hz hzpc
    obtain ⟨m, post', hpost⟩ := List.append_of_mem hp'
    have hdec : sL.1 = (pre ++ pc :: m) ++ p' :: post' := by rw [hs, hpost]; simp
    obtain ⟨_, _, _, d'⟩ := hdL _ _ _ hdec
    exact d'.tipAt_zero_of_mem (fun w hw => mem_iUnion₂.2 ⟨pc, by simp, hw⟩) hz hzpc
  have hno : ∀ p' ∈ post, ¬ p'.1.tipAt p'.2.1 0 (g t₀) := fun p' hp' h => hpF
    ⟨p', by rw [hs]; simp [hp'], Or.inl (by rw [← ht₀e]; exact h)⟩
  -- `p` is an interior fresh point of the piece
  have hend : 0 < t₀ ∧ (t₀ : ℝ≥0∞) < pc.2.2 := by
    refine ⟨?_, lt_of_le_of_ne ht₀D fun h => hpF ⟨pc, hpc, Or.inr ⟨t₀, h.symm, ?_⟩⟩⟩
    · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t₀) with h0 | h0
      · refine absurd ⟨pc, hpc, Or.inl ?_⟩ hpF
        rw [← ht₀e, ← h0]; exact d.tipAt (by simp)
      · exact h0
    · rw [← ht₀e]; exact d.tipAt ht₀D
  have hstart : ¬ pc.1.tipAt pc.2.1 0 (g t₀) := fun h => hpF ⟨pc, hpc, Or.inl (by rw [← ht₀e]; exact h)⟩
  have hgdom : g t₀ ∈ pc.1.2.1 '' H :=
    d.mem_image_of_frontier (hfrontL _ _ _ hs
    (lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hend.1) ht₀D)) hend.1 ht₀D (by show g t₀ ∈ H; rw [ht₀e]; exact hpH) hstart
  have hα₀ : α t₀ ∈ H := d.mem_H_of_mem_image ht₀D hgdom
  -- the fresh window, the prefix time and the model
  obtain ⟨ε, hε, hwin⟩ := d.exists_window ht₀D d.conf.isOpen_image hgdom
  obtain ⟨εU, hεU, hwinU⟩ := d.exists_window ht₀D hU (by show g t₀ ∈ U; rw [ht₀e]; exact hpU)
  set δ' : ℝ := min (min ε εU) (t₀ : ℝ) with hδ'def
  have hδ' : 0 < δ' := lt_min (lt_min hε hεU) (by exact_mod_cast hend.1)
  have hδ'1 : δ' ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hδ'U : δ' ≤ εU := (min_le_left _ _).trans (min_le_right _ _)
  have hδ'2 : δ' ≤ t₀ := min_le_right _ _
  obtain ⟨τ, hτ1, hτ2, hτS⟩ := exists_nnrat_window hend.2 hδ'
  set s₀ : ℝ := (t₀ : ℝ) - δ' / 2 with hs₀
  have hs₀0 : 0 ≤ s₀ := by rw [hs₀]; linarith
  have hs₀t : s₀ < t₀ := by rw [hs₀]; linarith
  have hHw : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ pc.2.2 → s₀ < t → (t : ℝ) ≤ (τ : ℝ≥0) → α t ∈ H := by
    intro t ht h1 h2
    refine d.mem_H_of_mem_image ht (hwin t ht ?_)
    rw [abs_lt]; constructor <;> linarith
  obtain ⟨W', η, T', hτT, hWc, hW0, hη, hpcT, hag, hηα⟩ := d.exists_model hτS
  have hηt : ∀ t : ℝ≥0, (t : ℝ) ≤ T' → η t = α t := fun t ht => by
    rw [hηα t ⟨t.coe_nonneg, ht⟩, Real.toNNReal_coe]
  have htS : ∀ t : ℝ≥0, (t : ℝ) ≤ (τ : ℝ≥0) → (t : ℝ≥0∞) ≤ pc.2.2 := fun t ht =>
    le_trans (ENNReal.coe_le_coe.2 (by exact_mod_cast ht)) hτS.le
  have hinj : InjOn η (Icc 0 ((τ : ℝ≥0) : ℝ)) := by
    intro r₁ hr₁ r₂ hr₂ he
    rw [hηα r₁ ⟨hr₁.1, hr₁.2.trans hτT.le⟩, hηα r₂ ⟨hr₂.1, hr₂.2.trans hτT.le⟩] at he
    have hd1 := htS r₁.toNNReal (by rw [Real.coe_toNNReal _ hr₁.1]; exact hr₁.2)
    have hd2 := htS r₂.toNNReal (by rw [Real.coe_toNNReal _ hr₂.1]; exact hr₂.2)
    have h := congrArg (fun t : ℝ≥0 => (t : ℝ)) (d.inj hd1 hd2 (show f (α _) = f (α _) by rw [he]))
    simp only [Real.coe_toNNReal _ hr₁.1, Real.coe_toNNReal _ hr₂.1] at h
    exact h
  have hfresh : ∀ s ∈ Ioc s₀ ((τ : ℝ≥0) : ℝ), η s ∈ H := by
    intro s hs
    have hs0 : 0 ≤ s := hs₀0.trans hs.1.le
    have hs' : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs0
    rw [hηα s ⟨hs0, hs.2.trans hτT.le⟩]
    exact hHw _ (htS _ (by rw [hs']; exact hs.2)) (by rw [hs']; exact hs.1) (by rw [hs']; exact hs.2)
  have hp' : pc.1.2.1 (η t₀) = p := by
    rw [hηt t₀ (hτ1.le.trans hτT.le), ← d.eq_of_mem_H hα₀]; exact ht₀e
  -- the walk near `p`, the left walk away from `p`, the prefix domain near `p`
  obtain ⟨ρw, hρw, hwalk⟩ := exists_ball_walk_window hs d hcl hpost hend.1 ht₀D hno
    (lo := s₀) (hi := ((τ : ℝ≥0) : ℝ)) hs₀t hτ1
  have hcp : f (α t₀) = p := ht₀e
  rw [hcp] at hwalk
  obtain ⟨ρL, hρL, hρLL⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl p hpR
  obtain ⟨ρd, hρd, hball⟩ := exists_ball_mem_loewner_image d.conf hη hWc hW0 hs₀0 hs₀t hτ1.le hinj hfresh
  rw [hp'] at hball
  -- the left side point and its landing
  have hFresh' : ∀ s ∈ Icc (t₀ : ℝ) ((τ : ℝ≥0) : ℝ), η s ∈ H := fun s hs =>
    hfresh s ⟨hs₀t.trans_le hs.1, hs.2⟩
  have hag' : EqOn (pieceDrv pc) W' (Icc 0 ((τ : ℝ≥0) : ℝ)) := hag.mono (Icc_subset_Icc_right hτT.le)
  obtain ⟨y, hyside, hFy, -⟩ := WalkNorm.exists_isRightSidePt_of_cut (pc := pc) (τ := (τ : ℝ≥0)) hη hWc hW0
    hag' t₀.coe_nonneg hτ1 hinj hFresh'
  have hlandy : Tendsto (prefixChart pc (τ : ℝ≥0)).2.1 (𝓝[H] (y : ℂ)) (𝓝 p) := by
    rw [← hp']
    exact WalkNorm.tendsto_prefixChart_inv_of_eq hη hWc hW0 d.conf hτT hpcT hag'
      (hFresh' t₀ ⟨le_rfl, hτ1.le⟩) hFy
  -- the landings of `c` near `x₀`
  set Λ : ℝ → ℂ := fun x => if h : x < 0 then Classical.choose (hlandL x h) else 0 with hΛdef
  have hΛ : ∀ x : ℝ, x < 0 → Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (Λ x)) ∧ (Λ x ∈ ordOf sL ∨ (Λ x).im = 0) :=
    fun x hx => by
      have e : Λ x = Classical.choose (hlandL x hx) := by simp only [hΛdef, hx, ↓reduceDIte]
      rw [e]; exact Classical.choose_spec (hlandL x hx)
  have hρ₁ : 0 < min ρw (min ρL (min ρd p.im)) := lt_min hρw (lt_min hρL (lt_min hρd hpH))
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := exists_landing_ball hp hρ₁
  set δ : ℝ := min δ₁ (-x₀) with hδdef
  have hδ : 0 < δ := lt_min hδ₁ (by linarith)
  have hrep : ∀ x : ℝ, |x - x₀| < δ → x < 0 ∧ ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ pc.2.2 ∧ s₀ < t ∧
      (t : ℝ) < (τ : ℝ≥0) ∧ Λ x = g t ∧ α t ∈ H := by
    intro x hx
    have hx0 : x < 0 := by
      have := (abs_lt.1 hx).2; have : δ ≤ -x₀ := min_le_right _ _; linarith
    refine ⟨hx0, ?_⟩
    obtain ⟨hl, hor⟩ := hΛ x hx0
    have hb := hδ₁b x (lt_of_lt_of_le hx (min_le_left _ _)) _ hl
    have hΛH : (Λ x).im ≠ 0 := by
      intro h0
      rw [mem_ball, dist_eq_norm] at hb
      have h1 := Complex.abs_im_le_norm (Λ x - p)
      rw [sub_im, h0, zero_sub, abs_neg] at h1
      have h2 : min ρw (min ρL (min ρd p.im)) ≤ p.im :=
        (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
      have h3 : (0 : ℝ) < p.im := hpH
      rw [abs_of_pos h3] at h1
      linarith
    obtain ⟨t, htD, ht1, ht2, hte⟩ := hwalk (Λ x) ⟨hor.resolve_right hΛH, ball_subset_ball (min_le_left _ _) hb⟩
    exact ⟨t, htD, ht1, ht2, hte, hHw t htD ht1 ht2.le⟩
  have : (𝓝[H] (x₀ : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ ((x₀ : ℂ)).im by simp)
  have hΛ₀ : Λ x₀ = p := tendsto_nhds_unique (hΛ x₀ hx₀).1 hp
  -- the transition
  have hinvEq : (prefixChart pc (τ : ℝ≥0)).2.1 = (pc.1.loewner W' (τ : ℝ≥0)).2.1 :=
    funext (prefixChart_inv_eq_loewner hWc hpcT hag hτT)
  obtain ⟨δd, hδd, hδdb⟩ := Metric.tendsto_nhdsWithin_nhds.1 hp ρd hρd
  obtain ⟨δt, hδt, hdomt, -, hlimt⟩ :=
    exists_prefix_transition_of_earlier (Λ := fun z : ℂ => Λ z.re) (x₀ := x₀) hc d.conf hη
    hWc hW0 hpcT hag hτT hs₀0 hs₀t hτ1 hinj hFresh' hyside.1 hFy
    ⟨δ, hδ, fun x hx => (hΛ x (hrep x (abs_sub_lt_iff.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩)).1).1⟩
    ⟨δ, hδ, fun x hx => by
      obtain ⟨-, t, htD, ht1, ht2, hte, hαt⟩ := hrep x (abs_sub_lt_iff.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      refine ⟨t, ⟨t.coe_nonneg, ht2.le⟩, by rw [hηt t (ht2.le.trans hτT.le)]; exact hαt, ?_⟩
      show Λ x = _
      rw [hηt t (ht2.le.trans hτT.le), hte]
      exact d.eq_of_mem_H hαt⟩
    ⟨δd, hδd, fun z hz => by
      have hwC : c.2.1 z ∈ C := hcC hz.1
      have hwb : c.2.1 z ∈ ball p ρd := hδdb hz.1 (by rw [← mem_ball]; exact hz.2)
      rw [hinvEq]
      refine hball _ hwb fun ⟨v, ⟨s', hs', hsv⟩, hvw⟩ => ?_
      have hsH := hfresh s' hs'
      have hmem : pc.1.2.1 (η s') ∈ wsetOf sL :=
        mem_wsetOf_of_model hs d.conf hη hWc hW0 hpcT hag (hs₀0.trans hs'.1.le) (hs'.2.trans_lt hτT)
          (le_trans (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs'.2)) hτS.le) hsH
      rw [hsv, hvw] at hmem
      exact Set.disjoint_left.1 hCL hwC hmem⟩
    (by show Λ x₀ = _; rw [hΛ₀, hp'])
    ⟨δ, hδ, fun x hx => by
      obtain ⟨hx0, t, htD, ht1, ht2, hte, hαt⟩ :=
        hrep x (abs_sub_lt_iff.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      have hlt : t < t₀ := horient pc hpc x₀ x t₀ t p (Λ x) hx.1 hx0 hp (hΛ x hx0).1 ht₀D htD
        (by rw [← ht₀e]; exact d.tipAt ht₀D) (by rw [hte]; exact d.tipAt htD)
      refine ⟨t, ⟨ht1, by exact_mod_cast hlt⟩, by rw [hηt t (ht2.le.trans hτT.le)]; exact hαt, ?_⟩
      show Λ x = _
      rw [hηt t (ht2.le.trans hτT.le), hte]
      exact d.eq_of_mem_H hαt⟩
  -- a fresh point of the piece just after the prefix, inside `U`
  have hzU : ∃ z ∈ U, z ∈ wsetOf sL ∧ z ∉ prefixSet pre pc ((τ : ℚ≥0) : ℝ≥0) := by
    obtain ⟨τ₂, h21, h22, h23⟩ := exists_nnrat_window hτS (δ := (t₀ : ℝ) + δ' - ((τ : ℝ≥0) : ℝ)) (by linarith)
    have hτ₂S : (((τ₂ : ℝ≥0)) : ℝ≥0∞) ≤ pc.2.2 := h23.le
    have hd2 : |((τ₂ : ℝ≥0) : ℝ) - t₀| < δ' := by rw [abs_lt]; constructor <;> linarith
    have hτ₂pos : 0 < (τ₂ : ℝ≥0) := by
      rw [← NNReal.coe_pos]; linarith [(show (0 : ℝ) < t₀ by exact_mod_cast hend.1)]
    have hαH : α τ₂ ∈ H := d.mem_H_of_mem_image hτ₂S (hwin _ hτ₂S (lt_of_lt_of_le hd2 hδ'1))
    have hgH : g τ₂ ∈ H := by
      show f (α τ₂) ∈ H
      rw [d.eq_of_mem_H hαH]
      exact d.conf.2.1 hαH
    refine ⟨g τ₂, hwinU _ hτ₂S (lt_of_lt_of_le hd2 hδ'U), ⟨mem_iUnion₂.2 ⟨pc, hpc, ?_⟩, hgH⟩, ?_⟩
    · rw [d.tipSet_eq]; exact ⟨τ₂, hτ₂S, rfl⟩
    · rintro ⟨hz | hz, -⟩
      · exact d.avoid _ hτ₂pos hτ₂S hz
      · obtain ⟨t, ht, htip⟩ := hz
        have htS' : (t : ℝ≥0∞) ≤ pc.2.2 := ht.trans hτS.le
        have he : g t = g τ₂ := Chart.tipAt_unique (d.tipAt htS') htip
        have htt := d.inj htS' hτ₂S he
        have hle : (t : ℝ) ≤ ((τ : ℝ≥0) : ℝ) := by exact_mod_cast ENNReal.coe_le_coe.1 ht
        rw [htt] at hle
        linarith
  refine ⟨pre, post, pc, τ, hs, hτS, hzU, ?_⟩
  intro d' B A hAB
  refine ⟨pre, post, pc, τ, y, p, min ρw ρL, δt, A, hs, hτS, ?_, hlandy, Or.inl ⟨hpL, hpH⟩,
    lt_min hρw hρL, ?_, ?_, hAB, hδt, hdomt, hlimt⟩
  · exact hyside
  · rintro z ⟨⟨hzO, hzH⟩, hzb⟩
    obtain ⟨t, htD, -, ht2, rfl⟩ := hwalk _ ⟨hzO, ball_subset_ball (min_le_left _ _) hzb⟩
    exact ⟨Or.inr ⟨t, ENNReal.coe_le_coe.2 (by exact_mod_cast ht2.le), d.tipAt htD⟩, hzH⟩
  · rintro z ⟨hzL, hzb⟩
    exact absurd (subset_closure hzL) (hρLL (ball_subset_ball (min_le_right _ _) hzb))


end InteractingSLE.Theorem14.WalkWd
