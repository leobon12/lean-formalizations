/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkTchMatch

/-!
# The controlled prefix match at a real touch point of the left walk

Packet PROVE-WALK-TOUCH. Mirror of `WalkTch.exists_controlledMatch_right_touch`: the component chart lands at
`x₀ < 0` on a real point `p = g(t₀)` of a recorded piece of the **left** walk; landings left of `x₀` are later points
of the piece, so the fresh landing `x₁` is taken left of `x₀` and the side point is a **right** side point
(`WalkTch.pos_and_margin_of_later`). The rest of the proof is that of the right walk.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.WalkTch

open WalkBdry WalkWords

/-- **The controlled prefix match at a real touch point of the left walk** (mirror). -/
theorem exists_controlledMatch_left_touch {sR sL : ExplState} {γ : ℝ≥0 → ℂ}
    (hγ : Supp9B.IsProperCurve γ) (hordγ : ordOf sL ⊆ range γ)
    (hdL : ∀ (pre post : List Piece) (pc : Piece), sL.1 = pre ++ pc :: post →
      ∃ (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ), PieceData pc (⋃ p ∈ pre, p.1.tipSet p.2.1 p.2.2) f W α)
    (hfrontL : ∀ (pre post : List Piece) (pc : Piece), sL.1 = pre ++ pc :: post →
      (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2 → frontier ((prefixChart pc 0).dom : Set ℂ) ∩ H ⊆ prefixSet pre pc 0)
    (hdisjL : ∀ (pre post : List Piece) (pc : Piece), sL.1 = pre ++ pc :: post →
      (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2 → Disjoint ((prefixChart pc 0).dom : Set ℂ) (prefixSet pre pc 0))
    (htip0L : ∀ pc ∈ sL.1, ∀ z, pc.1.tipAt pc.2.1 0 z → z.im = 0)
    {c : Chart} (hc : c.IsConformal)
    (hlandL : ∀ x : ℝ, x < 0 → ∃ z : ℂ, Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 z) ∧ z ∈ range γ)
    {x₀ : ℝ} {p : ℂ} (hx₀ : x₀ < 0) (hp : Tendsto c.2.1 (𝓝[H] (x₀ : ℂ)) (𝓝 p)) (hpre : p.im = 0)
    {U : Set ℂ} (hU : IsOpen U) (hpU : p ∈ U)
    (hpL : p ∈ ordOf sL) (hpF : p ∉ pieceEnds sL.1) (hpR : p ∉ closure (wsetOf sR))
    (horient : ∀ pc ∈ sL.1, ∀ (x x' : ℝ) (t t' : ℝ≥0) (z z' : ℂ), x < x' → x' < 0 →
      Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 z) → Tendsto c.2.1 (𝓝[H] (x' : ℂ)) (𝓝 z') →
      (t : ℝ≥0∞) ≤ pc.2.2 → (t' : ℝ≥0∞) ≤ pc.2.2 → pc.1.tipAt pc.2.1 t z → pc.1.tipAt pc.2.1 t' z' → t' < t)
    {U₀ : Set ℂ} (hU₀ : IsOpen U₀) (hpU₀ : p ∈ U₀)
    (hdomL : ∀ (pre post : List Piece) (pc : Piece) (τ : ℝ≥0), sL.1 = pre ++ pc :: post →
      (τ : ℝ≥0∞) < pc.2.2 → (∃ z ∈ U₀, z ∈ wsetOf sL ∧ z ∉ prefixSet pre pc τ) →
      ∀ w ∈ H, c.2.1 w ∈ (prefixChart pc τ).dom) :
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
  have hend : 0 < t₀ ∧ (t₀ : ℝ≥0∞) < pc.2.2 := by
    refine ⟨?_, lt_of_le_of_ne ht₀D fun h => hpF ⟨pc, hpc, Or.inr ⟨t₀, h.symm, ?_⟩⟩⟩
    · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t₀) with h0 | h0
      · refine absurd ⟨pc, hpc, Or.inl ?_⟩ hpF
        rw [← ht₀e, ← h0]; exact d.tipAt (by simp)
      · exact h0
    · rw [← ht₀e]; exact d.tipAt ht₀D
  -- launch-chart fibres and forward limits at the piece's points
  have hpre' : ∀ p' ∈ pre, ∃ (A' : Set ℂ) (f' : ℂ → ℂ) (W' : ℝ≥0 → ℝ) (α' : ℝ≥0 → ℂ),
      PieceData p' A' f' W' α' := by
    intro p' hp'
    obtain ⟨a, b, hab⟩ := List.append_of_mem hp'
    have hdec : sL.1 = a ++ p' :: (b ++ pc :: post) := by rw [hs, hab]; simp
    obtain ⟨f', W', α', d'⟩ := hdL _ _ _ hdec
    exact ⟨_, f', W', α', d'⟩
  have hconn := exists_preconnected_old hpre' fun p' hp' => htip0L p' (by rw [hs]; simp [hp'])
  have h0S : (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2 :=
    lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hend.1) ht₀D
  have hfwd : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ pc.2.2 →
      Tendsto pc.1.1 (𝓝[pc.1.2.1 '' H] (g t)) (𝓝 (α t)) := fun t ht0 ht =>
    PieceData.tendsto_fwd d ht fun y₁ y₂ h₁ h₂ => PieceData.eq_of_land_eq d (hfrontL _ _ _ hs h0S)
      (hdisjL _ _ _ hs h0S) (htip0L pc hpc) hconn ht0 ht h₁ h₂
  -- the time window `[lo, hi]` inside `U ∩ U₀`
  obtain ⟨εU, hεU, hwinU⟩ := d.exists_window ht₀D (hU.inter hU₀)
    (show g t₀ ∈ U ∩ U₀ by rw [ht₀e]; exact ⟨hpU, hpU₀⟩)
  set ε₀ : ℝ := min εU (t₀ : ℝ) with hε₀
  have ht₀pos : (0 : ℝ) < t₀ := by exact_mod_cast hend.1
  have hε₀pos : 0 < ε₀ := lt_min hεU ht₀pos
  have hε₀t : ε₀ ≤ t₀ := min_le_right _ _
  have hε₀U : ε₀ ≤ εU := min_le_left _ _
  set lo : ℝ≥0 := ((t₀ : ℝ) - ε₀ / 2).toNNReal with hlo
  have hloR : (lo : ℝ) = (t₀ : ℝ) - ε₀ / 2 := Real.coe_toNNReal _ (by linarith)
  obtain ⟨hiq, hhi1, hhi2, hhiS⟩ := exists_nnrat_window hend.2 (δ := ε₀ / 2) (by positivity)
  set hi : ℝ≥0 := (hiq : ℝ≥0) with hhi
  have hlot : lo < t₀ := by rw [← NNReal.coe_lt_coe, hloR]; linarith
  have htm : t₀ < hi := by exact_mod_cast hhi1
  have hlo0 : 0 < lo := by rw [← NNReal.coe_pos, hloR]; linarith
  have hIS : ∀ t ∈ Icc lo hi, (t : ℝ≥0∞) ≤ pc.2.2 := fun t ht =>
    le_trans (ENNReal.coe_le_coe.2 ht.2) hhiS.le
  have hIU : ∀ t ∈ Icc lo hi, g t ∈ U ∩ U₀ := by
    intro t ht
    refine hwinU t (hIS t ht) ?_
    have h1 : (lo : ℝ) ≤ t := by exact_mod_cast ht.1
    have h2 : (t : ℝ) ≤ hi := by exact_mod_cast ht.2
    rw [abs_lt]; constructor <;> linarith
  have hgc : ∀ b : ℝ≥0, b ≤ hi → ContinuousOn g (Icc lo b) := fun b hb =>
    d.continuousOn.mono fun t ht => hIS t ⟨ht.1, ht.2.trans hb⟩
  have hgi : InjOn g (Icc lo hi) := d.inj.mono fun t ht => hIS t ht
  have hgγ : ∀ b : ℝ≥0, b ≤ hi → g '' Icc lo b ⊆ range γ := by
    rintro b hb _ ⟨t, ht, rfl⟩
    exact hordγ (mem_iUnion₂.2 ⟨pc, hpc, by rw [d.tipSet_eq]; exact ⟨t, hIS t ⟨ht.1, ht.2.trans hb⟩, rfl⟩⟩)
  -- landings near `x₀` are points of the arc `g([lo, hi])`
  obtain ⟨rP, hrP, hphys⟩ := exists_ball_phys_window hγ hlot htm (hgc hi le_rfl) hgi (hgγ hi le_rfl)
  rw [ht₀e] at hphys
  set ℓ : ℝ → ℂ := fun x => extendFrom H c.2.1 (x : ℂ) with hℓdef
  have hℓ : ∀ x : ℝ, x < 0 → Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (ℓ x)) ∧ ℓ x ∈ range γ := by
    intro x hx
    obtain ⟨z, hz, hzγ⟩ := hlandL x hx
    have he : ℓ x = z := extendFrom_eq (by rw [closure_H]; show (0 : ℝ) ≤ ((x : ℂ)).im; simp) hz
    rw [he]; exact ⟨hz, hzγ⟩
  have hℓc : ContinuousOn ℓ (Iio 0) := continuousOn_landing fun x hx => ⟨_, (hℓ x hx).1⟩
  have hℓ₀ : ℓ x₀ = p := by
    have : (𝓝[H] (x₀ : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ ((x₀ : ℂ)).im by simp)
    exact tendsto_nhds_unique (hℓ x₀ hx₀).1 hp
  obtain ⟨δL, hδL, hδLb⟩ := exists_landing_ball hp hrP
  set δL' : ℝ := min δL (-x₀) with hδL'
  have hδL'pos : 0 < δL' := lt_min hδL (by linarith)
  have hwinL : ∀ x : ℝ, |x - x₀| < δL' → x < 0 ∧ ∃ t ∈ Icc lo hi, ℓ x = g t := by
    intro x hx
    have hx0 : x < 0 := by
      have := (abs_lt.1 hx).2; have : δL' ≤ -x₀ := min_le_right _ _; linarith
    refine ⟨hx0, ?_⟩
    obtain ⟨t, ht, hte⟩ := hphys (ℓ x) ⟨(hℓ x hx0).2, hδLb x (lt_of_lt_of_le hx (min_le_left _ _)) _ (hℓ x hx0).1⟩
    exact ⟨t, ht, hte⟩
  have hor : ∀ x x' : ℝ, x < x' → x' < 0 → ∀ t t' : ℝ≥0, t ∈ Icc lo hi → t' ∈ Icc lo hi →
      ℓ x = g t → ℓ x' = g t' → t' < t := by
    intro x x' hxx' hx' t t' ht ht' he he'
    exact horient pc hpc x x' t t' (ℓ x) (ℓ x') hxx' hx' (hℓ x (hxx'.trans hx')).1 (hℓ x' hx').1 (hIS t ht)
      (hIS t' ht') (by rw [he]; exact d.tipAt (hIS t ht)) (by rw [he']; exact d.tipAt (hIS t' ht'))
  have ht₀I : t₀ ∈ Icc lo hi := ⟨hlot.le, htm.le⟩
  -- a fresh landing left of `x₀`
  set xb : ℝ := x₀ - δL' / 2 with hxb
  obtain ⟨-, tb, htbI, htbe⟩ := hwinL xb (by rw [hxb, abs_lt]; constructor <;> linarith)
  have ht₀b : t₀ < tb := hor xb x₀ (by linarith) hx₀ tb t₀ htbI ht₀I htbe (by rw [hℓ₀, ht₀e])
  have hSsub : ℓ '' Icc xb x₀ ⊆ g '' Icc lo hi := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨-, t, ht, hte⟩ := hwinL x (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])
    exact ⟨t, ht, hte.symm⟩
  have hΘ := isPreconnected_inter_preimage (hgc hi le_rfl) hgi
    (isPreconnected_Icc.image ℓ (hℓc.mono fun x hx => lt_of_le_of_lt hx.2 hx₀)) hSsub
  have ht₀Θ : t₀ ∈ Icc lo hi ∩ g ⁻¹' (ℓ '' Icc xb x₀) := ⟨ht₀I, x₀, ⟨by linarith, le_rfl⟩, by rw [hℓ₀, ht₀e]⟩
  have htbΘ : tb ∈ Icc lo hi ∩ g ⁻¹' (ℓ '' Icc xb x₀) := ⟨htbI, xb, ⟨le_rfl, by linarith⟩, htbe⟩
  obtain ⟨s₁, hs₁, hα₁⟩ := d.exists_mem_H_of_lt ht₀b (hIS tb htbI)
  have hs₁I : s₁ ∈ Icc lo hi := ⟨hlot.le.trans hs₁.1.le, hs₁.2.le.trans htbI.2⟩
  obtain ⟨-, x₁, hx₁, hx₁e⟩ := hΘ.Icc_subset ht₀Θ htbΘ ⟨hs₁.1.le, hs₁.2.le⟩
  have hx₁0 : x₁ < x₀ := by
    refine lt_of_le_of_ne hx₁.2 fun h => ?_
    rw [h, hℓ₀, ← ht₀e] at hx₁e
    exact hs₁.1.ne (hgi ht₀I hs₁I hx₁e)
  -- the prefix time `τ` after `s₁`, with `α([s₁, τ]) ⊆ ℍ`
  have hs₁S : (s₁ : ℝ≥0∞) ≤ pc.2.2 := hIS s₁ hs₁I
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.mem_nhdsWithin_iff.1
    ((d.gen.2.1 s₁ hs₁S).preimage_mem_nhdsWithin (QuantumZipper.isOpen_H.mem_nhds hα₁))
  have hs₁hi : s₁ < hi := lt_of_lt_of_le hs₁.2 htbI.2
  have hs₁lt : (s₁ : ℝ≥0∞) < pc.2.2 :=
    lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hs₁hi) (hIS hi ⟨hlot.le.trans htm.le, le_rfl⟩)
  obtain ⟨τ, hτ1, hτ2, hτS⟩ := exists_nnrat_window hs₁lt (δ := min ε₁ ((hi : ℝ) - s₁))
    (lt_min hε₁ (sub_pos.2 (by exact_mod_cast hs₁hi)))
  have hτhi : (τ : ℝ≥0) < hi := by
    have h1 := min_le_right ε₁ ((hi : ℝ) - s₁)
    rw [← NNReal.coe_lt_coe]; linarith
  have hτI : (τ : ℝ≥0) ∈ Icc lo hi := ⟨hlot.le.trans (hs₁.1.trans (by exact_mod_cast hτ1)).le, hτhi.le⟩
  have hαH : ∀ t : ℝ≥0, s₁ ≤ t → (t : ℝ) ≤ (τ : ℝ≥0) → α t ∈ H := by
    intro t h1 h2
    refine hball₁ ⟨?_, le_trans (ENNReal.coe_le_coe.2 (by exact_mod_cast h2)) hτS.le⟩
    rw [mem_ball, NNReal.dist_eq, abs_lt]
    have h1' : (s₁ : ℝ) ≤ t := by exact_mod_cast h1
    have h3 := min_le_left ε₁ ((hi : ℝ) - s₁)
    constructor <;> linarith
  -- a fresh point after `τ` inside `U ∩ U₀`, and the domain condition
  obtain ⟨τ₂, hτ₂, hα₂⟩ := d.exists_mem_H_of_lt hτhi (hIS hi ⟨hlot.le.trans htm.le, le_rfl⟩)
  have hτ₂I : τ₂ ∈ Icc lo hi := ⟨hτI.1.trans hτ₂.1.le, hτ₂.2.le⟩
  have hfresh : g τ₂ ∈ U ∩ U₀ ∧ g τ₂ ∈ wsetOf sL ∧ g τ₂ ∉ prefixSet pre pc τ := by
    have hgH : g τ₂ ∈ H := by
      show f (α τ₂) ∈ H
      rw [d.eq_of_mem_H hα₂]
      exact d.conf.2.1 hα₂
    refine ⟨hIU τ₂ hτ₂I, ⟨mem_iUnion₂.2 ⟨pc, hpc, by rw [d.tipSet_eq]; exact ⟨τ₂, hIS τ₂ hτ₂I, rfl⟩⟩, hgH⟩, ?_⟩
    rintro ⟨hz | hz, -⟩
    · exact d.avoid _ (hlo0.trans_le hτ₂I.1) (hIS τ₂ hτ₂I) hz
    · obtain ⟨t, ht, htip⟩ := hz
      have htS' : (t : ℝ≥0∞) ≤ pc.2.2 := ht.trans hτS.le
      have he : g t = g τ₂ := Chart.tipAt_unique (d.tipAt htS') htip
      have htt := d.inj htS' (hIS τ₂ hτ₂I) he
      have hle : t ≤ (τ : ℝ≥0) := ENNReal.coe_le_coe.1 ht
      rw [htt] at hle
      exact absurd hτ₂.1 (not_lt.2 hle)
  have hdomG := hdomL pre post pc τ hs hτS ⟨g τ₂, hfresh.1.2, hfresh.2⟩
  -- the global model of the piece's driver
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
  -- landings right of `x₁` stay before `τ`
  set b₁ : ℝ≥0 := (((s₁ : ℝ) + ((τ : ℝ≥0) : ℝ)) / 2).toNNReal with hb₁
  have hb₁R : (b₁ : ℝ) = ((s₁ : ℝ) + ((τ : ℝ≥0) : ℝ)) / 2 := Real.coe_toNNReal _ (by positivity)
  have hτ1' : (s₁ : ℝ) < ((τ : ℝ≥0) : ℝ) := hτ1
  have hs₁b : s₁ < b₁ := by rw [← NNReal.coe_lt_coe, hb₁R]; linarith
  have hb₁τ : (b₁ : ℝ) < ((τ : ℝ≥0) : ℝ) := by rw [hb₁R]; linarith
  have hτhiR : ((τ : ℝ≥0) : ℝ) < hi := by exact_mod_cast hτhi
  have hb₁hi : b₁ ≤ hi := by
    have : (b₁ : ℝ) ≤ hi := by linarith
    exact_mod_cast this
  obtain ⟨r₁, hr₁, hphys₁⟩ := exists_ball_phys_window hγ (hlot.trans hs₁.1) hs₁b (hgc b₁ hb₁hi)
    (hgi.mono (Icc_subset_Icc_right hb₁hi)) (hgγ b₁ hb₁hi)
  have hℓ₁ : ℓ x₁ = g s₁ := hx₁e
  obtain ⟨δ₂, hδ₂, hδ₂b⟩ := exists_landing_ball (hℓ x₁ (hx₁0.trans hx₀)).1 hr₁
  rw [hℓ₁] at hδ₂b
  have hx₁b : x₀ - x₁ ≤ δL' / 2 := by linarith [hx₁.1]
  set δ : ℝ := min (x₀ - x₁ + δ₂ / 2) δL' with hδdef
  have hδ : 0 < δ := lt_min (by linarith) hδL'pos
  have hδle1 : δ ≤ x₀ - x₁ + δ₂ / 2 := min_le_left _ _
  have hδle2 : δ ≤ δL' := min_le_right _ _
  have hx₁δ : x₁ ∈ Ioo (x₀ - δ) x₀ := by
    refine ⟨?_, hx₁0⟩
    have : x₀ - x₁ < δ := lt_min (by linarith) (by linarith)
    linarith
  have hwin : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), ∃ t : ℝ≥0, t ∈ Icc lo hi ∧ (t : ℝ) < (τ : ℝ≥0) ∧ ℓ x = g t := by
    intro x hx
    have hxδ : |x - x₀| < δL' := by
      rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
    obtain ⟨hx0, t, ht, hte⟩ := hwinL x hxδ
    refine ⟨t, ht, ?_, hte⟩
    rcases le_or_gt x₁ x with hxx | hxx
    · have hts : t ≤ s₁ := by
        rcases eq_or_lt_of_le hxx with h | h
        · rw [← h, hℓ₁] at hte; exact (hgi hs₁I ht hte).ge
        · exact (hor x₁ x h hx0 s₁ t hs₁I ht hℓ₁ hte).le
      have : (t : ℝ) ≤ s₁ := by exact_mod_cast hts
      linarith
    · have hd : |x - x₁| < δ₂ := by
        rw [abs_of_neg (by linarith)]
        linarith [hx.1]
      obtain ⟨t', ht', hte'⟩ := hphys₁ (ℓ x) ⟨(hℓ x hx0).2, hδ₂b x hd _ (hℓ x hx0).1⟩
      have htt : t' = t := hgi ⟨ht'.1, ht'.2.trans hb₁hi⟩ ht (hte'.symm.trans hte)
      have : (t' : ℝ) ≤ b₁ := by exact_mod_cast ht'.2
      rw [htt] at this
      linarith
  choose! tf htfI htfτ htfe using hwin
  have htf0 : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), 0 < tf x := fun x hx => hlo0.trans_le (htfI x hx).1
  have hx₀δ : x₀ ∈ Ioo (x₀ - δ) (x₀ + δ) := ⟨by linarith, by linarith⟩
  have hx₁m : x₁ ∈ Ioo (x₀ - δ) (x₀ + δ) := ⟨hx₁δ.1, by linarith [hx₁δ.2]⟩
  have htf₀ : tf x₀ = t₀ := hgi (htfI x₀ hx₀δ) ht₀I (by rw [← htfe x₀ hx₀δ, hℓ₀, ht₀e])
  have htf₁ : tf x₁ = s₁ := hgi (htfI x₁ hx₁m) hs₁I (by rw [← htfe x₁ hx₁m, hℓ₁])
  -- the boundary function of the transition
  obtain ⟨m, hmono, hmc, hm⟩ := exists_boundary_fun d hτT hWc hW0 hη hpcT hag hηα hinj hc hdomG
    (x₀ := x₀) (δ := δ) (tf := tf) fun x hx => by
      have hx0 : x < 0 := (hwinL x (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])).1
      refine ⟨htfτ x hx, ?_, hfwd (tf x) (htf0 x hx) (hIS _ (htfI x hx))⟩
      have h := (hℓ x hx0).1
      rw [htfe x hx] at h
      exact h
  have hx₀F : extendFrom H (fwdMapInv W' (τ : ℝ≥0)) (m x₀) = η t₀ := by
    rw [(hm x₀ hx₀δ).2.1, htf₀]
  have hx₁F : extendFrom H (fwdMapInv W' (τ : ℝ≥0)) (m x₁) = η s₁ := by
    rw [(hm x₁ hx₁m).2.1, htf₁]
  have hH : ∀ s ∈ Icc (s₁ : ℝ) ((τ : ℝ≥0) : ℝ), η s ∈ H := by
    intro s hs
    have hs0 : 0 ≤ s := s₁.coe_nonneg.trans hs.1
    rw [hηα s ⟨hs0, hs.2.trans hτT.le⟩]
    refine hαH _ ?_ (by rw [Real.coe_toNNReal _ hs0]; exact hs.2)
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0]; exact hs.1
  obtain ⟨hneg, ε, hε, hmar⟩ := pos_and_margin_of_later hη hWc hW0 hinj hδ hmono hmc
    (fun x hx => (hm x hx).1) (fun x hx => ⟨tf x, ⟨(tf x).coe_nonneg, htfτ x hx⟩, (hm x hx).2.1⟩)
    t₀.coe_nonneg hx₀F hx₁δ (by exact_mod_cast hs₁.1) hτ1 hH hx₁F
  have hag' : EqOn (pieceDrv pc) W' (Icc 0 ((τ : ℝ≥0) : ℝ)) := hag.mono (Icc_subset_Icc_right hτT.le)
  have hside : IsRightSidePt pc τ (m x₀) := by
    refine ⟨hneg, ε, hε, fun X ⟨u, hu⟩ hX => ?_⟩
    have hu' := (WalkSide.isForwardSol_congr hag' _ _).1 hu
    have hf : fwdMap (pieceDrv pc) ((τ : ℝ≥0) : ℝ) X = fwdMap W' ((τ : ℝ≥0) : ℝ) X :=
      Ito.fwdMap_congr_of_eqOn_of_le hag' le_rfl
    rw [hf] at hX ⊢
    exact hmar X ⟨u, hu'⟩ hX
  have ht₀τ : (t₀ : ℝ) < ((τ : ℝ≥0) : ℝ) := lt_trans (by exact_mod_cast hs₁.1) hτ1
  -- the prefix inverse lands at `p`
  have hlandy : Tendsto (prefixChart pc τ).2.1 (𝓝[H] (m x₀ : ℂ)) (𝓝 p) := by
    have hτ0 : (0 : ℝ) ≤ ((τ : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    have h1 : Tendsto (fwdMapInv W' ((τ : ℝ≥0) : ℝ)) (𝓝[H] (m x₀ : ℂ)) (𝓝[H] (α t₀)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun w hw =>
        QuantumZipper.RS.fwdMapInv_mem_H hWc hW0 hτ0 hw⟩
      have := (hη.hasBdryLimits hWc hW0 hτ0).tendsto (show ((m x₀ : ℝ) : ℂ) ∈ Hbar by
        show (0 : ℝ) ≤ (((m x₀ : ℝ) : ℂ)).im; simp)
      rwa [hx₀F, hηt t₀ (ht₀τ.le.trans hτT.le)] at this
    have h2 := (d.land (α t₀) (d.mem_Hbar ht₀D)).comp h1
    have hft : f (α t₀) = p := ht₀e
    rw [hft] at h2
    refine h2.congr fun z => ?_
    show pc.1.2.1 (fwdMapInv W' ((τ : ℝ≥0) : ℝ) z) = (prefixChart pc τ).2.1 z
    rw [prefixChart_inv_eq_loewner hWc hpcT hag hτT]
    rfl
  -- the walks near `p`
  obtain ⟨ρw, hρw, hwalk⟩ := exists_ball_walk_window hs d hcl hpost hend.1 ht₀D hno
    (lo := (lo : ℝ)) (hi := ((τ : ℝ≥0) : ℝ)) (by exact_mod_cast hlot)
    (lt_trans (by exact_mod_cast hs₁.1) hτ1)
  have hcp : f (α t₀) = p := ht₀e
  rw [hcp] at hwalk
  obtain ⟨ρL, hρL, hρLL⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl p hpR
  refine ⟨pre, post, pc, τ, hs, hτS, ⟨g τ₂, hfresh.1.1, hfresh.2⟩, ?_⟩
  intro d' B A hAB
  refine ⟨pre, post, pc, τ, m x₀, p, min ρw ρL, δ, A, hs, hτS, hside, hlandy, Or.inr hpre,
    lt_min hρw hρL, ?_, ?_, hAB, hδ, fun w hw => hdomG w hw.1, (hm x₀ hx₀δ).2.2⟩
  · rintro z ⟨⟨hzO, hzH⟩, hzb⟩
    obtain ⟨t, htD, -, ht2, rfl⟩ := hwalk _ ⟨hzO, ball_subset_ball (min_le_left _ _) hzb⟩
    exact ⟨Or.inr ⟨t, ENNReal.coe_le_coe.2 (by exact_mod_cast ht2.le), d.tipAt htD⟩, hzH⟩
  · rintro z ⟨hzL, hzb⟩
    exact absurd (subset_closure hzL) (hρLL (ball_subset_ball (min_le_right _ _) hzb))

end InteractingSLE.Theorem14.WalkTch
