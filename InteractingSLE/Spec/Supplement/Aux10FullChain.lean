/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux10FullChainFactor

/-!
# Aux. lemma 10: the image chain of a protected conformal map

Packet PROVE-T14-BR9. Specification Aux. lemma 10, proof (pp. 69–71). With the factor data of
`exists_factor_data` (`φ = M ∘ g_A ∘ m` on `D`), the hulls `φ(K_t)`, `t ∈ [0, T]`, form a chordal Loewner chain after
a capacity time change (`exists_loewner_conformal`): the three factors are handled by the Möbius image theorem
(`Sec5.CrossRestart.exists_loewner_mobius_image`, twice) and Specification Aux. lemma 8
(`ConformalImageFull.exists_loewner_image`), as in GB6's `exists_loewner_relMap`. The theorem also records

* the filling transport `K_t = fill(S) ⇒ φ(K_t) = fill(φ(S ∩ ℍ))` (as GB6's `isFilling_relMap_image`);
* a comparison function `F_t` with `g̃_{τ(t)} ∘ φ = F_t ∘ g_t` on `D \ K_t` and `F_t → W̃_{τ(t)}` at `W_t` from `ℍ`
  (the driving-point identity (TD2) `W̃_{τ(t)} = R_t(W_t)`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE

namespace Aux10

open ConformalImage ConformalImageFull Sec5.CrossRestart

/-- The normal form `w ↦ α − κ/(w − P)` (`κ > 0`) maps `ℍ` into `ℍ`. -/
theorem nf_mem_H {α κ P : ℝ} (hκ : 0 < κ) {w : ℂ} (hw : w ∈ H) : nf α κ P w ∈ H := by
  have hwP : w - P ≠ 0 := sub_ne_zero_of_mem_H hw P
  have hn : 0 < Complex.normSq (w - P) := Complex.normSq_pos.2 hwP
  have him : (nf α κ P w).im = κ * w.im / Complex.normSq (w - P) := by
    simp [nf, Complex.div_im]
  show 0 < (nf α κ P w).im
  rw [him]
  exact div_pos (mul_pos hκ hw) hn

/-- The normal form is continuous off its pole. -/
theorem continuousAt_nf {α κ P : ℝ} {w : ℂ} (hw : w - P ≠ 0) : ContinuousAt (nf α κ P) w := by
  unfold nf
  exact continuousAt_const.sub (continuousAt_const.div (by fun_prop) hw)

/-- **The image chain of a protected conformal map** (Aux. lemma 10, the hull transport; general form of GB6's
`exists_loewner_relMap`), with the filling transport and the comparison function at each time. -/
theorem exists_loewner_conformal {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {D : Set ℂ} {φ : ℂ → ℂ} (hDo : IsOpen D) (hDH : D ⊆ H) (hφd : DifferentiableOn ℂ φ D)
    (hφinj : InjOn φ D) (hφim : φ '' D = H) {x : ℝ} (hx0 : x ≠ 0) {r₁ : ℝ}
    (hd₁ : Disjoint (ball (x : ℂ) r₁) (QuantumZipper.fwdHull W T)) (hr₁ : 0 < r₁) {δ ε : ℝ} (hδ : 0 < δ)
    (hε : 0 < ε) (hsep : ∀ z ∈ H \ D, δ ≤ ‖z - (x : ℂ)‖)
    (hsepK : ∀ z ∈ H \ D, ∀ w ∈ insert (0 : ℂ) (QuantumZipper.fwdHull W T), ε ≤ ‖z - w‖)
    (hφx : ∃ C : ℝ, ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ D ∧ ‖φ z‖ ≤ C)
    (hφ0 : ∀ᶠ z in 𝓝[H] (0 : ℂ), z ∈ D) (hφ0' : Tendsto φ (𝓝[H] (0 : ℂ)) (𝓝 0))
    (hφK : ∃ C : ℝ, ∀ w ∈ QuantumZipper.fwdHull W T, ‖φ w‖ ≤ C) :
    ∃ τ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ τ 0 = 0 ∧ StrictMonoOn τ (Icc 0 T) ∧
      ContinuousOn τ (Icc 0 T) ∧ ∀ t ∈ Icc (0 : ℝ) T,
        QuantumZipper.fwdHull W' (τ t) = φ '' QuantumZipper.fwdHull W t ∧
        (∀ S : Set ℂ, IsFilling (QuantumZipper.fwdHull W t) S →
          IsFilling (φ '' QuantumZipper.fwdHull W t) (φ '' (S ∩ H))) ∧
        ∃ F : ℂ → ℂ, (∀ z ∈ D \ QuantumZipper.fwdHull W t, gmap W' (τ t) (φ z) = F (gmap W t z)) ∧
          Tendsto F (𝓝[H] (W t : ℂ)) (𝓝 (W' (τ t) : ℂ)) := by
  obtain ⟨gA, a', b', c', d', x₁, r₃, hA, hgA, hdA', hgA0, hdet', hc', hx₁', hnum, hr₃pos, hclear, hfac⟩ :=
    exists_factor_data hW hT hDo hDH hφd hφinj hφim hx0 hδ hε hsep hsepK hφx hφ0 hφ0' hφK
  set K := QuantumZipper.fwdHull W T with hKdef
  set A := mobAt x '' (H \ D) with hAdef
  set M₁ := mobAt x with hM₁def
  set M₂ := realMobius a' b' c' d' with hM₂def
  set M₂' := realMobius a' (a' * x₁ + b') c' (c' * x₁ + d') with hM₂'def
  set P₂ := mobPole c' d' with hP₂
  have hK : IsHPHull K := isHPHull_fwdHull hW hT
  have hKH : ∀ w ∈ K, w ∈ H := fun w hw => hK.1 hw
  have hKD : ∀ w ∈ K, w ∈ D := fun w hw => by
    by_contra hwD
    have := hsepK w ⟨hKH w hw, hwD⟩ w (mem_insert_of_mem _ hw)
    simp at this
    linarith
  have hpole₁ : mobPole 1 (-x) = x := by simp [mobPole]
  have hd₁' : Disjoint (ball (mobPole 1 (-x) : ℂ) r₁) K := by rw [hpole₁]; exact hd₁
  have hp₁ : mobPole 1 (-x) ≠ 0 := by rw [hpole₁]; exact hx0
  -- step 1: the Möbius map `M₁ = m`
  obtain ⟨σ₁, W₁, α₁, κ₁, P₁, hW₁c, hW₁0, hσ₁0, hσ₁m, hσ₁c, h₁⟩ :=
    exists_loewner_mobius_image hW hW0 hT (mobAt_det x) one_ne_zero hp₁ hr₁ hd₁'
  have hK₁ : ∀ t ∈ Icc (0 : ℝ) T, QuantumZipper.fwdHull W₁ (σ₁ t) = M₁ '' QuantumZipper.fwdHull W t :=
    fun t ht => (h₁ t ht).2.1
  have hW₁0' : W₁ 0 = 1 / x := by rw [hW₁0, neg_div_neg_eq]
  have hT₁ : 0 ≤ σ₁ T := by
    rw [← hσ₁0]; exact hσ₁m.monotoneOn ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  have hdA : Disjoint (closure A) (insert (W₁ 0 : ℂ) (closure (QuantumZipper.fwdHull W₁ (σ₁ T)))) := by
    rw [hK₁ T ⟨hT, le_rfl⟩, hW₁0']
    exact hdA'
  -- Specification Aux. lemma 8 for `g_A`
  obtain ⟨a₂, W₂, hW₂c, ha₂0, ha₂m, ha₂c, h₂⟩ := exists_loewner_image hW₁c hT₁ hA hgA hdA
  have hK₂ : ∀ s ∈ Icc (0 : ℝ) (σ₁ T), QuantumZipper.fwdHull W₂ (a₂ s) =
      gA '' QuantumZipper.fwdHull W₁ s := fun s hs => (h₂ s hs).2.1
  have hW₂0 : W₂ 0 = x₁ := by
    obtain ⟨-, -, hR⟩ := h₂ 0 ⟨le_rfl, hT₁⟩
    have himg : (fun z => QuantumZipper.fwdMap W₁ 0 z + W₁ 0) '' A = A := by
      have : ∀ z ∈ A, QuantumZipper.fwdMap W₁ 0 z + W₁ 0 = z := fun z hz =>
        gmap_zero_apply hW₁c (hA.1 hz)
      rw [image_congr this, image_id']
    obtain ⟨-, hlim⟩ := hR gA (by rw [himg]; exact hgA)
    rw [ha₂0, hW₁0'] at hlim
    have := MobHyp.nhdsWithin_neBot (1 / x)
    exact_mod_cast tendsto_nhds_unique hlim hgA0
  have hT₂ : 0 ≤ a₂ (σ₁ T) := by
    rw [← ha₂0]; exact ha₂m.monotoneOn ⟨le_rfl, hT₁⟩ ⟨hT₁, le_rfl⟩ hT₁
  -- step 3: translate the `g_A`-chain to start at `0`, then apply `M₂'` (pole `P₂ − x₁ ≠ 0`)
  set W₃ : ℝ → ℝ := fun s => W₂ s + -x₁ with hW₃
  have hW₃c : Continuous W₃ := by fun_prop
  have hW₃0 : W₃ 0 = 0 := by simp [hW₃, hW₂0]
  have hK₃ : ∀ s, QuantumZipper.fwdHull W₃ s =
      (fun z : ℂ => z + ((-x₁ : ℝ) : ℂ)) '' QuantumZipper.fwdHull W₂ s :=
    fun s => fwdHull_add_const W₂ (-x₁) s
  have hdet₂ : 0 < a' * (c' * x₁ + d') - (a' * x₁ + b') * c' := by
    have : a' * (c' * x₁ + d') - (a' * x₁ + b') * c' = a' * d' - b' * c' := by ring
    rw [this]
    exact hdet'
  have hpole₂ : mobPole c' (c' * x₁ + d') ≠ 0 := by
    simp only [mobPole]
    exact div_ne_zero (neg_ne_zero.2 hx₁') hc'
  have hpole₂' : ((mobPole c' (c' * x₁ + d') : ℝ) : ℂ) = (P₂ : ℂ) - x₁ := by
    have hc'C : (c' : ℂ) ≠ 0 := ofReal_ne_zero.2 hc'
    simp only [hP₂, mobPole]
    push_cast
    field_simp
    ring
  have hM₁A : ∀ z ∈ D, M₁ z ∈ H \ A := fun z hz => (hfac z hz).1
  have hmaps₁ : MapsTo σ₁ (Icc 0 T) (Icc 0 (σ₁ T)) := fun t ht =>
    ⟨by rw [← hσ₁0]; exact hσ₁m.monotoneOn ⟨le_rfl, hT⟩ ht ht.1,
      hσ₁m.monotoneOn ht ⟨hT, le_rfl⟩ ht.2⟩
  have hmaps₂ : MapsTo a₂ (Icc 0 (σ₁ T)) (Icc 0 (a₂ (σ₁ T))) := fun s hs =>
    ⟨by rw [← ha₂0]; exact ha₂m.monotoneOn ⟨le_rfl, hT₁⟩ hs hs.1,
      ha₂m.monotoneOn hs ⟨hT₁, le_rfl⟩ hs.2⟩
  have hd4 : Disjoint (ball (mobPole c' (c' * x₁ + d') : ℂ) r₃)
      (QuantumZipper.fwdHull W₃ (a₂ (σ₁ T))) := by
    rw [hpole₂', hK₃, hK₂ (σ₁ T) ⟨hT₁, le_rfl⟩, hK₁ T ⟨hT, le_rfl⟩, Set.disjoint_left]
    rintro _ hb ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
    rw [mem_ball, dist_eq_norm] at hb
    have := hclear w hw
    have heq : gA (M₁ w) + ((-x₁ : ℝ) : ℂ) - ((P₂ : ℂ) - x₁) = gA (M₁ w) - P₂ := by
      push_cast
      ring
    rw [heq] at hb
    linarith
  obtain ⟨τ₄, W₄, α₄, κ₄, P₄, hW₄c, hW₄0, hτ₄0, hτ₄m, hτ₄c, h₄⟩ :=
    exists_loewner_mobius_image hW₃c hW₃0 hT₂ hdet₂ hc' hpole₂ hr₃pos hd4
  -- the factorization through `M₂'`
  have hM₂M₂' : ∀ v : ℂ, M₂' (v - x₁) = M₂ v := fun v => by
    simp only [hM₂'def, hM₂def, realMobius]
    congr 1 <;> push_cast <;> ring
  have hφfac : ∀ z ∈ D, φ z = M₂' (gA (M₁ z) + ((-x₁ : ℝ) : ℂ)) := fun z hz => by
    rw [(hfac z hz).2]
    push_cast
    rw [← sub_eq_add_neg, hM₂M₂']
  refine ⟨fun t => τ₄ (a₂ (σ₁ t)), W₄, hW₄c, ?_, by simp [hσ₁0, ha₂0, hτ₄0], ?_, ?_, fun t ht => ?_⟩
  · rw [hW₄0, hnum, zero_div]
  · intro t ht t' ht' htt'
    exact hτ₄m (hmaps₂ (hmaps₁ ht)) (hmaps₂ (hmaps₁ ht')) (ha₂m (hmaps₁ ht) (hmaps₁ ht') (hσ₁m ht ht' htt'))
  · exact hτ₄c.comp (ha₂c.comp hσ₁c hmaps₁) (hmaps₂.comp hmaps₁)
  set Kt := QuantumZipper.fwdHull W t with hKtdef
  have hmono : Kt ⊆ K := (QuantumZipper.fwdHull_mono (W := W)).1 ht.2
  have hs₁ := hmaps₁ ht
  have hs₂ := hmaps₂ hs₁
  set s₁ := σ₁ t with hs₁def
  set s₂ := a₂ s₁ with hs₂def
  -- (i) the hulls
  have hhull : QuantumZipper.fwdHull W₄ (τ₄ s₂) = φ '' Kt := by
    rw [(h₄ _ hs₂).2.1, hK₃, hK₂ _ hs₁, hK₁ t ht, image_image, image_image, image_image]
    exact image_congr fun w hw => (hφfac w (hKD w (hmono hw))).symm
  refine ⟨hhull, fun S hS => ?_, ?_⟩
  · -- (ii) the fillings, factor by factor (GB6's `isFilling_relMap_image`)
    have hKt : IsHPHull Kt := isHPHull_fwdHull hW ht.1
    have hd₁t : Disjoint (ball (mobPole 1 (-x) : ℂ) r₁) Kt := hd₁'.mono_right hmono
    have h1 := isFilling_image_realMobius (mobAt_det x) one_ne_zero hKt hr₁ hd₁t hS
    have hK₁t : IsHPHull (M₁ '' Kt) := isHPHull_image (mobAt_det x) one_ne_zero hKt hr₁ hd₁t
    have hdA₁ : Disjoint (closure A) (closure (M₁ '' Kt)) :=
      (Set.disjoint_insert_right.1 hdA').2.mono_right (closure_mono (image_mono hmono))
    have h2 := isFilling_image_mapOut hA hgA hK₁t hdA₁ h1
    have hK₂t : IsHPHull (gA '' (M₁ '' Kt)) := hgA.isHPHull_image_of_disjoint_closure hA hK₁t hdA₁
    have h3 := isFilling_image_add hK₂t (-x₁) h2
    have hK₃t := isHPHull_image_add hK₂t (-x₁)
    have hd₃ : Disjoint (ball (mobPole c' (c' * x₁ + d') : ℂ) r₃)
        ((fun z : ℂ => z + ((-x₁ : ℝ) : ℂ)) '' (gA '' (M₁ '' Kt))) := by
      rw [hpole₂', Set.disjoint_left]
      rintro _ hb ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
      rw [mem_ball, dist_eq_norm] at hb
      have := hclear w (hmono hw)
      have heq : gA (M₁ w) + ((-x₁ : ℝ) : ℂ) - ((P₂ : ℂ) - x₁) = gA (M₁ w) - P₂ := by
        push_cast
        ring
      rw [heq] at hb
      linarith
    have h4 := isFilling_image_realMobius hdet₂ hc' hK₃t hr₃pos hd₃ h3
    have hgH : ∀ w ∈ Kt, M₁ w ∈ H ∧ gA (M₁ w) ∈ H ∧ gA (M₁ w) + ((-x₁ : ℝ) : ℂ) ∈ H := by
      intro w hw
      have h := hM₁A w (hKD w (hmono hw))
      have hg : gA (M₁ w) ∈ H := hgA.1.2.mapsTo h
      refine ⟨h.1, hg, ?_⟩
      have hg' : 0 < (gA (M₁ w)).im := hg
      show 0 < (gA (M₁ w) + ((-x₁ : ℝ) : ℂ)).im
      simpa using hg'
    have hSK : S ∩ H ⊆ Kt := inter_H_subset_of_isFilling hS
    have hid : ∀ w ∈ Kt, M₂' (gA (M₁ w) + ((-x₁ : ℝ) : ℂ)) = φ w := fun w hw =>
      (hφfac w (hKD w (hmono hw))).symm
    convert h4 using 1
    · rw [image_image, image_image, image_image]
      exact (image_congr fun w hw => hid w hw).symm
    · ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hwK := hSK hw
        obtain ⟨hM, hg, hgx⟩ := hgH w hwK
        exact ⟨gA (M₁ w) + ((-x₁ : ℝ) : ℂ),
          ⟨⟨gA (M₁ w), ⟨⟨M₁ w, ⟨⟨w, hw, rfl⟩, hM⟩, rfl⟩, hg⟩, rfl⟩, hgx⟩, hid w hwK⟩
      · rintro ⟨_, ⟨⟨_, ⟨⟨_, ⟨⟨w, hw, rfl⟩, -⟩, rfl⟩, -⟩, rfl⟩, -⟩, rfl⟩
        exact ⟨w, hw, (hid w (hSK hw)).symm⟩
  -- (iii) the comparison function
  set E := (fun z => QuantumZipper.fwdMap W₁ s₁ z + W₁ s₁) '' A with hEdef
  have hK₁s : IsHPHull (QuantumZipper.fwdHull W₁ s₁) := isHPHull_fwdHull hW₁c hs₁.1
  have hdAK₁ : Disjoint (closure (QuantumZipper.fwdHull W₁ s₁)) (closure A) := by
    have h := (Set.disjoint_insert_right.1 hdA').2
    rw [hK₁ t ht]
    exact (h.mono_right (closure_mono (image_mono hmono))).symm
  have hE : IsHPHull E :=
    (gmap_isMapOut_gen hW₁c hs₁.1).isHPHull_image_of_disjoint_closure hK₁s hA hdAK₁
  obtain ⟨R₂, hR₂⟩ := hE.exists_isMapOut
  obtain ⟨hR₂eq, hR₂lim⟩ := (h₂ s₁ hs₁).2.2 R₂ hR₂
  obtain ⟨hW₁s, hκ₁pos, hP₁⟩ := (⟨(h₁ t ht).2.2.1, (h₁ t ht).2.2.2.1, (h₁ t ht).2.2.2.2.1⟩ :
    W₁ s₁ = α₁ t - κ₁ t / (W t - P₁ t) ∧ 0 < κ₁ t ∧ (P₁ t : ℂ) = bdryVal W (mobPole 1 (-x)) t)
  have hconj₁ := (h₁ t ht).2.2.2.2.2
  obtain ⟨-, -, hW₄s, hκ₄pos, hP₄, hconj₄⟩ := h₄ s₂ hs₂
  refine ⟨fun ζ => nf (α₄ s₂) (κ₄ s₂) (P₄ s₂) (R₂ (nf (α₁ t) (κ₁ t) (P₁ t) ζ) - x₁), ?_, ?_⟩
  · intro z hz
    have hzD := hz.1
    have hzH := hDH hzD
    have hzK : z ∉ Kt := hz.2
    have hv : M₁ z ∈ H \ (A ∪ QuantumZipper.fwdHull W₁ s₁) := by
      refine ⟨(hM₁A z hzD).1, ?_⟩
      rintro (hA' | hK')
      · exact (hM₁A z hzD).2 hA'
      · rw [hK₁ t ht] at hK'
        obtain ⟨w, hw, hwz⟩ := hK'
        have := (bijOn_mobAt x).injOn ((isHPHull_fwdHull hW ht.1).1 hw) hzH hwz
        exact hzK (this ▸ hw)
    have hgv : gA (M₁ z) ∈ H := hgA.1.2.mapsTo (hM₁A z hzD)
    have hu : gA (M₁ z) + ((-x₁ : ℝ) : ℂ) ∈ H \ QuantumZipper.fwdHull W₃ s₂ := by
      refine ⟨by show 0 < (gA (M₁ z) + ((-x₁ : ℝ) : ℂ)).im; simpa using (show 0 < (gA (M₁ z)).im from hgv),
        ?_⟩
      rw [hK₃, hK₂ _ hs₁]
      rintro ⟨_, ⟨w, hw, rfl⟩, hwz⟩
      have hwz' : gA w = gA (M₁ z) := by simpa using hwz
      have hwA : w ∈ H \ A := ⟨hK₁s.1 hw, fun hwA => Set.disjoint_left.1 hdAK₁ (subset_closure hw)
        (subset_closure hwA)⟩
      have := hgA.1.2.injOn hwA (hM₁A z hzD) hwz'
      exact hv.2 (Or.inr (this ▸ hw))
    have e4 := hconj₄ _ hu
    have e3 : gmap W₃ s₂ (gA (M₁ z) + ((-x₁ : ℝ) : ℂ)) = gmap W₂ s₂ (gA (M₁ z)) - x₁ := by
      simp only [gmap, hW₃]
      rw [fwdMap_add_const W₂ (-x₁) s₂]
      push_cast
      ring_nf
    have e2 := hR₂eq (M₁ z) hv
    have e1 := hconj₁ z ⟨hzH, hzK⟩
    rw [hφfac z hzD, e4, e3]
    simp only [gmap] at e1 e2 ⊢
    rw [e2, e1]
  · -- the limit at the driving point
    have hWP₁ : (W t : ℂ) - P₁ t ≠ 0 := by
      rw [hP₁, hpole₁]
      exact sub_ne_zero.2 (bdryVal_ne hW hW0 hr₁ hd₁ hx0 ht).symm
    have hn₁ : Tendsto (nf (α₁ t) (κ₁ t) (P₁ t)) (𝓝[H] (W t : ℂ)) (𝓝[H] (W₁ s₁ : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h := (continuousAt_nf (α := α₁ t) (κ := κ₁ t) hWP₁).tendsto
        have hv : nf (α₁ t) (κ₁ t) (P₁ t) (W t) = (W₁ s₁ : ℂ) := by
          rw [hW₁s, nf]
          push_cast
          ring
        rw [hv] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with w hw
        exact nf_mem_H hκ₁pos hw
    have hW₃P₄ : (W₃ s₂ : ℂ) - P₄ s₂ ≠ 0 := by
      rw [hP₄]
      exact sub_ne_zero.2 (bdryVal_ne hW₃c hW₃0 hr₃pos hd4 hpole₂ hs₂).symm
    have hc4 : ContinuousAt (fun u : ℂ => nf (α₄ s₂) (κ₄ s₂) (P₄ s₂) (u - x₁)) (W₂ s₂ : ℂ) := by
      have h1 : ContinuousAt (fun u : ℂ => u - x₁) (W₂ s₂ : ℂ) := by fun_prop
      have h2 : ContinuousAt (nf (α₄ s₂) (κ₄ s₂) (P₄ s₂)) ((W₂ s₂ : ℂ) - x₁) := by
        refine continuousAt_nf ?_
        convert hW₃P₄ using 2
        simp [hW₃, sub_eq_add_neg]
      exact ContinuousAt.comp (g := nf (α₄ s₂) (κ₄ s₂) (P₄ s₂)) (f := fun u : ℂ => u - (x₁ : ℂ)) h2 h1
    have hv4 : nf (α₄ s₂) (κ₄ s₂) (P₄ s₂) ((W₂ s₂ : ℂ) - x₁) = (W₄ (τ₄ s₂) : ℂ) := by
      rw [hW₄s, nf]
      simp only [hW₃]
      push_cast
      ring
    have h := hc4.tendsto.comp (hR₂lim.comp hn₁)
    rw [hv4] at h
    exact h

end Aux10

end InteractingSLE
