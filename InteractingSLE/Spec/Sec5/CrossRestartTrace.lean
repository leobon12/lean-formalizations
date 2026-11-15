/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartChart

/-!
# The restart chart at the level of traces: fillings under the coordinate change

Packet PROVE-SEC5-F (obstruction (ii) of `planning/handoffs/PROVE-SEC5-E.md`, trace level). A generating trace `γ`
of a Loewner chain describes its hulls through fillings: `K_t` is the filling `IsFilling K_t (γ[0, t])` (frozen
`IsFilling`: `ℍ \ K_t` is the unbounded component of `ℍ \ γ[0, t]`). This file transports fillings through the three
factors of the restart chart (`CrossRestartChart.restartMap`):

* `isFilling_image_realMobius`: a real Möbius map whose pole avoids the hull;
* `isFilling_image_mapOut`: the mapping-out function of a hull `A` whose closure is disjoint from that of the hull;
* `isFilling_image_add`: a real translation.

Only the points of the trace in `ℍ` matter (`isFilling_inter_H_iff`), and those lie in the hull
(`inter_H_subset_of_isFilling`); the real points of a trace (its start) are handled by boundary values.

The tool is `image_connectedComponentIn`: a map with a continuous inverse maps connected components onto connected
components.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE

namespace Sec5

namespace CrossRestart

open ConformalImage ConformalImageFull

/-! ### Connected components under maps with continuous inverses -/

/-- **A map with a continuous inverse maps connected components onto connected components.** -/
theorem image_connectedComponentIn {f g : ℂ → ℂ} {U V S : Set ℂ} (hf : ContinuousOn f U)
    (hg : ContinuousOn g V) (hfUV : MapsTo f U V) (hgf : ∀ z ∈ U, g (f z) = z)
    (hfg : ∀ w ∈ V, f (g w) = w) (hS : S ⊆ U) {z : ℂ} (hz : z ∈ S) :
    f '' connectedComponentIn S z = connectedComponentIn (f '' S) (f z) := by
  apply Subset.antisymm
  · exact (isPreconnected_connectedComponentIn.image f
      (hf.mono ((connectedComponentIn_subset S z).trans hS))).subset_connectedComponentIn
      ⟨z, mem_connectedComponentIn hz, rfl⟩ (image_mono (connectedComponentIn_subset S z))
  · set D := connectedComponentIn (f '' S) (f z) with hD
    have hDV : D ⊆ V := (connectedComponentIn_subset _ _).trans (image_subset_iff.2
      fun w hw => hfUV (hS hw))
    have hgD : g '' D ⊆ connectedComponentIn S z := by
      refine (isPreconnected_connectedComponentIn.image g (hg.mono hDV)).subset_connectedComponentIn
        ⟨f z, mem_connectedComponentIn ⟨z, hz, rfl⟩, hgf z (hS hz)⟩ ?_
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨y, hy, rfl⟩ := connectedComponentIn_subset _ _ hw
      rw [hgf y (hS hy)]
      exact hy
    intro w hw
    exact ⟨g w, hgD ⟨w, hw, rfl⟩, hfg w (hDV hw)⟩

/-! ### Fillings -/

theorem isFilling_inter_H_iff {K A : Set ℂ} : IsFilling K (A ∩ H) ↔ IsFilling K A := by
  have h : H \ (A ∩ H) = H \ A := by
    ext z; simp only [Set.mem_sdiff, mem_inter_iff, not_and]; tauto
  unfold IsFilling
  rw [h]

/-- The points of `ℍ` of a filled set lie in its filling. -/
theorem inter_H_subset_of_isFilling {K A : Set ℂ} (h : IsFilling K A) : A ∩ H ⊆ K := by
  obtain ⟨⟨z, -, hz⟩, -⟩ := h
  intro a ha
  by_contra haK
  have : a ∈ connectedComponentIn (H \ A) z := by rw [hz]; exact ⟨ha.2, haK⟩
  exact (connectedComponentIn_subset _ _ this).2 ha.1

theorem not_isBounded_H_diff {B : Set ℂ} (hB : Bornology.IsBounded B) :
    ¬ Bornology.IsBounded (H \ B) := by
  intro h
  apply not_isBounded_setOf_lt_im 0
  have : {w : ℂ | (0 : ℝ) < w.im} ⊆ (H \ B) ∪ B := fun w hw => by
    by_cases hwB : w ∈ B
    · exact Or.inr hwB
    · exact Or.inl ⟨hw, hwB⟩
  exact (h.union hB).subset this

/-- **Fillings under a real Möbius map** whose pole keeps a positive distance from the hull. -/
theorem isFilling_image_realMobius {a b c d : ℝ} (hdet : 0 < a * d - b * c) (hc : c ≠ 0) {K A : Set ℂ}
    (hK : IsHPHull K) {r : ℝ} (hr : 0 < r) (hd : Disjoint (ball (mobPole c d : ℂ) r) K)
    (h : IsFilling K A) : IsFilling (realMobius a b c d '' K) (realMobius a b c d '' (A ∩ H)) := by
  have hdet' : 0 < d * a - (-b) * (-c) := by linarith
  have hbij := QuantumZipper.CA.bijOn_realMobius_H hdet
  obtain ⟨⟨z, hzK, hz⟩, -⟩ := h
  have hzA : z ∈ H \ A := by
    rw [← hz] at hzK; exact connectedComponentIn_subset _ _ hzK
  have hAH : A ∩ H ⊆ H := inter_subset_right
  have hS : H \ (A ∩ H) = H \ A := by
    ext w; simp only [Set.mem_sdiff, mem_inter_iff, not_and]; tauto
  refine ⟨⟨realMobius a b c d z, ?_, ?_⟩, not_isBounded_H_diff
    (isHPHull_image hdet hc hK hr hd).2.1⟩
  · rw [← image_H_diff hdet hK.1]; exact ⟨z, hzK, rfl⟩
  · rw [← image_H_diff hdet hAH, hS, ← image_H_diff hdet hK.1, ← hz]
    exact (image_connectedComponentIn (differentiableOn_realMobius hdet).continuousOn
      (differentiableOn_realMobius hdet').continuousOn hbij.mapsTo
      (fun w hw => QuantumZipper.CA.realMobius_inv_apply hdet hw)
      (fun w hw => realMobius_mobInv hdet hw) sdiff_subset hzA).symm

/-- **Fillings under the mapping-out function of a hull `A`** whose closure is disjoint from that of the hull. -/
theorem isFilling_image_mapOut {A K A' : Set ℂ} {φ : ℂ → ℂ} (hA : IsHPHull A) (hφ : IsMapOut A φ)
    (hK : IsHPHull K) (hd : Disjoint (closure A) (closure K)) (h : IsFilling K A') :
    IsFilling (φ '' K) (φ '' (A' ∩ H)) := by
  have hAK : Disjoint A K := hd.mono subset_closure subset_closure
  have hA'K : A' ∩ H ⊆ K := inter_H_subset_of_isFilling h
  obtain ⟨⟨z₀, hz₀K, hz₀⟩, -⟩ := h
  -- a base point off `A ∪ K`
  have hne : (H \ (A ∪ K)).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    exact not_isBounded_H_diff (hA.2.1.union hK.2.1) (by rw [hemp]; exact Bornology.isBounded_empty)
  obtain ⟨z, hzH, hzAK⟩ := hne
  have hzK : z ∈ H \ K := ⟨hzH, fun h' => hzAK (Or.inr h')⟩
  have hcomp : connectedComponentIn (H \ A') z = H \ K := by
    rw [← hz₀] at hzK ⊢
    exact (connectedComponentIn_eq hzK).symm
  -- the component of `ℍ \ (A' ∪ A)` containing `z` is `ℍ \ (A ∪ K)`
  have hsub : H \ (A ∪ A' ∩ H) ⊆ H \ A' := fun w hw =>
    ⟨hw.1, fun hA' => hw.2 (Or.inr ⟨hA', hw.1⟩)⟩
  have hcomp' : connectedComponentIn (H \ (A ∪ A' ∩ H)) z = H \ (A ∪ K) := by
    apply Subset.antisymm
    · intro w hw
      have hw1 : w ∈ connectedComponentIn (H \ A') z := connectedComponentIn_mono z hsub hw
      rw [hcomp] at hw1
      have hw2 := connectedComponentIn_subset _ _ hw
      exact ⟨hw1.1, fun h' => h'.elim (fun hA' => hw2.2 (Or.inl hA')) hw1.2⟩
    · refine (isPreconnected_H_diff_union hA hK hd).subset_connectedComponentIn ⟨hzH, hzAK⟩ ?_
      intro w hw
      exact ⟨hw.1, fun h' => h'.elim (fun hA' => hw.2 (Or.inl hA')) fun hA' => hw.2 (Or.inr (hA'K hA'))⟩
  -- transport by `φ`, a homeomorphism of `ℍ \ A` onto `ℍ`
  set S := H \ A with hSdef
  have hSo : IsOpen S := hA.isOpen
  set e := QuantumZipper.CA.univalentOPH hSo hφ.1.1 hφ.1.2.injOn with he
  have himg : φ '' S = H := hφ.1.2.image_eq
  have hsc : ContinuousOn e.symm H := by
    have := QuantumZipper.CA.differentiableOn_univalentOPH_symm hSo hφ.1.1 hφ.1.2.injOn
    rw [himg] at this
    exact this.continuousOn
  have hleft : ∀ w ∈ S, e.symm (φ w) = w := fun w hw =>
    QuantumZipper.CA.univalentOPH_symm_apply_apply hSo hφ.1.1 hφ.1.2.injOn hw
  have hright : ∀ w ∈ H, φ (e.symm w) = w := fun w hw =>
    QuantumZipper.CA.univalentOPH_apply_symm_apply hSo hφ.1.1 hφ.1.2.injOn (himg.symm ▸ hw)
  have hAKH : A ∪ K ⊆ H := union_subset hA.1 hK.1
  have hAA'H : A ∪ A' ∩ H ⊆ H := union_subset hA.1 inter_subset_right
  have hK' : H \ φ '' K = φ '' (H \ (A ∪ K)) := by
    have := hφ.H_diff_image (subset_union_left (t := K)) hAKH
    rwa [union_sdiff_left_of_disjoint_closure hd] at this
  have hA'' : H \ φ '' (A' ∩ H) = φ '' (H \ (A ∪ A' ∩ H)) := by
    have := hφ.H_diff_image (subset_union_left (t := A' ∩ H)) hAA'H
    have heq : (A ∪ A' ∩ H) \ A = A' ∩ H := by
      ext w
      simp only [Set.mem_sdiff, mem_union]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd h1 h2
        · exact h1
      · intro h1
        exact ⟨Or.inr h1, fun hwA => Set.disjoint_left.1 hAK hwA (hA'K h1)⟩
    rwa [heq] at this
  refine ⟨⟨φ z, ?_, ?_⟩, not_isBounded_H_diff
    (hφ.isHPHull_image_of_disjoint_closure hA hK hd).2.1⟩
  · rw [hK']; exact ⟨z, ⟨hzH, hzAK⟩, rfl⟩
  · rw [hA'', hK', ← hcomp']
    have hzS : z ∈ H \ (A ∪ A' ∩ H) :=
      ⟨hzH, fun h' => h'.elim (fun h'' => hzAK (Or.inl h'')) fun h'' => hzK.2 (hA'K h'')⟩
    exact (image_connectedComponentIn hφ.1.1.continuousOn hsc hφ.1.2.mapsTo hleft hright
      (fun w hw => ⟨hw.1, fun hwA => hw.2 (Or.inl hwA)⟩) hzS).symm

/-- **Fillings under a real translation.** -/
theorem isFilling_image_add {K A : Set ℂ} (hK : IsHPHull K) (x : ℝ) (h : IsFilling K A) :
    IsFilling ((fun z : ℂ => z + x) '' K) ((fun z : ℂ => z + x) '' (A ∩ H)) := by
  have hdet : (0 : ℝ) < 1 * 1 - x * 0 := by norm_num
  have hm : ∀ z : ℂ, realMobius 1 x 0 1 z = z + x := fun z => by simp [realMobius]
  have hfun : realMobius 1 x 0 1 = fun z : ℂ => z + x := funext hm
  have hbij := QuantumZipper.CA.bijOn_realMobius_H hdet
  have hdet' : 0 < (1 : ℝ) * 1 - (-x) * (-0) := by norm_num
  obtain ⟨⟨z, hzK, hz⟩, -⟩ := h
  have hzA : z ∈ H \ A := by
    rw [← hz] at hzK; exact connectedComponentIn_subset _ _ hzK
  have hS : H \ (A ∩ H) = H \ A := by
    ext w; simp only [Set.mem_sdiff, mem_inter_iff, not_and]; tauto
  have hbdd : Bornology.IsBounded ((fun z : ℂ => z + x) '' K) := by
    obtain ⟨M, hM⟩ := hK.2.1.exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨M + |x|, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    calc ‖w + x‖ ≤ ‖w‖ + ‖(x : ℂ)‖ := norm_add_le _ _
      _ ≤ M + |x| := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith [hM w hw]
  rw [← hfun]
  refine ⟨⟨realMobius 1 x 0 1 z, ?_, ?_⟩, not_isBounded_H_diff (by rwa [hfun])⟩
  · rw [← image_H_diff hdet hK.1]; exact ⟨z, hzK, rfl⟩
  · rw [← image_H_diff hdet inter_subset_right, hS, ← image_H_diff hdet hK.1, ← hz]
    exact (image_connectedComponentIn (differentiableOn_realMobius hdet).continuousOn
      (differentiableOn_realMobius hdet').continuousOn hbij.mapsTo
      (fun w hw => QuantumZipper.CA.realMobius_inv_apply hdet hw)
      (fun w hw => realMobius_mobInv hdet hw) sdiff_subset hzA).symm

theorem isHPHull_image_add {K : Set ℂ} (hK : IsHPHull K) (x : ℝ) :
    IsHPHull ((fun z : ℂ => z + x) '' K) := by
  have h := hK.image_affHomeo (r := 1) (x := x) one_pos
  have hf : ⇑(affHomeo 1 one_pos x) = fun z : ℂ => z + x := by
    rw [coe_affHomeo]; funext z; simp
  rwa [hf] at h

/-! ### The restart chart at the level of traces -/

/-- **The counterflow trace in the restart chart** (trace level of Lemma 5.7's coordinate change). In the setting of
`exists_loewner_restartMap`, let `γ` be a trace of the counterflow hulls on `(0, T]` (`K′_t` is the filling of
`γ([0, t])`), continuous on `[0, T]`, starting at `0` and in `ℍ` at positive times. Then, with `W̃` and `τ` from
`exists_loewner_restartMap`:
* `K̃_{τ(t)}` is the filling of `Φ(γ([0, t]) ∩ ℍ)` for `t ∈ (0, T]`;
* `Φ ∘ γ` is continuous on `(0, T]` and tends to `0` as `t → 0⁺` within `(0, T]`.

So `Φ ∘ γ`, completed by `0` at time `0` and reparametrized by `τ`, is a generating trace of `W̃` on `[0, τ(T)]`. -/
theorem exists_loewner_restartMap_trace {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 ≤ T) {q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hd1 : Disjoint (ball (-1 : ℂ) r) (QuantumZipper.fwdHull W T)) {U : ℝ → ℝ} (hU : Continuous U)
    (hU0 : U 0 = 0) {σ : ℝ} (hσ : 0 ≤ σ)
    (hd2 : Disjoint (closure (QuantumZipper.fwdHull U σ))
      (insert ((-1 - q : ℝ) : ℂ) (closure (realMobius 0 (-(1 + q)) 1 1 '' QuantumZipper.fwdHull W T))))
    {x₁ : ℝ} (hx₁ : (x₁ : ℂ) = bdryVal U (-1 - q) σ) {r₃ : ℝ} (hr₃ : 0 < r₃)
    (hd3 : Disjoint (ball (U σ : ℂ) r₃)
      (gmap U σ '' (realMobius 0 (-(1 + q)) 1 1 '' QuantumZipper.fwdHull W T)))
    {γ : ℝ → ℂ} (hγ0 : γ 0 = 0) (hγc : ContinuousOn γ (Icc 0 T))
    (hγH : ∀ t ∈ Ioc (0 : ℝ) T, γ t ∈ H)
    (hγK : ∀ t ∈ Ioc (0 : ℝ) T, IsFilling (QuantumZipper.fwdHull W t) (γ '' Icc 0 t)) :
    ∃ (τ W' : ℝ → ℝ), Continuous W' ∧ W' 0 = 0 ∧ τ 0 = 0 ∧ StrictMonoOn τ (Icc 0 T) ∧
      ContinuousOn τ (Icc 0 T) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        QuantumZipper.fwdHull W' (τ t) = restartMap q U σ x₁ '' QuantumZipper.fwdHull W t) ∧
      (∀ t ∈ Ioc (0 : ℝ) T, IsFilling (QuantumZipper.fwdHull W' (τ t))
        (restartMap q U σ x₁ '' (γ '' Icc 0 t ∩ H))) ∧
      ContinuousOn (fun t => restartMap q U σ x₁ (γ t)) (Ioc 0 T) ∧
      Tendsto (fun t => restartMap q U σ x₁ (γ t)) (𝓝[Ioc 0 T] 0) (𝓝 0) := by
  obtain ⟨τ, W', hW'c, hW'0, hτ0, hτm, hτc, hK⟩ :=
    exists_loewner_restartMap hW hW0 hT hq hr hd1 hU hU0 hσ hd2 hx₁ hr₃ hd3
  set m₁ := realMobius 0 (-(1 + q)) 1 1 with hm₁
  set A := QuantumZipper.fwdHull U σ with hAdef
  set φ := gmap U σ with hφdef
  set P₂ : ℝ := U σ - x₁ with hP₂
  set m₂ := realMobius (-1) 0 1 (-P₂) with hm₂
  have hA : IsHPHull A := isHPHull_fwdHull hU hσ
  have hφ : IsMapOut A φ := isMapOut_fwdMap hU hU0 hσ
  have hdet₁ : 0 < (0 : ℝ) * 1 - (-(1 + q)) * 1 := by linarith
  have hpole₁ : ((mobPole 1 1 : ℝ) : ℂ) = -1 := by simp [mobPole]
  -- `x₁ < U σ` (as in `exists_loewner_restartMap`)
  have hcl : ((-1 - q : ℝ) : ℂ) ∉ closure A := fun h => Set.disjoint_left.1 hd2 h (mem_insert _ _)
  obtain ⟨r', hr', hr'd⟩ := Metric.mem_nhds_iff.1 (isOpen_compl_iff.2 isClosed_closure |>.mem_nhds hcl)
  have hball : Disjoint (ball ((-1 - q : ℝ) : ℂ) r') A :=
    Set.disjoint_left.2 fun z hz hzA => hr'd hz (subset_closure hzA)
  have hx₁lt : x₁ < U σ := by
    have := bdryVal_re_lt hU hU0 hσ hr' hball (by linarith)
    have hre : (bdryVal U (-1 - q) σ).re = x₁ := by rw [← hx₁]; simp
    linarith
  have hP₂pos : 0 < P₂ := by simp only [hP₂]; linarith
  have hdet₂ : 0 < (-1 : ℝ) * (-P₂) - 0 * 1 := by linarith
  have hpole₂ : ((mobPole 1 (-P₂) : ℝ) : ℂ) = P₂ := by simp [mobPole]
  -- the hulls of the factors at time `t ∈ [0, T]`
  have hKt : ∀ t ∈ Icc (0 : ℝ) T, IsHPHull (QuantumZipper.fwdHull W t) := fun t ht =>
    isHPHull_fwdHull hW ht.1
  have hmono : ∀ t ∈ Icc (0 : ℝ) T, QuantumZipper.fwdHull W t ⊆ QuantumZipper.fwdHull W T := fun t ht =>
    (QuantumZipper.fwdHull_mono (W := W)).1 ht.2
  have hd1t : ∀ t ∈ Icc (0 : ℝ) T, Disjoint (ball ((mobPole 1 1 : ℝ) : ℂ) r) (QuantumZipper.fwdHull W t) :=
    fun t ht => by rw [hpole₁]; exact hd1.mono_right (hmono t ht)
  have hK₁ : ∀ t ∈ Icc (0 : ℝ) T, IsHPHull (m₁ '' QuantumZipper.fwdHull W t) := fun t ht =>
    isHPHull_image hdet₁ one_ne_zero (hKt t ht) hr (hd1t t ht)
  have hd₁ : ∀ t ∈ Icc (0 : ℝ) T, Disjoint (closure A) (closure (m₁ '' QuantumZipper.fwdHull W t)) :=
    fun t ht => (hd2.mono_right (subset_insert _ _)).mono_right
      (closure_mono (image_mono (hmono t ht)))
  have hK₂ : ∀ t ∈ Icc (0 : ℝ) T, IsHPHull (φ '' (m₁ '' QuantumZipper.fwdHull W t)) := fun t ht =>
    hφ.isHPHull_image_of_disjoint_closure hA (hK₁ t ht) (hd₁ t ht)
  have hK₃ : ∀ t ∈ Icc (0 : ℝ) T,
      IsHPHull ((fun z : ℂ => z + ((-x₁ : ℝ) : ℂ)) '' (φ '' (m₁ '' QuantumZipper.fwdHull W t))) :=
    fun t ht => isHPHull_image_add (hK₂ t ht) (-x₁)
  have hd₃ : ∀ t ∈ Icc (0 : ℝ) T, Disjoint (ball ((mobPole 1 (-P₂) : ℝ) : ℂ) r₃)
      ((fun z : ℂ => z + ((-x₁ : ℝ) : ℂ)) '' (φ '' (m₁ '' QuantumZipper.fwdHull W t))) := by
    intro t ht
    rw [hpole₂, Set.disjoint_left]
    rintro w hw ⟨v, hv, rfl⟩
    have hv' : v ∈ ball (U σ : ℂ) r₃ := by
      rw [mem_ball, dist_eq_norm] at hw ⊢
      have : v + ((-x₁ : ℝ) : ℂ) - (P₂ : ℂ) = v - U σ := by simp only [hP₂]; push_cast; ring
      rwa [this] at hw
    exact Set.disjoint_left.1 hd3 hv' (image_mono (image_mono (hmono t ht)) hv)
  -- images of points of `ℍ` stay in `ℍ`
  have hm₁H : ∀ z ∈ H, m₁ z ∈ H := fun z hz => QuantumZipper.CA.realMobius_mem_H hdet₁ hz
  have hmapsH : ∀ t ∈ Icc (0 : ℝ) T, ∀ z ∈ γ '' Icc 0 t ∩ H,
      φ (m₁ z) ∈ H ∧ m₁ z ∈ H \ A := by
    intro t ht z hz
    have hzK : z ∈ QuantumZipper.fwdHull W t := by
      by_cases ht0 : t = 0
      · exfalso
        subst ht0
        obtain ⟨⟨s, hs, rfl⟩, hzH⟩ := hz
        have : s = 0 := le_antisymm hs.2 hs.1
        subst this
        rw [hγ0] at hzH
        have h0 : (0 : ℝ) < (0 : ℂ).im := hzH
        simp at h0
      · exact inter_H_subset_of_isFilling (hγK t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩) hz
    have h1 : m₁ z ∈ H \ A := ⟨hm₁H z hz.2, fun hA' => Set.disjoint_left.1 (hd₁ t ht)
      (subset_closure hA') (subset_closure ⟨z, hzK, rfl⟩)⟩
    exact ⟨hφ.1.2.mapsTo h1, h1⟩
  refine ⟨τ, W', hW'c, hW'0, hτ0, hτm, hτc, hK, fun t ht => ?_, ?_, ?_⟩
  · -- fillings
    have htI : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have f1 := isFilling_image_realMobius hdet₁ one_ne_zero (hKt t htI) hr (hd1t t htI) (hγK t ht)
    have f2 := isFilling_image_mapOut hA hφ (hK₁ t htI) (hd₁ t htI) f1
    have f3 := isFilling_image_add (hK₂ t htI) (-x₁) f2
    have f4 := isFilling_image_realMobius hdet₂ one_ne_zero (hK₃ t htI) hr₃ (hd₃ t htI) f3
    rw [hK t htI]
    have hset1 : restartMap q U σ x₁ '' QuantumZipper.fwdHull W t =
        m₂ '' ((fun z : ℂ => z + ((-x₁ : ℝ) : ℂ)) '' (φ '' (m₁ '' QuantumZipper.fwdHull W t))) := by
      simp only [image_image]
      refine image_congr fun z _ => ?_
      simp only [restartMap, hm₁, hφdef, hm₂, hP₂]
      congr 1
      push_cast
      ring
    have hset2 : restartMap q U σ x₁ '' (γ '' Icc 0 t ∩ H) =
        m₂ '' ((fun z : ℂ => z + ((-x₁ : ℝ) : ℂ)) ''
          (φ '' (m₁ '' (γ '' Icc 0 t ∩ H) ∩ H) ∩ H) ∩ H) := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨hφz, hm₁z⟩ := hmapsH t htI z hz
        have hshift : φ (m₁ z) + ((-x₁ : ℝ) : ℂ) ∈ H := by
          show 0 < (φ (m₁ z) + ((-x₁ : ℝ) : ℂ)).im
          have : 0 < (φ (m₁ z)).im := hφz
          simpa using this
        refine ⟨φ (m₁ z) + ((-x₁ : ℝ) : ℂ), ⟨⟨φ (m₁ z), ⟨⟨m₁ z, ⟨⟨z, hz, rfl⟩, hm₁z.1⟩, rfl⟩,
          hφz⟩, rfl⟩, hshift⟩, ?_⟩
        simp only [restartMap, hm₁, hφdef, hm₂, hP₂]
        congr 1
        push_cast
        ring
      · rintro ⟨_, ⟨⟨_, ⟨⟨y, ⟨⟨z, hz, rfl⟩, -⟩, rfl⟩, -⟩, rfl⟩, -⟩, rfl⟩
        refine ⟨z, hz, ?_⟩
        simp only [restartMap, hm₁, hφdef, hm₂, hP₂]
        congr 1
        push_cast
        ring
    rw [hset1, hset2]
    exact f4
  · -- continuity on `(0, T]`
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hz : γ t ∈ γ '' Icc 0 t ∩ H := ⟨⟨t, ⟨ht.1.le, le_rfl⟩, rfl⟩, hγH t ht⟩
    obtain ⟨hφz, hm₁z⟩ := hmapsH t htI (γ t) hz
    have hγt : ContinuousWithinAt γ (Ioc 0 T) t :=
      (hγc t htI).mono (fun s hs => ⟨hs.1.le, hs.2⟩)
    have hm₁c : ContinuousAt m₁ (γ t) :=
      continuousAt_realMobius (QuantumZipper.CA.realMobius_denom_ne_zero hdet₁ (hγH t ht))
    have hφc : ContinuousAt φ (m₁ (γ t)) :=
      (hφ.1.1.differentiableAt (hA.isOpen.mem_nhds hm₁z)).continuousAt
    have hm₂c : ContinuousAt m₂ (φ (m₁ (γ t)) - x₁) := by
      refine continuousAt_realMobius (QuantumZipper.CA.realMobius_denom_ne_zero hdet₂ ?_)
      show 0 < (φ (m₁ (γ t)) - x₁).im
      have : 0 < (φ (m₁ (γ t))).im := hφz
      simpa using this
    have hin : ContinuousAt (fun z => φ (m₁ z) - (x₁ : ℂ)) (γ t) :=
      (hφc.comp hm₁c).sub continuousAt_const
    exact (ContinuousAt.comp (f := fun z => φ (m₁ z) - (x₁ : ℂ)) hm₂c hin).comp_continuousWithinAt
      hγt
  · -- the limit `0` at the start
    have hγlim : Tendsto γ (𝓝[Ioc 0 T] 0) (𝓝 0) := by
      have := (hγc 0 ⟨le_rfl, hT⟩).tendsto
      rw [hγ0] at this
      exact this.mono_left (nhdsWithin_mono _ fun s hs => ⟨hs.1.le, hs.2⟩)
    have hm₁0 : m₁ 0 = ((-1 - q : ℝ) : ℂ) := by
      simp only [hm₁, realMobius]; push_cast; ring
    have hm₁lim : Tendsto (fun t => m₁ (γ t)) (𝓝[Ioc 0 T] 0) (𝓝[H] ((-1 - q : ℝ) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · rw [← hm₁0]
        exact (continuousAt_realMobius (by simp)).tendsto.comp hγlim
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact hm₁H _ (hγH t ht)
    have hφlim := (bdryVal_spec hU hU0 hσ hr' hball).2.comp hm₁lim
    rw [← hx₁] at hφlim
    have hsub : Tendsto (fun t => φ (m₁ (γ t)) - x₁) (𝓝[Ioc 0 T] 0) (𝓝 0) := by
      have := hφlim.sub_const (x₁ : ℂ)
      rwa [sub_self] at this
    have hm₂0 : m₂ 0 = 0 := by simp [hm₂, realMobius]
    have hm₂c : ContinuousAt m₂ 0 := by
      refine continuousAt_realMobius ?_
      simp only [ofReal_one, one_mul, ofReal_neg, zero_add, ne_eq, neg_eq_zero, ofReal_eq_zero]
      exact hP₂pos.ne'
    have := hm₂c.tendsto.comp hsub
    rw [hm₂0] at this
    refine this.congr fun t => ?_
    simp only [Function.comp_apply, restartMap, hm₁, hφdef, hm₂, hP₂]

end CrossRestart

end Sec5

end InteractingSLE
