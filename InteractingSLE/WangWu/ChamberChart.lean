/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ChamberArcs
import InteractingSLE.Spec.Sec6.DrivingUnconditional
import InteractingSLE.Spec.Sec7.Lemma71Pocket

/-!
# Wang–Wu Lemma 4.22: the chamber trace has a continuous driving function

Packet PROVE-WW-B4. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), §4.5:

> **Lemma 4.22** (Chamber trace and continuous driving function). Let three seed lines of heights `u₁ < 0 < u₂` be
> ordered. In each component `C` between the outer two lines, the middle line traverses `C` from its opening point
> `x` to its closing point `y`. For a conformal map `ψ : C → H` taking `x` to `0` and `y` to `∞`, its image has a
> continuous Loewner driving function after capacity parameterization.
>
> *Proof.* … Carathéodory's theorem gives a homeomorphism of the Jordan closures, understood in the sphere. Hence the
> image is continuous. … The preimage of the previous trace and the real boundary has empty interior. A nontrivial
> interval in the former would contradict simplicity; one in the latter would give a common arc with a wall. The
> deterministic Loewner trace criterion therefore gives a continuous driving function.

This file proves the lemma deterministically for three ordered simple proper arcs (`IsOrderedArcs`), with the
conclusion of Lemma 4.21 (the middle arc has no nontrivial common arc with either wall: its contact times have empty
interior) as the hypothesis it is in the source's proof.

* `exists_jordan_chart`: a **boundary chart** of a Jordan domain: `Ψ` continuous and injective on the closure minus
  the closing point `y`, mapping the domain into `ℍ`, the opening point `x` to `0`, and tending to `∞` at `y`
  (`cayleyInv ∘ discMob ∘ h⁻¹`, `h` the Schoenflies homeomorphism);
* `mappedSegment_of_chart`: for **every** such chart of a pocket the mapped middle segment is a continuous simple path
  in `ℍ̄` from `0` to `∞` whose real-boundary times have empty interior (the specification's
  `Sec7.Lemma71.mappedSegment_props`);
* **`IsOrderedArcs.lemma422`**: for every component `C ∈ betweenComponents R L`, the middle arc meets the closure of
  `C` exactly along a time interval starting at a common point `x` of the walls (with an increasing clock `κ` onto
  it), and for every chart `Ψ` of `C` (in `ℍ` coordinates, `x ↦ 0`, closing point `↦ ∞`) the image
  `u ↦ Ψ(M(κ u))` has, on every finite horizon, a continuous Loewner driving function after capacity
  parameterization (`Sec6.exists_driver_of_injOn`, the specification's Proposition 6.12); such charts exist.

The source's "conformal map `ψ`" enters only through its boundary homeomorphism (Carathéodory), which is a chart in
the sense above; the theorem holds for every chart, conformal or not.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)

namespace InteractingSLE.WangWu

variable {a b : ℂ}

theorem norm_discMob_lt_one (hb : ‖b‖ = 1) {w : ℂ} (hw : ‖w‖ < 1) : ‖discMob a b w‖ < 1 := by
  have hdpos : 0 < normSq (mobDen (mobK a b) b w) := normSq_pos.2 (mobDen_ne_zero _ hb hw.le)
  have hw2 : normSq w < 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  have h := normSq_discMob (a := a) hb hw.le
  have : normSq (discMob a b w) < 1 := by
    rw [h]
    have : 4 * (normSq w - 1) / normSq (mobDen (mobK a b) b w) < 0 :=
      div_neg_of_neg_of_pos (by linarith) hdpos
    linarith
  rw [Complex.normSq_eq_norm_sq] at this
  nlinarith [norm_nonneg (discMob a b w)]

theorem discMob_eq_one_iff (hb : ‖b‖ = 1) {w : ℂ} (hw : ‖w‖ ≤ 1) : discMob a b w = 1 ↔ w = b := by
  constructor
  · intro h
    exact discMob_injOn hb (by rwa [mem_closedBall, dist_zero_right])
      (by rw [mem_closedBall, dist_zero_right, hb]) (h.trans (discMob_right hb).symm)
  · rintro rfl; exact discMob_right hb

theorem cayleyInv_neg_one : cayleyInv (-1) = 0 := by simp [cayleyInv]

theorem cayleyInv_injOn : InjOn cayleyInv {w | w ≠ 1} := fun u hu v hv h => by
  rw [← QuantumZipper.CA.cayley_cayleyInv hu, h, QuantumZipper.CA.cayley_cayleyInv hv]

/-- **A boundary chart of a Jordan domain.** For a Jordan curve `Γ` and two distinct points `x, y ∈ Γ`, there is a
map `Ψ`, continuous and injective on `closure (jordanIn Γ) \ {y}`, with values in `ℍ̄`, mapping the inside into `ℍ`,
`x` to `0`, and tending to `∞` at `y`. -/
theorem exists_jordan_chart {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) {x y : ℂ} (hx : x ∈ Γ)
    (hy : y ∈ Γ) (hxy : x ≠ y) :
    ∃ Ψ : ℂ → ℂ, ContinuousOn Ψ (closure (jordanIn Γ) \ {y}) ∧ InjOn Ψ (closure (jordanIn Γ) \ {y}) ∧
      MapsTo Ψ (closure (jordanIn Γ) \ {y}) Hbar ∧ MapsTo Ψ (jordanIn Γ) H ∧ Ψ x = 0 ∧
      Tendsto Ψ (𝓝[closure (jordanIn Γ) \ {y}] y) (cobounded ℂ) := by
  obtain ⟨h, hs, hb⟩ := exists_homeomorph_jordanIn hΓ
  have hcl : closure (jordanIn Γ) = h '' closedBall 0 1 := by
    rw [closure_jordanIn hΓ, ← hb, ← hs, ← image_union, ball_union_sphere]
  have hsymm : ∀ w ∈ closure (jordanIn Γ), ‖h.symm w‖ ≤ 1 := by
    intro w hw
    rw [hcl] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    rw [h.symm_apply_apply, ← dist_zero_right, ← mem_closedBall]
    exact hv
  have hsph : ∀ w ∈ Γ, ‖h.symm w‖ = 1 := by
    intro w hw
    rw [← hs] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    rw [h.symm_apply_apply, ← mem_sphere_zero_iff_norm]
    exact hv
  have hxy' : h.symm x ≠ h.symm y := fun h' => hxy (h.symm.injective h')
  set Md := discMob (h.symm x) (h.symm y)
  have hy1 := hsph y hy
  have hMd1 : ∀ w ∈ closure (jordanIn Γ), Md (h.symm w) = 1 ↔ w = y := fun w hw => by
    rw [discMob_eq_one_iff hy1 (hsymm w hw)]
    exact ⟨fun h' => h.symm.injective h', fun h' => h' ▸ rfl⟩
  have hMdc : ContinuousOn (fun w => Md (h.symm w)) (closure (jordanIn Γ)) :=
    (continuousOn_discMob hy1).comp h.symm.continuous.continuousOn fun w hw => by
      rw [mem_closedBall, dist_zero_right]; exact hsymm w hw
  have hMdD : ∀ w ∈ closure (jordanIn Γ), ‖Md (h.symm w)‖ ≤ 1 := fun w hw =>
    norm_discMob_le hy1 (hsymm w hw)
  refine ⟨fun w => cayleyInv (Md (h.symm w)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    have hne : Md (h.symm w) ≠ 1 := fun h' => hw.2 ((hMd1 w hw.1).1 h')
    exact ContinuousAt.comp_continuousWithinAt (g := cayleyInv) (f := fun w => Md (h.symm w))
      (continuousAt_cayleyInv hne) ((hMdc w hw.1).mono sdiff_subset)
  · intro w hw w' hw' heq
    have hne : Md (h.symm w) ≠ 1 := fun h' => hw.2 ((hMd1 w hw.1).1 h')
    have hne' : Md (h.symm w') ≠ 1 := fun h' => hw'.2 ((hMd1 w' hw'.1).1 h')
    have h1 := cayleyInv_injOn hne hne' heq
    have h2 := discMob_injOn hy1 (by rw [mem_closedBall, dist_zero_right]; exact hsymm w hw.1)
      (by rw [mem_closedBall, dist_zero_right]; exact hsymm w' hw'.1) h1
    exact h.symm.injective h2
  · intro w hw
    exact QuantumZipper.CA.cayleyInv_mem_Hbar (by rw [mem_closedBall, dist_zero_right]; exact hMdD w hw.1)
  · intro w hw
    rw [← hb] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    refine QuantumZipper.CA.cayleyInv_mem_H ?_
    rw [h.symm_apply_apply, mem_ball, dist_zero_right]
    rw [mem_ball, dist_zero_right] at hv
    exact norm_discMob_lt_one hy1 hv
  · have hMdx : Md (h.symm x) = -1 := discMob_left (hsph x hx) hy1 hxy'
    show cayleyInv (Md (h.symm x)) = 0
    rw [hMdx, cayleyInv_neg_one]
  · refine QuantumZipper.CA.tendsto_cayleyInv_nhdsNE_one.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
    · have hyc : y ∈ closure (jordanIn Γ) := by rw [closure_jordanIn hΓ]; exact Or.inr hy
      have hMdy : Md (h.symm y) = 1 := discMob_right hy1
      have := (hMdc y hyc).mono (sdiff_subset (t := {y}))
      rw [ContinuousWithinAt, hMdy] at this
      exact this
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact fun h' => hw.2 ((hMd1 w hw.1).1 h')


/-- **The conclusion of Lemma 4.22 for a curve `γ`**: a continuous simple path in `ℍ̄` from `0` tending to `∞`, whose
real-boundary times have empty interior, and which on every finite horizon `[0, S]` is generated by a continuous
Loewner driver after a continuous strictly increasing (capacity) time change. -/
def IsChamberImage (γ : ℝ → ℂ) : Prop :=
  ContinuousOn γ (Ici 0) ∧ InjOn γ (Ici 0) ∧ MapsTo γ (Ici 0) Hbar ∧ γ 0 = 0 ∧
    Tendsto (fun u => ‖γ u‖) atTop atTop ∧ interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ u).im = 0} = ∅ ∧
    ∀ S : ℝ, 0 < S → ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∃ σ : ℝ → ℝ, σ 0 = 0 ∧
      StrictMonoOn σ (Icc 0 S) ∧ ContinuousOn σ (Icc 0 S) ∧
      ∀ t ∈ Icc 0 S, QuantumZipper.fwdHull W (σ t) = fillH (γ '' Icc 0 t)

/-- A continuous simple path in `ℍ̄` from `0` to `∞` with real-boundary times of empty interior satisfies
`IsChamberImage` (the specification's Proposition 6.12, `Sec6.exists_driver_of_injOn`). -/
theorem isChamberImage_of {γ : ℝ → ℂ} (hc : ContinuousOn γ (Ici 0)) (hi : InjOn γ (Ici 0))
    (hH : MapsTo γ (Ici 0) Hbar) (h0 : γ 0 = 0) (hinf : Tendsto (fun u => ‖γ u‖) atTop atTop)
    (hR : interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ u).im = 0} = ∅) : IsChamberImage γ := by
  refine ⟨hc, hi, hH, h0, hinf, hR, fun S hS => ?_⟩
  have hunb : ∀ u ∈ Ici (0 : ℝ), ¬ IsBounded (γ '' (Ici 0 ∩ Ici u)) := by
    intro u hu hb
    obtain ⟨K, hK⟩ := hb.exists_norm_le
    obtain ⟨v, hv⟩ := Filter.eventually_atTop.1 (tendsto_atTop.1 hinf (K + 1))
    have hmem : γ (max v u) ∈ γ '' (Ici 0 ∩ Ici u) :=
      ⟨max v u, ⟨mem_Ici.2 ((mem_Ici.1 hu).trans (le_max_right _ _)), mem_Ici.2 (le_max_right _ _)⟩, rfl⟩
    have h1 := hK _ hmem
    have h2 := hv (max v u) (le_max_left _ _)
    linarith
  obtain ⟨W, hW, hW0, σ, hσ0, hσm, hσc, hσ⟩ := Sec6.exists_driver_of_injOn ordConnected_Ici hc hi hH
    (mem_Ici.2 le_rfl) h0 hunb hR hS (mem_Ici.2 hS.le)
  exact ⟨W, hW, hW0, σ, hσ0, hσm, hσc, fun t ht => (hσ t ht).2.1⟩

namespace IsOrderedArcs

variable {R M L : ℝ → ℂ}

/-- **Wang–Wu Lemma 4.22** (chamber trace and continuous driving function), for three ordered simple proper arcs
`R` (right wall), `M` (middle), `L` (left wall) of `ℍ`, the middle arc having no nontrivial common arc with either
wall (Lemma 4.21). For every component `C` between the walls:

* the middle arc **traverses `C`**: with a continuous strictly increasing clock `κ` (from `[0, ∞)` onto the
  traversal time interval), `M(κ 0)` is a common point of the walls (the opening point `x`), `M(κ u) ∈ closure C`
  for all `u`, and every time at which `M` is in `C` is a time `κ u`;
* with `E ⊇ C` the closure of `C` minus the closing point and `yF` the filter at the closing point — explicitly,
  either the closing point is a common point `y` of the walls, `E = closure C \ {y}` and `yF ⊓ 𝓟 E = 𝓝[E] y`, or it
  is `∞`, `E = closure C` and `yF ⊓ 𝓟 E = cobounded ℂ ⊓ 𝓟 E` — **charts exist**: maps `Ψ` continuous and injective on `E`, with values in `ℍ̄`, `Ψ(C) ⊆ ℍ`, `Ψ(x) = 0`, `Ψ → ∞` at
  the closing point;
* **for every such chart `Ψ`, the image `u ↦ Ψ(M(κ u))` has a continuous Loewner driving function after capacity
  parameterization** on every finite horizon (`IsChamberImage`). -/
theorem lemma422 (h : IsOrderedArcs R M L) (hcR : interior {t ∈ Ici (0 : ℝ) | M t ∈ arcRange R} = ∅)
    (hcL : interior {t ∈ Ici (0 : ℝ) | M t ∈ arcRange L} = ∅) {C : Set ℂ}
    (hC : C ∈ betweenComponents (arcRange R) (arcRange L)) :
    ∃ κ : ℝ → ℝ, ContinuousOn κ (Ici 0) ∧ StrictMonoOn κ (Ici 0) ∧ 0 ≤ κ 0 ∧
      M (κ 0) ∈ arcRange R ∩ arcRange L ∧ (∀ u, 0 ≤ u → M (κ u) ∈ closure C) ∧
      (∀ t, 0 ≤ t → M t ∈ C → ∃ u, 0 ≤ u ∧ κ u = t) ∧
      ∃ (E : Set ℂ) (yF : Filter ℂ), C ⊆ E ∧
        ((∃ y ∈ arcRange R ∩ arcRange L, E = closure C \ {y} ∧ yF ⊓ 𝓟 E = 𝓝[E] y) ∨
          (E = closure C ∧ yF ⊓ 𝓟 E = cobounded ℂ ⊓ 𝓟 E)) ∧ (∀ u, 0 ≤ u → M (κ u) ∈ E) ∧
        Tendsto (fun u => M (κ u)) atTop yF ∧
        (∃ Ψ : ℂ → ℂ, ContinuousOn Ψ E ∧ InjOn Ψ E ∧ MapsTo Ψ E Hbar ∧ MapsTo Ψ C H ∧ Ψ (M (κ 0)) = 0 ∧
          Tendsto Ψ (yF ⊓ 𝓟 E) (cobounded ℂ)) ∧
        ∀ Ψ : ℂ → ℂ, ContinuousOn Ψ E → InjOn Ψ E → MapsTo Ψ E Hbar → MapsTo Ψ C H → Ψ (M (κ 0)) = 0 →
          Tendsto Ψ (yF ⊓ 𝓟 E) (cobounded ℂ) → IsChamberImage (fun u => Ψ (M (κ u))) := by
  obtain ⟨a, b, hg, hCU, σ, τ, hσ0, hστ, hτ1, hσa, hτb, hin, hout, hint⟩ := h.traverse_disc hcR hcL hC
  have hR := h.right
  have hM := h.middle
  have hL := h.left
  have hμ := hM.isDiscCrosscut_toDisc
  have hα := hR.isDiscCrosscut_toDisc
  have hβ := hL.isDiscCrosscut_toDisc
  obtain ⟨hJ, hUD, hUαβ, hUfr, -⟩ := pocket_props hα hβ h.toTriple.lower_upper hg
  set U := jordanIn (pocketCurve (toDisc R) (toDisc L) a b) with hUdef
  -- `C` in the half-plane, and its Cayley image `U`
  have hCH : C ⊆ H := by
    obtain ⟨z, -, -, -, rfl⟩ := hC
    exact (connectedComponentIn_subset _ _).trans sdiff_subset
  have hHbar : ∀ z ∈ H, z ∈ Hbar := fun z hz => le_of_lt (show (0 : ℝ) < z.im from hz)
  have hmemC : ∀ z ∈ Hbar, z ∈ C ↔ cayley z ∈ U := by
    intro z hz
    constructor
    · intro hzC; rw [← hCU]; exact ⟨z, hzC, rfl⟩
    · intro hzU
      rw [← hCU] at hzU
      obtain ⟨c, hc, hcz⟩ := hzU
      rwa [← cayley_injOn_Hbar (hHbar c (hCH hc)) hz hcz]
  have hCeq : C = cayleyInv '' U := by
    rw [← hCU]
    ext z
    constructor
    · intro hz; exact ⟨cayley z, ⟨z, hz, rfl⟩, cayleyInv_cayley_of_mem_Hbar (hHbar z (hCH hz))⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      rwa [cayleyInv_cayley_of_mem_Hbar (hHbar c (hCH hc))]
  have hclC : ∀ z ∈ Hbar, cayley z ∈ closure U → z ∈ closure C := by
    intro z hz hzU
    rw [hCeq, ← cayleyInv_cayley_of_mem_Hbar hz]
    exact mem_closure_image (continuousAt_cayleyInv (cayley_ne_one_of_Hbar hz)) hzU
  have hαbU : toDisc R b ∉ U := fun h' => Set.disjoint_left.1 hUαβ h'
    (Or.inl ⟨b, hg.2.1.1, rfl⟩)
  -- the clock
  have himg := Sec7.Lemma71.image_segClock hστ
  have hseg : ∀ u, 0 ≤ u → Sec7.Lemma71.segClock σ τ u ∈ Ico σ τ := fun u hu => by
    rw [← himg]; exact ⟨u, hu, rfl⟩
  have hseg01 : ∀ u, 0 ≤ u → Sec7.Lemma71.segClock σ τ u ∈ Ico (0 : ℝ) 1 := fun u hu =>
    ⟨hσ0.trans (hseg u hu).1, (hseg u hu).2.trans_le hτ1⟩
  set κ : ℝ → ℝ := fun u => arcTime (Sec7.Lemma71.segClock σ τ u) with hκ
  have hκ0 : ∀ u, 0 ≤ u → 0 ≤ κ u := fun u hu => arcTime_nonneg (hseg01 u hu)
  have hμκ : ∀ u, 0 ≤ u → toDisc M (Sec7.Lemma71.segClock σ τ u) = cayley (M (κ u)) := fun u hu =>
    toDisc_of_lt (hseg01 u hu).2
  have hκc : ContinuousOn κ (Ici 0) :=
    continuousOn_arcTime.comp (Sec7.Lemma71.continuousOn_segClock σ τ) fun u hu => (hseg01 u hu).2
  have hκm : StrictMonoOn κ (Ici 0) :=
    strictMonoOn_arcTime.comp (Sec7.Lemma71.strictMonoOn_segClock hστ) fun u hu => hseg01 u hu
  have hseg0 : Sec7.Lemma71.segClock σ τ 0 = σ := Sec7.Lemma71.segClock_zero σ τ
  -- the opening point
  have hx : cayley (M (κ 0)) = toDisc R a := by rw [← hμκ 0 le_rfl, hseg0, hσa]
  have hxR : M (κ 0) ∈ arcRange R ∩ arcRange L := by
    have hMx := hM.mem_Hbar (hκ0 0 le_rfl)
    obtain ⟨-, r, hr, hrs⟩ := hg.1
    refine ⟨(hR.cayley_mem_crossRange_iff hMx).1 ⟨a, hg.1.1, hx.symm⟩,
      (hL.cayley_mem_crossRange_iff hMx).1 ⟨r, hr, by rw [hrs, hx]⟩⟩
  -- the closing filter
  set E : Set ℂ := {z | z ∈ Hbar ∧ cayley z ∈ closure U ∧ cayley z ≠ toDisc R b} with hE
  set yF : Filter ℂ := comap cayley (𝓝 (toDisc R b)) with hyF
  have hηE : ∀ s ∈ Ico σ τ, M (arcTime s) ∈ E := by
    intro s hs
    have hs01 : s ∈ Ico (0 : ℝ) 1 := ⟨hσ0.trans hs.1, hs.2.trans_le hτ1⟩
    have hmem := hin s (Ico_subset_Icc_self hs)
    rw [toDisc_of_lt hs01.2] at hmem
    refine ⟨hM.mem_Hbar (arcTime_nonneg hs01), hmem, fun h' => ?_⟩
    rw [← hτb, ← toDisc_of_lt hs01.2] at h'
    exact hs.2.ne (hμ.inj (Ico_subset_Icc_self hs01) ⟨hσ0.trans hστ.le, hτ1⟩ h')
  have hκE : ∀ u, 0 ≤ u → M (κ u) ∈ E := fun u hu => hηE _ (hseg u hu)
  have hlim : Tendsto (fun u => M (κ u)) atTop yF := by
    rw [hyF, tendsto_comap_iff]
    have hτ01 : τ ∈ Icc (0 : ℝ) 1 := ⟨hσ0.trans hστ.le, hτ1⟩
    have h1 : Tendsto (Sec7.Lemma71.segClock σ τ) atTop (𝓝[Icc 0 1] τ) :=
      tendsto_nhdsWithin_iff.2 ⟨(Sec7.Lemma71.tendsto_segClock hστ).mono_right nhdsWithin_le_nhds,
        (eventually_ge_atTop 0).mono fun u hu => Ico_subset_Icc_self (hseg01 u hu)⟩
    have h2 := ((hμ.cont τ hτ01).tendsto.comp h1)
    rw [hτb] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with u hu
    exact hμκ u hu
  refine ⟨κ, hκc, hκm, hκ0 0 le_rfl, hxR, fun u hu => hclC _ (hM.mem_Hbar (hκ0 u hu)) ?_, ?_, E, yF, ?_, ?_,
    hκE, hlim, ?_, ?_⟩
  · rw [← hμκ u hu]; exact hin _ (Ico_subset_Icc_self (hseg u hu))
  · -- every time in `C` is a clock time
    intro t ht htC
    have hs01 := discTime_mem_Ico ht
    have hμs : toDisc M (discTime t) ∈ U := by
      rw [toDisc_discTime M ht]; exact (hmemC _ (hM.mem_Hbar ht)).1 htC
    have hsστ : discTime t ∈ Icc σ τ := by
      by_contra hnot
      exact hout _ (Ico_subset_Icc_self hs01) hnot (subset_closure hμs)
    have hsτ : discTime t ≠ τ := fun h' => hαbU (by rw [← hτb, ← h']; exact hμs)
    obtain ⟨u, hu, hsu⟩ : discTime t ∈ Sec7.Lemma71.segClock σ τ '' Ici 0 := by
      rw [himg]; exact ⟨hsστ.1, lt_of_le_of_ne hsστ.2 hsτ⟩
    exact ⟨u, hu, by simp only [hκ, hsu, arcTime_discTime ht]⟩
  · -- `C ⊆ E`
    intro z hz
    have hzH := hHbar z (hCH hz)
    have hzU := (hmemC z hzH).1 hz
    exact ⟨hzH, subset_closure hzU, fun h' => hαbU (h' ▸ hzU)⟩
  · -- the closing point: a common point of the walls, or `∞`
    have hHbarc : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im
    have hclCH : closure C ⊆ Hbar := closure_minimal (fun z hz => hHbar z (hCH hz)) hHbarc
    have hclC' : ∀ z ∈ Hbar, z ∈ closure C ↔ cayley z ∈ closure U := by
      intro z hz
      refine ⟨fun hzC => ?_, hclC z hz⟩
      rw [← hCU]
      exact mem_closure_image (continuousAt_cayley_of_mem_Hbar hz) hzC
    have hb1 : b ≤ 1 := hg.2.1.1.2
    rcases lt_or_eq_of_le hb1 with hb1 | hb1
    · left
      set y := R (arcTime b) with hy
      have hyH : y ∈ Hbar := hR.mem_Hbar (arcTime_nonneg ⟨hg.2.1.1.1, hb1⟩)
      have hcy : cayley y = toDisc R b := (toDisc_of_lt hb1).symm
      obtain ⟨-, r, hr, hrs⟩ := hg.2.1
      refine ⟨y, ⟨⟨arcTime b, mem_Ici.2 (arcTime_nonneg ⟨hg.2.1.1.1, hb1⟩), rfl⟩,
        (hL.cayley_mem_crossRange_iff hyH).1 ⟨r, hr, by rw [hrs, hcy]⟩⟩, ?_, ?_⟩
      · ext z
        constructor
        · rintro ⟨hz, hzU, hzy⟩
          exact ⟨(hclC' z hz).2 hzU, fun h' => hzy (by rw [mem_singleton_iff.1 h', hcy])⟩
        · rintro ⟨hz, hzy⟩
          have hzH := hclCH hz
          exact ⟨hzH, (hclC' z hzH).1 hz, fun h' => hzy (mem_singleton_iff.2
            (cayley_injOn_Hbar hzH hyH (h'.trans hcy.symm)))⟩
      · have hne : cayley y ≠ 1 := cayley_ne_one_of_Hbar hyH
        refine le_antisymm (le_inf ?_ inf_le_right) (inf_le_inf_right _ ?_)
        · have h1 : Tendsto (fun z => cayleyInv (cayley z)) (yF ⊓ 𝓟 E) (𝓝 y) := by
            have := ((continuousAt_cayleyInv hne).tendsto.comp (tendsto_comap (f := cayley)
              (x := 𝓝 (cayley y)))).mono_left (inf_le_left (b := 𝓟 E))
            rw [cayleyInv_cayley_of_mem_Hbar hyH] at this
            rw [hyF, ← hcy]
            exact this
          refine (h1.congr' ?_).le_comap.trans (by rw [comap_id])
          exact eventually_inf_principal.2 (Eventually.of_forall fun z hz =>
            cayleyInv_cayley_of_mem_Hbar hz.1)
        · rw [hyF, ← hcy]
          exact tendsto_iff_comap.1 (continuousAt_cayley_of_mem_Hbar hyH).tendsto
    · right
      have hb1' : toDisc R b = 1 := by rw [hb1, toDisc_one]
      refine ⟨?_, ?_⟩
      · ext z
        constructor
        · rintro ⟨hz, hzU, -⟩
          exact (hclC' z hz).2 hzU
        · intro hz
          have hzH := hclCH hz
          exact ⟨hzH, (hclC' z hzH).1 hz, by rw [hb1']; exact cayley_ne_one_of_Hbar hzH⟩
      · refine le_antisymm (le_inf ?_ inf_le_right) (inf_le_inf_right _ ?_)
        · have h1 : Tendsto cayley (yF ⊓ 𝓟 E) (𝓝[≠] 1) := by
            refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_inf_principal.2 (Eventually.of_forall
              fun z hz => cayley_ne_one_of_Hbar hz.1)⟩
            rw [hyF, hb1']
            exact tendsto_inf_left tendsto_comap
          have h2 := QuantumZipper.CA.tendsto_cayleyInv_nhdsNE_one.comp h1
          refine (h2.congr' ?_).le_comap.trans (by rw [comap_id])
          exact eventually_inf_principal.2 (Eventually.of_forall fun z hz =>
            cayleyInv_cayley_of_mem_Hbar hz.1)
        · rw [hyF, hb1']
          exact tendsto_iff_comap.1 QuantumZipper.CA.tendsto_cayley_cobounded
  · -- a chart exists
    have hxy : toDisc R a ≠ toDisc R b := fun h' =>
      hg.2.2.1.ne (hα.inj hg.1.1 hg.2.1.1 h')
    obtain ⟨Ψ', hΨc, hΨi, hΨH, hΨU, hΨx, hΨy⟩ := exists_jordan_chart hJ
      (Or.inl ⟨a, ⟨le_rfl, hg.2.2.1.le⟩, rfl⟩) (Or.inl ⟨b, ⟨hg.2.2.1.le, le_rfl⟩, rfl⟩) hxy
    have hcayE : MapsTo cayley E (closure U \ {toDisc R b}) := fun z hz => ⟨hz.2.1, hz.2.2⟩
    refine ⟨fun z => Ψ' (cayley z), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hΨc.comp (fun z hz => (continuousAt_cayley_of_mem_Hbar hz.1).continuousWithinAt) hcayE
    · exact fun z hz z' hz' heq => cayley_injOn_Hbar hz.1 hz'.1 (hΨi (hcayE hz) (hcayE hz') heq)
    · exact fun z hz => hΨH (hcayE hz)
    · exact fun z hz => hΨU ((hmemC z (hHbar z (hCH hz))).1 hz)
    · show Ψ' (cayley (M (κ 0))) = 0
      rw [hx]; exact hΨx
    · refine hΨy.comp (tendsto_inf.2 ⟨?_, ?_⟩)
      · exact tendsto_inf_left tendsto_comap
      · exact tendsto_principal.2 (eventually_inf_principal.2 (Eventually.of_forall fun z hz => hcayE hz))
  · -- every chart gives a chamber image
    intro Ψ hΨc hΨi hΨH hΨC hΨ0 hΨy
    have himg' : Sec7.Lemma71.segClock σ τ '' Ici 0 = Ico σ τ := himg
    have hηc : ContinuousOn (fun s => M (arcTime s)) (Ico σ τ) :=
      hM.cont.comp (continuousOn_arcTime.mono fun s hs => hs.2.trans_le hτ1)
        fun s hs => mem_Ici.2 (arcTime_nonneg ⟨hσ0.trans hs.1, hs.2.trans_le hτ1⟩)
    have hηi : InjOn (fun s => M (arcTime s)) (Ico σ τ) := fun s hs s' hs' heq =>
      strictMonoOn_arcTime.injOn ⟨hσ0.trans hs.1, hs.2.trans_le hτ1⟩ ⟨hσ0.trans hs'.1, hs'.2.trans_le hτ1⟩
        (hM.inj (mem_Ici.2 (arcTime_nonneg ⟨hσ0.trans hs.1, hs.2.trans_le hτ1⟩))
          (mem_Ici.2 (arcTime_nonneg ⟨hσ0.trans hs'.1, hs'.2.trans_le hτ1⟩)) heq)
    have hCint : interior {t ∈ Sec7.Lemma71.segClock σ τ '' Ici 0 |
        Sec7.Lemma71.segClock σ τ 0 < t ∧ M (arcTime t) ∉ C} = ∅ := by
      rw [himg', hseg0]
      refine subset_empty_iff.1 ((interior_mono ?_).trans hint.subset)
      rintro t ⟨ht, hσt, htC⟩
      have ht01 : t ∈ Ico (0 : ℝ) 1 := ⟨hσ0.trans ht.1, ht.2.trans_le hτ1⟩
      refine ⟨Ico_subset_Icc_self ht, hσt, fun h' => htC ?_⟩
      rw [toDisc_of_lt ht01.2] at h'
      exact (hmemC _ (hM.mem_Hbar (arcTime_nonneg ht01))).2 h'
    obtain ⟨hc, hi, hH, h0, hinf, hRr⟩ := Sec7.Lemma71.mappedSegment_props (η := fun s => M (arcTime s))
      (Sec7.Lemma71.continuousOn_segClock σ τ) (Sec7.Lemma71.strictMonoOn_segClock hστ) (himg' ▸ hηc)
      (himg' ▸ hηi) (himg' ▸ hηE) hΨc hΨi hΨH hΨC hΨ0 hlim hΨy hCint
    exact isChamberImage_of hc hi hH h0 hinf hRr

end IsOrderedArcs

end InteractingSLE.WangWu
