/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37SideSign

/-!
# Aux. lemma 37's side germ: the branch relation (BR)

Packet PROVE-STRIPSYS42. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L130–L134, p. 199:
"Let `L_f, L_c` be the inherited logarithmic derivatives of the own-flow and counterflow coordinates just used […].
Each transition from either own coordinate to `Φ` takes the same incident collar to the upper half-plane. It extends
across a smaller open real interval by Schwarz reflection and has positive derivative there").

Here the two coordinates are compared directly through the chart `c` of the pocket: on a band rectangle around the arc
value `f(v₁)` whose bottom edge lands at wall points visited by the counterflow at `s₀` and on the wall `X` before its
own time `q′`,

* the own chart `g^X_{q′} ∘ ℓ` and the counterflow chart `g_{s₀} ∘ m ∘ ℓ` of the chart are both conformal with real
  boundary values (`exists_ext`, `exists_ext_rect`);
* the transition `ψ = m ∘ ḡ_{s₀} ∘ m ∘ f̄^X_{q′}` from the own chart to the counterflow chart `Ψ = m ∘ g_{s₀} ∘ m` is
  conformal on an upper half-disc around the own-chart limit with real boundary values (the open mapping theorem for
  the reflected own chart identifies `f̄^X_{q′}` near the limit with the chart's landing map);
* **`exists_branch`**: hence (BR): `Im(L_Ψ − L_f) → 2πk` along the chart approach at `f(v₁)`, for every own time
  `q′` after the wall time of the witness point (`exists_int_tendsto_im_sub_of_transition'`).

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Function Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd)
open InteractingSLE.WangWu (negInv revChart)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal Real

namespace InteractingSLE.Sec7.Aux37Side

open WangWu Lemma71I PocketCoord PocketJordan Aux119Bdry Lemma71O Aux37Frame

/-! ### The own chart of the wall on a rectangle -/

section Own

variable {d : ℝ → ℝ} {X : ℝ≥0 → ℂ} {c : Chart} {κ : ℂ → ℂ} {P : Set ℂ} {q' a b δ : ℝ}

/-- **The own chart of the wall `X` on a chart rectangle** (as `exists_ext_rect`, with `M = id`): the pocket avoids the
wall, so the chart region lies in `D^X_{q′}`; the bottom edge lands on `X([0, q′])`. -/
theorem exists_own_ext (hXtr : IsLoewnerTrace d (realPath X)) (hd : Continuous d) (hd0 : d 0 = 0)
    (hXa : IsProperArc (realPath X)) (hq' : 0 ≤ q') (hc : c.IsConformal) (hcP : MapsTo c.2.1 H P)
    (hPX : Disjoint P (range X)) (hℓc : ContinuousOn (land c) Hbar) (hℓH : ∀ w ∈ H, land c w = c.2.1 w)
    (hκ : ∀ q ∈ Hbar, κ (land c q) = q) (hκc : ∀ q ∈ Hbar, ContinuousWithinAt κ (land c '' Hbar) (land c q))
    (hvis : ∀ q : ℝ, q ∈ Icc a b → land c q ∈ realPath X '' Icc 0 q') :
    ∃ G : ℂ → ℂ, ContinuousOn G (land c '' closure (rect a b δ)) ∧ InjOn G (land c '' closure (rect a b δ)) ∧
      (∀ z ∈ land c '' closure (rect a b δ), trMap d 0 q' (G z) = z) ∧
      (∀ z ∈ land c '' closure (rect a b δ), z ∈ H \ fwdHull d q' → G z = fwdMap d q' z) ∧
      (∀ q ∈ closure (rect a b δ), q ∈ H → land c q ∈ H \ fwdHull d q') ∧
      ∀ ξ ρ : ℝ, ρ ≤ ξ - a → ρ ≤ b - ξ → ρ ≤ δ →
        R16.IsRealBoundaryConformal (fun w => G (land c w)) ξ ρ := by
  set S := rect a b δ with hSdef
  have hKH : closure S ⊆ Hbar := closure_rect_subset.trans crect_subset_Hbar
  have hD : ∀ q ∈ closure S, q ∈ H → (fun z : ℂ => z) (land c q) ∈ H \ fwdHull d q' := by
    intro q _ hqH
    have hP := hcP hqH
    rw [← hℓH q hqH] at hP
    refine ⟨(hℓH q hqH).symm ▸ hc.2.1 hqH, fun hK => ?_⟩
    have := WangWu.fwdHull_subset_arcRange hXtr hXa hq' hK
    rw [arcRange_realPath] at this
    exact Set.disjoint_left.1 hPX hP this
  obtain ⟨G, h1, h2, -, h4, h5, h6⟩ := exists_ext (M := fun z => z) (M' := fun z => z) hXtr hd hd0 hq' convex_rect
    rect_subset_H isCompact_closure_rect hKH hℓc hκ hκc continuousOn_id (fun _ _ => rfl)
    (fun _ _ => continuousAt_id) hD
  simp only [image_id'] at h1 h2 h4 h5 h6
  refine ⟨G, h1, h2, h4, h5, hD, fun ξ ρ hρa hρb hρδ => ?_⟩
  obtain ⟨-, hball⟩ := ball_subset_rect (a := a) (b := b) (δ := δ) hρa hρb hρδ
  have h := isRealBoundaryConformal_ext (M := fun z => z) (M' := fun z => z) hd hq' hKH hℓc hκ
    continuousOn_id (fun _ _ => rfl) hD (G := G) (by simpa only [image_id'] using h1)
    (by simpa only [image_id'] using h2) (by simpa only [image_id'] using h5) (by simpa only [image_id'] using h6)
    hball ?_ ?_
  · exact h
  · intro q hq hqH
    have hqc := closure_rect_subset hq
    have him : q.im = 0 := le_antisymm (not_lt.1 hqH) hqc.1
    have hqr : q = ((q.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hqr]
    exact Sec6.notMem_domain_of_mem_trace hXtr hq' (hvis q.re hqc.2.2)
  · intro w hw
    refine ((hc.1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hw.1)).congr_of_eventuallyEq ?_)
      |>.differentiableWithinAt
    filter_upwards [QuantumZipper.isOpen_H.mem_nhds hw.1] with w' hw'
    exact hℓH w' hw'

end Own

/-! ### The transition from the own chart to the counterflow chart -/

section Transition

variable {W d : ℝ → ℝ} {X : ℝ≥0 → ℂ} {c : Chart} {S : Set ℂ} {Gc Gα : ℂ → ℂ} {s₀ q' ξ ρ : ℝ}

/-- **The transition `ψ = m ∘ ḡ_{s₀} ∘ m ∘ f̄^X_{q′}`** is conformal on an upper half-disc around the own-chart limit
`x_X = ḡ^X_{q′}(ℓ(ξ))` with real boundary values, and `f̄^X_{q′}` sends that half-disc to landing points of the chart
(the open mapping theorem for the reflected own transition). -/
theorem isRBC_transition (hW : Continuous W) (hs₀ : 0 ≤ s₀) (hXtr : IsLoewnerTrace d (realPath X))
    (hd : Continuous d) (hd0 : d 0 = 0) (hq' : 0 ≤ q') (hρ : 0 < ρ)
    (hℓ0 : ∀ q ∈ Hbar ∩ ball (ξ : ℂ) ρ, land c q ≠ 0)
    (hball : Hbar ∩ ball (ξ : ℂ) ρ ⊆ closure S)
    (hGcc : ContinuousOn Gc (negInv '' (land c '' closure S))) (hGci : InjOn Gc (negInv '' (land c '' closure S)))
    (hGcD : ∀ z ∈ negInv '' (land c '' closure S), z ∈ H \ fwdHull W s₀ → Gc z = fwdMap W s₀ z)
    (hGcR : ∀ z ∈ negInv '' (land c '' closure S), z ∉ H \ fwdHull W s₀ → (Gc z).im = 0)
    (hDs : ∀ u ∈ H ∩ ball (ξ : ℂ) ρ, negInv (land c u) ∈ H \ fwdHull W s₀)
    (hbot : ∀ u ∈ ball (ξ : ℂ) ρ, u.im = 0 → negInv (land c u) ∉ H \ fwdHull W s₀)
    (hφc0 : ∀ u ∈ Hbar ∩ ball (ξ : ℂ) ρ, Gc (negInv (land c u)) ≠ 0)
    (hR : R16.IsRealBoundaryConformal (fun w => Gα (land c w)) ξ ρ)
    (hGαF : ∀ u ∈ Hbar ∩ ball (ξ : ℂ) ρ, trMap d 0 q' (Gα (land c u)) = land c u) :
    ∃ ε > 0, R16.IsRealBoundaryConformal (fun w => negInv (Gc (negInv (trMap d 0 q' w)))) (Gα (land c ξ)).re ε ∧
      EqOn (fun w => negInv (Gc (negInv (trMap d 0 q' w)))) (revChart W s₀ ∘ trMap d 0 q')
        (H ∩ ball (((Gα (land c ξ)).re : ℝ) : ℂ) ε) ∧
      ∀ w ∈ Hbar ∩ ball (((Gα (land c ξ)).re : ℝ) : ℂ) ε, ∃ u ∈ Hbar ∩ ball (ξ : ℂ) ρ,
        trMap d 0 q' w = land c u ∧ (w ∈ H → u ∈ H) := by
  set g := trMap d 0 q' with hg
  have hξb : ((ξ : ℝ) : ℂ) ∈ ball (ξ : ℂ) ρ := mem_ball_self hρ
  have hreal : Gα (land c ξ) = (((Gα (land c ξ)).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [hR.2.2.1 _ hξb (by simp)])
  set xα : ℝ := (Gα (land c ξ)).re with hxα
  obtain ⟨ε, hε, himg⟩ := exists_ball_image hR hξb
  rw [hreal] at himg
  have key : ∀ w ∈ Hbar ∩ ball (xα : ℂ) ε, ∃ u ∈ Hbar ∩ ball (ξ : ℂ) ρ, g w = land c u ∧ (w ∈ H → u ∈ H) ∧
      (w.im = 0 → u.im = 0) := by
    intro w hw
    obtain ⟨u, hu, hu0, hφu, hpos, hzero⟩ := himg w hw.2 hw.1
    refine ⟨u, ⟨hu0, hu⟩, ?_, hpos, hzero⟩
    rw [← hφu]
    exact hGαF u ⟨hu0, hu⟩
  have hmemE : ∀ u ∈ Hbar ∩ ball (ξ : ℂ) ρ, negInv (land c u) ∈ negInv '' (land c '' closure S) := fun u hu =>
    ⟨land c u, ⟨u, hball hu, rfl⟩, rfl⟩
  have hgc : ContinuousOn g Hbar := YuanSimpleApprox.trMap_continuousOn hXtr hd hd0 le_rfl hq'
  have hgH : ∀ w ∈ H, g w ∈ H := fun w hw => YuanSimpleApprox.trMap_mem_H hd hq' hw
  -- the transition equals `Ψ ∘ g` on the open half-disc
  have heq : EqOn (fun w => negInv (Gc (negInv (g w)))) (revChart W s₀ ∘ g) (H ∩ ball (xα : ℂ) ε) := by
    intro w hw
    obtain ⟨u, hu, hgu, huH, -⟩ := key w ⟨QuantumZipper.H_subset_Hbar hw.1, hw.2⟩
    have hz := hDs u ⟨huH hw.1, hu.2⟩
    simp only [Function.comp_apply, revChart]
    rw [hgu, hGcD _ (hmemE u hu) hz]
  have hDo : IsOpen (H \ negInv '' fwdHull W s₀) := Sec5.GlueImg.isOpen_H_diff_negInv_fwdHull hW hs₀
  have hgD : ∀ w ∈ H ∩ ball (xα : ℂ) ε, g w ∈ H \ negInv '' fwdHull W s₀ := by
    intro w hw
    obtain ⟨u, hu, hgu, huH, -⟩ := key w ⟨QuantumZipper.H_subset_Hbar hw.1, hw.2⟩
    have hz := hDs u ⟨huH hw.1, hu.2⟩
    refine ⟨hgH w hw.1, fun hK => hz.2 ?_⟩
    rw [hgu, mem_negInv_image] at hK
    exact hK
  refine ⟨ε, hε, ⟨?_, ?_, ?_, ?_, ?_⟩, heq, fun w hw => ?_⟩
  · -- holomorphic
    refine DifferentiableOn.congr ?_ heq
    intro w hw
    have hgd : DifferentiableAt ℂ g w :=
      (YuanSimpleApprox.trMap_differentiableOn hXtr hd hd0 le_rfl hq').differentiableAt
        (QuantumZipper.isOpen_H.mem_nhds hw.1)
    have hΨd : DifferentiableAt ℂ (revChart W s₀) (g w) :=
      Aux37Germ.differentiableAt_of_isDerivLog (Sec5.GlueImg.isDerivLog_revChart hW hs₀) (hgD w hw)
    exact (hΨd.comp w hgd).differentiableWithinAt
  · -- continuous up to the diameter
    intro w hw
    obtain ⟨u, hu, hgu, -, -⟩ := key w hw
    have h1 : ContinuousWithinAt (fun w => negInv (g w)) (Hbar ∩ ball (xα : ℂ) ε) w := by
      refine (WangWu.continuousAt_negInv ?_).comp_continuousWithinAt ((hgc w hw.1).mono inter_subset_left)
      rw [hgu]; exact hℓ0 u hu
    have hmaps : MapsTo (fun w => negInv (g w)) (Hbar ∩ ball (xα : ℂ) ε) (negInv '' (land c '' closure S)) := by
      intro w' hw'
      obtain ⟨u', hu', hgu', -, -⟩ := key w' hw'
      simp only [hgu']
      exact hmemE u' hu'
    have h2 : ContinuousWithinAt (fun w => Gc (negInv (g w))) (Hbar ∩ ball (xα : ℂ) ε) w :=
      ContinuousWithinAt.comp (f := fun w => negInv (g w)) (hGcc _ (hmaps hw)) h1 hmaps
    refine (WangWu.continuousAt_negInv ?_).comp_continuousWithinAt h2
    simp only [hgu]
    exact hφc0 u hu
  · -- real on the diameter
    intro w hw hw0
    obtain ⟨u, hu, hgu, -, hu0⟩ := key w ⟨show (0 : ℝ) ≤ w.im by rw [hw0], hw⟩
    refine PocketJordan.im_negInv_eq_zero ?_
    rw [hgu]
    exact hGcR _ (hmemE u hu) (hbot u hu.2 (hu0 hw0))
  · -- into `ℍ`
    intro w hw
    rw [heq hw]
    exact WangWu.negInv_mem_H (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs₀ (by
      obtain ⟨u, hu, hgu, huH, -⟩ := key w ⟨QuantumZipper.H_subset_Hbar hw.1, hw.2⟩
      rw [hgu]; exact hDs u ⟨huH hw.1, hu.2⟩))
  · -- injective
    intro w hw w' hw' he
    obtain ⟨u, hu, hgu, -, -⟩ := key w ⟨QuantumZipper.H_subset_Hbar hw.1, hw.2⟩
    obtain ⟨u', hu', hgu', -, -⟩ := key w' ⟨QuantumZipper.H_subset_Hbar hw'.1, hw'.2⟩
    have h1 : Gc (negInv (g w)) = Gc (negInv (g w')) := by
      have := congrArg negInv he
      simpa only [WangWu.negInv_negInv] using this
    rw [hgu, hgu'] at h1
    have h2 := hGci (hmemE u hu) (hmemE u' hu') h1
    have h3 : g w = g w' := by
      rw [hgu, hgu', ← WangWu.negInv_negInv (land c u), h2, WangWu.negInv_negInv]
    exact YuanSimpleApprox.trMap_injOn hXtr hd hd0 le_rfl hq' hw.1 hw'.1 h3
  · obtain ⟨u, hu, hgu, huH, -⟩ := key w hw
    exact ⟨u, hu, hgu, huH⟩

end Transition

/-! ### (BR) at a rational witness -/

section Branch

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β A : ℝ → ℂ} {τ σ : ℝ} {P : Set ℂ} {X : ℝ≥0 → ℂ}
  {Wu : Set ℂ} {lo hi : ℝ} {c : Chart} {κ : ℂ → ℂ} {f : ℝ → ℝ} {ε : ℝ}

/-- **(BR) at a rational witness** (see the module docstring): along the chart approach at the arc value `f(v₁)`, the
branch `Im(L_Ψ − L_f)` of the counterflow chart at `s₀` and the own chart of the wall `X` at `q′` tends to `2πk`, for
every own time `q′` after the wall time of `A(v₁)` (`htq`: the wall times near `v₁` stay below `q′`), given the
counterflow limit `y ≠ 0` at `f(v₁)`. -/
theorem exists_branch (hS : IsArcChart C A P X Wu lo hi c κ f ε) {r₀ s₀ a₀ v v₁ v₂ : ℝ}
    (hV : IsArcVisit W η C A r₀ s₀ a₀ v v₂) (hvv₁ : v < v₁) (hv₁v₂ : v₁ < v₂) {d : ℝ → ℝ}
    (hXtr : IsLoewnerTrace d (realPath X))
    (hd : Continuous d) (hd0 : d 0 = 0) (hXa : IsProperArc (realPath X)) (hPX : Disjoint P (range X))
    {y : ℝ} (hy : Tendsto (fun w => fwdMap W s₀ (negInv (c.2.1 w))) (𝓝[H] (f v₁ : ℂ)) (𝓝 (y : ℂ))) (hy0 : y ≠ 0)
    {q' : ℝ} (hq'0 : 0 ≤ q') (htq : ∀ᶠ u in 𝓝 v₁, arcTime (lo + u * (hi - lo)) < q') :
    ∃ k : ℤ, Tendsto (fun z => (Sec5.GlueImg.logDerivPsi W s₀ z - logDerivFwd d q' z).im)
      (map c.2.1 (𝓝[H] (f v₁ : ℂ))) (𝓝 (2 * π * k)) := by
  have hη := hV.trace
  have hW := hV.continuous_W
  have hW0 := hV.W_zero
  have hs₀ : 0 ≤ s₀ := hV.nonneg.trans hV.lt.le
  have ha₀v := hV.a₀_lt
  have ha₀ := hV.pos
  have hv₂1 := hV.lt_one
  obtain ⟨δ, hδ, hband⟩ := exists_band_cf hV hS.hCP hS.hPH hS.hPW hS.hAX hS.conf hS.mapsTo hS.fc hS.lim
  have hI : ∀ u, a₀ ≤ u → u ≤ v₂ → u ∈ Ioo (0 : ℝ) 1 := fun u h1 h2 => ⟨by linarith, by linarith⟩
  -- the arc parameters around `v₁`
  obtain ⟨η₁, hη₁, hη₁t⟩ := Metric.eventually_nhds_iff.1 htq
  set m₁ : ℝ := min (η₁ / 2) ((v₁ - v) / 2) with hm₁
  set m₂ : ℝ := min (η₁ / 2) ((v₂ - v₁) / 2) with hm₂
  have hm₁0 : 0 < m₁ := lt_min (by linarith) (by linarith)
  have hm₂0 : 0 < m₂ := lt_min (by linarith) (by linarith)
  have hm₁a := min_le_left (η₁ / 2) ((v₁ - v) / 2)
  have hm₁b := min_le_right (η₁ / 2) ((v₁ - v) / 2)
  have hm₂a := min_le_left (η₁ / 2) ((v₂ - v₁) / 2)
  have hm₂b := min_le_right (η₁ / 2) ((v₂ - v₁) / 2)
  set p₁ : ℝ := v₁ - m₁ with hp₁
  set p₂ : ℝ := v₁ + m₂ with hp₂
  have hp₁I := hI p₁ (by linarith) (by linarith)
  have hp₂I := hI p₂ (by linarith) (by linarith)
  have hv₁I := hI v₁ (by linarith) (by linarith)
  have hσ₁I := hI a₀ le_rfl (by linarith)
  have hv₂I := hI v₂ (by linarith) le_rfl
  have hIp : ∀ u ∈ Icc p₁ p₂, u ∈ Ioo (0 : ℝ) 1 := fun u hu => hI u (by linarith [hu.1]) (by linarith [hu.2])
  set a' : ℝ := f p₁ ⊓ f p₂ with ha'
  set b' : ℝ := f p₁ ⊔ f p₂ with hb'
  have hfv₁ : f v₁ ∈ Ioo a' b' := by
    have h1 := hS.lt_of_lt hp₁I hv₁I (by linarith)
    have h2 := hS.lt_of_lt hv₁I hp₂I (by linarith)
    rcases hS.sign with he | he <;> rw [he] at h1 h2
    · exact ⟨inf_lt_of_left_lt (by linarith), lt_sup_of_lt_right (by linarith)⟩
    · exact ⟨inf_lt_of_right_lt (by linarith), lt_sup_of_lt_left (by linarith)⟩
  have hab' : a' < b' := hfv₁.1.trans hfv₁.2
  have hsub : Icc a' b' ⊆ uIcc (f a₀) (f v₂) :=
    Set.uIcc_subset_uIcc (hS.mem_uIcc hσ₁I hv₂I (by linarith) (by linarith))
      (hS.mem_uIcc hσ₁I hv₂I (by linarith) (by linarith))
  have hbot : ∀ q ∈ Icc a' b', ∃ u ∈ Icc p₁ p₂, f u = q := by
    intro q hq
    have hpp : p₁ ≤ p₂ := by linarith
    obtain ⟨u, hu, hfu⟩ := intermediate_value_uIcc (a := p₁) (b := p₂) (f := f)
      (hS.fc.mono (by rw [uIcc_of_le hpp]; exact hIp)) hq
    rw [uIcc_of_le hpp] at hu
    exact ⟨u, hu, hfu⟩
  have hband' : ∀ w ∈ H, w.re ∈ Icc (f a₀ ⊓ f v₂) (f a₀ ⊔ f v₂) → w.im < δ →
      c.2.1 w ∈ H \ (negInv '' fwdHull W s₀ ∪ Wu) := hband
  -- the counterflow chart at `s₀` and the own chart at `q′` on the rectangle
  have hvisc : ∀ q : ℝ, q ∈ Icc a' b' → negInv (land c q) ∉ H \ fwdHull W s₀ := by
    intro q hq
    obtain ⟨u, hu, rfl⟩ := hbot q hq
    rw [hS.negInv_land (hIp u hu)]
    exact Sec6.notMem_domain_of_mem_trace hη hs₀ (hV.vis_s u ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  have hrect0 : 0 < a' ∨ b' < 0 := hS.rect_base hp₁I hp₂I
  have hl0 : ∀ q ∈ closure (rect a' b' (δ / 2)), land c q ≠ 0 := fun q hq =>
    hS.land0 q (closure_rect_subset.trans crect_subset_Hbar hq) (ne_zero_of_mem_closure_rect hrect0 hq)
  obtain ⟨Gc, hGcc, hGci, -, -, hGcD, hGcR, hDsc, hRBCc⟩ := exists_ext_rect (δ' := δ / 2) hη hW hW0 hs₀ le_rfl
    hS.conf hS.landC hS.landH hS.read hS.readC hl0 hband' (hsub ⟨le_rfl, hab'.le⟩).1
    (hsub ⟨hab'.le, le_rfl⟩).2 (by linarith) hvisc
  have hvisX : ∀ q : ℝ, q ∈ Icc a' b' → land c q ∈ realPath X '' Icc 0 q' := by
    intro q hq
    obtain ⟨u, hu, rfl⟩ := hbot q hq
    have hl : land c (f u) = X (arcTime (lo + u * (hi - lo))).toNNReal := by
      rw [land, extendFrom_eq (by rw [closure_H]; exact IsArcChart.ofReal_mem_Hbar _) (hS.lim u (hIp u hu))]
    have ht : arcTime (lo + u * (hi - lo)) < q' :=
      hη₁t (show dist u v₁ < η₁ by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2])
    refine ⟨((arcTime (lo + u * (hi - lo))).toNNReal : ℝ), ⟨NNReal.coe_nonneg _, ?_⟩, ?_⟩
    · rcases le_total (arcTime (lo + u * (hi - lo))) 0 with h0 | h0
      · rw [Real.toNNReal_of_nonpos h0, NNReal.coe_zero]; exact hq'0
      · rw [Real.coe_toNNReal _ h0]; exact ht.le
    · simp only [realPath, Real.toNNReal_coe, hl]
  obtain ⟨Gα, -, -, hGαF, hGαD, hDα, hRBCα⟩ := exists_own_ext (δ := δ / 2) hXtr hd hd0 hXa hq'0 hS.conf hS.mapsTo
    hPX hS.landC hS.landH hS.read hS.readC hvisX
  set S := rect a' b' (δ / 2) with hSdef
  -- radii
  set ρ₀ : ℝ := min (min (f v₁ - a') (b' - f v₁)) (δ / 2) with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_min (lt_min (by linarith [hfv₁.1]) (by linarith [hfv₁.2])) (by linarith)
  have hρ₀a : ρ₀ ≤ f v₁ - a' := (min_le_left _ _).trans (min_le_left _ _)
  have hρ₀b : ρ₀ ≤ b' - f v₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hρ₀δ : ρ₀ ≤ δ / 2 := min_le_right _ _
  have hRc := hRBCc (f v₁) ρ₀ hρ₀a hρ₀b hρ₀δ
  have hξ0 : ((f v₁ : ℝ) : ℂ) ∈ Hbar ∩ ball (f v₁ : ℂ) ρ₀ := ⟨IsArcChart.ofReal_mem_Hbar _, mem_ball_self hρ₀⟩
  -- the counterflow value at `f(v₁)` is `y`
  have hHB₀ : H ∩ ball (f v₁ : ℂ) ρ₀ ∈ 𝓝[H] (f v₁ : ℂ) :=
    inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hρ₀))
  have hHρ₀ : H ∩ ball (f v₁ : ℂ) ρ₀ ⊆ S := (ball_subset_rect hρ₀a hρ₀b hρ₀δ).1
  have hφy : Gc (negInv (land c (f v₁))) = (y : ℂ) := by
    have hNe : (𝓝[H] (f v₁ : ℂ)).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact IsArcChart.ofReal_mem_Hbar _)
    have h1 := ((hRc.2.1 _ hξ0).tendsto).mono_left (nhdsWithin_le_of_mem (s := Hbar ∩ ball (f v₁ : ℂ) ρ₀)
      (mem_of_superset hHB₀ fun w hw => ⟨QuantumZipper.H_subset_Hbar hw.1, hw.2⟩))
    refine tendsto_nhds_unique h1 (hy.congr' ?_)
    filter_upwards [hHB₀] with w hw
    have hwS : w ∈ closure S := subset_closure (hHρ₀ hw)
    rw [hS.landH w hw.1, ← hGcD _ ⟨land c w, ⟨w, hwS, rfl⟩, by rw [hS.landH w hw.1]⟩
      (by rw [← hS.landH w hw.1]; exact hDsc w hwS hw.1)]
  -- the counterflow value does not vanish near `f(v₁)`
  obtain ⟨ρc, hρc, hρcy⟩ := Metric.continuousWithinAt_iff.1 (hRc.2.1 _ hξ0) |y| (abs_pos.2 hy0)
  set ρ : ℝ := min ρ₀ ρc with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ hρc
  have hρρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hball : Hbar ∩ ball (f v₁ : ℂ) ρ ⊆ closure S :=
    (ball_subset_rect (hρρ₀.trans hρ₀a) (hρρ₀.trans hρ₀b) (hρρ₀.trans hρ₀δ)).2
  have hHρ : H ∩ ball (f v₁ : ℂ) ρ ⊆ S :=
    (ball_subset_rect (hρρ₀.trans hρ₀a) (hρρ₀.trans hρ₀b) (hρρ₀.trans hρ₀δ)).1
  have hφc0 : ∀ u ∈ Hbar ∩ ball (f v₁ : ℂ) ρ, Gc (negInv (land c u)) ≠ 0 := by
    intro u hu h0
    have hu₀ : u ∈ Hbar ∩ ball (f v₁ : ℂ) ρ₀ := ⟨hu.1, ball_subset_ball hρρ₀ hu.2⟩
    have := hρcy hu₀ (lt_of_lt_of_le (mem_ball.1 hu.2) (min_le_right _ _))
    simp only [h0, hφy, dist_zero_left, Complex.norm_real, Real.norm_eq_abs] at this
    exact lt_irrefl _ this
  have hRα := hRBCα (f v₁) ρ (hρρ₀.trans hρ₀a) (hρρ₀.trans hρ₀b) (hρρ₀.trans hρ₀δ)
  -- the transition
  obtain ⟨εt, hεt, hψ, hψeq, hkey⟩ := isRBC_transition (S := S) (Gc := Gc) (Gα := Gα) hW hs₀ hXtr hd hd0 hq'0 hρ
    (fun q hq => hl0 q (hball hq)) hball hGcc hGci hGcD hGcR
    (fun u hu => hDsc u (hball ⟨QuantumZipper.H_subset_Hbar hu.1, hu.2⟩) hu.1)
    (fun u hu hu0 => by
      have hu' : u ∈ closure S := hball ⟨show (0 : ℝ) ≤ u.im by rw [hu0], hu⟩
      have hqc := closure_rect_subset hu'
      have hqr : u = ((u.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hu0])
      rw [hqr]
      exact hvisc u.re hqc.2.2)
    hφc0 hRα (fun u hu => hGαF _ ⟨u, hball hu, rfl⟩)
  set xα : ℝ := (Gα (land c (f v₁))).re with hxα
  have hxreal : Gα (land c (f v₁)) = (xα : ℂ) :=
    Complex.ext (by simp [hxα]) (by simp [hRα.2.2.1 _ (mem_ball_self hρ) (by simp)])
  -- the domain of both coordinates
  set D : Set ℂ := (H \ fwdHull d q') ∩ (H \ negInv '' fwdHull W s₀) with hDdef
  have hDo : IsOpen D := (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hd hq'0).inter
    (Sec5.GlueImg.isOpen_H_diff_negInv_fwdHull hW hs₀)
  have hlandD : ∀ u ∈ H ∩ ball (f v₁ : ℂ) ρ, land c u ∈ D := by
    intro u hu
    have huS : u ∈ closure S := subset_closure (hHρ hu)
    have h2 := hDsc u huS hu.1
    refine ⟨hDα u huS hu.1, (hDα u huS hu.1).1, fun hK => h2.2 ?_⟩
    rw [mem_negInv_image] at hK
    exact hK
  have hLf := (isDerivLog_fwdMap hd hq'0).mono (inter_subset_left (s := H \ fwdHull d q')
    (t := H \ negInv '' fwdHull W s₀))
  have hLc := (Sec5.GlueImg.isDerivLog_revChart hW hs₀).mono (inter_subset_right (s := H \ fwdHull d q')
    (t := H \ negInv '' fwdHull W s₀))
  have hHB : H ∩ ball (f v₁ : ℂ) ρ ∈ 𝓝[H] (f v₁ : ℂ) :=
    inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hρ))
  refine exists_int_tendsto_im_sub_of_transition' (x := xα) (ρ := εt) (g := trMap d 0 q') hDo hLf hLc hεt
    ?_ ?_ ?_ ?_ hψ hψeq ?_ ?_
  · intro w hw
    obtain ⟨u, hu, hgu, huH⟩ := hkey w ⟨QuantumZipper.H_subset_Hbar hw.1, hw.2⟩
    rw [hgu]
    exact hlandD u ⟨huH hw.1, hu.2⟩
  · exact (YuanSimpleApprox.trMap_continuousOn hXtr hd hd0 le_rfl hq'0).mono fun w hw =>
      QuantumZipper.H_subset_Hbar hw.1
  · intro w hw
    rw [YuanSimpleApprox.trMap_eq_fwdMapInv hd hq'0 hw.1, YuanSimpleApprox.shiftDrive_zero_eq hd0, sub_zero,
      QuantumZipper.RS.fwdMap_fwdMapInv hd hd0 hq'0 hw.1]
  · intro z hz _
    rw [YuanSimpleApprox.trMap_eq_fwdMapInv hd hq'0 (QuantumZipper.FwdHolo.mapsTo_fwdMap hd hq'0 hz.1),
      YuanSimpleApprox.shiftDrive_zero_eq hd0, sub_zero, QuantumZipper.RS.fwdMapInv_fwdMap hd hd0 hq'0 hz.1]
  · -- the own chart along the approach
    rw [tendsto_map'_iff]
    have h1 := ((hRα.2.1 _ ⟨IsArcChart.ofReal_mem_Hbar _, mem_ball_self hρ⟩).tendsto).mono_left
      (nhdsWithin_le_of_mem (s := Hbar ∩ ball (f v₁ : ℂ) ρ)
        (mem_of_superset hHB fun w hw => ⟨QuantumZipper.H_subset_Hbar hw.1, hw.2⟩))
    rw [hxreal] at h1
    refine tendsto_nhdsWithin_iff.2 ⟨h1.congr' ?_, ?_⟩
    · filter_upwards [hHB] with w hw
      have hwS : w ∈ closure S := subset_closure (hHρ hw)
      simp only [Function.comp_apply]
      rw [hGαD _ ⟨w, hwS, rfl⟩ (hDα w hwS hw.1), hS.landH w hw.1]
    · filter_upwards [hHB] with w hw
      have := (hlandD w hw).1
      rw [hS.landH w hw.1] at this
      exact QuantumZipper.FwdHolo.mapsTo_fwdMap hd hq'0 this
  · rw [Filter.eventually_map]
    filter_upwards [hHB] with w hw
    rw [← hS.landH w hw.1]
    exact hlandD w hw

end Branch

end InteractingSLE.Sec7.Aux37Side
