/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GlueCondUnionImgInf

/-!
# G3 (ii), Proposition 4.9 direction: the counterflow-side boundary limits in the counterflow chart

Packet PROVE-GLUECOND6. In the counterflow chart `Ψ = revChart w s` of `ℍ ∖ G` (`G = R(K′_s)`), every real point
`ζ₀ ≠ 0` of the chart is a prime end of `ℍ ∖ G` at a point of `G`, of the physical real line, or at physical `∞`
(the counterflow's start, possibly with infinitely many prime ends when the counterflow returns to its start). This file
transports the comparison "union mean − counterflow mean → 0" (PROVE-GLUECOND2's `ae_union_mean_cfGlue` at finite
points, `ae_tendsto_union_sub_cfMean_cobounded` at `∞`) and the identity of `cfMeanQ_add_eq_retMean` into the chart:

* **`tendsto_add_argPsi_sub_of_real`** (deterministic): if `M − m_G → 0` at every point of `G ∪ ℝ` away from the flow
  hull `A` and at `∞` (within `ℍ ∖ (A ∪ G)`), and `m_G + χ arg_Ψ = V ∘ Ψ` on `ℍ ∖ G`, then at every real `ζ₀ ≠ 0`
  of the chart, `M ∘ Ψ⁻¹ + χ arg_Ψ ∘ Ψ⁻¹ − V → 0`. The flow hull `A` only needs to be bounded with closure in `A ∪ {0}`
  (the simple flow prefix): `Ψ⁻¹(ζ)` then converges to a point of `G ∪ ℝ ∖ {0}` off `closure A`, or to `∞`.

No finiteness of the prime ends at physical `∞` is needed: the exceptional set of the chart identification on the
counterflow side is `{0}` (and the chart point `∞`, the counterflow tip).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal Real

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)

namespace InteractingSLE.Sec5.GlueImg

open WangWu hiding ratPt exists_ratPt_dist_lt

variable {w : ℝ → ℝ} {s : ℝ}

/-- A boundary value of the inverse Loewner map at a real point is not in `ℍ ∖ K_s`. -/
theorem boundary_value_notMem (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) {x : ℝ} {p : ℂ}
    (hp : Tendsto (fwdMapInv w s) (𝓝[H] (x : ℂ)) (𝓝 p)) : p ∉ H \ fwdHull w s := by
  intro hpH
  have hO : IsOpen (H \ fwdHull w s) := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw hs
  have hfc : ContinuousAt (fwdMap w s) p :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hw hs).continuousOn.continuousAt (hO.mem_nhds hpH)
  have h1 : Tendsto (fun y => fwdMap w s (fwdMapInv w s y)) (𝓝[H] (x : ℂ)) (𝓝 (fwdMap w s p)) :=
    hfc.tendsto.comp hp
  have h2 : Tendsto (fun y => fwdMap w s (fwdMapInv w s y)) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) := by
    refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (QuantumZipper.RS.fwdMap_fwdMapInv hw hw0 hs hy).symm
  have hne : (𝓝[H] (x : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]
    show (0 : ℝ) ≤ (x : ℂ).im
    simp
  have heq := tendsto_nhds_unique h1 h2
  have him := QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs hpH
  rw [heq] at him
  have : (0 : ℝ) < (x : ℂ).im := him
  simp at this

/-- **The counterflow-side limits in the counterflow chart** (deterministic). Let `A ⊆ ℍ` be bounded with
`closure A ⊆ A ∪ {0}` and disjoint from `G = R(K_s)`, `C = ℍ ∖ (A ∪ G)`. If `M − m_G → 0` at every point of
`G ∪ ℝ` near which `A ⊆ G` and at `∞` within `C`, and `m_G + χ arg_Ψ = V ∘ Ψ` on `ℍ ∖ G`, then at every real
`ζ₀ ≠ 0` of the chart `Ψ`, `M ∘ Ψ⁻¹ + χ arg_Ψ ∘ Ψ⁻¹ − V → 0`. -/
theorem tendsto_add_argPsi_sub_of_real (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (hB : HasBdryLimits (fwdMapInv w s)) {A : Set ℂ} (hAb : Bornology.IsBounded A)
    (hAcl : ∀ z ∈ closure A, z ∈ A ∨ z = 0) (hAG : Disjoint A (negInv '' fwdHull w s)) (hAH : A ⊆ H)
    {M mG V : ℂ → ℝ} {χ : ℝ}
    (hG : ∀ z₀ ∈ negInv '' fwdHull w s ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A ∩ ball z₀ r ⊆ negInv '' fwdHull w s) →
      Tendsto (fun z => M z - mG z) (𝓝[H \ (A ∪ negInv '' fwdHull w s)] z₀) (𝓝 0))
    (hInf : Tendsto (fun z => M z - mG z) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (A ∪ negInv '' fwdHull w s))) (𝓝 0))
    (hId : ∀ z ∈ H \ negInv '' fwdHull w s, mG z + χ * (logDerivPsi w s z).im = V (revChart w s z))
    {ζ₀ : ℝ} (hζ₀ : ζ₀ ≠ 0) :
    Tendsto (fun ζ => M (revChartInv w s ζ) + χ * (logDerivPsi w s (revChartInv w s ζ)).im - V ζ)
      (𝓝[H] (ζ₀ : ℂ)) (𝓝 0) := by
  set K := fwdHull w s with hKdef
  set G := negInv '' K with hGdef
  set C := H \ (A ∪ G) with hCdef
  -- the boundary value of `F_s` at `R ζ₀`
  have hx : ((-ζ₀⁻¹ : ℝ) : ℂ) ∈ Hbar := by show (0 : ℝ) ≤ ((-ζ₀⁻¹ : ℝ) : ℂ).im; simp
  obtain ⟨p, hp⟩ := hB _ hx
  have hF : Tendsto (fun ζ => fwdMapInv w s (negInv ζ)) (𝓝[H] (ζ₀ : ℂ)) (𝓝 p) :=
    hp.comp (tendsto_negInv_nhdsWithin_H hζ₀)
  have hpK : p ∉ H \ K := boundary_value_notMem hw hw0 hs hp
  -- `Ψ⁻¹` maps into `ℍ ∖ G`, and the identity there
  have hmemG : ∀ ζ ∈ H, revChartInv w s ζ ∈ H \ G := fun ζ hζ => revChartInv_mem hw hw0 hs hζ
  have hkey : ∀ ζ ∈ H, M (revChartInv w s ζ) + χ * (logDerivPsi w s (revChartInv w s ζ)).im - V ζ =
      M (revChartInv w s ζ) - mG (revChartInv w s ζ) := by
    intro ζ hζ
    have h := hId _ (hmemG ζ hζ)
    rw [revChart_revChartInv hw hw0 hs hζ] at h
    linarith
  have hcongr : ∀ {l : Filter ℂ}, Tendsto (fun z => M z - mG z) l (𝓝 0) →
      Tendsto (revChartInv w s) (𝓝[H] (ζ₀ : ℂ)) l →
      Tendsto (fun ζ => M (revChartInv w s ζ) + χ * (logDerivPsi w s (revChartInv w s ζ)).im - V ζ)
        (𝓝[H] (ζ₀ : ℂ)) (𝓝 0) := fun h1 h2 => by
    refine (h1.comp h2).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ζ hζ
    exact (hkey ζ hζ).symm
  by_cases hp0 : p = 0
  · -- `Ψ⁻¹ ζ → ∞`
    refine hcongr hInf (tendsto_inf.2 ⟨?_, tendsto_principal.2 ?_⟩)
    · rw [← tendsto_norm_atTop_iff_cobounded]
      have hn : Tendsto (fun ζ => ‖fwdMapInv w s (negInv ζ)‖) (𝓝[H] (ζ₀ : ℂ)) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have := hF.norm
          rwa [hp0, norm_zero] at this
        · filter_upwards [self_mem_nhdsWithin] with ζ hζ
          have hm := (hmemG ζ hζ).1
          have hm' : fwdMapInv w s (negInv ζ) ∈ H :=
            QuantumZipper.RS.fwdMapInv_mem_H hw hw0 hs (negInv_mem_H hζ)
          exact norm_pos_iff.2 (ne_zero_of_mem_H hm')
      refine (tendsto_inv_nhdsGT_zero.comp hn).congr fun ζ => ?_
      simp only [Function.comp_apply, revChartInv, norm_negInv]
    · have hev : ∀ᶠ ζ in 𝓝[H] (ζ₀ : ℂ), revChartInv w s ζ ∉ A := by
        obtain ⟨R, hR⟩ := hAb.subset_closedBall 0
        have hn : Tendsto (fun ζ => ‖revChartInv w s ζ‖) (𝓝[H] (ζ₀ : ℂ)) atTop := by
          have hn' : Tendsto (fun ζ => ‖fwdMapInv w s (negInv ζ)‖) (𝓝[H] (ζ₀ : ℂ)) (𝓝[>] 0) := by
            refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
            · have := hF.norm
              rwa [hp0, norm_zero] at this
            · filter_upwards [self_mem_nhdsWithin] with ζ hζ
              exact norm_pos_iff.2 (ne_zero_of_mem_H
                (QuantumZipper.RS.fwdMapInv_mem_H hw hw0 hs (negInv_mem_H hζ)))
          refine (tendsto_inv_nhdsGT_zero.comp hn').congr fun ζ => ?_
          simp only [Function.comp_apply, revChartInv, norm_negInv]
        filter_upwards [hn.eventually_gt_atTop R] with ζ hζ hA
        have := hR hA
        rw [mem_closedBall, dist_zero_right] at this
        linarith
      filter_upwards [hev, self_mem_nhdsWithin] with ζ h1 h2
      exact ⟨(hmemG ζ h2).1, fun h => h.elim h1 (hmemG ζ h2).2⟩
  · -- `Ψ⁻¹ ζ → R p`, a point of `G ∪ ℝ ∖ {0}` off `closure A`
    set z₀ := negInv p with hz₀def
    have hΨ : Tendsto (revChartInv w s) (𝓝[H] (ζ₀ : ℂ)) (𝓝 z₀) :=
      ((continuousAt_negInv hp0).tendsto.comp hF).congr fun ζ => rfl
    have hz₀0 : z₀ ≠ 0 := by
      intro h
      have := congrArg negInv h
      rw [hz₀def, WangWu.negInv_negInv] at this
      exact hp0 (by rw [this]; simp [negInv])
    -- `p ∈ K` or `p` is real
    have hne : (𝓝[H] (ζ₀ : ℂ)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]
      show (0 : ℝ) ≤ (ζ₀ : ℂ).im
      simp
    have hpHbar : p ∈ Hbar := by
      rw [← closure_H]
      exact mem_closure_of_tendsto hF (eventually_nhdsWithin_of_forall fun ζ hζ =>
        QuantumZipper.RS.fwdMapInv_mem_H hw hw0 hs (negInv_mem_H hζ))
    have hz₀mem : z₀ ∈ G ∪ {z : ℂ | z.im = 0} := by
      rcases (show (0 : ℝ) ≤ p.im from hpHbar).lt_or_eq with hpos | hzero
      · have hpK' : p ∈ K := by
          by_contra hn
          exact hpK ⟨hpos, hn⟩
        exact Or.inl ⟨p, hpK', rfl⟩
      · right
        show (negInv p).im = 0
        have e : p = ((p.re : ℝ) : ℂ) := Complex.ext rfl (by simp [← hzero])
        rw [e]
        simp [negInv, ← ofReal_inv]
    have hz₀A : z₀ ∉ closure A := by
      intro hc
      rcases hAcl z₀ hc with hA | h0
      · rcases hz₀mem with hG' | hR
        · exact Set.disjoint_left.1 hAG hA hG'
        · have := hAH hA
          have h' : (0 : ℝ) < z₀.im := this
          rw [show z₀.im = 0 from hR] at h'
          exact lt_irrefl _ h'
      · exact hz₀0 h0
    obtain ⟨r, hr, hrA⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl z₀ hz₀A
    have hloc : ∃ r > 0, A ∩ ball z₀ r ⊆ G :=
      ⟨r, hr, fun z hz => absurd (subset_closure hz.1) (hrA hz.2)⟩
    refine hcongr (hG z₀ hz₀mem hloc) (tendsto_nhdsWithin_iff.2 ⟨hΨ, ?_⟩)
    have hev : ∀ᶠ ζ in 𝓝[H] (ζ₀ : ℂ), revChartInv w s ζ ∈ ball z₀ r := hΨ.eventually (ball_mem_nhds _ hr)
    filter_upwards [hev, self_mem_nhdsWithin] with ζ h1 h2
    refine ⟨(hmemG ζ h2).1, fun h => h.elim (fun hA => hrA h1 (subset_closure hA)) (hmemG ζ h2).2⟩

/-- **The frozen coupling mean at an untouched real point**: for a Loewner chain `W` (continuous, `W 0 = 0`), a real
`x` with a ball off `K_T`, and a bounded harmonic extension `u` of data `d`, `couplingMean κ W T u z → d(g_T(x) − W_T)`
as `z → x` in `ℍ`, provided the image point is not exceptional for `u` (the derivative term vanishes there, Aux. 57). -/
theorem tendsto_couplingMean_of_real {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) {x ρ : ℝ}
    (hρ : 0 < ρ) (hd : Disjoint (ball (x : ℂ) ρ) (fwdHull W T)) (κ : ℝ) {d : ℝ → ℝ} {S : Set ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension d S u)
    (hxS : (ConformalImageFull.bdryVal W x T - W T).re ∉ S) :
    Tendsto (couplingMean κ W T u) (𝓝[H] (x : ℂ))
      (𝓝 (d (ConformalImageFull.bdryVal W x T - W T).re)) := by
  set L : ℂ := ConformalImageFull.bdryVal W x T - W T with hLdef
  obtain ⟨him, hlim⟩ := ConformalImageFull.bdryVal_spec hW hW0 hT hρ hd
  have hLre : ((L.re : ℝ) : ℂ) = L := Complex.ext rfl (by simp [hLdef, him])
  have hf : Tendsto (fwdMap W T) (𝓝[H] (x : ℂ)) (𝓝 L) :=
    (hlim.sub_const (W T : ℂ)).congr fun z => by simp only [ConformalImage.gmap, add_sub_cancel_right]
  have hev : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H \ fwdHull W T := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (x : ℂ) hρ), self_mem_nhdsWithin] with z hz hzH
    exact ⟨hzH, fun hK => Set.disjoint_left.1 hd hz hK⟩
  have hfH : Tendsto (fwdMap W T) (𝓝[H] (x : ℂ)) (𝓝[H] ((L.re : ℝ) : ℂ)) := by
    rw [hLre]
    exact tendsto_nhdsWithin_iff.2 ⟨hf, hev.mono fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hW hT hz⟩
  have h1 := (hu.2.2 L.re hxS).comp hfH
  have h2 := Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero (isHPHull_fwdHull hW hT)
    (Sec7.SideHeight.isCanonicalDerivLog_fwdMap hW hW0 hT) (isMapOut_fwdMap hW hW0 hT) hρ hd
  have h := h1.sub (h2.const_mul (chiC κ))
  rw [mul_zero, sub_zero] at h
  exact h.congr fun z => rfl

end InteractingSLE.Sec5.GlueImg
