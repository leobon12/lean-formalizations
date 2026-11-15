/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ReverseArcMain
import InteractingSLE.Spec.Supplement.G7ClockGeom
import InteractingSLE.Spec.Supplement.G7RetainedMeas
import InteractingSLE.Spec.Supplement.RLCBGerm
import InteractingSLE.Foundations.Loewner.CapacityEstimates

/-!
# (III-a): the later-line chart is the stop-line chart followed by the continuation's Loewner map

Packet PROVE-RETAUX79 (PROVE-DOMAINMARKOV8 §2, (III-a)). Let `K ⊆ P` be compact sets with filled hulls
`A = fill K ⊆ B = fill P`, and let `φ₀ = g_A − x₀`, `φ₁ = g_B − x₁` be hydrodynamic charts of `ℍ \ A`, `ℍ \ B`
(`g` the mapping-out functions, `x₀, x₁` real) with inverses `ψ₀`, `ψ₁` (`Supp7.IsDomChart`). Suppose `P` is `K`
plus the `ψ₀`-image of a simple generating trace `γ` of a continuous driver `W` up to capacity time `Q > 0` (the
continuation's chart path read in its own capacity clock), and that `ψ₀(γ(Q)) = ψ₁(0)` is the only `ψ₁`-preimage of
the tip. Then

* `ψ₁ = ψ₀ ∘ f_Q⁻¹` on `ℍ` (`f_Q = fwdMap W Q`, the centred Loewner map), and
* `Im L_B ∘ ψ₁ = Im log f_Q′ ∘ f_Q⁻¹ + Im L_A ∘ ψ₀ ∘ f_Q⁻¹` on `ℍ` for the canonical logarithms
  `L = canonDerivLog` (the lift `lift = Im L` of `Supp7.RetData`).

These are the hypotheses `hinv`, `hlift` of `RetAux79.chartTransport_eq_integral_couplingMean_of_trans`.

Proof: `φ₀(B \ A) = fill γ([0, Q])` (`IsDomChart.fwd_image_fillH_diff_eq`), so `g_A(B \ A)` is the hull of the trace
`γ + x₀`, mapped out by `z ↦ f_Q(z − x₀) + κ` with canonical logarithm `log f_Q′(· − x₀)`
(`ReverseArc.exists_physChart`). The composition rule (`IsMapOut.comp`, `IsCanonicalDerivLog.comp`) and uniqueness
give `φ₁ = f_Q ∘ φ₀ + c`, `c = κ − x₁` real, and the chain rule for the logarithms. The constant vanishes: on `ℍ`,
`ψ₁(w) = ψ₀(f_Q⁻¹(w − c))`, and letting `w → c` the continuous extension of `f_Q⁻¹` (`ReverseArc.isChart`) gives
`ψ₁(c) = ψ₀(γ(Q)) = ψ₁(0)`, so `c = 0` by the uniqueness of the tip's preimage.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv logDerivFwd)

namespace InteractingSLE

namespace Restart.RetAux79

open Sec7 Supp7

variable {K P : Set ℂ} {x₀ x₁ : ℝ} {ψ₀ ψ₁ : ℂ → ℂ} {γ : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ} {ζc : ℝ≥0∞} {Q : ℝ≥0}

/-- **(III-a), deterministic.** See the module docstring. -/
theorem chartComp_of_trace (hP : IsCompact P) (hAh : IsHPHull (fillH K)) (hBh : IsHPHull (fillH P))
    (hKP : fillH K ⊆ fillH P)
    (hD₀ : IsDomChart K (fun z => ConformalImage.mapOut (fillH K) z - x₀) ψ₀)
    (hD₁ : IsDomChart P (fun z => ConformalImage.mapOut (fillH P) z - x₁) ψ₁)
    (hg : IsGeneratingTrace W ζc γ) (hWc : Continuous W) (hW0 : W 0 = 0)
    (hinj : InjOn γ {s | (s : ℝ≥0∞) ≤ ζc}) (hQ : (Q : ℝ≥0∞) < ζc) (hQ0 : 0 < Q)
    (hPK : P ⊆ K ∪ ψ₀ '' (γ '' Icc 0 Q)) (hγP : ∀ s ∈ Icc 0 Q, ψ₀ (γ s) ∈ P)
    (htip : ψ₀ (γ Q) = ψ₁ 0) (huniq : ∀ w ∈ Hbar, ψ₁ w = ψ₁ 0 → w = 0) :
    (∀ w ∈ H, ψ₁ w = ψ₀ (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) ∧
    ∀ w ∈ H, (canonDerivLog (fillH P) (ψ₁ w)).im =
      (logDerivFwd (fun s : ℝ => W s.toNNReal) Q (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)).im +
        (canonDerivLog (fillH K) (ψ₀ (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w))).im := by
  set w' : ℝ → ℝ := fun s => W s.toNNReal with hw'
  have hw'c : Continuous w' := hWc.comp continuous_real_toNNReal
  have hw'0 : w' 0 = 0 := by simp [hw', hW0]
  have hQr : (0 : ℝ) ≤ Q := Q.coe_nonneg
  set g₀ := ConformalImage.mapOut (fillH K) with hg₀def
  set g₁ := ConformalImage.mapOut (fillH P) with hg₁def
  set f := fwdMap w' Q with hfdef
  -- the image of the new part of the hull
  have hγc : ContinuousOn γ (Icc 0 Q) :=
    hg.2.1.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans hQ.le
  have hC := hD₀.fwd_image_fillH_diff_eq hP hKP hPK hγc hγP
  set α : ℝ≥0 → ℂ := fun s => γ s + x₀ with hαdef
  have hαx : (fun s => α s - x₀) = γ := funext fun s => by simp [hαdef]
  have hgα : IsGeneratingTrace W ζc (fun s => α s - x₀) := by rw [hαx]; exact hg
  obtain ⟨κ, -, hgC, hLC⟩ := ReverseArc.exists_physChart hgα hWc.continuousOn hW0 hQ
  have hCeq : g₀ '' (fillH P \ fillH K) = fillH (α '' Icc 0 Q) := by
    rw [ReverseArc.fillH_image_eq (α := α) x₀ Q, hαx, ← hC, image_image]
    exact image_congr fun z _ => by ring
  -- the composition rule and uniqueness
  have hg₀ : IsMapOut (fillH K) g₀ := ConformalImage.isMapOut_mapOut hAh
  have hg₁ : IsMapOut (fillH P) g₁ := ConformalImage.isMapOut_mapOut hBh
  set gC : ℂ → ℂ := fun z => f (z - x₀) + κ with hgCdef
  have hgC' : IsMapOut (g₀ '' (fillH P \ fillH K)) gC := by rw [hCeq]; exact hgC
  have hcomp : IsMapOut (fillH P) (gC ∘ g₀) := hg₀.comp hAh hBh hKP hgC'
  have heq : EqOn g₁ (gC ∘ g₀) (H \ fillH P) := IsMapOut.eqOn hBh hg₁ hcomp
  -- the chain rule for the canonical logarithms
  have hLA := isCanonicalDerivLog_canonDerivLog hAh
  have hLC' : IsCanonicalDerivLog (g₀ '' (fillH P \ fillH K)) gC (fun z => logDerivFwd w' Q (z - x₀)) := by
    rw [hCeq]; exact hLC
  have hcL := IsCanonicalDerivLog.comp hAh hBh hKP hg₀ hgC' hLA hLC'
  have hLB := (isCanonicalDerivLog_canonDerivLog hBh).congr hBh heq
  have hLeq := IsCanonicalDerivLog.eqOn hLB hcL hBh hcomp
  -- the forward chart identity up to the constant `c`
  set c : ℝ := κ - x₁ with hcdef
  have hφ₁ : ∀ z ∈ H \ fillH P, g₁ z - x₁ = f (g₀ z - x₀) + c := fun z hz => by
    rw [heq hz]
    simp only [Function.comp_apply, hgCdef, hcdef]
    push_cast
    ring
  -- the continuous extension of `f_Q⁻¹`
  have hch := ReverseArc.isChart hg hWc.continuousOn hW0 hinj hQ hQ0
  set Φ := extendFrom H (fwdMapInv w' Q) with hΦdef
  have hΦeq : ∀ v ∈ H, Φ v = fwdMapInv w' Q v := fun v hv =>
    extendFrom_eq (subset_closure hv)
      ((QuantumZipper.RS.continuousAt_fwdMapInv hw'c hw'0 hQr hv).tendsto.mono_left nhdsWithin_le_nhds)
  -- preimages through the composite
  have hpre : ∀ v ∈ H, ψ₀ (fwdMapInv w' Q v) ∈ H \ fillH P ∧
      g₀ (ψ₀ (fwdMapInv w' Q v)) - x₀ = fwdMapInv w' Q v := fun v hv => by
    have hy : fwdMapInv w' Q v ∈ H \ fillH (γ '' Icc 0 Q) := by
      rw [← hΦeq v hv]; exact hch.inv_mem hv
    exact ⟨hD₀.inv_image_subset hP hPK hγc ⟨_, hy, rfl⟩, hD₀.fwd_inv _ hy.1⟩
  have hψ₁c : ∀ w ∈ H, ψ₁ w = ψ₀ (fwdMapInv w' Q (w - c)) := fun w hw => by
    have hv : w - (c : ℂ) ∈ H := Restart.sub_ofReal_mem_H hw c
    obtain ⟨hz, hφz⟩ := hpre _ hv
    have h1 : g₁ (ψ₀ (fwdMapInv w' Q (w - c))) - x₁ = w := by
      rw [hφ₁ _ hz, hφz, hfdef, QuantumZipper.RS.fwdMap_fwdMapInv hw'c hw'0 hQr hv, sub_add_cancel]
    rw [← hD₁.inv_fwd hz]
    exact congrArg ψ₁ h1.symm
  -- the constant vanishes
  have hγQ : γ Q ∈ Hbar := by
    have := hch.inv_mem_Hbar (show (0 : ℂ) ∈ Hbar from show (0 : ℝ) ≤ (0 : ℂ).im by simp)
    rwa [hch.tip] at this
  have hc0 : c = 0 := by
    have hcH : (c : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (c : ℂ).im by simp
    have hNe : (𝓝[H] (c : ℂ)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hcH
    have hlim₁ : Tendsto ψ₁ (𝓝[H] (c : ℂ)) (𝓝 (ψ₁ c)) :=
      ((hD₁.continuousOn_inv _ hcH).mono QuantumZipper.H_subset_Hbar).tendsto
    have h1 : Tendsto (fun w => w - (c : ℂ)) (𝓝[H] (c : ℂ)) (𝓝[H] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun w hw =>
        Restart.sub_ofReal_mem_H hw c⟩
      have h0 : Tendsto (fun w : ℂ => w - (c : ℂ)) (𝓝 (c : ℂ)) (𝓝 ((c : ℂ) - c)) :=
        (continuous_id.sub continuous_const).tendsto _
      rw [sub_self] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto Φ (𝓝[H] 0) (𝓝[Hbar] (γ Q)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun v hv =>
        QuantumZipper.H_subset_Hbar (hch.inv_mem hv).1⟩
      rw [← hch.tip]
      exact ((hch.inv_cont 0 (show (0 : ℝ) ≤ (0 : ℂ).im by simp)).mono QuantumZipper.H_subset_Hbar).tendsto
    have h3 : Tendsto ψ₀ (𝓝[Hbar] (γ Q)) (𝓝 (ψ₀ (γ Q))) := hD₀.continuousOn_inv _ hγQ
    have hlim₂ : Tendsto ψ₁ (𝓝[H] (c : ℂ)) (𝓝 (ψ₀ (γ Q))) := by
      refine (h3.comp (h2.comp h1)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      simp only [Function.comp_apply]
      rw [hψ₁c w hw, hΦeq _ (Restart.sub_ofReal_mem_H hw c)]
    have he : ψ₁ c = ψ₁ 0 := (tendsto_nhds_unique hlim₁ hlim₂).trans htip
    exact_mod_cast huniq _ hcH he
  have hψ₁ : ∀ w ∈ H, ψ₁ w = ψ₀ (fwdMapInv w' Q w) := fun w hw => by
    rw [hψ₁c w hw, hc0, ofReal_zero, sub_zero]
  refine ⟨hψ₁, fun w hw => ?_⟩
  obtain ⟨hz, hφz⟩ := hpre w hw
  rw [hψ₁ w hw, hLeq hz]
  simp only [add_im, hφz]

/-- **(III-a) for the retained charts of `Supp7.RetData`.** Let `d`, `d'` be retained data (the stop line and a later
line) and `ω` a point of both chart events. If the later union `K' = d'.K ω` is the earlier union `K = d.K ω` plus the
`d.inv ω`-image of a simple generating trace `γ` of a continuous driver `W` up to capacity time `Q > 0` (the
continuation's chart path read in its capacity clock), ending at the later tip, then the later chart is the earlier
chart followed by the centred Loewner map `f_Q`: same inverse on `ℍ` and the chain-rule lift. -/
theorem retChart_trans {Ω : Type*} [MeasurableSpace Ω] {d d' : RetData Ω} (hd : d.IsMeasGood)
    (hd' : d'.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) (hω' : ω ∈ d'.E)
    (hg : IsGeneratingTrace W ζc γ) (hWc : Continuous W) (hW0 : W 0 = 0)
    (hinj : InjOn γ {s | (s : ℝ≥0∞) ≤ ζc}) (hQ : (Q : ℝ≥0∞) < ζc) (hQ0 : 0 < Q)
    (hKP : fillH (d.K ω) ⊆ fillH (d'.K ω)) (hPK : d'.K ω ⊆ d.K ω ∪ d.inv ω '' (γ '' Icc 0 Q))
    (hγP : ∀ s ∈ Icc 0 Q, d.inv ω (γ s) ∈ d'.K ω) (htip : d.inv ω (γ Q) = d'.η₂ ω d'.r) :
    (∀ w ∈ H, (d'.chart ω).2.1 w = (d.chart ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) ∧
    ∀ w ∈ H, (d'.chart ω).2.2 ((d'.chart ω).2.1 w) =
      (logDerivFwd (fun s : ℝ => W s.toNNReal) Q (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)).im +
        (d.chart ω).2.2 ((d.chart ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) := by
  obtain ⟨⟨x₀, hx₀⟩, hC₀⟩ := hd.isRetChart hω
  obtain ⟨⟨x₁, hx₁⟩, hC₁⟩ := hd'.isRetChart hω'
  have hω₀ := RetData.E_subset_E₀ hω
  have hω₀' := RetData.E_subset_E₀ hω'
  have hgd := hd.good ω (RetData.E_subset_G hω)
  have hgd' := hd'.good ω (RetData.E_subset_G hω')
  have hK₀ := RetData.K_of_mem hω
  have hK₁ := RetData.K_of_mem hω'
  have hD₀ : IsDomChart (d.K ω) (fun z => ConformalImage.mapOut (fillH (d.K ω)) z - x₀) (d.inv ω) := by
    have h := hC₀.isDomChart hgd.2.2.2.2.2.1 (by rw [← hK₀]; exact (hd.isCompact_K ω).isClosed)
    rw [← hK₀] at h
    have hf : d.fwd ω = fun z => ConformalImage.mapOut (fillH (d.K ω)) z - x₀ := by
      funext z; rw [RetData.fwd, hx₀]; rfl
    rwa [hf] at h
  have hD₁ : IsDomChart (d'.K ω) (fun z => ConformalImage.mapOut (fillH (d'.K ω)) z - x₁) (d'.inv ω) := by
    have h := hC₁.isDomChart hgd'.2.2.2.2.2.1 (by rw [← hK₁]; exact (hd'.isCompact_K ω).isClosed)
    rw [← hK₁] at h
    have hf : d'.fwd ω = fun z => ConformalImage.mapOut (fillH (d'.K ω)) z - x₁ := by
      funext z; rw [RetData.fwd, hx₁]; rfl
    rwa [hf] at h
  have h0 : d'.inv ω 0 = d'.η₂ ω d'.r := hC₁.inv_zero hgd'.2.2.2.2.2.1
  have hreg := RLC.isChartRegularPoint_tip₂ hgd'.1 hgd'.2.1 hgd'.2.2.2.2.1 hgd'.2.2.2.2.2.1 hω₀'.2
    hgd'.2.2.2.2.2.2
  have huniq : ∀ w ∈ Hbar, d'.inv ω w = d'.inv ω 0 → w = 0 := fun w hw he =>
    RLC.eq_of_inv_eq_of_regular hC₁ hgd'.2.2.2.2.2.1 hreg (show (0 : ℝ) ≤ (0 : ℂ).im by simp) h0 hw
      (he.trans h0)
  obtain ⟨hinv, hlift⟩ := chartComp_of_trace (hd'.isCompact_K ω) (hd.isHPHull ω) (hd'.isHPHull ω) hKP hD₀ hD₁
    hg hWc hW0 hinj hQ hQ0 hPK hγP (htip.trans h0.symm) huniq
  rw [RetData.chart_of_mem hω, RetData.chart_of_mem hω']
  exact ⟨hinv, hlift⟩

/-- **(III-a) for retained data at a later line of the same pair**: `retChart_trans` when `d'` is `d` with the second
cutoff moved from `r` to `r + t`, and the continuation's chart path `γ` traces, through the stop-line chart inverse,
exactly the new piece `η₂([r, r + t])`, ending at the later tip. -/
theorem retChart_trans_of_image {Ω : Type*} [MeasurableSpace Ω] {d d' : RetData Ω} (hd : d.IsMeasGood)
    (hd' : d'.IsMeasGood) (h₁ : d'.η₁ = d.η₁) (h₂ : d'.η₂ = d.η₂) (hu : d'.u = d.u) {t : ℝ≥0}
    (hr : d'.r = d.r + t) {ω : Ω} (hω : ω ∈ d.E) (hω' : ω ∈ d'.E)
    (hg : IsGeneratingTrace W ζc γ) (hWc : Continuous W) (hW0 : W 0 = 0)
    (hinj : InjOn γ {s | (s : ℝ≥0∞) ≤ ζc}) (hQ : (Q : ℝ≥0∞) < ζc) (hQ0 : 0 < Q)
    (himg : (fun s => d.inv ω (γ s)) '' Icc 0 Q = d.η₂ ω '' Icc d.r (d.r + t))
    (htip : d.inv ω (γ Q) = d.η₂ ω (d.r + t)) :
    (∀ w ∈ H, (d'.chart ω).2.1 w = (d.chart ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) ∧
    ∀ w ∈ H, (d'.chart ω).2.2 ((d'.chart ω).2.1 w) =
      (logDerivFwd (fun s : ℝ => W s.toNNReal) Q (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)).im +
        (d.chart ω).2.2 ((d.chart ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) := by
  have hK₀ : d.K ω = prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r := RetData.K_of_mem hω
  have hK₁ : d'.K ω = prefixSet (d.η₁ ω) d.u (d.η₂ ω) (d.r + t) := by
    rw [RetData.K_of_mem hω', h₁, h₂, hu, hr]
  have himg' : d.inv ω '' (γ '' Icc 0 Q) = d.η₂ ω '' Icc d.r (d.r + t) := by rw [image_image]; exact himg
  have hsub : d.K ω ⊆ d'.K ω := by
    rw [hK₀, hK₁]
    exact union_subset_union_right _ (image_mono (Icc_subset_Icc_right le_self_add))
  have hnew : d.η₂ ω '' Icc d.r (d.r + t) ⊆ d'.K ω := by
    rw [hK₁]
    exact subset_union_of_subset_right (image_mono (Icc_subset_Icc_left zero_le)) _
  refine retChart_trans hd hd' hω hω' hg hWc hW0 hinj hQ hQ0 (fillH_mono hsub) ?_ ?_ ?_
  · rw [hK₁, himg', hK₀]
    rintro z (hz | ⟨s, hs, rfl⟩)
    · exact Or.inl (Or.inl hz)
    · rcases le_total s d.r with hsr | hrs
      · exact Or.inl (Or.inr ⟨s, ⟨zero_le, hsr⟩, rfl⟩)
      · exact Or.inr ⟨s, ⟨hrs, hs.2⟩, rfl⟩
  · intro s hs
    exact hnew (himg ▸ ⟨s, hs, rfl⟩)
  · rw [htip, h₂, hr]

end Restart.RetAux79

end InteractingSLE
