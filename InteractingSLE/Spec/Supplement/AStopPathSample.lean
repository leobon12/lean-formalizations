/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopPathZone
import InteractingSLE.Spec.Restart.RetLifeLine

/-!
# The A-stop at one ordinary sample of retained data

Packet PROVE-T15-ASTOP-PATH. At a sample `ω` of the good event of measurable good retained data `d`, with good paths
`η₁ ω`, `η₂ ω` agreeing with `d`'s on the prefixes and forming an ordinary retained pair (`IsOrdSample`):

* `IsOrdSample.mem_E`, `IsOrdSample.D_eq` (the chart domain is `ℍ \ fill(η₁[0,u] ∪ η₂[0,r])`),
  `IsOrdSample.tipPos_eq` (the first tip's chart position);
* **`IsOrdSample.isRetCont_snd`**, **`IsOrdSample.isRetCont_fst`**: both continuations are retained continuations
  (`Supp7.IsRetCont`), the first one in the chart translated by `tipPos`;
* **`IsOrdSample.isAChart_snd`**, **`IsOrdSample.isAChart_fst`**: the chart-boundary facts of the A-stop, from Lemma
  7.6's zones (disjoint prefixes) or Aux. lemma 85's zones (touching prefixes).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE.RLC.AStopPath

open Supp7 Restart Sec7.Lemma76G RetTouch

variable {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω} {ω : Ω} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
  {x₁ x₂ : ℝ}

/-- **An ordinary sample of retained data** (see the module docstring). -/
structure IsOrdSample (d : RetData Ω) (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (x₁ x₂ : ℝ) (ω : Ω) : Prop where
  G : ω ∈ d.G
  p₁ : IsPathGood (η₁ ω) (ζ₁ ω) x₁
  p₂ : IsPathGood (η₂ ω) (ζ₂ ω) x₂
  x : x₂ ≤ x₁
  a₁ : ∀ s ≤ d.u, d.η₁ ω s = η₁ ω s
  a₂ : ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t
  ord : IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r

namespace IsOrdSample

variable (hd : d.IsMeasGood) (hS : IsOrdSample d η₁ η₂ ζ₁ ζ₂ x₁ x₂ ω)
include hd hS

theorem mem_E : ω ∈ d.E := hd.mem_E_of_ordinary hS.G hS.a₁ hS.a₂ hS.ord

omit [MeasurableSpace Ω] hd in
theorem isClosed_K : IsClosed (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) :=
  ((Sec7.IsPathGood.isCompact_image hS.p₁ hS.ord.1.le).union
    (Sec7.IsPathGood.isCompact_image hS.p₂ hS.ord.2.1.le)).isClosed

omit [MeasurableSpace Ω] hd in
theorem activeDomain_eq' : activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r = activeDomain (η₁ ω) d.u (η₂ ω) d.r :=
  activeDomain_congr_Icc (fun s hs => hS.a₁ s hs.2) (fun t ht => hS.a₂ t ht.2)

theorem D_eq : d.D ω = H \ fillH (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) := by
  rw [hd.D_of_mem (hS.mem_E hd), hS.activeDomain_eq']
  exact activeDomain_eq (hS.isClosed_K)

theorem chart : IsRetChart (η₁ ω) d.u (η₂ ω) d.r (d.fwd ω) (d.inv ω) (d.lift ω) :=
  (Sec7.Lemma76F.isRetChart_congr hS.a₁ hS.a₂).1 (hd.isRetChart (hS.mem_E hd)).2

theorem continuousOn_inv : ContinuousOn (d.inv ω) Hbar :=
  (IsRetChart.isDomChart (hS.chart hd) (by rw [Sec7.IsPathGood.zero hS.p₂, ofReal_im])
    (hS.isClosed_K)).continuousOn_inv

theorem tipPos_eq :
    tipPos d η₁ ω = (limUnder (𝓝[activeDomain (η₁ ω) d.u (η₂ ω) d.r] (η₁ ω d.u)) (d.fwd ω)).re := by
  unfold tipPos
  rw [hd.D_of_mem (hS.mem_E hd), hS.activeDomain_eq']

theorem isRetCont_both :
    IsRetCont (η₂ ω) (ζ₂ ω) x₂ d.r (η₁ ω '' Icc 0 d.u) (d.fwd ω) (d.inv ω) ∧
      IsRetCont (η₁ ω) (ζ₁ ω) x₁ d.u (η₂ ω '' Icc 0 d.r) (fun z => d.fwd ω z - tipPos d η₁ ω)
        (fun w => d.inv ω (w + tipPos d η₁ ω)) := by
  have hE := hS.mem_E hd
  have hg := hd.good ω hS.G
  obtain ⟨⟨x₀, hx₀⟩, hC⟩ := hd.isRetChart hE
  have hφ : ∃ x₀ : ℝ, ∀ z, d.fwd ω z =
      ConformalImage.mapOut (fillH (prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r)) z - x₀ :=
    ⟨x₀, fun z => by
      show d.g ω z - d.shift ω = _
      rw [hx₀, RetData.g, RetData.K_of_mem hE]⟩
  obtain ⟨hR₂, -, hR₁⟩ := isRetCont_of_ordinary hg hC hφ hS.p₁ hS.p₂ hS.a₁ hS.a₂ hS.ord
  have hi₁ : d.η₁ ω '' Icc 0 d.u = η₁ ω '' Icc 0 d.u := image_congr fun s hs => hS.a₁ s hs.2
  have hi₂ : d.η₂ ω '' Icc 0 d.r = η₂ ω '' Icc 0 d.r := image_congr fun t ht => hS.a₂ t ht.2
  rw [hi₁] at hR₂
  rw [hi₂] at hR₁
  have hw : (limUnder (𝓝[activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r] (η₁ ω d.u)) (d.fwd ω)).re =
      tipPos d η₁ ω := by
    rw [hS.tipPos_eq hd, hS.activeDomain_eq']
  rw [hw] at hR₁
  exact ⟨hR₂, hR₁⟩

theorem isRetCont_snd : IsRetCont (η₂ ω) (ζ₂ ω) x₂ d.r (η₁ ω '' Icc 0 d.u) (d.fwd ω) (d.inv ω) :=
  (hS.isRetCont_both hd).1

theorem isRetCont_fst :
    IsRetCont (η₁ ω) (ζ₁ ω) x₁ d.u (η₂ ω '' Icc 0 d.r) (fun z => d.fwd ω z - tipPos d η₁ ω)
      (fun w => d.inv ω (w + tipPos d η₁ ω)) :=
  (hS.isRetCont_both hd).2

/-- **The second continuation's chart facts at an ordinary sample.** -/
theorem isAChart_snd : IsAChart (d.inv ω) (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) x₂ := by
  by_cases hdis : Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r)
  · have hx : x₂ < x₁ := by
      refine lt_of_le_of_ne hS.x fun he => Set.disjoint_left.1 hdis
        ⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hS.p₁⟩ ?_
      rw [← he]
      exact ⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hS.p₂⟩
    have hpair : Sec7.Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r :=
      ⟨hS.ord.1, hS.ord.2.1, hS.ord.2.2.2.1, hdis, hS.ord.2.2.2.2.2.2.2.1, hS.ord.2.2.2.2.2.2.1⟩
    obtain ⟨-, hs⟩ := RetAux79.isSetting_of_retData hd hS.G hS.p₁ hS.p₂ hx hS.a₁ hS.a₂ hpair
    exact isAChart_snd_of_setting hs
  · have ht := RLC.Aux85.retTouchZonesStatement _ _ _ _ _ _ _ _ _ _ _ hS.p₁ hS.p₂ hS.x hS.ord hdis (hS.chart hd)
    exact isAChart_snd_of_touch ht hS.p₁ hS.p₂ hS.ord.1.le hS.ord.2.1.le hS.x rfl rfl (hS.continuousOn_inv hd)

/-- **The first continuation's chart facts at an ordinary sample** (chart translated by `tipPos`). -/
theorem isAChart_fst :
    IsAChart (fun w => d.inv ω (w + tipPos d η₁ ω)) (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) x₁ := by
  have htp := hS.tipPos_eq hd
  by_cases hdis : Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r)
  · have hx : x₂ < x₁ := by
      refine lt_of_le_of_ne hS.x fun he => Set.disjoint_left.1 hdis
        ⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hS.p₁⟩ ?_
      rw [← he]
      exact ⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hS.p₂⟩
    have hpair : Sec7.Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r :=
      ⟨hS.ord.1, hS.ord.2.1, hS.ord.2.2.2.1, hdis, hS.ord.2.2.2.2.2.2.2.1, hS.ord.2.2.2.2.2.2.1⟩
    obtain ⟨-, hs⟩ := RetAux79.isSetting_of_retData hd hS.G hS.p₁ hS.p₂ hx hS.a₁ hS.a₂ hpair
    have h := isAChart_fst_of_setting hs
    have hM : (zoneData (d.fwd ω) (η₁ ω) d.u (η₂ ω) d.r).M₁ = tipPos d η₁ ω := htp.symm
    rw [hM] at h
    exact h
  · have ht := RLC.Aux85.retTouchZonesStatement _ _ _ _ _ _ _ _ _ _ _ hS.p₁ hS.p₂ hS.x hS.ord hdis (hS.chart hd)
    have h := isAChart_fst_of_touch ht hS.p₁ hS.p₂ hS.ord.1.le hS.ord.2.1.le hS.x rfl rfl (hS.continuousOn_inv hd)
    have hM : (RetChart.zoneDataT (d.fwd ω) (activeDomain (η₁ ω) d.u (η₂ ω) d.r) (d.inv ω) (η₁ ω) d.u (η₂ ω)
        d.r).M₁ = tipPos d η₁ ω := htp.symm
    rw [hM] at h
    exact h

end IsOrdSample

end InteractingSLE.RLC.AStopPath
