/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3AsmSecond
import InteractingSLE.Spec.Supplement.SBS3MarkedBoundary
import InteractingSLE.Spec.Sec7.LocalExtGChart
import InteractingSLE.Spec.Supplement.SBS3TerminalExposed
import InteractingSLE.Spec.Supplement.WalkIntCanonModelRun

/-!
# Lemma S3: the second history's inputs at one sample

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3, specification pp. 579–580). Deterministic.

* **`stageOneChart_facts`**: the run chart after one piece of angle `ϑ` stopped at `q` (launched from the root `0`)
  is the flow line's Loewner chart: a core chart of the flow line up to `q`, holomorphic with finite fibres, with
  hull model `c + W q` and physical readout `Φ = extendFrom ℍ (fwdMapInv W q)`.
* **`second_sample_facts`**: with the post-stop mean formula and the explicit stop word of `SBS3AsmPost`, the second
  inputs of `exists_protectedWordComparison_upper` hold, including the exact exposed value `−λ − ϑχ` at unmarked
  negative interior landings.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv chiC)

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Geo

/-- **The chart after one piece stopped at `q` is the flow line's Loewner chart** (deterministic). Let `β` be an
injective generating trace of a driver `W` (continuous before its lifetime `ζ > q`, `W 0 = 0`), and `D` a driver
agreeing with `W` up to `q`, continuous up to `min q D.2`, with `q < D.2`. The chart `c` of the launch from the root
`0` (`ExplState.launch`: `Chart.id.recenter 0` composed with the Loewner chart of `D` stopped at `q`) has forward map
`fwdMap W q` and inverse `fwdMapInv W q`; it is a core chart of `β` up to `q` with `Φ = extendFrom ℍ (fwdMapInv W q)`
(holomorphic, finite fibres, open domain), `c + W q` maps out `fill β([0, q])`, and its physical readout `LuM.bdVal`
is `Φ` on `ℍ̄`. -/
theorem stageOneChart_facts {W : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {β : ℝ≥0 → ℂ} (hβ : IsGeneratingTrace W ζ β)
    (hW : ContinuousOn W {s | (s : ℝ≥0∞) < ζ}) (hW0 : W 0 = 0) (hinj : InjOn β {t | (t : ℝ≥0∞) ≤ ζ})
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < ζ) (hq0 : 0 < q) {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hDq : (q : ℝ≥0∞) < D.2)
    (hDW : ∀ t : ℝ≥0, t ≤ q → D.1 t = W t) (hDc : ContinuousOn D.1 {s | (s : ℝ≥0∞) ≤ min (q : ℝ≥0∞) D.2})
    {c : Chart} (hc : c = (Chart.id.recenter 0).loewner
      (fun x : ℝ => D.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (q : ℝ≥0∞) D.2)).toNNReal)
      ((min (q : ℝ≥0∞) D.2).toNNReal : ℝ)) :
    IsChartCore β q c.1 (extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) q)) ∧
      DifferentiableOn ℂ c.1 (H \ fillH (β '' Icc 0 q)) ∧
      (∀ z, (extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) q) ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) ∧
      IsOpen (H \ fillH (β '' Icc 0 q)) ∧ IsHPHull (fillH (β '' Icc 0 q)) ∧
      IsMapOut (fillH (β '' Icc 0 q)) (fun z => c.1 z + (W q : ℂ)) ∧
      (∀ y : ℂ, y ∈ Hbar → LuM.bdVal c y = extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) q) y) ∧
      (∀ x ∈ Hbar, Tendsto c.2.1 (𝓝[H] x) (𝓝 (extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) q) x))) ∧
      EqOn c.2.1 (extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) q)) H := by
  have hmin : min (q : ℝ≥0∞) D.2 = q := min_eq_left hDq.le
  set Ws : ℝ → ℝ := fun x : ℝ => D.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (q : ℝ≥0∞) D.2)).toNNReal with hWsdef
  set W' : ℝ → ℝ := fun r : ℝ => W r.toNNReal with hW'def
  have hWs : ∀ x : ℝ, Ws x = D.1 (min x.toNNReal q) := fun x => by
    simp only [hWsdef, hmin, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
  have hT : ((min (q : ℝ≥0∞) D.2).toNNReal : ℝ) = q := by rw [hmin, ENNReal.toNNReal_coe]
  have hDc' : ContinuousOn D.1 (Iic q) := by
    refine hDc.mono fun s (hs : s ≤ q) => ?_
    show (s : ℝ≥0∞) ≤ min (q : ℝ≥0∞) D.2
    rw [hmin]; exact ENNReal.coe_le_coe.2 hs
  have hWsc : Continuous Ws := by
    have h1 : Continuous fun x : ℝ => min x.toNNReal q := continuous_real_toNNReal.min continuous_const
    have h2 : Continuous fun x : ℝ => D.1 (min x.toNNReal q) :=
      hDc'.comp_continuous h1 fun x => Set.mem_Iic.2 (min_le_right _ _)
    exact h2.congr fun x => (hWs x).symm
  have hWs0 : Ws 0 = 0 := by rw [hWs, Real.toNNReal_zero, min_eq_left zero_le, hDW 0 zero_le, hW0]
  have heqI : ∀ r ∈ Icc (0 : ℝ) q, Ws r = W' r := fun r hr => by
    have hr' : r.toNNReal ≤ q := Real.toNNReal_le_iff_le_coe.2 hr.2
    rw [hWs, min_eq_left hr', hDW _ hr']
  have hfwd : fwdMap Ws q = fwdMap W' q := QuantumZipper.CharFunRhs.fwdMap_eq_of_eqOn heqI
  obtain ⟨t'', hqt'', ht''ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hW'c : ContinuousOn W' (Icc 0 (t'' : ℝ)) := by
    refine hW.comp continuous_real_toNNReal.continuousOn fun r hr => ?_
    show ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) ht''ζ
  have hinv : ∀ w, fwdMapInv Ws q w = fwdMapInv W' q w := fun w =>
    LocalExt.fwdMapInv_congr_of_continuousOn hWsc.continuousOn hW'c q.2 (by exact_mod_cast hqt'') heqI w
  have hc1 : ∀ z, c.1 z = fwdMap W' q z := fun z => by
    rw [hc]
    show fwdMap Ws ((min (q : ℝ≥0∞) D.2).toNNReal : ℝ) ((Chart.id.recenter 0).1 z) = _
    rw [hT, hfwd]
    simp [Chart.recenter, Chart.id]
  have hc2 : ∀ w, c.2.1 w = fwdMapInv W' q w := fun w => by
    rw [hc]
    show (Chart.id.recenter 0).2.1 (fwdMapInv Ws ((min (q : ℝ≥0∞) D.2).toNNReal : ℝ) w) = _
    rw [hT, hinv]
    simp [Chart.recenter, Chart.id]
  have hc1f : c.1 = fwdMap W' q := funext hc1
  obtain ⟨hch, -, hHull, hmo, hfd, hfin⟩ := secondChart_facts hβ hW hW0 hinj hq hq0
  have hΦc : ContinuousOn (fwdMapInv W' q) H := by
    have h := continuousOn_fwdMapInv hWsc hWs0 q.2
    exact h.congr fun w _ => (hinv w).symm
  have hΦH : ∀ w ∈ H, extendFrom H (fwdMapInv W' q) w = fwdMapInv W' q w := extendFrom_extends hΦc
  have hlim : ∀ x ∈ Hbar, Tendsto c.2.1 (𝓝[H] x) (𝓝 (extendFrom H (fwdMapInv W' q) x)) := by
    intro x hx
    refine ((hch.inv_cont x hx).tendsto.mono_left (nhdsWithin_mono _ H_subset_Hbar)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [hc2, hΦH w hw]
  refine ⟨hc1f ▸ IsChart.toCore hch, hc1f ▸ hfd, hfin, hHull.2.2.1, hHull, ?_, fun y hy => ?_, hlim,
    fun w hw => by rw [hc2, hΦH w hw]⟩
  · rw [hc1f]; exact hmo
  · rw [bdVal_eq_extendFrom (fun x hx => ⟨_, hlim x hx⟩) hy]
    exact extendFrom_eq (by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hy) (hlim y hy)

open Exist.Staged Exist.StagedLaw Restart in
/-- **The second side of Lemma S3 at one sample** (deterministic). For the one-instruction program
`(0, true, [(ϑ, q)])` with drivers `D` (regular launched piece, `D 0` agreeing with the flow driver `W` up to
`q < ζ_D`): its stage-1 run chart `c₂` is the flow line's Loewner chart. Given a sorted word `β₂` with the mean
formula on the chart domain, equal off both mark sets to an explicit stop word `stopWord κ (w, ϑ, r)` whose record
chart is `c₂`, the second inputs of `exists_protectedWordComparison_upper` hold: a core chart `(c₂.1, Φ)` of `β`
up to `q` (holomorphic, finite fibres, open domain), the hull model `c₂ + W q`, the mean formula with the canonical
logarithm of `fill β([0, q])`, and the exact exposed left value `−λ − ϑχ` off the stop word's marks. -/
theorem second_sample_facts {κ ϑ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {q : ℝ≥0}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hreg : ∀ k c θ', (ExplState.run κ b jumps ((0 : ℝ), true, [Sum.inl (ϑ, (q : ℝ≥0∞))]) D (k + 1)).2.2.2.1 k =
      some (c, θ') → GW1P.PieceRegular (D k).1
        (min (instrTime ((0 : ℝ), true, [Sum.inl (ϑ, (q : ℝ≥0∞))]) k) (D k).2))
    {W : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {β : ℝ≥0 → ℂ} (hβ : IsGeneratingTrace W ζ β)
    (hW : ContinuousOn W {s | (s : ℝ≥0∞) < ζ}) (hW0 : W 0 = 0) (hinj : InjOn β {t | (t : ℝ≥0∞) ≤ ζ})
    (hq : (q : ℝ≥0∞) < ζ) (hq0 : 0 < q) (hDq : (q : ℝ≥0∞) < (D 0).2)
    (hDW : ∀ t : ℝ≥0, t ≤ q → (D 0).1 t = W t)
    (hDc : ContinuousOn (D 0).1 {s | (s : ℝ≥0∞) ≤ min (q : ℝ≥0∞) (D 0).2})
    {β₂ w : BoundaryWord} {r : RecData} {v₂ u₀ : ℂ → ℝ}
    (hmean : EqOn (fun z => v₂ z + u₀ z + chiC κ *
        (ExplState.run κ b jumps ((0 : ℝ), true, [Sum.inl (ϑ, (q : ℝ≥0∞))]) D 1).2.2.2.2.1.2.2 z)
      (fun z => β₂.mean ((ExplState.run κ b jumps ((0 : ℝ), true, [Sum.inl (ϑ, (q : ℝ≥0∞))]) D 1).2.2.2.2.1.1 z))
      (ExplState.run κ b jumps ((0 : ℝ), true, [Sum.inl (ϑ, (q : ℝ≥0∞))]) D 1).2.2.2.2.1.dom)
    (hid : ∀ x : ℝ, x ∉ β₂.jumps → x ∉ (stopWord κ (w, ϑ, r)).jumps → β₂.fn x = (stopWord κ (w, ϑ, r)).fn x)
    (hcid : (ExplState.run κ b jumps ((0 : ℝ), true, [Sum.inl (ϑ, (q : ℝ≥0∞))]) D 1).2.2.2.2.1 =
      (Chart.id.recenter 0).loewner (rdrv r) (rtime r)) :
    ∃ (f Φ : ℂ → ℂ) (e₂ : ℝ) (Jx : Finset ℝ),
      Geo.IsChartCore β q f Φ ∧ DifferentiableOn ℂ f (H \ fillH (β '' Icc 0 q)) ∧
      (∀ z, (Φ ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) ∧ IsOpen (H \ fillH (β '' Icc 0 q)) ∧
      IsMapOut (fillH (β '' Icc 0 q)) (fun z => f z + (e₂ : ℂ)) ∧
      EqOn (fun z => v₂ z + u₀ z + chiC κ * (canonDerivLog (fillH (β '' Icc 0 q)) z).im)
        (fun z => β₂.mean (f z)) (H \ fillH (β '' Icc 0 q)) ∧
      ∀ y : ℝ, y < 0 → y ∉ β₂.jumps → y ∉ Jx → Φ y ∈ H → β₂.fn y = -sleLambda κ - ϑ * chiC κ := by
  set spec : ExplSpec := ((0 : ℝ), true, [Sum.inl (ϑ, (q : ℝ≥0∞))]) with hspec
  set c₂ := (ExplState.run κ b jumps spec D 1).2.2.2.2.1 with hc₂
  have hl := GW1.launches_run_one_of_cons κ b jumps spec (θ := ϑ) (t := (q : ℝ≥0∞)) (rest := []) rfl D
  obtain ⟨-, he, -⟩ := eq_launch_of_launches spec D hl
  have hfin : min (instrTime spec 0) (D 0).2 ≠ ⊤ := by
    have : instrTime spec 0 = (q : ℝ≥0∞) := rfl
    rw [this]
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  have hcform : c₂ = (Chart.id.recenter 0).loewner
      (fun x : ℝ => (D 0).1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (q : ℝ≥0∞) (D 0).2)).toNNReal)
      ((min (q : ℝ≥0∞) (D 0).2).toNNReal : ℝ) := by
    rw [hc₂, he, chart_launch _ _ _ _ _ hfin]
    rfl
  obtain ⟨hch, hfd, hfinΦ, hDo, hHull, hmo, hbd, hlim, hinvH⟩ :=
    stageOneChart_facts hβ hW hW0 hinj hq hq0 hDq hDW hDc hcform
  set Φ := extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) q) with hΦ
  set F := fillH (β '' Icc 0 q) with hF
  -- the chart domain is `ℍ ∖ fill β[0, q]`
  have hcc : c₂.IsConformal :=
    (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) spec D 1 fun j _ c θ h => hreg j c θ h).1
  have hdom : (c₂.dom : Set ℂ) = H \ F := by
    rw [hcc.coe_dom]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hinvH hw]
      exact hch.inv_mem hw
    · intro hz
      refine ⟨c₂.1 z, hch.maps hz, ?_⟩
      rw [hinvH (hch.maps hz)]
      exact hch.inv_f z hz
  obtain ⟨M⟩ := WalkIntCanon.exists_hullModel_runChart (κ := κ) (b := b) (jumps := jumps) spec D 1
    fun j _ => hreg j
  have hN := WalkIntCanon.isNormalized_runChart (κ := κ) (b := b) (jumps := jumps) spec D 1
    fun j _ c θ h => hreg j c θ h
  have hMF : M.hull = F := by
    have h1 : H \ M.hull = H \ F := M.dom_eq.symm.trans hdom
    have hM : M.hull ⊆ H := M.isHull.1
    have hFH : F ⊆ H := fun z hz => hz.1
    ext z
    constructor
    · intro hz
      by_contra hzF
      have : z ∈ H \ F := ⟨hM hz, hzF⟩
      rw [← h1] at this
      exact this.2 hz
    · intro hz
      by_contra hzM
      have : z ∈ H \ M.hull := ⟨hFH hz, hzM⟩
      rw [h1] at this
      exact this.2 hz
  refine ⟨c₂.1, Φ, W q, (stopWord κ (w, ϑ, r)).jumps, hch, hfd, hfinΦ, hDo, hmo, ?_, ?_⟩
  · intro z hz
    have hzd : z ∈ (c₂.dom : Set ℂ) := by rw [hdom]; exact hz
    have he' := hmean hzd
    have hlift := M.lift_eq_canonDerivLog hN (show z ∈ H \ M.hull by rw [hMF]; exact hz)
    simp only at he' ⊢
    rw [← he', ← hMF]
    show v₂ z + u₀ z + chiC κ * (canonDerivLog M.hull z).im = v₂ z + u₀ z + chiC κ * c₂.2.2 z
    rw [hlift]
  · intro y hy hyJ hyX hyH
    have hyHbar : (y : ℂ) ∈ Hbar := by simp [Hbar]
    have hbdy : LuM.bdVal c₂ (y : ℂ) ∈ H := by rw [hbd y hyHbar]; exact hyH
    rw [hcid] at hbdy
    have hB : HasBdryLimits (QuantumZipper.fwdMapInv (rdrv r) (rtime r)) := by
      intro x hx
      refine ⟨Φ x, (hlim x hx).congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z _
      rw [hcid]
      show (fwdMapInv (rdrv r) (rtime r) z) + ((0 : ℝ) : ℂ) = fwdMapInv (rdrv r) (rtime r) z
      simp
    have hv := stopWord_exposed_value_from_real_seed (word := w) (θ := ϑ) 0 hB hy.ne hyX hbdy
    rw [hid y hyJ hyX, hv, ite_cond_eq_true _ _ (eq_true hy)]

end InteractingSLE.Theorem14.SB.S3.Asm
