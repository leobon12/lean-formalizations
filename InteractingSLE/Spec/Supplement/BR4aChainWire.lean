/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR4aChainMeas

/-!
# BR4a's relative chain from two named inputs

Packet PROVE-T14-BR4A2. `Supp8.HullDetGen.BR4aRelChainStatement` (PROVE-HULLDET's named input, Theorem 1.4 leaf `hBR`)
is reduced to two named inputs and Theorem 1.3:

* **`BR4aClockStatement`**: infinite relative capacity (supplement p. 610: "If its relative capacity had a finite
  limit, the admissible integrated law and nonexplosion would bound the relative driver and hulls through that limit
  … This contradiction gives infinite relative capacity");
* **`BR4aRelWordStatement`**: the words of the relative chain (seed, no threshold, the coupling-mean identity through
  `brChart v`; (BR4a.1)–(BR4a.2)).

Everything else is proved: the relative driver is Zhan's explicit retargeted driver of each sample (`relDrv`,
`BR4aChainPath`), the stopping times are its inverse clock and the driver is adapted to their stopped σ-algebras
(`relTime`, `stronglyAdapted_relProc`, `BR4aChainMeas`), the hull versions are `mobInv v`-images of the relative hulls,
and the active-domain and hull identities follow from the per-sample hull identity.

* `relDrvProc`, `BR4aClockStatement`, `BR4aRelWordStatement`;
* helpers `mobInv_image_mob_image`, `mem_mobInv_image_iff`, `mobInv_image_diff`, `isOpen_H_diff_mobInv_image`,
  `thr_congr`, `bheProc_geom_congr`;
* **`br4aRelChainStatement_of_clock_word`**.

R48: Theorem 1.3 is a permitted root of Theorem 1.4; nothing here is an input of Theorems 1.2–1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal Classical

universe u

namespace InteractingSLE.Theorem14.BR4aChain

open Restart Restart.FCDet Restart.DomainMarkov Restart.DomainMarkov.K2 Sec2.Assembly Sec7.PocketTraversal
  BR4aPath Supp8.HullDetGen

/-- **Named input: BR4a's relative capacity is infinite** (supplement p. 610, Corollary BR4 and BR4a: "If its
relative capacity had a finite limit, the admissible integrated law and nonexplosion would bound the relative driver
and hulls through that limit. But continuity of the original prefix at its hit of `z` makes its image under `ψ`
approach infinity. This contradiction gives infinite relative capacity"). In BR4a's setting (the original coupling
`(h', W', …)` of the infinity-source field, infinite lifetime, `v ≠ 0` visited almost surely), almost surely the
capacity clock `clock v` of the target change `mob v` is unbounded before the first visit of `v`. -/
def BR4aClockStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ v : ℝ, v ≠ 0 → (∀ᵐ ω ∂P, (v : ℂ) ∈ infinitySourceChart.tipSet (fun t => W' t ω) ⊤) →
    ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens), IsPiecewiseConstantBoundaryData b' J' →
      (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω)) →
    ∀ (𝓕 : Filtration ℝ≥0 mΩ) (VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ)
      (VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsOptionalHullCoupling (16 / κ) (flowLineXL b' J' 0) (flowLineXR b' J' 0) (flowLineRhoL (16 / κ) b' J' 0 0)
        (flowLineRhoR (16 / κ) b' J' 0 0) P 𝓕 W' VL VR B ζ' h' →
    ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => W' s ω) {(v : ℂ)} ∧
      M ≤ clock v (fun s : ℝ => W' s.toNNReal ω) t

/-- The relative driver process of the target change to `v` (`relDrv` sample by sample). -/
def relDrvProc {Ω : Type*} (v : ℝ) (W' : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun q ω => relDrv v (W' · ω) q

/-- **Named input: the words of BR4a's relative chain** (supplement p. 610, (BR4a.1)–(BR4a.2): the transformed
field `F^ψ = F ∘ f − χ Im L_f` has the original heights on the base side of the pole and the retained old-target
weight beyond it; HULLDET §4.1 (b)–(c)). In BR4a's setting, with the trace of Theorem 1.3 and the unbounded clock,
for every sorted word `c` of the target-change transport `X = chartTransport (brChart v) 1 0 χ' h'`: the flow-line
seed of `c` is admissible; almost surely the relative driver `relDrv v W'` never reaches a continuation threshold of
the flowed marks of `c`; and almost surely, at every original time `t` before the first visit and relative time
`q = clock v W' t`, the coupling mean of the original chain at `t`, read through `brChart v`, is the coupling mean of
the relative driver at `q` with the flowed word of `c`. -/
def BR4aRelWordStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ v : ℝ, v ≠ 0 → (∀ᵐ ω ∂P, (v : ℂ) ∈ infinitySourceChart.tipSet (fun t => W' t ω) ⊤) →
    ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens), IsPiecewiseConstantBoundaryData b' J' →
      (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω)) →
    ∀ (𝓕 : Filtration ℝ≥0 mΩ) (VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ)
      (VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsOptionalHullCoupling (16 / κ) (flowLineXL b' J' 0) (flowLineXR b' J' 0) (flowLineRhoL (16 / κ) b' J' 0 0)
        (flowLineRhoR (16 / κ) b' J' 0 0) P 𝓕 W' VL VR B ζ' h' →
    (∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ ∧ Tendsto (fun t => ‖γ t‖) atTop atTop) →
    (∀ᵐ ω ∂P, ∀ M : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => W' s ω) {(v : ℂ)} ∧
      M ≤ clock v (fun s : ℝ => W' s.toNNReal ω) t) →
    ∀ c : BoundaryWord, c.IsSorted →
      IsGFFWithBoundaryData P (fun ω => Chart.chartTransport (isConformal_brChart v) 1 0 (chiC (16 / κ)) (h' ω))
        c.fn c.jumps →
      ¬ ForceWord.ThresholdCondition (flowLineRhoL (16 / κ) c.fn c.jumps 0 0)
          (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) 0 (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0) ∧
      (∀ᵐ ω ∂P, thr (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0)
          (relDrvProc v W') (fun _ => flowLineXL c.fn c.jumps 0) (fun _ => flowLineXR c.fn c.jumps 0) ω = ⊤) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => W' s ω) {(v : ℂ)} →
        ∀ w ∈ H \ fwdHull (fun s : ℝ => relDrvProc v W' s.toNNReal ω)
            ((clock v (fun s : ℝ => W' s.toNNReal ω) t).toNNReal : ℝ),
          couplingMean (16 / κ) (fun s : ℝ => W' s.toNNReal ω) t
              (bheProc (16 / κ) (flowLineRhoL (16 / κ) b' J' 0 0) (flowLineRhoR (16 / κ) b' J' 0 0) W' VL VR ω t)
              (mobInv v w) + 0 + chiC (16 / κ) * (brChart v).2.2 (mobInv v w) =
            couplingMean (16 / κ) (fun s : ℝ => relDrvProc v W' s.toNNReal ω)
              ((clock v (fun s : ℝ => W' s.toNNReal ω) t).toNNReal : ℝ)
              (bheProc (16 / κ) (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0)
                (relDrvProc v W') (geomLW (relDrvProc v W') fun _ => flowLineXL c.fn c.jumps 0)
                (geomRW (relDrvProc v W') fun _ => flowLineXR c.fn c.jumps 0) ω
                (clock v (fun s : ℝ => W' s.toNNReal ω) t).toNNReal) w


/-! ### Helpers -/

theorem mobInv_image_mob_image (v : ℝ) {K : Set ℂ} (hK : K ⊆ H) : mobInv v '' (BR4aPath.mob v '' K) = K := by
  rw [image_image]
  exact (image_congr fun z hz => mobInv_mob v (hK hz)).trans (image_id' K)

theorem mem_mobInv_image_iff (v : ℝ) {K : Set ℂ} (hKH : K ⊆ H) {z : ℂ} (hz : z ∈ H) :
    z ∈ mobInv v '' K ↔ BR4aPath.mob v z ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mob_mobInv v (hKH hy)]
    exact hy
  · intro h
    exact ⟨BR4aPath.mob v z, h, mobInv_mob v hz⟩

theorem mobInv_image_diff (v : ℝ) {K : Set ℂ} (hKH : K ⊆ H) :
    mobInv v '' (H \ BR4aPath.mob v '' K) = H \ K := by
  ext z
  constructor
  · rintro ⟨y, ⟨hyH, hyK⟩, rfl⟩
    exact ⟨mobInv_mem_H v hyH, fun hz => hyK ⟨_, hz, mob_mobInv v hyH⟩⟩
  · rintro ⟨hzH, hzK⟩
    refine ⟨BR4aPath.mob v z, ⟨mob_mem_H v hzH, ?_⟩, mobInv_mob v hzH⟩
    rintro ⟨y, hy, he⟩
    have := congrArg (mobInv v) he
    rw [mobInv_mob v (hKH hy), mobInv_mob v hzH] at this
    exact hzK (this ▸ hy)

theorem isOpen_H_diff_mobInv_image {v : ℝ} (hv : v ≠ 0) {K : Set ℂ} (hKH : K ⊆ H) (hK : IsOpen (H \ K)) :
    IsOpen (H \ mobInv v '' K) := by
  have he : H \ mobInv v '' K = H ∩ BR4aPath.mob v ⁻¹' (H \ K) := by
    ext z
    constructor
    · rintro ⟨hz, hzK⟩
      exact ⟨hz, mob_mem_H v hz, fun h => hzK ((mem_mobInv_image_iff v hKH hz).2 h)⟩
    · rintro ⟨hz, -, hzK⟩
      exact ⟨hz, fun h => hzK ((mem_mobInv_image_iff v hKH hz).1 h)⟩
  rw [he]
  have hc : ContinuousOn (BR4aPath.mob v) H := by
    intro z hz
    have : (fun z : ℂ => z / ((v : ℂ) * z + 1)) = BR4aPath.mob v := funext fun z => (mob_apply v z).symm
    rw [← this]
    exact (continuousAt_id.div ((continuousAt_const.mul continuousAt_id).add continuousAt_const)
      (mul_add_one_ne_zero hv hz)).continuousWithinAt
  exact hc.isOpen_inter_preimage QuantumZipper.isOpen_H hK

theorem thr_congr {Ω : Type*} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W R : ℝ≥0 → Ω → ℝ}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {ω : Ω} (h : ∀ t, W t ω = R t ω) :
    thr ρL ρR W xL xR ω = thr ρL ρR R xL xR ω := by
  have hp : Bessel.realPath W ω = Bessel.realPath R ω := funext fun s => h _
  have hpn : Bessel.realPath (fun t ω => -W t ω) ω = Bessel.realPath (fun t ω => -R t ω) ω :=
    funext fun s => by simp only [Bessel.realPath, h]
  simp only [thr, geomLW, geomRW, hp, hpn, h]

theorem bheProc_geom_congr {Ω : Type*} {nL nR : ℕ} (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {W R : ℝ≥0 → Ω → ℝ} (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) {ω : Ω} (h : ∀ t, W t ω = R t ω)
    (s : ℝ≥0) :
    bheProc κ ρL ρR W (geomLW W xL) (geomRW W xR) ω s = bheProc κ ρL ρR R (geomLW R xL) (geomRW R xR) ω s := by
  have hp : Bessel.realPath W ω = Bessel.realPath R ω := funext fun s => h _
  have hpn : Bessel.realPath (fun t ω => -W t ω) ω = Bessel.realPath (fun t ω => -R t ω) ω :=
    funext fun s => by simp only [Bessel.realPath, h]
  simp only [bheProc, geomLW, geomRW, hp, hpn, h]


/-! ### The relative chain -/

/-- **BR4a's relative chain from its two remaining inputs** (conditional helper with a distinct name; named inputs
`BR4aClockStatement` (infinite relative capacity) and `BR4aRelWordStatement` (the words); Theorem 1.3 is a permitted
root of Theorem 1.4, R48). The relative driver is Zhan's explicit retargeted driver of the original counterflow
(`relDrv`), the stopping times are its inverse clock (`relTime`), and the hull versions are the `mobInv v`-images of
the relative hulls. -/
theorem br4aRelChainStatement_of_clock_word (hclk : BR4aClockStatement.{u}) (hword : BR4aRelWordStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : BR4aRelChainStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hζ' v hv0 hvis b' J' h' hb' htr' 𝓕 VL VR B hC hX c hcs hXc
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) hκ
  have hclkω := hclk κ hκ hκ4 b jumps hb P h hh W' ζ' hζ' v hv0 hvis b' J' h' hb' htr' 𝓕 VL VR B hC
  have htrace : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ ∧
      Tendsto (fun t => ‖γ t‖) atTop atTop := by
    filter_upwards [h13 hκ' (Theorem15.isOrderedForceWord_flowLine b' J' 0) hC.1, hζ'] with ω hω hζω
    obtain ⟨-, η, hη, htr⟩ := hω
    rw [hζω] at hη htr
    exact ⟨η, hη, htr rfl⟩
  have hpath : ∀ᵐ ω ∂P, W' 0 ω = 0 ∧ ContinuousOn (fun t => W' t ω) {t | (t : ℝ≥0∞) < ζ' ω} := by
    filter_upwards [hC.1.2.2.2.2] with ω hp
    exact ⟨hp.1, hp.2.2.2.1⟩
  obtain ⟨hseed, hthr, hmean⟩ := hword κ hκ hκ4 b jumps hb P h hh W' ζ' hζ' v hv0 hvis b' J' h' hb' htr' 𝓕 VL VR
    B hC htrace hclkω c hcs hXc
  -- the good event
  have hgae : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ IsGoodSample v (fun t => W' t ω) := by
    filter_upwards [hζ', htrace, hpath, hvis, hclkω] with ω hζω hγω hpω hvisω hcω
    obtain ⟨γ, hγ, -⟩ := hγω
    obtain ⟨h0, hc⟩ := hpω
    rw [hζω] at hc
    refine ⟨hζω, continuousOn_univ.1 (by simpa using hc), h0, ⟨γ, hγ⟩, hvisω, hcω⟩
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgae)
  set G : Set Ω := Nᶜ with hGdef
  have hGm : MeasurableSet G := hNm.compl
  have hG : MeasurableSet[drivingFiltration P hX 0] G :=
    (Ito.measurableSet_usualAugmentation_of_null (𝓕 := killedDrivingFiltration hX) hNm hN0 0).compl
  have hGa : ∀ᵐ ω ∂P, ω ∈ G := measure_eq_zero_iff_ae_notMem.1 hN0
  have hGgood : ∀ ω ∈ G, ζ' ω = ⊤ ∧ IsGoodSample v (fun t => W' t ω) := fun ω hω => by
    by_contra hn
    exact hω (hNsub hn)
  -- the masked driver
  set wG : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then W' t ω else 0 with hwGdef
  have hwG : ∀ ω ∈ G, (fun t => wG t ω) = fun t => W' t ω := fun ω hω => funext fun t => by
    simp only [hwGdef, hω, ↓reduceIte]
  have hwc : ∀ ω, Continuous (wG · ω) := fun ω => by
    by_cases hω : ω ∈ G
    · rw [hwG ω hω]; exact (hGgood ω hω).2.1
    · simp only [hwGdef, hω, ↓reduceIte]; exact continuous_const
  have hWa : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have hwm : ∀ t, Measurable[drivingFiltration P hX t] (wG t) := fun t A hA => by
    have hGt : MeasurableSet[drivingFiltration P hX t] G := (drivingFiltration P hX).mono zero_le _ hG
    have he : wG t ⁻¹' A = (G ∩ {ω | (t : ℝ≥0∞) < ζ' ω ∧ W' t ω ∈ A}) ∪ (Gᶜ ∩ {_ω | (0 : ℝ) ∈ A}) := by
      ext ω
      by_cases hω : ω ∈ G
      · simp only [mem_preimage, hwGdef, hω, ↓reduceIte, (hGgood ω hω).1, ENNReal.coe_lt_top, true_and,
          mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff, not_true_eq_false, false_and, or_false]
      · simp only [mem_preimage, hwGdef, hω, ↓reduceIte, mem_union, mem_inter_iff, false_and,
          mem_compl_iff, not_false_eq_true, true_and, false_or, mem_ofPred_eq]
    rw [he]
    exact (hGt.inter (hWa t A hA)).union (hGt.compl.inter (MeasurableSet.const _))
  have hgood : ∀ ω ∈ G, IsGoodSample v (wG · ω) := fun ω hω => by rw [hwG ω hω]; exact (hGgood ω hω).2
  -- the relative chain
  have hℓ : ∀ q, IsStoppingTime (drivingFiltration P hX) (relTime G v wG q) :=
    isStoppingTime_relTime hwc hwm hv0 hG hgood
  have hℓm : ∀ ω, Monotone fun q => relTime G v wG q ω := monotone_relTime hv0 hgood
  have hWa := stronglyAdapted_relProc hwc hwm hv0 hG hgood
  have hWω : ∀ ω ∈ G, ∀ t, relProc G v wG t ω = relDrvProc v W' t ω := fun ω hω t => by
    simp only [relProc, hω, ↓reduceIte, relDrvProc, hwG ω hω]
  have hwr : ∀ ω ∈ G, (fun s : ℝ => wG s.toNNReal ω) = fun s : ℝ => W' s.toNNReal ω := fun ω hω => funext fun s => by
    simp only [hwGdef, hω, ↓reduceIte]
  have hrel : ∀ ω ∈ G, ∀ q : ℝ≥0, ∃ t : ℝ≥0, relTime G v wG q ω = t ∧
      (t : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => W' s ω) {(v : ℂ)} ∧
      clock v (fun s : ℝ => W' s.toNNReal ω) t = q := fun ω hω q => by
    obtain ⟨t, h1, h2, h3⟩ := relTime_spec (G := G) hv0 hω (hgood ω hω) q
    refine ⟨t, h1, ?_, ?_⟩
    · have : tipT v wG ω = firstTipTime infinitySourceChart (fun s => W' s ω) {(v : ℂ)} := by
        rw [tipT, hwG ω hω]
      rwa [← this]
    · rwa [← hwr ω hω]
  have hWc : ∀ ω, Continuous fun t => relProc G v wG t ω := fun ω => by
    by_cases hω : ω ∈ G
    · obtain ⟨-, -, -, -, -, hc, -⟩ := (hGgood ω hω).2.spec hv0
      simpa only [hWω ω hω, relDrvProc] using hc
    · simp only [relProc, hω, ↓reduceIte]; exact continuous_const
  have hWm : ∀ r, Measurable (relProc G v wG r) := fun r =>
    (hWa r).measurable.mono ((Supp8.HullDetGen.stoppedFiltration hℓ hℓm).le r) le_rfl
  have hhull : ∀ ω ∈ G, ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => W' s ω) {(v : ℂ)} →
      fwdHull (fun s : ℝ => relProc G v wG s.toNNReal ω) (clock v (fun s : ℝ => W' s.toNNReal ω) t) =
        BR4aPath.mob v '' fwdHull (fun s : ℝ => W' s.toNNReal ω) t := fun ω hω t ht => by
    obtain ⟨T₀, hT, -, -, -, -, -, hK⟩ := (hGgood ω hω).2.spec hv0
    rw [hT, ENNReal.coe_lt_coe] at ht
    simpa only [hWω ω hω, relDrvProc] using (hK t ht).1
  refine ⟨relTime G v wG, hℓ, hℓm, relProc G v wG,
    fun s ω => if ω ∈ G then mobInv v '' fwdHull (fun r : ℝ => relProc G v wG r.toNNReal ω) s else ∅,
    fun q => ?_, fun ω => ?_, hWc, hWa, hseed, fun s => ?_, fun s ω => ?_, fun s => ?_, ?_, fun q => ?_, fun q => ?_,
    ?_⟩
  · -- the stops are before the lifetime
    filter_upwards [hGa] with ω hω
    obtain ⟨t, ht, -, -⟩ := hrel ω hω q
    rw [ht, (hGgood ω hω).1]
    exact ENNReal.coe_lt_top
  · -- the driver starts at `0`
    by_cases hω : ω ∈ G
    · obtain ⟨-, -, -, -, -, -, h0, -⟩ := (hGgood ω hω).2.spec hv0
      rw [hWω ω hω]; exact h0
    · simp only [relProc, hω, ↓reduceIte]
  · -- the hull versions are hitting-measurable
    exact Measurable.ite hGm (measurable_image_fwdHull hWc hWm (v := -v) (neg_ne_zero.2 hv0) s.coe_nonneg)
      measurable_const
  · -- the hull versions are relatively closed in `ℍ`
    by_cases hω : ω ∈ G
    · simp only [hω, ↓reduceIte]
      have hKH := (QuantumZipper.fwdHull_mono (W := fun r : ℝ => relProc G v wG r.toNNReal ω)).2 s
      refine ⟨image_subset_iff.2 fun z hz => mobInv_mem_H v (hKH hz), isOpen_H_diff_mobInv_image hv0 hKH
        (QuantumZipper.FwdHolo.isOpen_compl_fwdHull ((hWc ω).comp continuous_real_toNNReal) s.coe_nonneg)⟩
    · simp only [hω, ↓reduceIte, empty_subset, sdiff_empty, true_and]
      exact QuantumZipper.isOpen_H
  · -- the hull versions are the original hulls at the stops
    filter_upwards [hGa] with ω hω
    obtain ⟨t, ht, htT, hct⟩ := hrel ω hω s
    have hKt := hhull ω hω t htT
    rw [hct] at hKt
    simp only [hω, ↓reduceIte, hKt, ht, WithTop.untopD_coe]
    exact mobInv_image_mob_image v ((QuantumZipper.fwdHull_mono).2 _)
  · -- the threshold is never reached
    filter_upwards [hthr, hGa] with ω h1 hω
    rw [thr_congr (hWω ω hω)]
    exact h1
  · -- the active domains correspond
    filter_upwards [hGa] with ω hω
    obtain ⟨t, ht, htT, hct⟩ := hrel ω hω q
    have hKt := hhull ω hω t htT
    rw [hct] at hKt
    rw [hKt, ht, WithTop.untopD_coe]
    exact mobInv_image_diff v ((QuantumZipper.fwdHull_mono).2 _)
  · -- the mean identity
    filter_upwards [hmean, hGa] with ω h1 hω
    intro w hw
    obtain ⟨t, ht, htT, hct⟩ := hrel ω hω q
    have hq : (clock v (fun s : ℝ => W' s.toNNReal ω) t).toNNReal = q := by rw [hct, Real.toNNReal_coe]
    have hfun : (fun s : ℝ => relProc G v wG s.toNNReal ω) = fun s : ℝ => relDrvProc v W' s.toNNReal ω :=
      funext fun s => hWω ω hω _
    rw [hfun] at hw ⊢
    have h2 := h1 t htT w (by rw [hq]; exact hw)
    rw [hq] at h2
    rw [ht, WithTop.untopD_coe, bheProc_geom_congr _ _ _ _ _ (hWω ω hω)]
    exact h2
  · -- the hull identity
    filter_upwards [hGa] with ω hω
    exact hhull ω hω

end InteractingSLE.Theorem14.BR4aChain
