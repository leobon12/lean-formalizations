/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3GeoChart
import InteractingSLE.Spec.Supplement.SB2LkDom
import InteractingSLE.Spec.Sec7.ContinuityProb2Join
import InteractingSLE.Spec.Restart.ChartMeasHull
import InteractingSLE.Spec.Sec7.ReverseArcLift
import InteractingSLE.Spec.Supplement.SB2HEntry
import InteractingSLE.Spec.Supplement.WalkIntCanonRun

/-!
# Lemma S3's second chart for a staged prefix: the composed chart, and the lower-orientation geometry

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3 with the roles of the histories exchanged, supplement p. 631).
Deterministic. When the second history is a staged prefix (the lower walk of SB2(2)) its chart is the old run chart
composed with the Loewner chart of the current piece. This file proves that this composed chart has everything the
S3 geometry needs, and assembles the lower-orientation geometry with it:

* `cluster_of_bdd`: cluster values of a chart within bounded distance of the identity;
* **`isChartCore_comp`**: `(f_α ∘ c, ĝ ∘ Φ_α)` is a core chart of the physical prefix (domain by Lemma (T),
  `Lk.image_H_diff_fillH_of_chart`; tip fibre by `Lk.ext_notMem_image`);
* **`comp_chart_facts`**: in addition holomorphic, finite fibres, open domain, and `f + (w(q) + s₁)` maps out the
  prefix's fill (`IsMapOut.comp` with the hull model `c + s₁` and the translated Loewner map-out);
* `translate_second`; **`exists_s3_geometry_lower`**: the reflected S3 geometry (`exists_s3_geometry_of_chart_right`)
  with the composed second chart: positive limit `y` (exposed right side), the normalized second map-out, its limit
  and transition gap — the second chart of `S3.JointPhaseGaps` for SB2(2)'s lower pieces;
* **`runChart_package`**: every chart input above for the actual run chart of any staged program (domain chart,
  compact prefix, hull model, boundary map within bounded distance of the identity), except finite fibres.

R48 (as amended for Theorem 1.4): nothing here uses Theorem 1.4 or `Theorem14Statement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.SB.S3.Canon

open Geo
open Supp9B (IsProperCurve leftSide rightSide closedRightSide)

/-- **Cluster values from bounded displacement**: a map `f` of `X ⊆ ℍ` into `ℍ` within bounded distance of the
identity, with a continuous left inverse `Φ` on `ℍ̄`, has at every point a limit along every ultrafilter of `X`,
in `ℍ̄`, with `Φ` of the limit the point. -/
theorem cluster_of_bdd {X : Set ℂ} {f Φ : ℂ → ℂ} (hmaps : MapsTo f X H) {C : ℝ}
    (hb : ∀ z ∈ X, ‖f z - z‖ ≤ C) (hΦ : ContinuousOn Φ Hbar) (hinv : ∀ z ∈ X, Φ (f z) = z) :
    ∀ (U : Ultrafilter ℂ) (p : ℂ), (U : Filter ℂ) ≤ 𝓝[X] p →
      ∃ y ∈ Hbar, Tendsto f U (𝓝 y) ∧ Φ y = p := by
  intro U p hU
  have hUX : X ∈ (U : Filter ℂ) := hU self_mem_nhdsWithin
  have hUb : ball p 1 ∈ (U : Filter ℂ) := hU (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds p one_pos))
  set K : Set ℂ := closedBall 0 (‖p‖ + 1 + C) ∩ Hbar with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 _).inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hfK : ((U.map f : Ultrafilter ℂ) : Filter ℂ) ≤ 𝓟 K := by
    rw [Ultrafilter.coe_map, le_principal_iff, mem_map]
    filter_upwards [hUX, hUb] with z hz hzb
    refine ⟨?_, le_of_lt (show (0 : ℝ) < (f z).im from hmaps hz)⟩
    rw [mem_closedBall_zero_iff]
    have h1 := hb z hz
    have h2 : ‖z‖ < ‖p‖ + 1 := by
      have := norm_sub_norm_le z p
      rw [← dist_eq_norm] at this
      linarith [mem_ball.1 hzb]
    have h3 := norm_sub_norm_le (f z) z
    linarith
  obtain ⟨y, hyK, hy⟩ := hKc.ultrafilter_le_nhds (U.map f) hfK
  rw [Ultrafilter.coe_map] at hy
  refine ⟨y, hyK.2, hy, ?_⟩
  have hyw : Tendsto f (U : Filter ℂ) (𝓝[Hbar] y) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hy, ?_⟩
    filter_upwards [hUX] with z hz
    exact le_of_lt (show (0 : ℝ) < (f z).im from hmaps hz)
  have h1 : Tendsto (fun z => Φ (f z)) (U : Filter ℂ) (𝓝 (Φ y)) := (hΦ y hyK.2).tendsto.comp hyw
  have h2 : Tendsto (fun z => Φ (f z)) (U : Filter ℂ) (𝓝 p) := by
    refine (tendsto_id.mono_right (hU.trans nhdsWithin_le_nhds)).congr' ?_
    filter_upwards [hUX] with z hz
    exact (hinv z hz).symm
  exact tendsto_nhds_unique h1 h2

/-- **The composed chart is a core chart** (a staged history's prefix: an old domain chart composed with the Loewner
chart of the new piece in its coordinates). Let `c` be a domain chart of `ℍ ∖ fill P` (`P` compact) whose inverse has
a continuous extension `ĝ` to `ℍ̄` within distance `C` of the identity, and let `(f_α, Φ_α)` be a core chart of the
trace `α` up to `q` (in the coordinates of `c`) with interior tip. If the physical prefix `η([0, q'])` has the fill of
`P ∪ ĝ(α[0, q])`, contains `ĝ(α[0, q])` and every interior boundary value `ĝ(x)`, `x` real, and ends at `ĝ(α(q))`, then
`(f_α ∘ c, ĝ ∘ Φ_α)` is a core chart of `η` up to `q'`. The domain identity is Lemma (T)
(`Lk.image_H_diff_fillH_of_chart`); cluster values come from bounded displacement (`cluster_of_bdd`); the tip fibre
uses injectivity of `c⁻¹` on `ℍ` and that boundary values miss `c⁻¹(ℍ)` (`Lk.ext_notMem_image`). -/
theorem isChartCore_comp {P : Set ℂ} {c : Chart} (hD : IsDomainChart (H \ fillH P) c) (hPc : IsCompact P)
    {gc : ℂ → ℂ} (hgc : ContinuousOn gc Hbar) (hgi : EqOn gc c.2.1 H) {C : ℝ}
    (hC : ∀ p ∈ Hbar, ‖gc p - p‖ ≤ C)
    {α : ℝ≥0 → ℂ} {q : ℝ≥0} {fα Φα : ℂ → ℂ} (hch : IsChartCore α q fα Φα) (hαc : IsCompact (α '' Icc 0 q))
    (hαH : α '' Icc 0 q ⊆ Hbar) (hαq : α q ∈ H)
    {η : ℝ≥0 → ℂ} {q' : ℝ≥0} (hfill : fillH (η '' Icc 0 q') = fillH (P ∪ gc '' (α '' Icc 0 q)))
    (htip : η q' = gc (α q)) (hsub : gc '' (α '' Icc 0 q) ⊆ η '' Icc 0 q')
    (hreal : ∀ x : ℝ, gc x ∈ H → gc x ∈ η '' Icc 0 q') :
    IsChartCore η q' (fun z => fα (c.1 z)) (fun v => gc (Φα v)) := by
  have hgd : DifferentiableOn ℂ c.2.1 H := hD.isConformal.1
  have hginj : InjOn c.2.1 H := hD.isConformal.injOn
  have hdom : c.2.1 '' (H \ fillH (α '' Icc 0 q)) = H \ fillH (η '' Icc 0 q') := by
    rw [hfill]
    exact Lk.image_H_diff_fillH_of_chart hgd hginj hgc hgi hC hPc hD.image_eq hαc hαH
  have hDP : H \ fillH (η '' Icc 0 q') ⊆ H \ fillH P := by
    rw [← hdom, ← hD.image_eq]; exact image_mono sdiff_subset
  have hfw : ∀ {z}, z ∈ H \ fillH (η '' Icc 0 q') → c.1 z ∈ H \ fillH (α '' Icc 0 q) := fun {z} hz => by
    rw [← hdom] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [hD.fwd_inv hw.1]; exact hw
  have hinvf : ∀ {z}, z ∈ H \ fillH (η '' Icc 0 q') → c.2.1 (c.1 z) = z := fun {z} hz =>
    hD.inv_fwd (hDP hz)
  have hbw : ∀ {w}, w ∈ H \ fillH (α '' Icc 0 q) → c.2.1 w ∈ H \ fillH (η '' Icc 0 q') := fun {w} hw => by
    rw [← hdom]; exact mem_image_of_mem _ hw
  have hmaps : MapsTo (fun z => fα (c.1 z)) (H \ fillH (η '' Icc 0 q')) H := fun z hz => hch.maps (hfw hz)
  have hcont : ContinuousOn (fun v => gc (Φα v)) Hbar :=
    hgc.comp hch.inv_cont fun v hv => hch.inv_mem_Hbar hv
  have hinvF : ∀ z ∈ H \ fillH (η '' Icc 0 q'), gc (Φα (fα (c.1 z))) = z := fun z hz => by
    rw [hch.inv_f _ (hfw hz), hgi (hfw hz).1, hinvf hz]
  obtain ⟨Cα, hCα⟩ := hch.bdd
  have hbdd : ∀ z ∈ H \ fillH (η '' Icc 0 q'), ‖fα (c.1 z) - z‖ ≤ Cα + C := fun z hz => by
    have h1 := hCα _ (hfw hz)
    have h2 := hC _ (le_of_lt (show (0 : ℝ) < (c.1 z).im from (hfw hz).1))
    rw [hgi (hfw hz).1, hinvf hz] at h2
    have h3 : fα (c.1 z) - z = (fα (c.1 z) - c.1 z) + (c.1 z - z) := by ring
    rw [h3]
    have h4 : ‖c.1 z - z‖ = ‖z - c.1 z‖ := norm_sub_rev _ _
    linarith [norm_add_le (fα (c.1 z) - c.1 z) (c.1 z - z)]
  refine ⟨hmaps, fun z₁ hz₁ z₂ hz₂ he => ?_, ?_, ⟨Cα + C, hbdd⟩, hcont,
    fun v hv => ?_, fun v hv => ?_, hinvF, cluster_of_bdd hmaps hbdd hcont hinvF, ?_, ?_, ?_⟩
  · have := hch.injOn (hfw hz₁) (hfw hz₂) he
    rw [← hinvf hz₁, ← hinvf hz₂, this]
  · exact hch.cont.comp ((hD.differentiableOn_fwd.continuousOn).mono hDP) fun z hz => hfw hz
  · have h1 := hch.inv_mem hv
    rw [hgi h1.1]; exact hbw h1
  · have h1 := hch.inv_mem hv
    show fα (c.1 (gc (Φα v))) = v
    rw [hgi h1.1, hD.fwd_inv h1.1, hch.f_inv v hv]
  · show gc (Φα 0) = η q'
    rw [hch.tip, htip]
  · intro hq y hy
    change gc (Φα y) = η q' at hy
    rw [htip] at hy
    by_cases hyH : Φα y ∈ H
    · rw [hgi hyH, hgi hαq] at hy
      exact hch.tip_fibre hαq y (hginj hyH hαq hy)
    · exfalso
      have hy' : Φα y ∈ Hbar := hch.inv_mem_Hbar (show (0 : ℝ) ≤ ((y : ℂ)).im by simp)
      refine Lk.ext_notMem_image hgd hginj hgc hgi hy' hyH ?_
      rw [hy, hgi hαq]; exact mem_image_of_mem _ hαq
  · intro y hy
    change gc (Φα y) ∈ H at hy
    show gc (Φα y) ∈ η '' Icc 0 q'
    have hy' : Φα y ∈ Hbar := hch.inv_mem_Hbar (show (0 : ℝ) ≤ ((y : ℂ)).im by simp)
    by_cases hyH : Φα y ∈ H
    · exact hsub (mem_image_of_mem _ (hch.bdry y hyH))
    · have him : (Φα y).im = 0 := le_antisymm (not_lt.1 hyH) hy'
      have hr : Φα y = (((Φα y).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
      rw [hr] at hy ⊢
      exact hreal _ hy

/-- **The composed chart of a staged prefix** (deterministic). For a domain chart `c` of `ℍ ∖ fill P` with hull
model `c + s₁` (a mapping-out function of `fill P`) and a continuous finite-fibre boundary map `ĝ` within distance
`C` of the identity, and a generating trace `α` (continuous driver `w`) in the coordinates of `c` with interior tip
at `q`, any physical prefix `η([0, q'])` with the fill of `P ∪ ĝ(α[0, q])` (containing `ĝ(α[0, q])` and the interior
boundary values, ending at `ĝ(α(q))`) has the core chart `f = f_q ∘ c`, `Φ = ĝ ∘ Φ_q`: holomorphic, finite fibres,
open domain, and `f + (w(q) + s₁)` maps out `fill η([0, q'])`. -/
theorem comp_chart_facts {P : Set ℂ} {c : Chart} (hD : IsDomainChart (H \ fillH P) c) (hPc : IsCompact P)
    {s₁ : ℝ} (hPh : IsHPHull (fillH P)) (hmo₁ : IsMapOut (fillH P) (fun z => c.1 z + (s₁ : ℂ)))
    {gc : ℂ → ℂ} (hgc : ContinuousOn gc Hbar) (hgi : EqOn gc c.2.1 H) {C : ℝ}
    (hC : ∀ p ∈ Hbar, ‖gc p - p‖ ≤ C) (hgf : ∀ z, (gc ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite)
    {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace w ζ α)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) (hinj : InjOn α {t | (t : ℝ≥0∞) ≤ ζ})
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < ζ) (hq0 : 0 < q) (hαq : α q ∈ H)
    {η : ℝ≥0 → ℂ} {q' : ℝ≥0} (hηc : ContinuousOn η (Icc 0 q')) (hη0 : (η 0).im = 0)
    (hfill : fillH (η '' Icc 0 q') = fillH (P ∪ gc '' (α '' Icc 0 q)))
    (htip : η q' = gc (α q)) (hsub : gc '' (α '' Icc 0 q) ⊆ η '' Icc 0 q')
    (hreal : ∀ x : ℝ, gc x ∈ H → gc x ∈ η '' Icc 0 q') :
    IsChartCore η q' (fun z => fwdMap (fun r : ℝ => w r.toNNReal) q (c.1 z))
        (fun v => gc (extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) q) v)) ∧
      DifferentiableOn ℂ (fun z => fwdMap (fun r : ℝ => w r.toNNReal) q (c.1 z)) (H \ fillH (η '' Icc 0 q')) ∧
      (∀ z, ((fun v => gc (extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) q) v)) ⁻¹' {z} ∩
        {v | 0 ≤ v.im}).Finite) ∧
      IsOpen (H \ fillH (η '' Icc 0 q')) ∧
      IsMapOut (fillH (η '' Icc 0 q'))
        (fun z => fwdMap (fun r : ℝ => w r.toNNReal) q (c.1 z) + ((w q + s₁ : ℝ) : ℂ)) := by
  obtain ⟨hch, -, hαh, hmoα, hfd, hfin⟩ := secondChart_facts hα hw hw0 hinj hq hq0
  set fα := fwdMap (fun r : ℝ => w r.toNNReal) q with hfα
  set Φα := extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) q) with hΦα
  have hαc : IsCompact (α '' Icc 0 q) := isCompact_Icc.image_of_continuousOn
    (hα.2.1.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans hq.le)
  have hαH : α '' Icc 0 q ⊆ Hbar := by
    rintro _ ⟨s, hs, rfl⟩
    exact Sec7.IsGeneratingTrace.mem_Hbar hα hw hw0 ((ENNReal.coe_le_coe.2 hs.2).trans hq.le)
  have hcore := isChartCore_comp hD hPc hgc hgi hC (IsChart.toCore hch) hαc hαH hαq hfill htip hsub hreal
  have hgd : DifferentiableOn ℂ c.2.1 H := hD.isConformal.1
  have hginj : InjOn c.2.1 H := hD.isConformal.injOn
  have hdom : c.2.1 '' (H \ fillH (α '' Icc 0 q)) = H \ fillH (η '' Icc 0 q') := by
    rw [hfill]
    exact Lk.image_H_diff_fillH_of_chart hgd hginj hgc hgi hC hPc hD.image_eq hαc hαH
  -- the physical prefix is a hull
  have hηK : IsCompact (η '' Icc 0 q') := isCompact_Icc.image_of_continuousOn hηc
  have hηconn : IsPreconnected (η '' Icc 0 q' ∪ Restart.lowerHalf) := by
    refine (isPreconnected_Icc.image _ hηc).union (η 0) ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩ ?_
      (convex_halfSpace_le (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected
    show (η 0).im ≤ 0
    rw [hη0]
  have hBh : IsHPHull (fillH (η '' Icc 0 q')) := Restart.isHPHull_fillH_of_compact hηK hηconn
  have hAB : fillH P ⊆ fillH (η '' Icc 0 q') := by
    rw [hfill]; exact fillH_mono subset_union_left
  -- the new part of the hull is the image of the trace's fill
  have hBA : fillH (η '' Icc 0 q') \ fillH P = c.2.1 '' fillH (α '' Icc 0 q) := by
    ext z
    constructor
    · rintro ⟨hzB, hzA⟩
      have hzH : z ∈ H := fillH_subset_H _ hzB
      have hz1 : z ∈ c.2.1 '' H := by rw [hD.image_eq]; exact ⟨hzH, hzA⟩
      obtain ⟨v, hv, rfl⟩ := hz1
      refine ⟨v, ?_, rfl⟩
      by_contra hvn
      have : c.2.1 v ∈ H \ fillH (η '' Icc 0 q') := by rw [← hdom]; exact ⟨v, ⟨hv, hvn⟩, rfl⟩
      exact this.2 hzB
    · rintro ⟨v, hv, rfl⟩
      have hvH : v ∈ H := fillH_subset_H _ hv
      have h1 : c.2.1 v ∈ H \ fillH P := by rw [← hD.image_eq]; exact mem_image_of_mem _ hvH
      refine ⟨?_, h1.2⟩
      by_contra hn
      have h2 : c.2.1 v ∈ c.2.1 '' (H \ fillH (α '' Icc 0 q)) := by rw [hdom]; exact ⟨h1.1, hn⟩
      obtain ⟨v', hv', he⟩ := h2
      rw [hginj hv'.1 hvH he] at hv'
      exact hv'.2 hv
  have himg : (fun z => c.1 z + (s₁ : ℂ)) '' (fillH (η '' Icc 0 q') \ fillH P) =
      (fun z => z + (s₁ : ℂ)) '' fillH (α '' Icc 0 q) := by
    rw [hBA, image_image]
    refine image_congr fun v hv => ?_
    rw [hD.fwd_inv (fillH_subset_H _ hv)]
  have hgC := Sec7.ReverseArc.isMapOut_translate hmoα s₁
  rw [← himg] at hgC
  have hcomp := hmo₁.comp hPh hBh hAB hgC
  have hfun : ((fun v => fα (v - (s₁ : ℂ)) + (w q : ℂ) + (s₁ : ℂ)) ∘ fun z => c.1 z + (s₁ : ℂ)) =
      fun z => fα (c.1 z) + ((w q + s₁ : ℝ) : ℂ) := by
    funext z
    simp only [Function.comp_apply, add_sub_cancel_right, Complex.ofReal_add]
    ring
  rw [hfun] at hcomp
  -- domain facts
  have hDP : H \ fillH (η '' Icc 0 q') ⊆ H \ fillH P := fun z hz => ⟨hz.1, fun h => hz.2 (hAB h)⟩
  have hfw : ∀ {z}, z ∈ H \ fillH (η '' Icc 0 q') → c.1 z ∈ H \ fillH (α '' Icc 0 q) := fun {z} hz => by
    rw [← hdom] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    rw [hD.fwd_inv hv.1]; exact hv
  refine ⟨hcore, ?_, ?_, hBh.2.2.1, hcomp⟩
  · exact hfd.comp (hD.differentiableOn_fwd.mono hDP) fun z hz => hfw hz
  · intro z
    refine ((hgf z).biUnion fun x _ => hfin x).subset fun v hv => ?_
    obtain ⟨hvz, hvi⟩ := hv
    have hΦv : Φα v ∈ Hbar := (IsChart.toCore hch).inv_mem_Hbar hvi
    exact mem_iUnion₂.2 ⟨Φα v, ⟨hvz, hΦv⟩, rfl, hvi⟩

/-- Translating a chart by a real constant moves its limit and its transition gap. -/
theorem translate_second {f : ℂ → ℂ} {F : Filter ℂ} {y : ℝ} {X : Set ℂ} {r : ℝ} (κ₂ : ℝ)
    (hfy : Tendsto f F (𝓝[H] (y : ℂ))) (hgap : Disjoint (ball (y : ℂ) r) (f '' X)) :
    Tendsto (fun z => f z + (κ₂ : ℂ)) F (𝓝[H] ((y + κ₂ : ℝ) : ℂ)) ∧
      Disjoint (ball ((y + κ₂ : ℝ) : ℂ) r) ((fun z => f z + (κ₂ : ℂ)) '' X) := by
  have htrans : Tendsto (fun v : ℂ => v + (κ₂ : ℂ)) (𝓝[H] (y : ℂ)) (𝓝[H] ((y + κ₂ : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc' : Continuous fun v : ℂ => v + (κ₂ : ℂ) := continuous_id.add continuous_const
      have h := (hc'.tendsto (y : ℂ)).mono_left (nhdsWithin_le_nhds (s := H))
      rwa [← Complex.ofReal_add] at h
    · filter_upwards [self_mem_nhdsWithin] with v hv
      show (0 : ℝ) < (v + (κ₂ : ℂ)).im
      rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact hv
  refine ⟨htrans.comp hfy, ?_⟩
  rw [Set.disjoint_left]
  rintro _ hu ⟨z, hz, rfl⟩
  refine Set.disjoint_left.1 hgap ?_ ⟨z, hz, rfl⟩
  rw [mem_ball, Complex.dist_eq] at hu ⊢
  have he : ∀ v : ℂ, v + (κ₂ : ℂ) - ((y + κ₂ : ℝ) : ℂ) = v - (y : ℂ) := fun v => by
    rw [Complex.ofReal_add]; ring
  simp only [he] at hu
  exact hu

/-- **The S3 geometry for the lower orientation with a composed second chart** (Lemma S3 with the roles of the
histories exchanged, SB2(2)'s lower pieces; supplement p. 631). On the reflected S2 lift (old history on the closed
left of the proper witness `β₀`, right entry chart at `R`), for every common arc `β₀(t_R + [a, b]) ⊆ A` with interior
end and every `t ∈ (a, b)`, the approach `F = g_*(𝓝[ℍ] γ(t))` is on the right of `β₀`, in the joint domain, with both
component accesses; and for **every** staged description of the witness prefix — an old domain chart `c` of
`ℍ ∖ fill P` with hull model `c + s₁`, a finite-fibre boundary map within bounded distance of the identity, and the
current piece's generating trace `α` (interior tip at `q`) in the coordinates of `c`, with `fill β₀[0, t_R + b] =
fill(P ∪ ĝ(α[0, q]))` and the bookkeeping identities of `comp_chart_facts` — the normalized second map-out
`f_q ∘ c + (w(q) + s₁)` of `fill β₀[0, t_R + b]` tends along `F` to `y + w(q) + s₁` from `ℍ`, with `y > 0` (the exposed
right side) and `ĝ(Φ_q(y))` the physical point, and a ball about the limit misses the transition hull. -/
theorem exists_s3_geometry_lower {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0) (hA : p '' Icc 0 1 ⊆ closedLeftSide β₀)
    {c₀ : Chart} {g : ℂ → ℂ} (hc : IsRightEntryChart (p '' Icc 0 1) (realMax (p '' Icc 0 1)) c₀)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c₀.2.1 H)
    (hgf : ∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) :
    ∃ (tR : ℝ≥0) (γ : ℝ≥0 → ℂ),
      β₀ tR = realMax (p '' Icc 0 1) ∧ IsProperCurve γ ∧ γ 0 = 0 ∧ (∀ s, g (γ s) = β₀ (tR + s)) ∧
      ∀ a b t : ℝ≥0, t ∈ Ioo a b → β₀ '' Icc (tR + a) (tR + b) ⊆ p '' Icc 0 1 → β₀ (tR + b) ∈ H →
        (γ t).re < 0 ∧ (𝓝[H] (γ t)).NeBot ∧
        Filter.map g (𝓝[H] (γ t)) ≤ 𝓟 (rightSide β₀ ∩ (H \ fillH (p '' Icc 0 1 ∪ β₀ '' Icc 0 (tR + b)))) ∧
        Filter.map g (𝓝[H] (γ t)) ≤ 𝓝[H \ fillH (p '' Icc 0 1 ∪ β₀ '' Icc 0 (tR + b))] (β₀ (tR + t)) ∧
        (∀ S T : Set ℂ, β₀ '' Icc (tR + a) (tR + b) ⊆ S →
          S ⊆ fillH (p '' Icc 0 1 ∪ β₀ '' Icc 0 (tR + b)) → T ⊆ fillH (p '' Icc 0 1 ∪ β₀ '' Icc 0 (tR + b)) →
          ∃ r > 0, Filter.map g (𝓝[H] (γ t)) ≤ 𝓝[FinRel.freeNear T S (β₀ (tR + t)) r] (β₀ (tR + t))) ∧
        ∀ {P : Set ℂ} {c : Chart} {s₁ : ℝ} {gc : ℂ → ℂ} {C : ℝ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {α : ℝ≥0 → ℂ}
          {q : ℝ≥0}, IsDomainChart (H \ fillH P) c → IsCompact P → IsHPHull (fillH P) →
          IsMapOut (fillH P) (fun z => c.1 z + (s₁ : ℂ)) → ContinuousOn gc Hbar → EqOn gc c.2.1 H →
          (∀ p ∈ Hbar, ‖gc p - p‖ ≤ C) → (∀ z, (gc ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) →
          IsGeneratingTrace w ζ α → ContinuousOn w {s | (s : ℝ≥0∞) < ζ} → w 0 = 0 →
          InjOn α {t | (t : ℝ≥0∞) ≤ ζ} → (q : ℝ≥0∞) < ζ → 0 < q → α q ∈ H →
          fillH (β₀ '' Icc 0 (tR + b)) = fillH (P ∪ gc '' (α '' Icc 0 q)) → β₀ (tR + b) = gc (α q) →
          gc '' (α '' Icc 0 q) ⊆ β₀ '' Icc 0 (tR + b) →
          (∀ x : ℝ, gc x ∈ H → gc x ∈ β₀ '' Icc 0 (tR + b)) →
          IsMapOut (fillH (β₀ '' Icc 0 (tR + b)))
              (fun z => fwdMap (fun r : ℝ => w r.toNNReal) q (c.1 z) + ((w q + s₁ : ℝ) : ℂ)) ∧
            ∃ y : ℝ, 0 < y ∧ gc (extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) q) y) = β₀ (tR + t) ∧
              Tendsto (fun z => fwdMap (fun r : ℝ => w r.toNNReal) q (c.1 z) + ((w q + s₁ : ℝ) : ℂ))
                (Filter.map g (𝓝[H] (γ t))) (𝓝[H] ((y + (w q + s₁) : ℝ) : ℂ)) ∧
              ∃ r > 0, Disjoint (ball ((y + (w q + s₁) : ℝ) : ℂ) r)
                ((fun z => fwdMap (fun r : ℝ => w r.toNNReal) q (c.1 z) + ((w q + s₁ : ℝ) : ℂ)) ''
                  (fillH (p '' Icc 0 1 ∪ β₀ '' Icc 0 (tR + b)) \ fillH (β₀ '' Icc 0 (tR + b)))) := by
  obtain ⟨tR, γ, htR, hγ, hγ0, hlift, hall⟩ :=
    exists_s3_geometry_of_chart_right hp hp0 hpH hβ hβ0 hA hc hgc hgi hgf
  refine ⟨tR, γ, htR, hγ, hγ0, hlift, fun a b t ht harc hqH => ?_⟩
  obtain ⟨hneg, hne, hFR, hFJ, hacc, hsec⟩ := hall a b t ht harc hqH
  refine ⟨hneg, hne, hFR, hFJ, hacc, fun {P c s₁ gc C w ζ α q} hD hPc hPh hmo₁ hgc' hgi' hC hgf' hα hw hw0 hinj
    hq hq0 hαq hfill htip hsub hreal => ?_⟩
  have hη0 : (β₀ 0).im = 0 := by rw [hβ0, Complex.zero_im]
  obtain ⟨hcore, hfd, hfin, hDo, hmo⟩ := comp_chart_facts hD hPc hPh hmo₁ hgc' hgi' hC hgf' hα hw hw0 hinj hq hq0
    hαq hβ.1.continuousOn hη0 hfill htip hsub hreal
  obtain ⟨y, hy0, hΦy, hfy, r, hr, hgap⟩ := hsec hcore hfd hfin hDo
  obtain ⟨hT, hG⟩ := translate_second (w q + s₁) hfy hgap
  exact ⟨hmo, y, hy0, hΦy, hT, r, hr, hG⟩

open Exist.Staged Exist.StagedLaw in
/-- **The chart package of an actual run** (any staged program with regular launched pieces, at a state that is not
finished): the run chart is a domain chart of the unbounded domain of the compact physical prefix `P`, `fill P` is a
hull mapped out by the chart shifted by a real `s₁` (its hull model), and the inverse has a continuous boundary map
`ĝ` on `ℍ̄` with linear growth, boundary limits, and within bounded distance of the identity — every chart input of
`comp_chart_facts` / `exists_s3_geometry_lower` except the finite fibres (which need the prefix path, e.g.
`Lk.pinv_schedule`, `LuM.pinv_prefix_walk` with `Lk.finite_fibre_of_pinv`). -/
theorem runChart_package {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) :
    ∃ (s₁ : ℝ) (gc : ℂ → ℂ) (C : ℝ),
      IsDomainChart (H \ fillH (prefixPhysSet κ b jumps spec D n)) (stChart (ExplState.run κ b jumps spec D n)) ∧
      IsCompact (prefixPhysSet κ b jumps spec D n) ∧ IsHPHull (fillH (prefixPhysSet κ b jumps spec D n)) ∧
      IsMapOut (fillH (prefixPhysSet κ b jumps spec D n))
        (fun z => (stChart (ExplState.run κ b jumps spec D n)).1 z + (s₁ : ℂ)) ∧
      ContinuousOn gc Hbar ∧ EqOn gc (stChart (ExplState.run κ b jumps spec D n)).2.1 H ∧
      (∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖gc w‖ + C₂) ∧
      (∀ q ∈ Hbar, Tendsto (stChart (ExplState.run κ b jumps spec D n)).2.1 (𝓝[H] q) (𝓝 (gc q))) ∧
      ∀ q ∈ Hbar, ‖gc q - q‖ ≤ C := by
  set c := stChart (ExplState.run κ b jumps spec D n) with hcdef
  have hD := Lw.isDomainChart_runChart (κ := κ) (b := b) (jumps := jumps) spec D hreg n hnot
  have hPc := Lx.isCompact_prefixPhysSet_run spec D hreg n hnot
  obtain ⟨M, hM⟩ := Lw.exists_hullModel_fill (κ := κ) (b := b) (jumps := jumps) spec D hreg n hnot
  have hcc : c.IsConformal :=
    (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) spec D n fun j _ c θ h => hreg j c θ h).1
  obtain ⟨gc, hgc, hgi, hgb, hgt⟩ :=
    Lw.exists_bdryMap_of_hasProperBdryExt hcc (GW1P.isClosed_pieces_run spec D hreg n).1
  have hN := WalkIntCanon.isNormalized_runChart (κ := κ) (b := b) (jumps := jumps) spec D n
    fun j _ c θ h => hreg j c θ h
  obtain ⟨C, hC⟩ := hN.inverse_bound
  refine ⟨M.shift, gc, C, hD, hPc, hM ▸ M.isHull, hM ▸ M.mapOut, hgc, hgi, hgb, hgt, fun q hq => ?_⟩
  have hne : (𝓝[H] q).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hq
  have hlim : Tendsto (fun z => c.2.1 z - z) (𝓝[H] q) (𝓝 (gc q - q)) :=
    (hgt q hq).sub (tendsto_id.mono_left nhdsWithin_le_nhds)
  exact le_of_tendsto hlim.norm (eventually_nhdsWithin_of_forall fun z hz => hC z hz)

end InteractingSLE.Theorem14.SB.S3.Canon
