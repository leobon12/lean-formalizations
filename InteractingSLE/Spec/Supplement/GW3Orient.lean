/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Prop74BOrient
import InteractingSLE.Spec.Supplement.GW3Chart

/-!
# Lemma GW3, the orientation of the component charts

Packet PROVE-ORIENT. The named geometry input `Theorem14.GW3.GW3GeometryStatement` (PROVE-T14-GW4) asks, for every
component `C` between the boundary walks, for a bounded two-arc Jordan component or an **oriented uniformizer**
(`GW3.HasOrientedUniformizer`: a conformal map `C → ℍ` whose inverse tends to a point of `R` at positive and of `L` at
negative real points). For an unbounded component the chart must send `∞` to `∞`, so the orientation is genuine
content (p. 636; GB13a's winding-number argument, p. 559). Here the orientation is proved.

## Main results

* **`hasOrientedUniformizer_of_mem_betweenComponents`** (unconditional, deterministic): for simple proper walls
  (`Lemma71I.IsSimpleProper`: from `0`, in `ℍ` at positive times) with `L` on the closed left side of `R`, every
  component between them (bounded or not) has an oriented uniformizer. Chart: the two-point uniformizer of the marked
  pocket (`Lemma71F.exists_twoPoint_uniformizer_ext_of_jordan`); orientation: `Prop74B.pocketChartOrientationStatement`;
  boundary correspondence: `Prop74B.pocketInv_boundary`.
* **`hasOrientedUniformizer_of_crossLoop`** (deterministic, for walls that may touch `ℝ`, as the GW1 walks with their
  original-real connectors do): a marked pocket `C` of a proper curve `R` from `0` with frontier on `R ∪ L`, on the left
  of `R` and reachable from the right of `R` (the two topological inputs of `Prop74B.re_pos_of_crossLoop`), has an
  oriented uniformizer.
* `windNum_crossLoop_of_subset_leftSideOf`, `exists_right_of_component`, `exists_right_of_norm_eq_one`: the two inputs
  from the sides of `R`; **`hasOrientedUniformizer_of_sides`** combines them;
* **`gw3GeometryStatement_of_sided`**: `GW3GeometryStatement` follows from `GW3GeometrySidedStatement`, the same
  almost-sure geometry with `HasOrientedUniformizer` replaced by the purely topological `IsSidedWallPocket`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Function Bornology Metric
open QuantumZipper (H Hbar isOpen_H)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal Real
open MeasureTheory

universe u

namespace InteractingSLE.Theorem14.GW3

open Sec7.Lemma71K (IsMarkedPocket wallPt)
open Sec7.Prop74B (pocketInv pocketInv_boundary pocketChartOrientationStatement)
open WangWu (semiArc crossRange)
open _root_.InteractingSLE.Orientation

/-- The inverse of a chart `f` with an extended inverse `G` continuous on `ℍ̄`: boundary limits at real points. -/
theorem tendsto_invFunOn_of_pocketInv {C : Set ℂ} {f G : ℂ → ℂ} (hf : IsConformalBijection f C H)
    (hGc : ContinuousOn G Hbar) (hGinv : ∀ w ∈ H, ∀ z ∈ C, f z = w → G w = z) (x : ℝ) :
    Tendsto (invFunOn f C) (𝓝[H] (x : ℂ)) (𝓝 (G x)) := by
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have h1 : Tendsto G (𝓝[H] (x : ℂ)) (𝓝 (G x)) :=
    ((hGc _ hxH).mono fun w hw => Sec7.Prop74B.mem_Hbar_of_mem_H hw).tendsto
  refine h1.congr' (eventually_nhdsWithin_of_forall fun w hw => ?_)
  exact hGinv w hw _ (invFunOn_mem (hf.2.surjOn hw)) (invFunOn_eq (hf.2.surjOn hw))

/-- **Components between simple proper walls have oriented uniformizers** (Lemma GW3's common-lift chart, every
component, bounded or not). -/
theorem hasOrientedUniformizer_of_mem_betweenComponents {R L : ℝ≥0 → ℂ} (hR : Sec7.Lemma71I.IsSimpleProper R)
    (hL : Sec7.Lemma71I.IsSimpleProper L) (hLR : range L ⊆ closedLeftSide R) {C : Set ℂ}
    (hC : C ∈ betweenComponents (range R) (range L)) : HasOrientedUniformizer (range R) (range L) C := by
  have hCsub := Sec7.Prop74B.subset_of_mem_betweenComponents hC
  have hCH : C ⊆ H := fun z hz => (hCsub hz).1
  have hRc : IsClosed (range R) :=
    Sec7.Lemma71I.arcRange_realPath R ▸ (Sec7.Lemma71I.IsSimpleProper.isProperArc hR).isClosed_arcRange
  have hLc : IsClosed (range L) :=
    Sec7.Lemma71I.arcRange_realPath L ▸ (Sec7.Lemma71I.IsSimpleProper.isProperArc hL).isClosed_arcRange
  obtain ⟨z₀, hz₀, -, -, hCz⟩ := id hC
  have hCo : IsOpen C := hCz ▸ (isOpen_H.sdiff (hRc.union hLc)).connectedComponentIn
  have hCc : IsConnected C := hCz ▸ isConnected_connectedComponentIn_iff.2 hz₀
  have hord := Sec7.Lemma71I.disjoint_rightSideOf_of_subset_closedLeftSide hR.isProperCurve hR.2.2.1 hLR
  obtain ⟨a, b, hM⟩ := Sec7.Lemma71K.isMarkedPocket_of_mem_betweenComponents hR hL hord hC
  obtain ⟨-, -, -, -, hJ, hpa, hpb, hpq⟩ := id hM
  obtain ⟨Ψ, hΨ, hΨc, hΨi, hΨH, hΨ0, hΨinf⟩ := Sec7.Lemma71F.exists_twoPoint_uniformizer_ext_of_jordan
    (Sec7.Lemma71F.isOpen_cayley_image hCo hCH) (Sec7.Lemma71F.isConnected_cayley_image hCc hCH)
    (Sec7.Lemma71F.isBounded_cayley_image hCH) hJ hpa hpb hpq
  have hf : IsConformalBijection (Ψ ∘ cayley) C H :=
    isConformalBijection_comp hΨ (Sec7.Lemma71F.isConformalBijection_cayley_image hCH)
  have hΨf : ∀ x ∈ C, (Ψ ∘ cayley) x = Ψ (cayley x) := fun _ _ => rfl
  have hor := pocketChartOrientationStatement R L hR hL hLR C hC a b hM (Ψ ∘ cayley) Ψ hf hΨc hΨi hΨH hΨ0 hΨinf
    hΨf
  obtain ⟨hGc, -, hGinv, hGL, hGR, -⟩ :=
    pocketInv_boundary hR hL hLR hCo hC hM hf hΨc hΨi hΨH hΨ0 hΨinf hΨf hor
  exact ⟨hCo, hCH, Ψ ∘ cayley, hf, fun x => ⟨_, tendsto_invFunOn_of_pocketInv hf hGc hGinv x,
    fun hx => hGR x hx, fun hx => hGL x hx⟩⟩

/-- **Components between simple proper walls have component charts** (the frozen `IsComponentChart`). -/
theorem exists_isComponentChart_of_mem_betweenComponents {R L : ℝ≥0 → ℂ} (hR : Sec7.Lemma71I.IsSimpleProper R)
    (hL : Sec7.Lemma71I.IsSimpleProper L) (hLR : range L ⊆ closedLeftSide R) {C : Set ℂ}
    (hC : C ∈ betweenComponents (range R) (range L)) : ∃ c : Chart, IsComponentChart (range R) (range L) C c :=
  exists_isComponentChart_of_hasOrientedUniformizer (hasOrientedUniformizer_of_mem_betweenComponents hR hL hLR hC)

/-! ### Walls that may touch the real line -/

section Wall

variable {R : ℝ≥0 → ℂ}

theorem realPath_mem_Hbar (hR : Supp9B.IsProperCurve R) (t : ℝ) : Sec7.Lemma71I.realPath R t ∈ Hbar :=
  hR.2.2.1 _

/-- **The disc picture of a proper curve from `0`** (in `ℍ̄`, possibly touching `ℝ`): `wallPt R` is continuous and
injective on `[0, 1]`, from `−1` to `1`, in the closed disc. -/
theorem wallPt_props (hR : Supp9B.IsProperCurve R) (hR0 : R 0 = 0) :
    ContinuousOn (wallPt R) (Icc 0 1) ∧ InjOn (wallPt R) (Icc 0 1) ∧ wallPt R 0 = -1 ∧ wallPt R 1 = 1 ∧
      wallPt R '' Icc 0 1 ⊆ closedBall 0 1 := by
  set γ := Sec7.Lemma71I.realPath R with hγ
  have hγc : ContinuousOn γ (Ici 0) := (hR.1.comp continuous_real_toNNReal).continuousOn
  have hγH : ∀ t, γ t ∈ Hbar := realPath_mem_Hbar hR
  have hγi : InjOn γ (Ici 0) := fun s hs t ht hst => by
    have h := hR.2.1 hst
    rw [← Real.coe_toNNReal s hs, ← Real.coe_toNNReal t ht, h]
  have hγinf : Tendsto γ atTop (cobounded ℂ) :=
    tendsto_norm_atTop_iff_cobounded.1 (hR.2.2.2.comp tendsto_real_toNNReal_atTop)
  have hw : ∀ s, wallPt R s = WangWu.toDisc γ s := fun s => rfl
  have h0 : WangWu.arcTime 0 = 0 := by simp [WangWu.arcTime]
  have hIco : ContinuousOn (WangWu.toDisc γ) (Ico 0 1) := by
    have h1 : ContinuousOn (fun s => cayley (γ (WangWu.arcTime s))) (Ico 0 1) := by
      intro s hs
      have hγs : ContinuousWithinAt (fun s => γ (WangWu.arcTime s)) (Ico 0 1) s :=
        (hγc (WangWu.arcTime s) (WangWu.arcTime_nonneg hs)).comp
          ((WangWu.continuousOn_arcTime s hs.2).mono fun u hu => hu.2) fun u hu => WangWu.arcTime_nonneg hu
      exact ContinuousAt.comp_continuousWithinAt (f := fun s => γ (WangWu.arcTime s)) (g := cayley)
        (WangWu.continuousAt_cayley_of_mem_Hbar (hγH _)) hγs
    exact h1.congr fun s hs => WangWu.toDisc_of_lt hs.2
  refine ⟨fun s hs => ?_, fun s hs s' hs' h => ?_, ?_, WangWu.toDisc_one γ, ?_⟩
  · show ContinuousWithinAt (WangWu.toDisc γ) (Icc 0 1) s
    rcases eq_or_lt_of_le hs.2 with h | h
    · subst h
      refine ContinuousWithinAt.mono ?_ (fun u hu => mem_Iic.2 hu.2)
      refine continuousWithinAt_Iio_iff_Iic.1 ?_
      have ht : Tendsto (fun s => cayley (γ (WangWu.arcTime s))) (𝓝[<] 1) (𝓝 1) :=
        QuantumZipper.CA.tendsto_cayley_cobounded.comp (hγinf.comp WangWu.tendsto_arcTime)
      rw [ContinuousWithinAt, WangWu.toDisc_one]
      refine ht.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (WangWu.toDisc_of_lt (mem_Iio.1 hu)).symm
    · refine (hIco s ⟨hs.1, h⟩).mono_of_mem_nhdsWithin ?_
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds h)] with u hu hu'
      exact ⟨hu.1, hu'⟩
  · rw [hw, hw] at h
    rcases eq_or_lt_of_le hs.2 with h1 | h1 <;> rcases eq_or_lt_of_le hs'.2 with h1' | h1'
    · rw [h1, h1']
    · rw [h1, WangWu.toDisc_one, WangWu.toDisc_of_lt h1'] at h
      exact absurd h.symm (WangWu.cayley_ne_one_of_Hbar (hγH _))
    · rw [h1', WangWu.toDisc_one, WangWu.toDisc_of_lt h1] at h
      exact absurd h (WangWu.cayley_ne_one_of_Hbar (hγH _))
    · rw [WangWu.toDisc_of_lt h1, WangWu.toDisc_of_lt h1'] at h
      have h2 := WangWu.cayley_injOn_Hbar (hγH _) (hγH _) h
      have h3 := hγi (mem_Ici.2 (WangWu.arcTime_nonneg ⟨hs.1, h1⟩))
        (mem_Ici.2 (WangWu.arcTime_nonneg ⟨hs'.1, h1'⟩)) h2
      exact WangWu.strictMonoOn_arcTime.injOn ⟨hs.1, h1⟩ ⟨hs'.1, h1'⟩ h3
  · rw [hw, WangWu.toDisc_of_lt one_pos, h0, hγ, Sec7.Lemma71I.realPath, Real.toNNReal_zero, hR0, WangWu.cayley_zero]
  · rintro _ ⟨s, hs, rfl⟩
    rw [hw]
    rcases eq_or_lt_of_le hs.2 with h | h
    · rw [h, WangWu.toDisc_one, mem_closedBall, dist_zero_right, norm_one]
    · rw [WangWu.toDisc_of_lt h]
      exact QuantumZipper.CA.cayley_mem_closedBall (hγH _)

/-- A point of `ℍ̄` whose Cayley image lies on the disc picture of the wall lies on the wall. -/
theorem mem_range_of_cayley_mem_wallPt_image (hR : Supp9B.IsProperCurve R) {z : ℂ} (hz : z ∈ Hbar)
    (h : cayley z ∈ wallPt R '' Icc 0 1) : z ∈ range R := by
  obtain ⟨s, -, hs⟩ := h
  exact Sec7.Prop74B.mem_range_of_cayley_eq_toDisc hR.2.2.1 hz hs.symm

/-- **An oriented uniformizer for a pocket of a wall that may touch `ℝ`.** Let `R` be a proper curve from `0` in `ℍ̄`
(the right wall; it may contain real intervals) and `L ⊆ ℍ̄` (the left wall). Let `C ⊆ ℍ` be open and connected, off
`R`, a marked pocket `[a, b]` of `R` whose Cayley frontier lies on `R̃([a, b]) ∪ cayley(L)`. If `C` is on the left of
`R` and some point of the open arc `R̃((a, b))` is reached from the right of `R` (the two topological inputs of
`Prop74B.re_pos_of_crossLoop`), then the two-point chart of the pocket is an oriented uniformizer. -/
theorem hasOrientedUniformizer_of_crossLoop {R : ℝ≥0 → ℂ} (hR : Supp9B.IsProperCurve R) (hR0 : R 0 = 0)
    {L C : Set ℂ} (hLH : L ⊆ Hbar) (hCo : IsOpen C) (hCc : IsConnected C) (hCH : C ⊆ H)
    (hCR : Disjoint C (range R)) {a b : ℝ} (hM : IsMarkedPocket R C a b)
    (hfr : frontier (cayley '' C) ⊆ wallPt R '' Icc a b ∪ cayley '' L)
    (hleft : ∀ z ∈ cayley '' C, windNum (crossLoop (wallPt R)) z = 1)
    (hright : ∃ p ∈ wallPt R '' Ioo a b, p ∉ semiArc 1 ∧ ∃ V : Set ℂ, IsPreconnected V ∧ ¬ IsBounded V ∧
      p ∈ closure V ∧ Disjoint V (closure (cayley '' C) ∪ wallPt R '' Icc 0 1 ∪ semiArc 1)) :
    HasOrientedUniformizer (range R) L C := by
  obtain ⟨hαc, hαi, hα0, hα1, -⟩ := wallPt_props hR hR0
  obtain ⟨ha0, hab, hb1, hI, hJ, hpa, hpb, hpq⟩ := id hM
  obtain ⟨Ψ, hΨ, hΨc, hΨi, hΨH, hΨ0, hΨinf⟩ := Sec7.Lemma71F.exists_twoPoint_uniformizer_ext_of_jordan
    (Sec7.Lemma71F.isOpen_cayley_image hCo hCH) (Sec7.Lemma71F.isConnected_cayley_image hCc hCH)
    (Sec7.Lemma71F.isBounded_cayley_image hCH) hJ hpa hpb hpq
  have hf : IsConformalBijection (Ψ ∘ cayley) C H :=
    isConformalBijection_comp hΨ (Sec7.Lemma71F.isConformalBijection_cayley_image hCH)
  have hΨf : ∀ x ∈ C, (Ψ ∘ cayley) x = Ψ (cayley x) := fun _ _ => rfl
  have hCα : ∀ x ∈ C, cayley x ∉ wallPt R '' Icc 0 1 := fun x hx h =>
    Set.disjoint_left.1 hCR hx
      (mem_range_of_cayley_mem_wallPt_image hR (Sec7.Prop74B.mem_Hbar_of_mem_H (hCH hx)) h)
  have hor := Sec7.Prop74B.re_pos_of_crossLoop hαc hαi hα0 hα1 hCo hCc.isPreconnected hCH hCα ha0 hab hb1 hI hf
    hΨc hΨi hΨH hΨ0 hΨinf hΨf hleft hright
  -- the extended inverse chart
  set q := wallPt R b with hq
  set U := cayley '' C with hU
  set E := closure U \ {q} with hE
  have hqC : ∀ x ∈ C, cayley x ≠ q := fun x hx h => hCα x hx ⟨b, ⟨ha0.trans hab.le, hb1⟩, h.symm⟩
  have hIcc : Icc a b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha0 hb1
  have hcl : ∀ s ∈ Icc a b, wallPt R s ∈ closure U := fun s hs => by
    have hmem : s ∈ {s ∈ Icc (0 : ℝ) 1 | wallPt R s ∈ closure U} := by rw [hI]; exact hs
    exact hmem.2
  have hq1 : (1 : ℂ) ∈ closure U → q = 1 := fun h1 => by
    have hmem : (1 : ℝ) ∈ {s ∈ Icc (0 : ℝ) 1 | wallPt R s ∈ closure U} :=
      ⟨⟨zero_le_one, le_rfl⟩, by rw [hα1]; exact h1⟩
    rw [hI] at hmem
    rw [hq, le_antisymm hb1 hmem.2, hα1]
  obtain ⟨hGc, -, hGinv, hGcl⟩ := Sec7.Prop74B.pocketInv_props hCH hf hqC hΨc hΨi hΨH hΨinf hΨf hq1
  have hspec := fun {z : ℂ} (hz : z ∈ Hbar) =>
    Sec7.Prop74B.invFunOn_boundaryMap_spec hCH hf hqC hΨc hΨH hΨinf hΨf hz
  set G := pocketInv Ψ E with hG
  have hxH : ∀ x : ℝ, (x : ℂ) ∈ Hbar := fun x => show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hGE : ∀ x : ℝ, cayley (G x) ∈ E ∧ Ψ (cayley (G x)) = x := fun x => by
    obtain ⟨-, h1, h2⟩ := hGcl x (hxH x)
    exact ⟨h1 ▸ (hspec (hxH x)).1, h2⟩
  have hGHbar : ∀ x : ℝ, G x ∈ Hbar := fun x =>
    (closure_mono hCH).trans QuantumZipper.CA.Car.closure_H_eq_Hbar.le (hGcl x (hxH x)).1
  have hwE : ∀ s ∈ Ico a b, wallPt R s ∈ E := fun s hs =>
    ⟨hcl s (Ico_subset_Icc_self hs), fun hsq => hs.2.ne
      (hαi (hIcc (Ico_subset_Icc_self hs)) (hIcc (right_mem_Icc.2 hab.le)) hsq)⟩
  refine ⟨hCo, hCH, Ψ ∘ cayley, hf, fun x => ⟨G x, tendsto_invFunOn_of_pocketInv hf hGc hGinv x,
    fun hx => ?_, fun hx => ?_⟩⟩
  · -- positive points: the intermediate value theorem along the open right-wall arc
    have hreal : ∀ s ∈ Ico a b, (Ψ (wallPt R s)).im = 0 := fun s hs => by
      have h0 : 0 ≤ (Ψ (wallPt R s)).im := hΨH (hwE s hs)
      refine le_antisymm (not_lt.1 fun hpos => ?_) h0
      obtain ⟨z, hz, hzw⟩ := hf.2.surjOn (show Ψ (wallPt R s) ∈ H from hpos)
      have hzE : cayley z ∈ E := ⟨subset_closure ⟨z, hz, rfl⟩, hqC z hz⟩
      have h1 : wallPt R s = cayley z := hΨi (hwE s hs) hzE (by rw [← hΨf z hz, hzw])
      exact hCα z hz ⟨s, hIcc (Ico_subset_Icc_self hs), h1⟩
    have hcont : ContinuousOn (fun s => Ψ (wallPt R s)) (Ico a b) :=
      hΨc.comp (hαc.mono (Ico_subset_Icc_self.trans hIcc)) hwE
    have hbI : b ∈ Icc (0 : ℝ) 1 := hIcc (right_mem_Icc.2 hab.le)
    have hlimq : Tendsto (fun s => wallPt R s) (𝓝[Ioo a b] b) (𝓝[E] q) :=
      tendsto_nhdsWithin_iff.2 ⟨((hαc b hbI).tendsto).mono_left
        (nhdsWithin_mono b (Ioo_subset_Icc_self.trans hIcc)),
        eventually_nhdsWithin_of_forall fun s hs => hwE s (Ioo_subset_Ico_self hs)⟩
    have htend : Tendsto (fun s => ‖Ψ (wallPt R s)‖) (𝓝[Ioo a b] b) atTop := hΨinf.comp hlimq
    have := right_nhdsWithin_Ioo_neBot hab
    obtain ⟨s₁, hs₁x, hs₁I⟩ := ((htend.eventually_gt_atTop x).and self_mem_nhdsWithin).exists
    have hg₁ : (Ψ (wallPt R s₁)).re = ‖Ψ (wallPt R s₁)‖ :=
      (Sec7.Prop74B.norm_eq_re_of_im_eq_zero (hreal s₁ (Ioo_subset_Ico_self hs₁I)) (hor s₁ hs₁I)).symm
    obtain ⟨s, hs, hsx⟩ := intermediate_value_Icc hs₁I.1.le
      ((Complex.continuous_re.comp_continuousOn hcont).mono (Icc_subset_Ico_right hs₁I.2))
      ⟨show (Ψ (wallPt R a)).re ≤ x by rw [hΨ0, Complex.zero_re]; exact hx.le,
        show x ≤ (Ψ (wallPt R s₁)).re by rw [hg₁]; exact hs₁x.le⟩
    have hsI : s ∈ Ico a b := ⟨hs.1, hs.2.trans_lt hs₁I.2⟩
    have hΨs : Ψ (wallPt R s) = x := Complex.ext (by rw [Function.comp_apply] at hsx; rw [hsx, ofReal_re])
      (by rw [hreal s hsI, ofReal_im])
    have h1 : cayley (G x) = wallPt R s := hΨi (hGE x).1 (hwE s hsI) (by rw [(hGE x).2, hΨs])
    exact Sec7.Prop74B.mem_range_of_cayley_eq_toDisc hR.2.2.1 (hGHbar x) h1
  · -- negative points: the rest of the frontier lies on `L`
    have hUo : IsOpen U := Sec7.Lemma71F.isOpen_cayley_image hCo hCH
    have hnU : cayley (G x) ∉ U := by
      rintro ⟨z, hz, hzx⟩
      have h1 : Ψ (cayley z) ∈ H := (hΨf z hz) ▸ hf.2.mapsTo hz
      rw [hzx, (hGE x).2] at h1
      exact lt_irrefl (0 : ℝ) (by simpa using (show (0 : ℝ) < (x : ℂ).im from h1))
    have hfrx : cayley (G x) ∈ frontier U := by
      rw [hUo.frontier_eq]
      exact ⟨(hGE x).1.1, hnU⟩
    rcases hfr hfrx with ⟨s, hs, hse⟩ | ⟨l, hl, hle⟩
    · exfalso
      have hΨs : Ψ (wallPt R s) = x := hse ▸ (hGE x).2
      rcases eq_or_lt_of_le hs.1 with hsa | hsa
      · rw [← hsa, hΨ0] at hΨs
        exact hx.ne (by exact_mod_cast hΨs.symm)
      rcases eq_or_lt_of_le hs.2 with hsb | hsb
      · exact (hGE x).1.2 (by rw [← hse, hsb]; rfl)
      · have h1 := hor s ⟨hsa, hsb⟩
        rw [hΨs, ofReal_re] at h1
        exact absurd hx (not_lt.2 h1.le)
    · rw [WangWu.cayley_injOn_Hbar (hGHbar x) (hLH hl) hle.symm]
      exact hl

/-! ### The two topological inputs from the sides of the wall -/

/-- The Cayley image of a component of `ℍ \ R` lies in the open disc off the disc picture of `R`. -/
theorem cayley_component_props (hR : Supp9B.IsProperCurve R) {z : ℂ} :
    cayley '' connectedComponentIn (H \ range R) z ⊆ ball 0 1 ∧
      Disjoint (cayley '' connectedComponentIn (H \ range R) z) (wallPt R '' Icc 0 1) ∧
      IsPreconnected (cayley '' connectedComponentIn (H \ range R) z) := by
  have hsub : connectedComponentIn (H \ range R) z ⊆ H \ range R := connectedComponentIn_subset _ _
  refine ⟨?_, Set.disjoint_left.2 ?_, isPreconnected_connectedComponentIn.image _ fun y hy =>
    (WangWu.continuousAt_cayley_of_mem_Hbar (Sec7.Prop74B.mem_Hbar_of_mem_H (hsub hy).1)).continuousWithinAt⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact QuantumZipper.CA.cayley_mem_ball (hsub hy).1
  · rintro _ ⟨y, hy, rfl⟩ h
    exact (hsub hy).2 (mem_range_of_cayley_mem_wallPt_image hR (Sec7.Prop74B.mem_Hbar_of_mem_H (hsub hy).1) h)

/-- **The left input from the left side**: if `C` lies on the left of `R` (`leftSideOf`, its components touch the
negative half-line off `R`), the reference loop of the disc picture of `R` winds once about `cayley(C)`. -/
theorem windNum_crossLoop_of_subset_leftSideOf (hR : Supp9B.IsProperCurve R) (hR0 : R 0 = 0) {C : Set ℂ}
    (hCl : C ⊆ leftSideOf (range R)) : ∀ z ∈ cayley '' C, windNum (crossLoop (wallPt R)) z = 1 := by
  obtain ⟨hαc, -, hα0, hα1, hαD⟩ := wallPt_props hR hR0
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨⟨hzH, hzR⟩, x, hx0, hxR, hxcl⟩ := hCl hz
  obtain ⟨hKD, hKα, hKpc⟩ := cayley_component_props hR (z := z)
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  refine windNum_crossLoop_eq_one_of_mem_closure hαc hα0 hα1 hαD hKpc hKD hKα
    (mem_closure_image (WangWu.continuousAt_cayley_of_mem_Hbar hxH) hxcl) (WangWu.cayley_ofReal_norm x) ?_
    (fun h => hxR (mem_range_of_cayley_mem_wallPt_image hR hxH h)) ⟨z, mem_connectedComponentIn ⟨hzH, hzR⟩, rfl⟩
  rw [WangWu.cayley_ofReal_im]
  exact div_pos (by linarith) (by positivity)

/-- **The right input from a right-side component**: let `K` be the component of `ℍ \ R` of a point `z'`, touching the
positive half-line at a point `x ∉ R ∪ L`, disjoint from `C`. If `p` is a limit of `cayley(K)`, then `p` is reached
from infinity through `cayley(K)` and the ray `{r · cayley x : r ≥ 1}` without crossing `cl(cayley C)`, the wall or
the upper semicircle. -/
theorem exists_right_of_component (hR : Supp9B.IsProperCurve R) (hR0 : R 0 = 0) {L C : Set ℂ} (hLH : L ⊆ Hbar)
    (hCo : IsOpen C) (hCH : C ⊆ H) (hfr : frontier (cayley '' C) ⊆ wallPt R '' Icc 0 1 ∪ cayley '' L)
    {z' : ℂ} (hK : Disjoint (connectedComponentIn (H \ range R) z') C) {x : ℝ} (hx0 : 0 < x)
    (hxR : (x : ℂ) ∉ range R) (hxL : (x : ℂ) ∉ L)
    (hxcl : (x : ℂ) ∈ closure (connectedComponentIn (H \ range R) z')) {p : ℂ}
    (hp : p ∈ closure (cayley '' connectedComponentIn (H \ range R) z')) :
    ∃ V : Set ℂ, IsPreconnected V ∧ ¬ IsBounded V ∧ p ∈ closure V ∧
      Disjoint V (closure (cayley '' C) ∪ wallPt R '' Icc 0 1 ∪ semiArc 1) := by
  obtain ⟨-, -, -, -, hαD⟩ := wallPt_props hR hR0
  set K := connectedComponentIn (H \ range R) z' with hKdef
  obtain ⟨hKD, hKα, hKpc⟩ := cayley_component_props hR (z := z')
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  set u := cayley (x : ℂ) with hu
  have hun : ‖u‖ = 1 := WangWu.cayley_ofReal_norm x
  have hui : u.im < 0 := by
    rw [hu, WangWu.cayley_ofReal_im]
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  have hucl : u ∈ closure (cayley '' K) := mem_closure_image (WangWu.continuousAt_cayley_of_mem_Hbar hxH) hxcl
  set ray := (fun r : ℝ => (r : ℂ) * u) '' Ici 1 with hray
  have hrayc : IsPreconnected ray := isPreconnected_Ici.image _ (by fun_prop)
  have hKu : IsPreconnected (insert u (cayley '' K)) :=
    hKpc.subset_closure (subset_insert _ _) (insert_subset hucl subset_closure)
  have hnr : ∀ r : ℝ, 1 ≤ r → ‖(r : ℂ) * u‖ = r := fun r hr => by
    rw [norm_mul, hun, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  refine ⟨insert u (cayley '' K) ∪ ray, hKu.union u (mem_insert _ _) ⟨1, mem_Ici.2 le_rfl, by simp⟩ hrayc,
    fun hb => ?_, closure_mono (subset_union_left.trans' (subset_insert _ _)) hp, ?_⟩
  · -- the ray is unbounded
    obtain ⟨M, hM⟩ := (hb.subset subset_union_right).exists_norm_le
    have h := hM _ ⟨max M 1 + 1, mem_Ici.2 (by linarith [le_max_right M 1]), rfl⟩
    rw [hnr _ (by linarith [le_max_right M 1])] at h
    linarith [le_max_left M 1]
  -- `cl(cayley C)` lies in the closed disc and avoids `cayley(K)` and `u`
  have hUo : IsOpen (cayley '' C) := Sec7.Lemma71F.isOpen_cayley_image hCo hCH
  have hclD : closure (cayley '' C) ⊆ closedBall 0 1 :=
    closure_minimal (fun _ ⟨y, hy, he⟩ => he ▸ QuantumZipper.CA.cayley_mem_closedBall
      (Sec7.Prop74B.mem_Hbar_of_mem_H (hCH hy))) isClosed_closedBall
  have huα : u ∉ wallPt R '' Icc 0 1 := fun h => hxR (mem_range_of_cayley_mem_wallPt_image hR hxH h)
  have hunot : u ∉ closure (cayley '' C) := fun h => by
    rw [closure_eq_self_union_frontier] at h
    rcases h with ⟨y, hy, hyu⟩ | h
    · have := QuantumZipper.CA.cayley_mem_ball (hCH hy)
      rw [hyu, mem_ball, dist_zero_right, hun] at this
      exact lt_irrefl _ this
    · rcases hfr h with h' | ⟨l, hl, hle⟩
      · exact huα h'
      · exact hxL (WangWu.cayley_injOn_Hbar (hLH hl) hxH hle ▸ hl)
  have hRc : IsClosed (range R) := by rw [← image_univ]; exact Supp9B.isClosed_image hR isClosed_univ
  have hKo : IsOpen K := (isOpen_H.sdiff hRc).connectedComponentIn
  have hKH : K ⊆ H := fun y hy => (connectedComponentIn_subset _ _ hy).1
  have hKC : Disjoint (cayley '' K) (closure (cayley '' C)) := by
    refine Disjoint.closure_right (Set.disjoint_left.2 ?_) (Sec7.Lemma71F.isOpen_cayley_image hKo hKH)
    rintro _ ⟨k, hk, rfl⟩ ⟨c, hc, hce⟩
    have := WangWu.cayley_injOn_Hbar (Sec7.Prop74B.mem_Hbar_of_mem_H (hCH hc))
      (Sec7.Prop74B.mem_Hbar_of_mem_H (hKH hk)) hce
    exact Set.disjoint_left.1 hK hk (this ▸ hc)
  refine Set.disjoint_left.2 fun v hv hvc => ?_
  have hsemi : ∀ {w : ℂ}, w ∈ semiArc 1 → ‖w‖ = 1 := fun h => h.1
  rcases hv with (rfl | hvK) | ⟨r, hr, rfl⟩
  · rcases hvc with (h | h) | h
    · exact hunot h
    · exact huα h
    · have := h.2; rw [one_mul] at this; linarith
  · rcases hvc with (h | h) | h
    · exact Set.disjoint_left.1 hKC hvK h
    · exact Set.disjoint_left.1 hKα hvK h
    · have := hKD hvK; rw [mem_ball, dist_zero_right, hsemi h] at this; exact lt_irrefl _ this
  · rcases eq_or_lt_of_le (mem_Ici.1 hr) with h1 | h1
    · have hv1 : (fun r : ℝ => (r : ℂ) * u) r = u := by rw [← h1]; simp
      rw [hv1] at hvc
      rcases hvc with (h | h) | h
      · exact hunot h
      · exact huα h
      · have := h.2; rw [one_mul] at this; linarith
    · have hn := hnr r h1.le
      rcases hvc with (h | h) | h
      · have := hclD h; rw [mem_closedBall, dist_zero_right, hn] at this; linarith
      · have := hαD h; rw [mem_closedBall, dist_zero_right, hn] at this; linarith
      · rw [hsemi h] at hn; linarith

/-- **The right input at a real point of the wall**: a point `p` of the unit circle is reached from infinity through
`{|w| > 1}`, which avoids the closed disc (hence `cl(cayley C)`, the wall and the upper semicircle). -/
theorem exists_right_of_norm_eq_one (hR : Supp9B.IsProperCurve R) (hR0 : R 0 = 0) {C : Set ℂ} (hCH : C ⊆ H)
    {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ V : Set ℂ, IsPreconnected V ∧ ¬ IsBounded V ∧ p ∈ closure V ∧
      Disjoint V (closure (cayley '' C) ∪ wallPt R '' Icc 0 1 ∪ semiArc 1) := by
  obtain ⟨-, -, -, -, hαD⟩ := wallPt_props hR hR0
  have hclD : closure (cayley '' C) ⊆ closedBall 0 1 :=
    closure_minimal (fun _ ⟨y, hy, he⟩ => he ▸ QuantumZipper.CA.cayley_mem_closedBall
      (Sec7.Prop74B.mem_Hbar_of_mem_H (hCH hy))) isClosed_closedBall
  refine ⟨{w : ℂ | 1 < ‖w‖}, WangWu.isPreconnected_one_lt_norm, WangWu.not_isBounded_one_lt_norm,
    Metric.mem_closure_iff.2 fun ε hε => ⟨((1 + ε / 2 : ℝ) : ℂ) * p, ?_, ?_⟩, Set.disjoint_left.2 fun w hw hwc => ?_⟩
  · show 1 < ‖((1 + ε / 2 : ℝ) : ℂ) * p‖
    rw [norm_mul, hp, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  · rw [dist_eq_norm, show p - ((1 + ε / 2 : ℝ) : ℂ) * p = ((-(ε / 2) : ℝ) : ℂ) * p by push_cast; ring, norm_mul, hp,
      mul_one, norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith)]
    linarith
  · have hw1 : 1 < ‖w‖ := hw
    rcases hwc with (h | h) | h
    · have := hclD h; rw [mem_closedBall, dist_zero_right] at this; linarith
    · have := hαD h; rw [mem_closedBall, dist_zero_right] at this; linarith
    · rw [h.1] at hw1; exact lt_irrefl _ hw1

/-- **Oriented uniformizers from the sides of the wall** (deterministic; all holomorphic content discharged). Let `R`
be a proper curve from `0` in `ℍ̄` (it may contain real intervals), `L ⊆ ℍ̄`, and `C` an open connected marked pocket
`[a, b]` of `R` on the left of `R`, with Cayley frontier on `R̃([a, b]) ∪ cayley(L)`. Suppose some point `R̃ s`,
`s ∈ (a, b)`, off the upper semicircle, is either on the unit circle (a real point of `R`) or a limit of the Cayley
image of a component of `ℍ \ R` that is disjoint from `C` and touches the positive half-line at a point off `R ∪ L` (the
right of `R`). Then `C` has an oriented uniformizer. -/
theorem hasOrientedUniformizer_of_sides {R : ℝ≥0 → ℂ} (hR : Supp9B.IsProperCurve R) (hR0 : R 0 = 0)
    {L C : Set ℂ} (hLH : L ⊆ Hbar) (hCo : IsOpen C) (hCc : IsConnected C) (hCl : C ⊆ leftSideOf (range R))
    {a b : ℝ} (hM : IsMarkedPocket R C a b) (hfr : frontier (cayley '' C) ⊆ wallPt R '' Icc a b ∪ cayley '' L)
    (hright : ∃ s ∈ Ioo a b, wallPt R s ∉ semiArc 1 ∧ (‖wallPt R s‖ = 1 ∨ ∃ z' : ℂ,
      Disjoint (connectedComponentIn (H \ range R) z') C ∧
      wallPt R s ∈ closure (cayley '' connectedComponentIn (H \ range R) z') ∧
      ∃ x : ℝ, 0 < x ∧ (x : ℂ) ∉ range R ∧ (x : ℂ) ∉ L ∧
        (x : ℂ) ∈ closure (connectedComponentIn (H \ range R) z'))) :
    HasOrientedUniformizer (range R) L C := by
  have hCH : C ⊆ H := fun z hz => (hCl hz).1.1
  have hCR : Disjoint C (range R) := Set.disjoint_left.2 fun z hz => (hCl hz).1.2
  obtain ⟨ha0, -, hb1, -⟩ := id hM
  have hfr' : frontier (cayley '' C) ⊆ wallPt R '' Icc 0 1 ∪ cayley '' L := fun w hw => by
    rcases hfr hw with h | h
    · exact Or.inl (image_mono (Icc_subset_Icc ha0 hb1) h)
    · exact Or.inr h
  refine hasOrientedUniformizer_of_crossLoop hR hR0 hLH hCo hCc hCH hCR hM hfr
    (windNum_crossLoop_of_subset_leftSideOf hR hR0 hCl) ?_
  obtain ⟨s, hs, hsS, h | ⟨z', hK, hp, x, hx0, hxR, hxL, hxcl⟩⟩ := hright
  · exact ⟨_, ⟨s, hs, rfl⟩, hsS, exists_right_of_norm_eq_one hR hR0 hCH h⟩
  · exact ⟨_, ⟨s, hs, rfl⟩, hsS, exists_right_of_component hR hR0 hLH hCo hCH hfr' hK hx0 hxR hxL hxcl hp⟩

end Wall

/-! ### `GW3GeometryStatement` without the orientation -/

/-- An oriented uniformizer for a smaller right wall is one for a larger right wall. -/
theorem HasOrientedUniformizer.mono_right {R R' L C : Set ℂ} (h : HasOrientedUniformizer R' L C) (hR : R' ⊆ R) :
    HasOrientedUniformizer R L C := by
  obtain ⟨hCo, hCH, ψ, hψ, hlim⟩ := h
  exact ⟨hCo, hCH, ψ, hψ, fun x => by
    obtain ⟨p, hp, hpR, hpL⟩ := hlim x
    exact ⟨p, hp, fun hx => hR (hpR hx), hpL⟩⟩

/-- `C` is a **sided wall pocket** of the walls `R`, `L` (sets): the hypotheses of `hasOrientedUniformizer_of_sides`
for a proper curve `R'` from `0` whose range lies in `R` (purely topological; no conformal map is involved). -/
def IsSidedWallPocket (R L C : Set ℂ) : Prop :=
  ∃ R' : ℝ≥0 → ℂ, Supp9B.IsProperCurve R' ∧ R' 0 = 0 ∧ range R' ⊆ R ∧ L ⊆ Hbar ∧ IsOpen C ∧ IsConnected C ∧
    C ⊆ leftSideOf (range R') ∧ ∃ a b : ℝ, IsMarkedPocket R' C a b ∧
      frontier (cayley '' C) ⊆ wallPt R' '' Icc a b ∪ cayley '' L ∧
      ∃ s ∈ Ioo a b, wallPt R' s ∉ semiArc 1 ∧ (‖wallPt R' s‖ = 1 ∨ ∃ z' : ℂ,
        Disjoint (connectedComponentIn (H \ range R') z') C ∧
        wallPt R' s ∈ closure (cayley '' connectedComponentIn (H \ range R') z') ∧
        ∃ x : ℝ, 0 < x ∧ (x : ℂ) ∉ range R' ∧ (x : ℂ) ∉ L ∧
          (x : ℂ) ∈ closure (connectedComponentIn (H \ range R') z'))

/-- **A sided wall pocket has an oriented uniformizer.** -/
theorem hasOrientedUniformizer_of_isSidedWallPocket {R L C : Set ℂ} (h : IsSidedWallPocket R L C) :
    HasOrientedUniformizer R L C := by
  obtain ⟨R', hR', hR'0, hR'R, hLH, hCo, hCc, hCl, a, b, hM, hfr, hright⟩ := h
  exact (hasOrientedUniformizer_of_sides hR' hR'0 hLH hCo hCc hCl hM hfr hright).mono_right hR'R

/-- **`GW3GeometryStatement` with the orientation removed**: the same almost-sure geometry of the components between
the boundary walks, with the alternative `HasOrientedUniformizer` (a conformal map with the oriented boundary
correspondence) replaced by the purely topological `IsSidedWallPocket`. -/
def GW3GeometrySidedStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      ∀ᵐ ω₀ ∂P,
        ∀ C ∈ betweenComponents
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)),
          IsTwoArcJordanComponent
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
                (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
                (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)) C ∨
            IsSidedWallPocket
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
                (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
                (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)) C

/-- **The orientation part of `GW3GeometryStatement`**: it follows from its topological form. -/
theorem gw3GeometryStatement_of_sided (hG : GW3GeometrySidedStatement.{u}) : GW3GeometryStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE
  filter_upwards [hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE] with ω₀ hω C hC
  rcases hω C hC with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (hasOrientedUniformizer_of_isSidedWallPocket h2)

end InteractingSLE.Theorem14.GW3
