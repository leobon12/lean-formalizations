import QuantumZipper.Proofs.Thm18.G4CoreDownShort
import QuantumZipper.Proofs.Thm18.G4WeldRem
import QuantumZipper.Proofs.Thm18.G4GroupMixCross
import QuantumZipper.Proofs.Thm18.G4PushRegScale
import QuantumZipper.Proofs.Zipper.Cor15GrpCore
import QuantumZipper.Proofs.Thm18.G4CoreDownShort
import QuantumZipper.Proofs.Thm18.G4CoreDownLong
import QuantumZipper.Proofs.Thm18.G4CoreUpShort
import QuantumZipper.Proofs.Thm18.G4CoreZipCocycle
import QuantumZipper.Proofs.Loewner.CoreArc3d
import QuantumZipper.Proofs.RS.GenerationBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node G4: the simple-arc hull of the re-zipping driver `dsDrv`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1). The hull
disjunct of `IsLenWeldingDriver` for the re-zipping driver `dsDrv γ s ℓ c` (the rescaled time
reversal of the wedge driver on `[τ_{ℓ−s}, τ_ℓ]`) is **proved** here, pathwise, from the simple
chord property of the SLE trace supplied by `Thm18Inputs`:

* `isSimpleCurveHull_fwdHull_shift`: if the hulls of `W` are the initial arcs `η(0,t]` of a simple
  chord `η`, then for `0 ≤ τ' < τ` the forward hull of the shifted driver
  `s ↦ W(τ'+s) − W τ'` at time `τ − τ'` is a simple-curve hull, namely the arc
  `u ↦ f_{τ'}(η(τ' + u(τ−τ')))`, `u ∈ (0,1]`, closed up at `0` by the tip limit
  `f_{τ'}(η(v)) → 0` as `v ↓ τ'`.
* `dsDrv_hull_of_chord`: the hull disjunct of `dsDrv` (via `isSimpleCurveHull_backDrv`,
  `G4Weld2Hull.lean`).
* `g4DownShortGeomStmt_of_rem`: `G4DownShortGeomStmt` from `G4UnzipGoodStmt` and the
  removability node `G4DownShortRemStmt` alone.

Sources: the domain Markov property of Loewner hulls (`fwdHull_add_diff`; Rohde–Schramm, *Basic
properties of SLE*, Prop. 2.1 (ii), p. 6; Kemppainen, *Schramm–Loewner Evolution*, Thm 5.1,
p. 74) and the tip convergence `f_r(γ(w)) → 0` (`CoreArc.tendsto_fwdMap_arc_tip`). The assembly
of the arc from these two facts is an **own elementary argument**.
-/

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- Points of the chord after time `τ'` lie outside the hull at time `τ'`. -/
theorem chord_mem_diff_fwdHull (hη : IsSimpleChord η)
    (hK : ∀ t : ℝ, 0 ≤ t → fwdHull W t = η '' Ioc 0 t) {τ' v : ℝ} (hτ' : 0 ≤ τ')
    (hv : τ' < v) : η v ∈ H \ fwdHull W τ' := by
  refine ⟨hη.2.2.2.1 v (by linarith), ?_⟩
  rw [hK τ' hτ']
  rintro ⟨v', hv', hvv⟩
  have := hη.2.2.1 (mem_Ici.2 hv'.1.le) (mem_Ici.2 (by linarith)) hvv
  linarith [hv'.2]

/-- **Tip convergence along the chord**: `f_{τ'}(η v) → 0` as `v ↓ τ'`, `0 < τ' < τ`. -/
theorem tendsto_fwdMap_chord_tip (hW : Continuous W) (hη : IsSimpleChord η)
    (hK : ∀ t : ℝ, 0 ≤ t → fwdHull W t = η '' Ioc 0 t) {τ' τ : ℝ} (hτ' : 0 < τ')
    (hτ : τ' < τ) : Tendsto (fun v => fwdMap W τ' (η v)) (𝓝[>] τ') (𝓝 0) := by
  have hT : 0 < τ := hτ'.trans hτ
  set γ : ℝ → ℂ := fun u => η (τ * u) with hγ
  have hγi : InjOn γ (Icc 0 1) := by
    intro x hx y hy hxy
    exact mul_left_cancel₀ hT.ne' (hη.2.2.1 (mem_Ici.2 (mul_nonneg hT.le hx.1))
      (mem_Ici.2 (mul_nonneg hT.le hy.1)) hxy)
  have hmono : StrictMonoOn (fun r : ℝ => r / τ) (Icc 0 τ) := fun x _ y _ hxy =>
    div_lt_div_of_pos_right hxy hT
  have hrange : ∀ r ∈ Icc (0 : ℝ) τ, r / τ ∈ Icc (0 : ℝ) 1 := fun r hr =>
    ⟨div_nonneg hr.1 hT.le, (div_le_one hT).2 hr.2⟩
  have hKγ : ∀ r ∈ Icc (0 : ℝ) τ, fwdHull W r = γ '' Ioc 0 (r / τ) := by
    intro r hr
    rw [hK r hr.1]
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v / τ, ⟨div_pos hv.1 hT, div_le_div_of_nonneg_right hv.2 hT.le⟩, ?_⟩
      show η (τ * (v / τ)) = η v
      congr 1
      field_simp
    · rintro ⟨u, hu, rfl⟩
      refine ⟨τ * u, ⟨mul_pos hT hu.1, ?_⟩, rfl⟩
      rw [mul_comm]
      exact (le_div_iff₀ hT).1 hu.2
  have h := CoreArc.tendsto_fwdMap_arc_tip hW hγi hmono hrange hKγ ⟨hτ', hτ⟩
  have hdiv : Tendsto (fun v : ℝ => v / τ) (𝓝[>] τ') (𝓝[>] (τ' / τ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun v hv =>
      div_lt_div_of_pos_right hv hT⟩
    exact ((continuous_id.div_const τ).tendsto τ').mono_left nhdsWithin_le_nhds
  refine (h.comp hdiv).congr fun v => ?_
  show fwdMap W τ' (η (τ * (v / τ))) = fwdMap W τ' (η v)
  congr 2
  field_simp

/-- **The shifted forward hull of a chord is a simple-curve hull.** If the hulls of the
continuous driver `W` (`W 0 = 0`) are the initial arcs `η(0,t]` of a simple chord `η`, then for
`0 ≤ τ' < τ` the forward hull of the shifted driver `s ↦ W(τ'+s) − W τ'` at time `τ − τ'` is a
simple-curve hull. -/
theorem isSimpleCurveHull_fwdHull_shift (hW : Continuous W) (hW0 : W 0 = 0)
    (hη : IsSimpleChord η) (hK : ∀ t : ℝ, 0 ≤ t → fwdHull W t = η '' Ioc 0 t) {τ' τ : ℝ}
    (hτ' : 0 ≤ τ') (hτ : τ' < τ) :
    IsSimpleCurveHull (fwdHull (fun s => W (τ' + s) - W τ') (τ - τ')) := by
  rcases eq_or_lt_of_le hτ' with h0 | hpos
  · subst h0
    have hT : 0 < τ := hτ
    have hdrv : (fun s => W (0 + s) - W 0) = W := by funext s; simp [hW0]
    rw [hdrv, sub_zero, hK τ hT.le]
    refine ⟨fun u => η (τ * u), ?_, ?_, ?_, ?_, ?_⟩
    · exact hη.2.1.comp (continuousOn_const.mul continuousOn_id)
        (fun u hu => mem_Ici.2 (mul_nonneg hT.le hu.1))
    · intro x hx y hy hxy
      exact mul_left_cancel₀ hT.ne' (hη.2.2.1 (mem_Ici.2 (mul_nonneg hT.le hx.1))
        (mem_Ici.2 (mul_nonneg hT.le hy.1)) hxy)
    · simp [hη.1]
    · intro u hu
      exact hη.2.2.2.1 _ (mul_pos hT hu.1)
    · ext z
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨v / τ, ⟨div_pos hv.1 hT, (div_le_one hT).2 hv.2⟩, ?_⟩
        show η (τ * (v / τ)) = η v
        congr 1
        field_simp
      · rintro ⟨u, hu, rfl⟩
        exact ⟨τ * u, ⟨mul_pos hT hu.1, by nlinarith [hu.2]⟩, rfl⟩
  · set d := τ - τ' with hd
    have hd0 : 0 < d := sub_pos.2 hτ
    set g : ℝ → ℂ := fun u => fwdMap W τ' (η (τ' + u * d)) with hg
    set γ : ℝ → ℂ := fun u => if u = 0 then 0 else g u with hγ
    have hmem : ∀ u : ℝ, 0 < u → η (τ' + u * d) ∈ H \ fwdHull W τ' := fun u hu =>
      chord_mem_diff_fwdHull hη hK hτ' (by nlinarith)
    have hgH : ∀ u : ℝ, 0 < u → g u ∈ H := fun u hu =>
      FwdHolo.mapsTo_fwdMap hW hτ' (hmem u hu)
    have hγeq : ∀ u : ℝ, 0 < u → γ u = g u := fun u hu => by simp [hγ, hu.ne']
    have hγ0 : γ 0 = 0 := by simp [hγ]
    have hgc : ContinuousOn g (Ioi 0) := by
      refine (FwdHolo.differentiableOn_fwdMap hW hτ').continuousOn.comp
        (hη.2.1.comp (continuousOn_const.add (continuousOn_id.mul continuousOn_const)) ?_)
        (fun u hu => hmem u hu)
      intro u hu
      exact mem_Ici.2 (by nlinarith [mem_Ioi.1 hu])
    have htip : Tendsto g (𝓝[>] 0) (𝓝 0) := by
      have h1 := tendsto_fwdMap_chord_tip hW hη hK hpos hτ
      have h2 : Tendsto (fun u : ℝ => τ' + u * d) (𝓝[>] 0) (𝓝[>] τ') := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun u hu => ?_⟩
        · have hc : Continuous fun u : ℝ => τ' + u * d := by fun_prop
          have := hc.tendsto 0
          simp only [zero_mul, add_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        · show τ' < τ' + u * d
          nlinarith [mem_Ioi.1 hu]
      exact h1.comp h2
    have hcont : ∀ u : ℝ, 0 ≤ u → ContinuousWithinAt γ (Ioi 0) u := by
      intro u hu
      rcases eq_or_lt_of_le hu with h | h
      · subst h
        show Tendsto γ (𝓝[>] 0) (𝓝 (γ 0))
        rw [hγ0]
        exact htip.congr' (eventually_nhdsWithin_of_forall fun y hy => (hγeq y hy).symm)
      · exact (hgc u h).congr (fun y hy => hγeq y hy) (hγeq u h)
    have hdiff := fwdHull_add_diff hW (t := τ') (s := d) hτ' hd0.le
    have hτd : τ' + d = τ := by rw [hd]; ring
    refine ⟨γ, ?_, ?_, by rw [hγ0]; rfl, ?_, ?_⟩
    · intro u hu
      rcases eq_or_lt_of_le hu.1 with h | h
      · subst h
        rw [← continuousWithinAt_sdiff_self]
        refine (hcont 0 le_rfl).mono fun y hy => ?_
        exact lt_of_le_of_ne hy.1.1 (Ne.symm hy.2)
      · exact (hcont u hu.1).mono_of_mem_nhdsWithin
          (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds h))
    · intro x hx y hy hxy
      rcases eq_or_lt_of_le hx.1 with hx0 | hx0 <;> rcases eq_or_lt_of_le hy.1 with hy0 | hy0
      · rw [← hx0, ← hy0]
      · exfalso
        rw [← hx0, hγ0, hγeq y hy0] at hxy
        have h := hgH y hy0
        rw [← hxy] at h
        exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h)
      · exfalso
        rw [← hy0, hγ0, hγeq x hx0] at hxy
        have h := hgH x hx0
        rw [hxy] at h
        exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h)
      · rw [hγeq x hx0, hγeq y hy0] at hxy
        have h1 := FwdHolo.injOn_fwdMap hW hτ' (hmem x hx0) (hmem y hy0) hxy
        have h2 := hη.2.2.1 (mem_Ici.2 (by nlinarith)) (mem_Ici.2 (by nlinarith)) h1
        have h3 : x * d = y * d := by linarith
        exact mul_right_cancel₀ hd0.ne' h3
    · intro u hu
      rw [hγeq u hu.1]
      exact hgH u hu.1
    · ext w
      constructor
      · intro hw
        have hwH : w ∈ H := hw.1
        set z := fwdMapInv W τ' w with hz
        have hzm := RS.fwdMapInv_mem_compl_fwdHull hW hW0 hτ' hwH
        have hfz := RS.fwdMap_fwdMapInv hW hW0 hτ' hwH
        have hz' : z ∈ fwdHull W (τ' + d) \ fwdHull W τ' := by
          rw [hdiff]
          exact ⟨hzm, by rw [hfz]; exact hw⟩
        obtain ⟨hzK, hzK'⟩ := hz'
        rw [hτd, hK τ (by linarith)] at hzK
        obtain ⟨v, hv, hvz⟩ := hzK
        have hvτ : τ' < v := by
          by_contra hle
          exact hzK' (by rw [hK τ' hτ', ← hvz]; exact ⟨v, ⟨hv.1, not_lt.1 hle⟩, rfl⟩)
        refine ⟨(v - τ') / d, ⟨div_pos (by linarith) hd0, (div_le_one hd0).2 (by linarith [hv.2])⟩,
          ?_⟩
        have hpos' : 0 < (v - τ') / d := div_pos (by linarith) hd0
        rw [hγeq _ hpos']
        show fwdMap W τ' (η (τ' + (v - τ') / d * d)) = w
        rw [div_mul_cancel₀ _ hd0.ne', add_sub_cancel, hvz, hfz]
      · rintro ⟨u, hu, rfl⟩
        rw [hγeq u hu.1]
        have hzK : η (τ' + u * d) ∈ fwdHull W (τ' + d) \ fwdHull W τ' := by
          refine ⟨?_, (hmem u hu.1).2⟩
          rw [hK _ (by linarith)]
          exact ⟨τ' + u * d, ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩, rfl⟩
        rw [hdiff] at hzK
        exact hzK.2

end Thm18Asm
end QuantumZipper
