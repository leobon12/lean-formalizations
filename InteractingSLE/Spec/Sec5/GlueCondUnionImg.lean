/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux8Inf
import InteractingSLE.Spec.Sec7.Aux57

/-!
# G3 (ii), Proposition 4.9 direction: the image chart is a Möbius image of a hull map

Packet PROVE-GLUECOND4 (specification §4.2, proofs of Lemma 4.7 and Proposition 4.9, pp. 117–120). Setting of the
Proposition 4.9 direction (`planning/handoffs/PROVE-GLUECOND3.md`, "What remains" 1): a flow hull `A = K^α_t` (chart
`f_t = fwdMap Wα t`, inverse `F_t`), a counterflow hull `K′ = K^β_s` with reflected hull `G = R(K′)` (`R z = −1/z`),
the chart `Ψ = revChart Wβ s = R ∘ f^β_s ∘ R` of `ℍ ∖ G`, and an image chain `K′_T = fwdHull W' T = Ψ(A)` with map
`g_T = fwdMap W' T`. The union mean lives on `C = ℍ ∖ (A ∪ G)`; its candidate is read through the image chart
`F = g_T ∘ Ψ : C → ℍ`, and the comparison with the flow mean `m_A` (chart `f_t`) goes through the transition map

  `φ = g_T ∘ Ψ ∘ F_t : ℍ ∖ f_t(G) → ℍ`   (`imgPhi`).

WangWu B14 (κ = 4) settled the sides of the flow slit by a separating arc built from the simple reverse slit; for the
non-simple counterflow hull at `κ′ = 16/κ` that arc does not exist. Here the transition map is identified instead:

* **`fwdMap_image_negInv_eq`**: `f_t(G) = R(K2)` with `K2 = Ψ_t(K′)`, `Ψ_t = revChart Wα t`, and Aux. 8 for the
  obstacle `R(A)` (PROVE-GLUECOND3, `Aux8Inf.exists_loewner_revChart_image`) makes `K2 = fwdHull W'' τ` a Loewner hull.
* **`exists_imgPhi_eq_realMobius`**: `φ(ξ) = N(g''(R ξ))` on `ℍ ∖ f_t(G)`, with `g'' = fwdMap W'' τ + W''(τ)` the
  hydrodynamic map of `K″` and `N` a real Möbius map of positive determinant (two conformal maps of `ℍ ∖ K″` onto `ℍ`
  differ by an automorphism of `ℍ`: `CrossRestart.exists_realMobius_conj`).

Consequently `φ` is real-analytic across every real point `ξ ≠ 0` with `R ξ` off the hull `K″` (Aux. 57's reflection of
`g''`), with positive derivative there — the analytic form of "the sides of `A` and the real line are mapped to the
real line in order" that the boundary correspondence needs.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open QuantumZipper (H fwdHull fwdMap fwdMapInv)
open QuantumZipper.CA (realMobius)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec5.GlueImg

open WangWu hiding ratPt exists_ratPt_dist_lt

/-- The **transition map** of the Proposition 4.9 direction: `φ = g_T ∘ Ψ ∘ F_t`, from the flow chart `f_t` (where the
union domain is `ℍ ∖ f_t(G)`) to the image chart of the counterflow chart `Ψ = revChart Wβ s`. -/
def imgPhi (Wα : ℝ → ℝ) (t : ℝ) (Wβ : ℝ → ℝ) (s : ℝ) (W' : ℝ → ℝ) (T : ℝ) (ξ : ℂ) : ℂ :=
  fwdMap W' T (revChart Wβ s (fwdMapInv Wα t ξ))

variable {Wα Wβ W' : ℝ → ℝ} {t s T : ℝ}

/-- `f_t(R(K′)) = R(Ψ_t(K′))`, `Ψ_t = revChart Wα t`. -/
theorem fwdMap_image_negInv_eq (K : Set ℂ) :
    fwdMap Wα t '' (negInv '' K) = negInv '' (revChart Wα t '' K) := by
  ext ξ
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨revChart Wα t k, ⟨k, hk, rfl⟩, by rw [revChart, negInv_negInv']⟩
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨negInv k, ⟨k, hk, rfl⟩, by rw [revChart, negInv_negInv']⟩

/-- **The union domain in the flow chart.** `F_t` maps `ℍ ∖ f_t(G)` into `C = ℍ ∖ (A ∪ G)`. -/
theorem fwdMapInv_mem_union_compl (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 ≤ t) {G : Set ℂ}
    {ξ : ℂ} (hξ : ξ ∈ H \ fwdMap Wα t '' G) :
    fwdMapInv Wα t ξ ∈ H \ (fwdHull Wα t ∪ G) := by
  have h1 := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWα hWα0 ht hξ.1
  refine ⟨h1.1, ?_⟩
  rintro (hA | hG)
  · exact h1.2 hA
  · exact hξ.2 ⟨_, hG, QuantumZipper.RS.fwdMap_fwdMapInv hWα hWα0 ht hξ.1⟩

/-- `Ψ = revChart W s` is complex-differentiable on `ℍ ∖ R(K_s)`. -/
theorem differentiableAt_revChart {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : z ∈ H \ negInv '' fwdHull W s) : DifferentiableAt ℂ (revChart W s) z := by
  have hz0 : z ≠ 0 := Aux8Inf.ne_zero_of_mem_H' hz.1
  have hw := negInv_notMem_fwdHull hz
  have h2 : DifferentiableAt ℂ (fwdMap W s) (negInv z) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hs _ hw).differentiableAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hs).mem_nhds hw)
  have h3 : fwdMap W s (negInv z) ≠ 0 :=
    Aux8Inf.ne_zero_of_mem_H' (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs hw)
  have h1 : DifferentiableAt ℂ negInv z := (differentiableAt_inv hz0).neg
  have h4 : DifferentiableAt ℂ negInv (fwdMap W s (negInv z)) := (differentiableAt_inv h3).neg
  exact h4.comp z (h2.comp z h1)

section Transition

/-- `f_t` is injective on `ℍ ∖ K_t`. -/
theorem injOn_fwdMap' {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {r : ℝ} (hr : 0 ≤ r) :
    InjOn (fwdMap W r) (H \ fwdHull W r) := fun z hz z' hz' e => by
  rw [← QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hr hz, e, QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hr hz']

/-- `Ψ` maps `C = ℍ ∖ (A ∪ G)` into `ℍ ∖ K′_T`. -/
theorem revChart_mem_compl_imgHull (hWα : Continuous Wα) (ht : 0 ≤ t) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0)
    (hs : 0 ≤ s) (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) {p : ℂ}
    (hp : p ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)) :
    revChart Wβ s p ∈ H \ fwdHull W' T := by
  have hpG : p ∈ H \ negInv '' fwdHull Wβ s := ⟨hp.1, fun h => hp.2 (Or.inr h)⟩
  refine ⟨revChart_mem_H hWβ hs hpG, fun hK => ?_⟩
  rw [hK'] at hK
  obtain ⟨a, ha, hae⟩ := hK
  have haG : a ∈ H \ negInv '' fwdHull Wβ s :=
    ⟨(isHPHull_fwdHull hWα ht).1 ha, fun h => disjoint_left.1 hdisj ha h⟩
  have := injOn_revChart hWβ hWβ0 hs haG hpG hae
  exact hp.2 (Or.inl (this ▸ ha))

/-- **The transition map read from `ℍ ∖ K2` is a conformal bijection onto `ℍ`** (`K2 = Ψ_t(K′)`). -/
theorem isConformalBijection_imgPhi_negInv (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 ≤ t)
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) :
    IsConformalBijection (fun z => imgPhi Wα t Wβ s W' T (negInv z)) (H \ revChart Wα t '' fwdHull Wβ s) H := by
  set K2 := revChart Wα t '' fwdHull Wβ s with hK2
  set G := negInv '' fwdHull Wβ s with hGdef
  have hfG : fwdMap Wα t '' G = negInv '' K2 := fwdMap_image_negInv_eq _
  -- the point `F_t(R z)` of the union domain
  have hpt : ∀ z ∈ H \ K2, fwdMapInv Wα t (negInv z) ∈ H \ (fwdHull Wα t ∪ G) := by
    intro z hz
    refine fwdMapInv_mem_union_compl hWα hWα0 ht ⟨negInv_mem_H hz.1, fun h => ?_⟩
    rw [hfG] at h
    obtain ⟨k, hk, hke⟩ := h
    have : k = z := by rw [← negInv_negInv' k, hke, negInv_negInv']
    exact hz.2 (this ▸ hk)
  have hGs : ∀ p ∈ H \ (fwdHull Wα t ∪ G), p ∈ H \ G := fun p hp => ⟨hp.1, fun h => hp.2 (Or.inr h)⟩
  refine ⟨fun z hz => ?_, ⟨fun z hz => ?_, fun z₁ hz₁ z₂ hz₂ e => ?_, fun y hy => ?_⟩⟩
  · -- differentiability
    have hz0 : z ≠ 0 := Aux8Inf.ne_zero_of_mem_H' hz.1
    have hξ : negInv z ∈ H := negInv_mem_H hz.1
    have hp := hpt z hz
    have hq := revChart_mem_compl_imgHull hWα ht hWβ hWβ0 hs hdisj hK' hp
    have d1 : DifferentiableAt ℂ negInv z := (differentiableAt_inv hz0).neg
    have d2 : DifferentiableAt ℂ (fwdMapInv Wα t) (negInv z) :=
      (QuantumZipper.RS.differentiableOn_fwdMapInv hWα hWα0 ht).differentiableAt
        (QuantumZipper.isOpen_H.mem_nhds hξ)
    have d3 : DifferentiableAt ℂ (revChart Wβ s) (fwdMapInv Wα t (negInv z)) :=
      differentiableAt_revChart hWβ hs (hGs _ hp)
    have d4 : DifferentiableAt ℂ (fwdMap W' T) (revChart Wβ s (fwdMapInv Wα t (negInv z))) :=
      (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW' hT _ hq).differentiableAt
        ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW' hT).mem_nhds hq)
    exact (d4.comp z (d3.comp z (d2.comp z d1))).differentiableWithinAt
  · exact QuantumZipper.FwdHolo.mapsTo_fwdMap hW' hT
      (revChart_mem_compl_imgHull hWα ht hWβ hWβ0 hs hdisj hK' (hpt z hz))
  · have hp₁ := hpt z₁ hz₁
    have hp₂ := hpt z₂ hz₂
    have e1 := injOn_fwdMap' hW' hW'0 hT
      (revChart_mem_compl_imgHull hWα ht hWβ hWβ0 hs hdisj hK' hp₁)
      (revChart_mem_compl_imgHull hWα ht hWβ hWβ0 hs hdisj hK' hp₂) e
    have e2 := injOn_revChart hWβ hWβ0 hs (hGs _ hp₁) (hGs _ hp₂) e1
    have e3 : negInv z₁ = negInv z₂ := by
      rw [← QuantumZipper.RS.fwdMap_fwdMapInv hWα hWα0 ht (negInv_mem_H hz₁.1), e2,
        QuantumZipper.RS.fwdMap_fwdMapInv hWα hWα0 ht (negInv_mem_H hz₂.1)]
    rw [← negInv_negInv' z₁, e3, negInv_negInv']
  · -- surjectivity
    have hy' : y ∈ H := hy
    have hζ := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW' hW'0 hT hy'
    set ζ := fwdMapInv W' T y
    have hpG := revChartInv_mem hWβ hWβ0 hs hζ.1
    set p := revChartInv Wβ s ζ
    have hpA : p ∉ fwdHull Wα t := fun hA => by
      apply hζ.2
      rw [hK', ← revChart_revChartInv hWβ hWβ0 hs hζ.1]
      exact mem_image_of_mem _ hA
    have hpC : p ∈ H \ fwdHull Wα t := ⟨hpG.1, hpA⟩
    set ξ := fwdMap Wα t p
    have hξH : ξ ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht hpC
    have hξG : ξ ∉ negInv '' K2 := by
      rw [← hfG]
      rintro ⟨g, hg, hge⟩
      have hgA : g ∈ H \ fwdHull Wα t := by
        obtain ⟨k, hk, rfl⟩ := hg
        exact ⟨negInv_mem_H ((isHPHull_fwdHull hWβ hs).1 hk), fun h => disjoint_left.1 hdisj h ⟨k, hk, rfl⟩⟩
      have := injOn_fwdMap' hWα hWα0 ht hgA hpC hge
      exact hpG.2 (this ▸ hg)
    refine ⟨negInv ξ, ⟨negInv_mem_H hξH, fun hK => hξG ⟨negInv ξ, hK, negInv_negInv' ξ⟩⟩, ?_⟩
    show fwdMap W' T (revChart Wβ s (fwdMapInv Wα t (negInv (negInv ξ)))) = y
    rw [negInv_negInv', QuantumZipper.RS.fwdMapInv_fwdMap hWα hWα0 ht hpC, revChart_revChartInv hWβ hWβ0 hs hζ.1,
      QuantumZipper.RS.fwdMap_fwdMapInv hW' hW'0 hT hy']

/-- **The transition map is a Möbius image of a hull map** (G3 (ii), Proposition 4.9 direction). Under the hypotheses
of Aux. 8 for the obstacle `R(A)` (the flow hull reaches `ℝ` only at `0`; the counterflow hull and `R(A)` have disjoint
closures), the hull `K″ = Ψ_t(K′)` is a Loewner hull `fwdHull W'' τ`, and on `ℍ ∖ f_t(G) = ℍ ∖ R(K″)` the transition map
is `φ(ξ) = N(g''(R ξ))`, `g'' = fwdMap W'' τ + W''(τ)`, for a real Möbius map `N` of positive determinant. -/
theorem exists_imgPhi_eq_realMobius (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 ≤ t)
    (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hdis : Disjoint (closure (fwdHull Wβ s)) (closure (negInv '' fwdHull Wα t)))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) :
    ∃ (W'' : ℝ → ℝ) (τ a b c d : ℝ), Continuous W'' ∧ W'' 0 = 0 ∧ 0 ≤ τ ∧
      fwdHull W'' τ = revChart Wα t '' fwdHull Wβ s ∧ 0 < a * d - b * c ∧
      ∀ ξ ∈ H \ negInv '' fwdHull W'' τ,
        imgPhi Wα t Wβ s W' T ξ = realMobius a b c d (fwdMap W'' τ (negInv ξ) + W'' τ) := by
  obtain ⟨τf, W'', hW''c, hW''0, hτ0, hτmono, -, hτ⟩ :=
    Aux8Inf.exists_loewner_revChart_image hWα hWα0 ht hKt hWβ hWβ0 hs hdis
  have hK2 := (hτ s ⟨hs, le_rfl⟩).2
  have hτs : 0 ≤ τf s := by
    rw [← hτ0]
    exact hτmono.monotoneOn ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs
  have hA := isHPHull_fwdHull hW''c hτs
  have hg := isMapOut_fwdMap hW''c hW''0 hτs
  have hG := isConformalBijection_imgPhi_negInv hWα hWα0 ht hWβ hWβ0 hs hW' hW'0 hT hdisj hK'
  rw [← hK2] at hG
  obtain ⟨a, b, c, d, hdet, hconj⟩ := CrossRestart.exists_realMobius_conj hA hg differentiableOn_id
    (bijOn_id _) hG
  refine ⟨W'', τf s, a, b, c, d, hW''c, hW''0, hτs, hK2, hdet, fun ξ hξ => ?_⟩
  have hz := Aux8Inf.negInv_mem_H_diff hξ.1 hξ.2
  have := hconj _ hz
  simpa only [id, negInv_negInv'] using this

/-! ### The real line of the flow chart is free of `f_t(G)` -/

/-- **No real point is a limit of `f_t(G)`** when `G` is closed, inside `ℍ` and disjoint from the flow hull `A` (a
generated hull): a limit `f_t(g_n) → x` would give `g_n = F_t(f_t(g_n)) → F̄_t(x) ∉ ℍ ∖ A` (boundary extension of
`F_t`), while `G` is closed in `ℍ ∖ A`. -/
theorem ofReal_notMem_closure_fwdMap_image {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hWα : Continuous Wα)
    (hWα0 : Wα 0 = 0) (ht : 0 ≤ t) {G : Set ℂ} (hGc : IsClosed G) (hGH : G ⊆ H)
    (hdisj : Disjoint (fwdHull Wα t) G) (x : ℝ) : (x : ℂ) ∉ closure (fwdMap Wα t '' G) := by
  intro hx
  have hxH : (x : ℂ) ∈ QuantumZipper.Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hGA : ∀ g ∈ G, g ∈ H \ fwdHull Wα t := fun g hg => ⟨hGH hg, fun h => disjoint_left.1 hdisj h hg⟩
  have hfGH : fwdMap Wα t '' G ⊆ H := by
    rintro _ ⟨g, hg, rfl⟩
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht (hGA g hg)
  have : (𝓝[fwdMap Wα t '' G] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hx
  have hlim := ((hα.hasBdryLimits hWα hWα0 ht).tendsto hxH).mono_left (nhdsWithin_mono _ hfGH)
  have hmem : extendFrom H (fwdMapInv Wα t) x ∈ G := by
    refine hGc.mem_of_tendsto hlim (eventually_nhdsWithin_of_forall ?_)
    rintro _ ⟨g, hg, rfl⟩
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hWα hWα0 ht (hGA g hg)]
    exact hg
  exact hα.extendFrom_not_mem hWα hWα0 ht (by simp) (hGA _ hmem)

/-- **The hull `K″ = Ψ_t(K′)` reaches `ℝ` at most at `0`**: every real `x ≠ 0` has a ball disjoint from `K″`. -/
theorem exists_ball_disjoint_revChart_image {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hWα : Continuous Wα)
    (hWα0 : Wα 0 = 0) (ht : 0 ≤ t) {K : Set ℂ} (hGc : IsClosed (negInv '' K)) (hGH : negInv '' K ⊆ H)
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' K)) {x : ℝ} (hx : x ≠ 0) :
    ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (revChart Wα t '' K) := by
  have hR := ofReal_notMem_closure_fwdMap_image hα hWα hWα0 ht hGc hGH hdisj (-x⁻¹)
  rw [fwdMap_image_negInv_eq, mem_closure_iff_nhds] at hR
  push Not at hR
  obtain ⟨U, hU, hUe⟩ := hR
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hc : ContinuousAt negInv (x : ℂ) := continuousAt_negInv hx0
  have hval : negInv (x : ℂ) = ((-x⁻¹ : ℝ) : ℂ) := by simp [negInv]
  rw [← hval] at hU
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 (hc.preimage_mem_nhds hU)
  refine ⟨ρ, hρ, disjoint_left.2 fun z hz hzK => ?_⟩
  have h1 : negInv z ∈ U := hball hz
  exact (eq_empty_iff_forall_notMem.1 hUe) (negInv z) ⟨h1, z, hzK, rfl⟩

/-! ### Reflection of the transition map across the real line -/

theorem hasDerivAt_realMobius {a b c d : ℝ} {w : ℂ} (hw : (c : ℂ) * w + d ≠ 0) :
    HasDerivAt (realMobius a b c d) (((a * d - b * c : ℝ) : ℂ) / ((c : ℂ) * w + d) ^ 2) w := by
  have h1 : HasDerivAt (fun z : ℂ => (a : ℂ) * z + b) a w := by
    simpa using ((hasDerivAt_id w).const_mul (a : ℂ)).add_const (b : ℂ)
  have h2 : HasDerivAt (fun z : ℂ => (c : ℂ) * z + d) c w := by
    simpa using ((hasDerivAt_id w).const_mul (c : ℂ)).add_const (d : ℂ)
  have h := h1.div h2 hw
  have e : ((a : ℂ) * ((c : ℂ) * w + d) - ((a : ℂ) * w + b) * c) / ((c : ℂ) * w + d) ^ 2 =
      ((a * d - b * c : ℝ) : ℂ) / ((c : ℂ) * w + d) ^ 2 := by push_cast; ring
  rw [e] at h
  exact h

theorem realMobius_conj (a b c d : ℝ) (z : ℂ) : realMobius a b c d (conj z) = conj (realMobius a b c d z) := by
  simp [realMobius, map_div₀, Complex.conj_ofReal]

theorem negInv_conj (z : ℂ) : negInv (conj z) = conj (negInv z) := by simp [negInv]

/-- **The transition map extends across a real point** `x₁ ≠ 0` at which `R(x₁)` is off the hull `K″`, provided it has
a finite limit along some ultrafilter at `x₁` (which excludes the pole of the Möbius factor): it extends to a
holomorphic map on a ball around `x₁`, commuting with `conj`, with real positive derivative at `x₁`. -/
theorem exists_reflection_imgPhi {W'' : ℝ → ℝ} {τ a b c d : ℝ} (hW'' : Continuous W'') (hW''0 : W'' 0 = 0)
    (hτ : 0 ≤ τ) (hdet : 0 < a * d - b * c)
    (hdecomp : ∀ ξ ∈ H \ negInv '' fwdHull W'' τ,
      imgPhi Wα t Wβ s W' T ξ = realMobius a b c d (fwdMap W'' τ (negInv ξ) + W'' τ))
    {x₁ : ℝ} (hx₁ : x₁ ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) (hdK : Disjoint (ball ((-x₁⁻¹ : ℝ) : ℂ) ρ) (fwdHull W'' τ))
    {y₀ : ℂ} {U : Ultrafilter ℂ} (hU : (U : Filter ℂ) ≤ 𝓝[H] (x₁ : ℂ))
    (hlim : Tendsto (imgPhi Wα t Wβ s W' T) U (𝓝 y₀)) :
    ∃ r > 0, ∃ Φt : ℂ → ℂ, DifferentiableOn ℂ Φt (ball (x₁ : ℂ) r) ∧
      EqOn Φt (imgPhi Wα t Wβ s W' T) (ball (x₁ : ℂ) r ∩ H) ∧
      (∀ ξ ∈ ball (x₁ : ℂ) r, Φt (conj ξ) = conj (Φt ξ)) ∧
      (deriv Φt x₁).im = 0 ∧ 0 < (deriv Φt x₁).re ∧ ball (x₁ : ℂ) r ∩ H ⊆ H \ negInv '' fwdHull W'' τ := by
  set K := fwdHull W'' τ with hKdef
  set x₀ : ℝ := -x₁⁻¹ with hx₀
  have hA := isHPHull_fwdHull hW'' hτ
  have hg := isMapOut_fwdMap hW'' hW''0 hτ
  obtain ⟨Gh, hG⟩ := Sec7.exists_isBdryReflection hA hg hρ hdK
  set rG := ρ / 2 with hrG
  have hrG0 : 0 < rG := hG.pos
  have hx₁c : (x₁ : ℂ) ≠ 0 := by exact_mod_cast hx₁
  have hnx : negInv (x₁ : ℂ) = (x₀ : ℂ) := by simp [negInv, hx₀]
  have hx₀B : (x₀ : ℂ) ∈ ball (x₀ : ℂ) rG := mem_ball_self hrG0
  have hGc : ContinuousAt Gh (x₀ : ℂ) := (hG.diff.differentiableAt (isOpen_ball.mem_nhds hx₀B)).continuousAt
  set w₀ := Gh x₀ with hw₀
  have hw₀im : w₀.im = 0 := hG.real_of_im _ hx₀B (by simp)
  have hnc : ContinuousAt negInv (x₁ : ℂ) := continuousAt_negInv hx₁c
  -- the pole is excluded by the finite limit
  have hden : (c : ℂ) * w₀ + d ≠ 0 := by
    intro h0
    have hc : c ≠ 0 := by
      intro hc0
      rw [hc0] at h0 hdet
      have : (d : ℂ) = 0 := by simpa using h0
      have hd : d = 0 := by exact_mod_cast this
      rw [hd] at hdet; simp at hdet
    have hpole : w₀ = (CrossRestart.mobPole c d : ℂ) := by
      have hw : w₀ = ((w₀.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hw₀im])
      rw [hw] at h0 ⊢
      have h0' : c * w₀.re + d = 0 := by exact_mod_cast h0
      congr 1
      rw [CrossRestart.mobPole]
      field_simp
      linear_combination h0'
    have hUH : ∀ᶠ ξ in (U : Filter ℂ), ξ ∈ H := hU self_mem_nhdsWithin
    have hUx : Tendsto (fun ξ : ℂ => ξ) (U : Filter ℂ) (𝓝 (x₁ : ℂ)) := hU.trans nhdsWithin_le_nhds
    have hneg : Tendsto negInv (U : Filter ℂ) (𝓝 (x₀ : ℂ)) := by rw [← hnx]; exact hnc.tendsto.comp hUx
    have hballU : ∀ᶠ ξ in (U : Filter ℂ), negInv ξ ∈ ball (x₀ : ℂ) rG := hneg (isOpen_ball.mem_nhds hx₀B)
    have hmemK : ∀ᶠ ξ in (U : Filter ℂ), ξ ∈ H \ negInv '' K := by
      filter_upwards [hUH, hballU] with ξ hξ hb
      refine ⟨hξ, ?_⟩
      rintro ⟨k, hk, hke⟩
      have : negInv ξ = k := by rw [← hke, negInv_negInv']
      exact disjoint_left.1 hG.disj (ball_subset_ball (by linarith) hb) (this ▸ hk)
    have hgv : Tendsto (fun ξ => fwdMap W'' τ (negInv ξ) + W'' τ) (U : Filter ℂ)
        (𝓝 (CrossRestart.mobPole c d : ℂ)) := by
      rw [← hpole]
      refine (hGc.tendsto.comp hneg).congr' ?_
      filter_upwards [hUH, hballU] with ξ hξ hb
      exact hG.eqOn ⟨hb, negInv_mem_H hξ⟩
    have hgH : ∀ᶠ ξ in (U : Filter ℂ), fwdMap W'' τ (negInv ξ) + W'' τ ∈ H := by
      filter_upwards [hmemK] with ξ hξ
      exact hg.1.2.mapsTo (Aux8Inf.negInv_mem_H_diff hξ.1 hξ.2)
    have h1 := Aux8Inf.tendsto_negInv_realMobius_of_tendsto_pole hdet hc hgv hgH
    have h2 : Tendsto (fun ξ => negInv (imgPhi Wα t Wβ s W' T ξ)) (U : Filter ℂ) (𝓝 0) := by
      refine h1.congr' ?_
      filter_upwards [hmemK] with ξ hξ
      rw [hdecomp ξ hξ]
    -- `‖φ‖` stays bounded while `‖R ∘ φ‖ → 0`
    have hb1 : ∀ᶠ ξ in (U : Filter ℂ), ‖imgPhi Wα t Wβ s W' T ξ‖ < ‖y₀‖ + 1 := by
      have := (continuous_norm.tendsto y₀).comp hlim
      exact this (Iio_mem_nhds (by linarith))
    have hb2 : ∀ᶠ ξ in (U : Filter ℂ), ‖negInv (imgPhi Wα t Wβ s W' T ξ)‖ < 1 / (‖y₀‖ + 1) := by
      have := (continuous_norm.tendsto (0 : ℂ)).comp h2
      rw [norm_zero] at this
      exact this (Iio_mem_nhds (by positivity))
    obtain ⟨ξ, h3, h4, h5, h6⟩ := (hb1.and (hb2.and (hmemK.and hgH))).exists
    set v := imgPhi Wα t Wβ s W' T ξ
    have hv0 : v ≠ 0 := by
      have hvH : v ∈ H := by
        rw [show v = _ from hdecomp ξ h5]
        exact (QuantumZipper.CA.bijOn_realMobius_H hdet).mapsTo h6
      exact Aux8Inf.ne_zero_of_mem_H' hvH
    have hnv : ‖negInv v‖ = 1 / ‖v‖ := by simp [negInv, norm_inv]
    rw [hnv, div_lt_div_iff₀ (norm_pos_iff.2 hv0) (by positivity)] at h4
    nlinarith [norm_nonneg y₀]
  -- the extension `Φt = N ∘ Gh ∘ R` near `x₁`
  have hGn : ContinuousAt (fun ξ => Gh (negInv ξ)) (x₁ : ℂ) := by
    have h : ContinuousAt Gh (negInv (x₁ : ℂ)) := by rw [hnx]; exact hGc
    exact h.comp hnc
  have hneg : Tendsto negInv (𝓝 (x₁ : ℂ)) (𝓝 (x₀ : ℂ)) := by rw [← hnx]; exact hnc.tendsto
  have hdenc : ContinuousAt (fun ξ => (c : ℂ) * Gh (negInv ξ) + d) (x₁ : ℂ) :=
    (continuousAt_const.mul hGn).add continuousAt_const
  have hev : ∀ᶠ ξ in 𝓝 (x₁ : ℂ), ξ ≠ 0 ∧ negInv ξ ∈ ball (x₀ : ℂ) rG ∧ (c : ℂ) * Gh (negInv ξ) + d ≠ 0 :=
    (eventually_ne_nhds hx₁c).and ((hneg.eventually (isOpen_ball.mem_nhds hx₀B)).and
      (hdenc.eventually_ne (by rw [hnx]; exact hden)))
  obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hsub : ball (x₁ : ℂ) r ∩ H ⊆ H \ negInv '' K := by
    rintro ξ ⟨hξ, hξH⟩
    refine ⟨hξH, ?_⟩
    rintro ⟨k, hk, hke⟩
    have : negInv ξ = k := by rw [← hke, negInv_negInv']
    exact disjoint_left.1 hG.disj (ball_subset_ball (by linarith) (hrb ξ hξ).2.1) (this ▸ hk)
  refine ⟨r, hr, fun ξ => realMobius a b c d (Gh (negInv ξ)), fun ξ hξ => ?_, fun ξ hξ => ?_, fun ξ hξ => ?_, ?_⟩
  · obtain ⟨h0, hb, hd⟩ := hrb ξ hξ
    have d1 : DifferentiableAt ℂ negInv ξ := (differentiableAt_inv h0).neg
    have d2 : DifferentiableAt ℂ Gh (negInv ξ) := hG.diff.differentiableAt (isOpen_ball.mem_nhds hb)
    exact ((hasDerivAt_realMobius hd).differentiableAt.comp ξ (d2.comp ξ d1)).differentiableWithinAt
  · show realMobius a b c d (Gh (negInv ξ)) = imgPhi Wα t Wβ s W' T ξ
    rw [hdecomp ξ (hsub hξ), hG.eqOn ⟨(hrb ξ hξ.1).2.1, negInv_mem_H hξ.2⟩]
  · have hcξ : conj ξ ∈ ball (x₁ : ℂ) r := by
      rw [mem_ball, dist_eq_norm] at hξ ⊢
      rw [show conj ξ - (x₁ : ℂ) = conj (ξ - x₁) by simp, Complex.norm_conj]
      exact hξ
    show realMobius a b c d (Gh (negInv (conj ξ))) = conj (realMobius a b c d (Gh (negInv ξ)))
    rw [negInv_conj, hG.map_conj _ (hrb ξ hξ).2.1, realMobius_conj]
  · have d1 : HasDerivAt negInv (((x₁ : ℂ) ^ 2)⁻¹) (x₁ : ℂ) := by
      have := (hasDerivAt_inv hx₁c).neg
      rw [neg_neg] at this
      exact this
    have d2 : HasDerivAt Gh (deriv Gh (x₀ : ℂ)) (negInv (x₁ : ℂ)) := by
      rw [hnx]; exact (hG.diff.differentiableAt (isOpen_ball.mem_nhds hx₀B)).hasDerivAt
    have hd' : (c : ℂ) * Gh (negInv (x₁ : ℂ)) + d ≠ 0 := by rw [hnx]; exact hden
    have hD := (hasDerivAt_realMobius (a := a) (b := b) hd').comp (x₁ : ℂ) (d2.comp (x₁ : ℂ) d1)
    have hDd : deriv (fun ξ => realMobius a b c d (Gh (negInv ξ))) (x₁ : ℂ) =
        ((a * d - b * c : ℝ) : ℂ) / ((c : ℂ) * Gh (negInv (x₁ : ℂ)) + d) ^ 2 *
          (deriv Gh (x₀ : ℂ) * ((x₁ : ℂ) ^ 2)⁻¹) := hD.deriv
    rw [hDd, hnx]
    obtain ⟨hGim, hGre⟩ := hG.deriv_im_eq_zero_and_re_pos hg
    set q := deriv Gh (x₀ : ℂ) with hqdef
    have hq : q = ((q.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hGim])
    have hw : w₀ = ((w₀.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hw₀im])
    set e := c * w₀.re + d with hedef
    have he : (c : ℂ) * w₀ + d = (e : ℂ) := by rw [hedef]; push_cast; rw [← hw]
    have he0 : e ≠ 0 := by
      intro h; apply hden; rw [he, h, Complex.ofReal_zero]
    have key : ((a * d - b * c : ℝ) : ℂ) / ((c : ℂ) * w₀ + d) ^ 2 * (q * ((x₁ : ℂ) ^ 2)⁻¹) =
        (((a * d - b * c) / e ^ 2 * (q.re * (x₁ ^ 2)⁻¹) : ℝ) : ℂ) := by
      rw [he]; conv_lhs => rw [hq]
      push_cast; ring
    rw [key, Complex.ofReal_im, Complex.ofReal_re]
    refine ⟨rfl, ?_, hsub⟩
    have he2 : 0 < e ^ 2 := by positivity
    have hx2 : 0 < x₁ ^ 2 := by positivity
    positivity

/-! ### The inverse transition map and its local inverse form -/

/-- The **inverse transition map** `Θ = f_t ∘ Ψ⁻¹ ∘ F'_T : ℍ → ℍ ∖ f_t(G)` (the image chart read in the flow chart). -/
def imgTheta (Wα : ℝ → ℝ) (t : ℝ) (Wβ : ℝ → ℝ) (s : ℝ) (W' : ℝ → ℝ) (T : ℝ) (y : ℂ) : ℂ :=
  fwdMap Wα t (revChartInv Wβ s (fwdMapInv W' T y))

theorem revChartInv_fwdMapInv_mem (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0)
    (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) {y : ℂ} (hy : y ∈ H) :
    revChartInv Wβ s (fwdMapInv W' T y) ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s) := by
  have hζ := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW' hW'0 hT hy
  have hpG := revChartInv_mem hWβ hWβ0 hs hζ.1
  refine ⟨hpG.1, ?_⟩
  rintro (hA | hG)
  · apply hζ.2
    rw [hK', ← revChart_revChartInv hWβ hWβ0 hs hζ.1]
    exact mem_image_of_mem _ hA
  · exact hpG.2 hG

theorem imgPhi_mem_H (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 ≤ t) (hWβ : Continuous Wβ)
    (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hT : 0 ≤ T) (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) {ξ : ℂ}
    (hξ : ξ ∈ H \ fwdMap Wα t '' (negInv '' fwdHull Wβ s)) (hW' : Continuous W') : imgPhi Wα t Wβ s W' T ξ ∈ H :=
  QuantumZipper.FwdHolo.mapsTo_fwdMap hW' hT
    (revChart_mem_compl_imgHull hWα ht hWβ hWβ0 hs hdisj hK' (fwdMapInv_mem_union_compl hWα hWα0 ht hξ))

theorem imgTheta_imgPhi (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 ≤ t) (hWβ : Continuous Wβ)
    (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) {ξ : ℂ}
    (hξ : ξ ∈ H \ fwdMap Wα t '' (negInv '' fwdHull Wβ s)) :
    imgTheta Wα t Wβ s W' T (imgPhi Wα t Wβ s W' T ξ) = ξ := by
  have hp := fwdMapInv_mem_union_compl hWα hWα0 ht hξ
  have hq := revChart_mem_compl_imgHull hWα ht hWβ hWβ0 hs hdisj hK' hp
  rw [imgTheta, imgPhi, QuantumZipper.RS.fwdMapInv_fwdMap hW' hW'0 hT hq,
    revChartInv_revChart hWβ hWβ0 hs ⟨hp.1, fun h => hp.2 (Or.inr h)⟩,
    QuantumZipper.RS.fwdMap_fwdMapInv hWα hWα0 ht hξ.1]

theorem imgPhi_imgTheta (hWα : Continuous Wα) (ht : 0 ≤ t) (hWβ : Continuous Wβ)
    (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) (hWα0 : Wα 0 = 0) {y : ℂ} (hy : y ∈ H) :
    imgPhi Wα t Wβ s W' T (imgTheta Wα t Wβ s W' T y) = y := by
  have hp := revChartInv_fwdMapInv_mem hWβ hWβ0 hs hW' hW'0 hT hK' hy
  rw [imgPhi, imgTheta, QuantumZipper.RS.fwdMapInv_fwdMap hWα hWα0 ht ⟨hp.1, fun h => hp.2 (Or.inl h)⟩,
    revChart_revChartInv hWβ hWβ0 hs (QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT hy),
    QuantumZipper.RS.fwdMap_fwdMapInv hW' hW'0 hT hy]

theorem differentiableAt_imgTheta (hWα : Continuous Wα) (ht : 0 ≤ t) (hWβ : Continuous Wβ)
    (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) {y : ℂ} (hy : y ∈ H) :
    DifferentiableAt ℂ (imgTheta Wα t Wβ s W' T) y := by
  have hζ := QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT hy
  have hp := revChartInv_fwdMapInv_mem hWβ hWβ0 hs hW' hW'0 hT hK' hy
  have hpA : revChartInv Wβ s (fwdMapInv W' T y) ∈ H \ fwdHull Wα t := ⟨hp.1, fun h => hp.2 (Or.inl h)⟩
  have d1 : DifferentiableAt ℂ (fwdMapInv W' T) y :=
    (QuantumZipper.RS.differentiableOn_fwdMapInv hW' hW'0 hT).differentiableAt (QuantumZipper.isOpen_H.mem_nhds hy)
  have d2 : DifferentiableAt ℂ (revChartInv Wβ s) (fwdMapInv W' T y) :=
    (isConformalBijection_revChartInv hWβ hWβ0 hs).1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hζ)
  have d3 : DifferentiableAt ℂ (fwdMap Wα t) (revChartInv Wβ s (fwdMapInv W' T y)) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWα ht _ hpA).differentiableAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWα ht).mem_nhds hpA)
  exact d3.comp y (d2.comp y d1)

/-- **The inverse transition map near a reflected real point.** If the transition map `φ` extends across the real
point `x₁` to a holomorphic `Φt` commuting with `conj`, with `Φt′(x₁) ≠ 0`, then near `y₁ = Φt(x₁)` the inverse map
`Θ` is the local inverse of `Φt`: `Θ(y) → x₁` and `Θ′(y) → Φt′(x₁)⁻¹` as `y → y₁` in `ℍ`. -/
theorem tendsto_imgTheta_of_reflection (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 ≤ t) (hWβ : Continuous Wβ)
    (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) {x₁ r : ℝ} (hr : 0 < r) {Φt : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φt (ball (x₁ : ℂ) r)) (hΦeq : EqOn Φt (imgPhi Wα t Wβ s W' T) (ball (x₁ : ℂ) r ∩ H))
    (hconj : ∀ ξ ∈ ball (x₁ : ℂ) r, Φt (conj ξ) = conj (Φt ξ)) (hd0 : deriv Φt x₁ ≠ 0)
    (hsub : ball (x₁ : ℂ) r ∩ H ⊆ H \ fwdMap Wα t '' (negInv '' fwdHull Wβ s)) :
    Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (Φt x₁)) (𝓝 (x₁ : ℂ)) ∧
      Tendsto (deriv (imgTheta Wα t Wβ s W' T)) (𝓝[H] (Φt x₁)) (𝓝 (deriv Φt x₁)⁻¹) := by
  have hx₁B : (x₁ : ℂ) ∈ ball (x₁ : ℂ) r := mem_ball_self hr
  have hs' : HasStrictDerivAt Φt (deriv Φt x₁) x₁ :=
    (hΦd.analyticAt (isOpen_ball.mem_nhds hx₁B)).hasStrictDerivAt
  set g := hs'.localInverse Φt (deriv Φt x₁) x₁ hd0 with hgdef
  have hg1 : g (Φt x₁) = x₁ := (hs'.eventually_left_inverse hd0).self_of_nhds
  have hgc : ContinuousAt g (Φt x₁) := (hs'.to_localInverse hd0).hasDerivAt.continuousAt
  have hgB : ∀ᶠ y in 𝓝 (Φt x₁), g y ∈ ball (x₁ : ℂ) r := by
    have := hgc.tendsto
    rw [hg1] at this
    exact this (isOpen_ball.mem_nhds hx₁B)
  have hright := hs'.eventually_right_inverse hd0
  -- `Θ = g` near `y₁` in `ℍ`
  have heq : ∀ᶠ y in 𝓝[H] (Φt x₁), imgTheta Wα t Wβ s W' T y = g y := by
    filter_upwards [nhdsWithin_le_nhds (hgB.and hright), self_mem_nhdsWithin] with y ⟨hyB, hyr⟩ hyH
    have hyH' : (0 : ℝ) < y.im := hyH
    have hgH : g y ∈ H := by
      by_contra hn
      have hle : (g y).im ≤ 0 := not_lt.1 hn
      rcases hle.lt_or_eq with hlt | h0
      · have hcB : conj (g y) ∈ ball (x₁ : ℂ) r := by
          rw [mem_ball, dist_eq_norm] at hyB ⊢
          rw [show conj (g y) - (x₁ : ℂ) = conj (g y - x₁) by simp, Complex.norm_conj]
          exact hyB
        have hcH : conj (g y) ∈ H := show (0 : ℝ) < (conj (g y)).im by simp; linarith
        have h1 := hconj _ hcB
        rw [Complex.conj_conj] at h1
        have h2 := imgPhi_mem_H hWα hWα0 ht hWβ hWβ0 hs hT hdisj hK' (hsub ⟨hcB, hcH⟩) hW'
        rw [← hΦeq ⟨hcB, hcH⟩] at h2
        have h2' : 0 < (Φt (conj (g y))).im := h2
        have h3 : (Φt (g y)).im < 0 := by rw [h1]; simpa using h2'
        rw [hyr] at h3
        linarith
      · have hc : conj (g y) = g y := Complex.conj_eq_iff_im.2 h0
        have h1 := hconj _ hyB
        rw [hc, hyr] at h1
        have := congrArg Complex.im h1
        simp at this
        linarith
    have hmem := hsub ⟨hyB, hgH⟩
    have e1 : imgPhi Wα t Wβ s W' T (g y) = y := by rw [← hΦeq ⟨hyB, hgH⟩]; exact hyr
    calc imgTheta Wα t Wβ s W' T y = imgTheta Wα t Wβ s W' T (imgPhi Wα t Wβ s W' T (g y)) := by rw [e1]
      _ = g y := imgTheta_imgPhi hWα hWα0 ht hWβ hWβ0 hs hW' hW'0 hT hdisj hK' hmem
  have h1 : Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (Φt x₁)) (𝓝 (x₁ : ℂ)) := by
    have := hgc.tendsto.mono_left (nhdsWithin_le_nhds (s := H))
    rw [hg1] at this
    exact this.congr' (heq.mono fun y hy => hy.symm)
  refine ⟨h1, ?_⟩
  -- the derivative
  have hΦ'c : ContinuousAt (deriv Φt) (x₁ : ℂ) :=
    ((hΦd.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hx₁B)).continuousAt
  have h2 : Tendsto (fun y => (deriv Φt (imgTheta Wα t Wβ s W' T y))⁻¹) (𝓝[H] (Φt x₁)) (𝓝 (deriv Φt x₁)⁻¹) :=
    ((continuousAt_inv₀ hd0).tendsto.comp hΦ'c.tendsto).comp h1
  refine h2.congr' ?_
  filter_upwards [h1 (isOpen_ball.mem_nhds hx₁B), self_mem_nhdsWithin] with y hyB hyH
  set θ := imgTheta Wα t Wβ s W' T y with hθ
  have hθH : θ ∈ H := by
    have hp := revChartInv_fwdMapInv_mem hWβ hWβ0 hs hW' hW'0 hT hK' hyH
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht ⟨hp.1, fun h => hp.2 (Or.inl h)⟩
  have hOpen : IsOpen (ball (x₁ : ℂ) r ∩ H) := isOpen_ball.inter QuantumZipper.isOpen_H
  have hΦθ : HasDerivAt (imgPhi Wα t Wβ s W' T) (deriv Φt θ) θ := by
    have hd : HasDerivAt Φt (deriv Φt θ) θ := (hΦd.differentiableAt (isOpen_ball.mem_nhds hyB)).hasDerivAt
    exact hd.congr_of_eventuallyEq
      (Filter.eventually_of_mem (hOpen.mem_nhds ⟨hyB, hθH⟩) fun z hz => (hΦeq hz).symm)
  have hΘd : HasDerivAt (imgTheta Wα t Wβ s W' T) (deriv (imgTheta Wα t Wβ s W' T) y) y :=
    (differentiableAt_imgTheta hWα ht hWβ hWβ0 hs hW' hW'0 hT hK' hyH).hasDerivAt
  have hcomp := hΦθ.comp y hΘd
  have hid : HasDerivAt (imgPhi Wα t Wβ s W' T ∘ imgTheta Wα t Wβ s W' T) 1 y :=
    (hasDerivAt_id y).congr_of_eventuallyEq (Filter.eventually_of_mem (QuantumZipper.isOpen_H.mem_nhds hyH)
      fun z hz => imgPhi_imgTheta hWα ht hWβ hWβ0 hs hW' hW'0 hT hK' hWα0 hz)
  exact (eq_inv_of_mul_eq_one_right (hcomp.unique hid)).symm

/-- **Boundary correspondence on the flow side and the real line, at every real point with a real nonzero cluster
value.** Let `y₀` be a real point of the image chart such that `Θ = f_t ∘ Ψ⁻¹ ∘ F'_T` tends to a real `x₁ ≠ 0` along
some ultrafilter at `y₀` (within `ℍ`). Then `Θ(y) → x₁` as `y → y₀` in `ℍ` (no other cluster value), and `Θ′(y)` tends
to a positive real number. This is the boundary behaviour of the image chart at the sides of the flow slit and at the
original real line, for the non-simple counterflow hull (B14's separating-arc argument needed a simple reverse slit). -/
theorem tendsto_imgTheta_of_ultrafilter {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hWα : Continuous Wα)
    (hWα0 : Wα 0 = 0) (ht : 0 ≤ t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hGc : IsClosed (negInv '' fwdHull Wβ s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hdis : Disjoint (closure (fwdHull Wβ s)) (closure (negInv '' fwdHull Wα t)))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t)
    {y₀ : ℂ} {x₁ : ℝ} (hx₁ : x₁ ≠ 0) {U : Ultrafilter ℂ} (hU : (U : Filter ℂ) ≤ 𝓝[H] y₀)
    (hΘ : Tendsto (imgTheta Wα t Wβ s W' T) U (𝓝 (x₁ : ℂ))) :
    Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] y₀) (𝓝 (x₁ : ℂ)) ∧
      ∃ lam : ℝ, 0 < lam ∧ Tendsto (deriv (imgTheta Wα t Wβ s W' T)) (𝓝[H] y₀) (𝓝 (lam : ℂ)) := by
  obtain ⟨W'', τ, a, b, c, d, hW''c, hW''0, hτ, hK2, hdet, hdecomp⟩ :=
    exists_imgPhi_eq_realMobius hWα hWα0 ht hKt hWβ hWβ0 hs hW' hW'0 hT hdisj hdis hK'
  have hGH : negInv '' fwdHull Wβ s ⊆ H := by
    rintro _ ⟨k, hk, rfl⟩; exact negInv_mem_H ((isHPHull_fwdHull hWβ hs).1 hk)
  have hx₀ : (-x₁⁻¹ : ℝ) ≠ 0 := neg_ne_zero.2 (inv_ne_zero hx₁)
  obtain ⟨ρ, hρ, hdK⟩ := exists_ball_disjoint_revChart_image hα hWα hWα0 ht hGc hGH hdisj hx₀
  rw [← hK2] at hdK
  have hfG : negInv '' fwdHull W'' τ = fwdMap Wα t '' (negInv '' fwdHull Wβ s) := by
    rw [hK2, fwdMap_image_negInv_eq]
  -- the pushed ultrafilter at `x₁`
  have hUH : ∀ᶠ y in (U : Filter ℂ), y ∈ H := hU self_mem_nhdsWithin
  set U' := U.map (imgTheta Wα t Wβ s W' T)
  have hU' : (U' : Filter ℂ) ≤ 𝓝[H] (x₁ : ℂ) := by
    rw [Ultrafilter.coe_map]
    refine tendsto_nhdsWithin_iff.2 ⟨hΘ, hUH.mono fun y hy => ?_⟩
    have hp := revChartInv_fwdMapInv_mem hWβ hWβ0 hs hW' hW'0 hT hK' hy
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht ⟨hp.1, fun h => hp.2 (Or.inl h)⟩
  have hlim : Tendsto (imgPhi Wα t Wβ s W' T) U' (𝓝 y₀) := by
    rw [Ultrafilter.coe_map, tendsto_map'_iff]
    have hid : Tendsto (fun y : ℂ => y) (U : Filter ℂ) (𝓝 y₀) := hU.trans nhdsWithin_le_nhds
    refine hid.congr' (hUH.mono fun y hy => ?_)
    exact (imgPhi_imgTheta hWα ht hWβ hWβ0 hs hW' hW'0 hT hK' hWα0 hy).symm
  obtain ⟨r, hr, Φt, hΦd, hΦeq, hconj, hdim, hdre, hsub⟩ :=
    exists_reflection_imgPhi hW''c hW''0 hτ hdet hdecomp hx₁ hρ hdK hU' hlim
  -- `Φt(x₁) = y₀`
  have hx₁B : (x₁ : ℂ) ∈ ball (x₁ : ℂ) r := mem_ball_self hr
  have hΦc : ContinuousAt Φt (x₁ : ℂ) := (hΦd.differentiableAt (isOpen_ball.mem_nhds hx₁B)).continuousAt
  have hy₀ : Φt x₁ = y₀ := by
    have h1 : Tendsto Φt U' (𝓝 (Φt x₁)) := hΦc.tendsto.comp (hU'.trans nhdsWithin_le_nhds)
    have h2 : Tendsto Φt U' (𝓝 y₀) := by
      refine hlim.congr' ?_
      have : ∀ᶠ ξ in (U' : Filter ℂ), ξ ∈ ball (x₁ : ℂ) r ∩ H :=
        hU' (mem_nhdsWithin.2 ⟨ball (x₁ : ℂ) r, isOpen_ball, hx₁B, fun ξ hξ => ⟨hξ.1, hξ.2⟩⟩)
      exact this.mono fun ξ hξ => (hΦeq hξ).symm
    exact tendsto_nhds_unique h1 h2
  have hd0 : deriv Φt x₁ ≠ 0 := fun h => by rw [h] at hdre; simp at hdre
  rw [hfG] at hsub
  obtain ⟨h1, h2⟩ := tendsto_imgTheta_of_reflection hWα hWα0 ht hWβ hWβ0 hs hW' hW'0 hT hdisj hK' hr hΦd hΦeq
    hconj hd0 hsub
  rw [hy₀] at h1 h2
  refine ⟨h1, (deriv Φt x₁).re⁻¹, inv_pos.2 hdre, ?_⟩
  have e : (deriv Φt x₁)⁻¹ = (((deriv Φt x₁).re⁻¹ : ℝ) : ℂ) := by
    have hq : deriv Φt x₁ = (((deriv Φt x₁).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hdim])
    rw [hq]; push_cast; simp
  rwa [e] at h2

/-- **The sides of the flow slit** (Case H of the boundary correspondence, general `κ`, non-simple counterflow hull).
Let `α` be a simple proper flow trace, `η′` a generating trace of the image chain, and `x` a real point of the image
chart whose boundary image `F̄'_T(x)` is the image `Ψ(α(u))` of a non-tip point of the flow slit (`0 < u < t`). Then
`Θ(y) → x₁` as `y → x` in `ℍ` for a real `x₁ ≠ 0` with `F̄_t(x₁) = α(u)`, and `Θ′(y)` tends to a positive real. -/
theorem tendsto_imgTheta_of_mem_slit {α η' : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hη' : IsLoewnerTrace W' η') (hGc : IsClosed (negInv '' fwdHull Wβ s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hdis : Disjoint (closure (fwdHull Wβ s)) (closure (negInv '' fwdHull Wα t)))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) {x u : ℝ} (hu : 0 < u) (hut : u < t)
    (hFx : extendFrom H (fwdMapInv W' T) x = revChart Wβ s (α u)) :
    ∃ x₁ : ℝ, x₁ ≠ 0 ∧ extendFrom H (fwdMapInv Wα t) x₁ = α u ∧
      Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (x₁ : ℂ)) ∧
      ∃ lam : ℝ, 0 < lam ∧ Tendsto (deriv (imgTheta Wα t Wβ s W' T)) (𝓝[H] (x : ℂ)) (𝓝 (lam : ℂ)) := by
  have hxH : (x : ℂ) ∈ QuantumZipper.Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  set S := H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s) with hS
  have hαu : α u ∈ fwdHull Wα t := by rw [fwdHull_eq_image_Ioc hα hαp ht.le]; exact ⟨u, ⟨hu, hut.le⟩, rfl⟩
  have hαuG : α u ∈ H \ negInv '' fwdHull Wβ s :=
    ⟨hαp.mem_H u hu, fun h => disjoint_left.1 hdisj hαu h⟩
  -- `Φ(y) → α(u)` within `C`
  have hΦ : Tendsto (fun y => revChartInv Wβ s (fwdMapInv W' T y)) (𝓝[H] (x : ℂ)) (𝓝[S] (α u)) := by
    have h1 := (hη'.hasBdryLimits hW' hW'0 hT).tendsto hxH
    rw [hFx] at h1
    have hrH : revChart Wβ s (α u) ∈ H := revChart_mem_H hWβ hs hαuG
    have h2 : ContinuousAt (revChartInv Wβ s) (revChart Wβ s (α u)) :=
      (continuousOn_revChartInv hWβ hWβ0 hs).continuousAt (QuantumZipper.isOpen_H.mem_nhds hrH)
    have h3 := h2.tendsto.comp h1
    rw [revChartInv_revChart hWβ hWβ0 hs hαuG] at h3
    exact tendsto_nhdsWithin_iff.2 ⟨h3, eventually_nhdsWithin_of_forall fun y hy =>
      revChartInv_fwdMapInv_mem hWβ hWβ0 hs hW' hW'0 hT hK' hy⟩
  have : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ hxH)
  set U := Ultrafilter.of (𝓝[H] (x : ℂ))
  have hU : (U : Filter ℂ) ≤ 𝓝[H] (x : ℂ) := Ultrafilter.of_le _
  have hSA : S ⊆ H \ fwdHull Wα t := fun z hz => ⟨hz.1, fun h => hz.2 (Or.inl h)⟩
  obtain ⟨x₁, hx₁0, hFx₁, hlim₁, -⟩ := exists_real_tendsto_fwdMap hα hαp hWα hWα0 hu hut hSA
    (U.map fun y => revChartInv Wβ s (fwdMapInv W' T y)) (by rw [Ultrafilter.coe_map]; exact hΦ.mono_left hU)
  have hΘU : Tendsto (imgTheta Wα t Wβ s W' T) U (𝓝 (x₁ : ℂ)) := by
    have := (tendsto_nhdsWithin_iff.1 hlim₁).1
    rw [Ultrafilter.coe_map, tendsto_map'_iff] at this
    exact this
  obtain ⟨h1, h2⟩ := tendsto_imgTheta_of_ultrafilter hα hWα hWα0 ht.le hKt hWβ hWβ0 hs hW' hW'0 hT hGc hdisj hdis
    hK' hx₁0 hU hΘU
  exact ⟨x₁, hx₁0, hFx₁, h1, h2⟩

end Transition

end InteractingSLE.Sec5.GlueImg
