/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.D9Gap

/-!
# (D9), fourth part: two curves in separated enclosures

Packet PROVE-ZHAN-GT4-A6. Source: Astra, *Follow-up proofs*, Part A.1.3 (`ig1_followup_proofs.txt` L300–L340, ruling
R38): "the hull image interval stays a uniformly positive distance from both crosscut endpoint images … the integrand in
(D4) is bounded since the two image tips are separated."

Curve `1` (driver `W₁`, any start `x₁ = W₁ 0`) grows on `[0, T]` inside an enclosure `H₁`; curve `2` (driver `W₂`) is
frozen at time `t₂` with hull inside `H₂`; `ImgData` is the conformal-image data of curve `1` in the complement of
`K₂(t₂)`, in the chart `φ = g^{(2)}_{t₂}` of curve `2` (image driver `W'`, clock `a`). For a real point `q` with
`B(q, 2d)` missing `H₁ ∪ H₂` there is `γ > 0`, depending only on `H₁, H₂, q, d`, such that:

* `exists_le_norm_fwdMap_protected`: the image `p = g^{(2)}_{t₂}(q)` of `q` stays at distance `≥ γ` from the image driver:
  `γ ≤ |f̃_{a(s)}(p)|` (Koebe at `p` for the image chain, with the radius from Koebe for `g^{(2)}_{t₂}` at `q`; the two
  boundary derivatives multiply to the boundary derivative at `q` of the map of `K₁(s) ∪ K₂(t₂)`, which is at least that
  of the fixed hull `H₁ ∪ H₂`, `re_deriv_le_of_subset`);
* `exists_le_re_fwdMap_tip_right` / `exists_le_neg_re_fwdMap_tip_left`: **the separation `E` of the two image tips**: if
  `q` lies between the two starting points, `γ ≤ ±f̃_{a(s)}(W₂(t₂))` (order of real points along the image chain);
* `exists_exp_le_norm_deriv_refl_own`: **the own derivative factor from below** — `e^{−2t₂/γ²} ≤ |G'(W₁(s))|` for every
  Schwarz reflection `G` of every mapping-out function of `g^{(1)}_s(K₂(t₂))`, by the other-time ODE in the transposed
  configuration (curve `2` growing in the complement of `K₁(s)`, `ImgData.exp_neg_le_norm_deriv_fwdMap_image`) and the
  tip separation;
* marks: `ImgData.clock_le` (`a(s) ≤ s`), `ImgData.norm_fwdMap_sub_bounds` (the mutual distances `|C_{mn}|` change by at
  most `e^{±2a(s)/γ²}`), `exists_deriv_fwdMap_real_bounds` (the frozen curve's boundary derivative at a protected real
  point lies in `[m, 1]`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdHull logDerivFwd)

/-! ### Starting points -/

/-- The starting point `W 0` is in the closure of `K_T` for `T > 0` (any starting point). -/
theorem start_mem_closure_fwdHull {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T) :
    ((W 0 : ℝ) : ℂ) ∈ closure (fwdHull W T) := by
  set c := W 0 with hc
  set U : ℝ → ℝ := fun s => W s - c with hUdef
  have hU : Continuous U := hW.sub continuous_const
  have hU0 : U 0 = 0 := by simp [hUdef, hc]
  have hWU : W = fun s => U s + c := by funext s; simp [hUdef]
  have h0 := ConformalImageFull.zero_mem_closure_fwdHull hU hU0 hT
  have hcont : Continuous (fun z : ℂ => z + (c : ℂ)) := continuous_id.add continuous_const
  have himg := image_closure_subset_closure_image (s := fwdHull U T) hcont ⟨0, h0, rfl⟩
  rw [← ConformalImageFull.fwdHull_add_const, ← hWU] at himg
  simpa using himg

/-- At time `0` the centred map is the translation by the starting point. -/
theorem fwdMap_zero_gen {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} (hz : z ∈ H) (hzK : z ∉ fwdHull W 0) :
    fwdMap W 0 z = z - W 0 := by
  obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull le_rfl hz hzK
  rw [fwdMap_eq_of_isForwardSol hW hu ⟨le_rfl, le_rfl⟩, QuantumZipper.F1.isForwardSol_zero hu le_rfl]

/-- **The image driver starts at the image of the starting point**: if `φ` tends to `L` at `W 0`, then `W' 0 = L`. -/
theorem ImgData.W'_zero_eq {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ}
    (h : ImgData W A φ T a W') {L : ℂ} (hL : Tendsto φ (𝓝[H] (W 0 : ℂ)) (𝓝 L)) : (W' 0 : ℂ) = L := by
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, h.pos.le⟩
  have hdisj0 := h.disjoint_A_K h0mem
  have himg0 : (fun z => fwdMap W 0 z + W 0) '' A = A := by
    ext w; constructor
    · rintro ⟨z, hz, rfl⟩
      have hzK0 : z ∉ fwdHull W 0 := fun hz0 => Set.disjoint_left.1 hdisj0 hz hz0
      show fwdMap W 0 z + ((W 0 : ℝ) : ℂ) ∈ A
      rw [fwdMap_zero_gen h.cont (h.hull.1 hz) hzK0, sub_add_cancel]; exact hz
    · intro hw
      have hwK0 : w ∉ fwdHull W 0 := fun hw0 => Set.disjoint_left.1 hdisj0 hw hw0
      refine ⟨w, hw, ?_⟩
      show fwdMap W 0 w + ((W 0 : ℝ) : ℂ) = w
      rw [fwdMap_zero_gen h.cont (h.hull.1 hw) hwK0, sub_add_cancel]
  have hR : IsMapOut ((fun z => fwdMap W 0 z + W 0) '' A) φ := by rw [himg0]; exact h.mapOut
  have ht1 := (h.rate 0 h0mem φ hR).2.1
  rw [h.a0] at ht1
  have hne : (𝓝[H] ((W 0 : ℝ) : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  exact tendsto_nhds_unique ht1 hL

/-! ### The image of a protected real point -/

/-- **(D9), protected real points.** Fix compact `ℍ`-hulls `H₁, H₂` with disjoint closures and a real `q` with
`B(q, 2d)` missing `H₁ ∪ H₂`. There is `γ > 0` such that, for every curve `1` (driver `W₁`) growing in `H₁` on
`[0, T]`, every curve `2` (driver `W₂`, start in `closure H₂`) frozen at `t₂` with hull in `H₂`, and the
conformal-image data `ImgData` of curve `1` in curve `2`'s chart: the image `p = g^{(2)}_{t₂}(q)` is real, alive for the
image chain, and `γ ≤ |f̃_{a(s)}(p)|` for `s ∈ [0, T]`. -/
theorem exists_le_norm_fwdMap_protected {H₁ H₂ : Set ℂ} (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂)
    (hsep : Disjoint (closure H₁) (closure H₂)) {q d : ℝ} (hd : 0 < d)
    (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)) :
    ∃ γ > 0, ∀ (W₁ W₂ : ℝ → ℝ) (t₂ T : ℝ) (a W' : ℝ → ℝ),
      ImgData W₁ (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W' →
      Continuous W₂ → 0 ≤ t₂ → ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ →
      fwdHull W₁ T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
      ∀ s ∈ Icc (0 : ℝ) T, (∃ v, IsForwardSol W' ((((fwdMap W₂ t₂ q).re + W₂ t₂ : ℝ)) : ℂ) (a s) v) ∧
        γ ≤ ‖fwdMap W' (a s) (((fwdMap W₂ t₂ q).re + W₂ t₂ : ℝ) : ℂ)‖ := by
  -- the fixed constant: the boundary derivative of the map of `H₁ ∪ H₂` at `q`
  have hU : IsHPHull (H₁ ∪ H₂) := hH₁.union_of_disjoint_closure hH₂ hsep
  obtain ⟨gU, hgU⟩ := hU.exists_isMapOut
  have h2d : 0 < 2 * d := by linarith
  obtain ⟨GU, hGUd, hGUe, -, -, -, hGUinj, -, -, hGUreal⟩ :=
    ConformalImageFull.IsMapOut.exists_reflection_full hU hgU h2d hqH
  have e2d : 2 * d / 2 = d := by ring
  rw [e2d] at hGUd hGUe hGUinj hGUreal
  have hqd : Disjoint (ball (q : ℂ) d) (H₁ ∪ H₂) :=
    hqH.mono_left (ball_subset_ball (by linarith))
  obtain ⟨-, hm⟩ := deriv_refl_re_pos hgU hd hGUd hGUinj hGUe hGUreal hqd
  set m := (deriv GU q).re with hmdef
  refine ⟨d * m / 4608, by positivity, ?_⟩
  intro W₁ W₂ t₂ T a W' h hW₂ ht₂ hW₂H hK₁ hK₂ s hs
  have hW₁ := h.cont
  have hT := h.pos
  have hW'c := h.contW'
  set x₁ := W₁ 0 with hx₁def
  set A := fwdHull W₂ t₂ with hAdef
  set K := fwdHull W₁ T with hKdef
  set φ : ℂ → ℂ := fun z => fwdMap W₂ t₂ z + W₂ t₂ with hφdef
  have hA : IsHPHull A := h.hull
  have hφ : IsMapOut A φ := h.mapOut
  have h0K : ((x₁ : ℝ) : ℂ) ∈ closure K := start_mem_closure_fwdHull hW₁ hT
  have hdistH : ∀ z ∈ H₁ ∪ H₂, 2 * d ≤ ‖z - q‖ := fun z hz => by
    by_contra hcon
    exact Set.disjoint_left.1 hqH (by rw [mem_ball, dist_eq_norm]; linarith) hz
  have hdistcl : ∀ z ∈ closure (H₁ ∪ H₂), 2 * d ≤ ‖z - q‖ := by
    intro z hz
    have hc : IsClosed {w : ℂ | 2 * d ≤ ‖w - q‖} := isClosed_le continuous_const (by fun_prop)
    exact closure_minimal hdistH hc hz
  have hrealdist : ∀ y : ℝ, ((y : ℝ) : ℂ) ∈ closure (H₁ ∪ H₂) → 2 * d ≤ |y - q| := fun y hy => by
    have := hdistcl _ hy
    rwa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
  have hq1 : 2 * d ≤ |x₁ - q| := hrealdist x₁ (closure_mono subset_union_left (closure_mono hK₁ h0K))
  have hq2 : 2 * d ≤ |W₂ 0 - q| := hrealdist (W₂ 0) (closure_mono subset_union_right hW₂H)
  have hqA : Disjoint (ball (q : ℂ) (2 * d)) A :=
    hqH.mono_right (hK₂.trans subset_union_right)
  have hqK : Disjoint (ball (q : ℂ) (2 * d)) K :=
    hqH.mono_right (hK₁.trans subset_union_left)
  have halive₂ : ∀ y : ℝ, (y : ℂ) ∈ ball (q : ℂ) d → ∃ v, IsForwardSol W₂ (y : ℂ) t₂ v := by
    intro y hy
    have hyq := abs_sub_lt_of_mem_ball hy
    have hy0 : y ≠ W₂ 0 := by
      intro hyW; rw [hyW] at hyq; linarith
    refine exists_isForwardSol_of_disjoint_ball_gen hW₂ hy0 ht₂ hd ?_
    refine hqA.mono_left (ball_subset_ball' ?_)
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; linarith
  obtain ⟨uq, huq⟩ := halive₂ q (mem_ball_self hd)
  -- the starting point of curve `1` is alive for curve `2`
  have h0A : ((x₁ : ℝ) : ℂ) ∉ closure A := fun h0 => Set.disjoint_left.1 h.disj h0 h0K
  obtain ⟨ε₀, hε₀, hε₀A⟩ : ∃ ε > 0, Disjoint (ball ((x₁ : ℝ) : ℂ) ε) A := by
    rw [Metric.mem_closure_iff] at h0A
    push Not at h0A
    obtain ⟨ε, hε, hεA⟩ := h0A
    refine ⟨ε, hε, Set.disjoint_left.2 fun z hz hzA => ?_⟩
    have := hεA z hzA
    rw [mem_ball, dist_comm] at hz
    linarith
  have hx₁W₂ : x₁ ≠ W₂ 0 := by
    intro he
    have h1 : ((W₂ 0 : ℝ) : ℂ) ∈ closure H₁ := by rw [← he]; exact closure_mono hK₁ h0K
    exact Set.disjoint_left.1 hsep h1 hW₂H
  obtain ⟨u0, hu0⟩ := exists_isForwardSol_of_disjoint_ball_gen hW₂ hx₁W₂ ht₂ hε₀ hε₀A
  have ht₂mem : t₂ ∈ Icc (0 : ℝ) t₂ := ⟨ht₂, le_rfl⟩
  have hu0im : (u0 t₂).im = 0 := im_eq_zero_of_isForwardSol_real hW₂ hu0 ht₂mem
  have huqim : (uq t₂).im = 0 := im_eq_zero_of_isForwardSol_real hW₂ huq ht₂mem
  have hfq : fwdMap W₂ t₂ q = uq t₂ := fwdMap_eq_of_isForwardSol hW₂ huq ht₂mem
  set p0 : ℝ := (u0 t₂).re + W₂ t₂ with hp0def
  set p : ℝ := (fwdMap W₂ t₂ q).re + W₂ t₂ with hpdef
  -- the image driver starts at `φ(x₁)`
  have hW'0 : W' 0 = p0 := by
    have ht2 : Tendsto φ (𝓝[H] ((x₁ : ℝ) : ℂ)) (𝓝 (p0 : ℂ)) := by
      have := (tendsto_fwdMap_of_isForwardSol hW₂ ht₂ hu0).add
        (tendsto_const_nhds (x := ((W₂ t₂ : ℝ) : ℂ)))
      have e0 : u0 t₂ + ((W₂ t₂ : ℝ) : ℂ) = (p0 : ℂ) := by
        apply Complex.ext <;> simp [hp0def, hu0im]
      rw [e0] at this; exact this
    exact_mod_cast h.W'_zero_eq ht2
  -- the reflection of `φ` at `q` and the image disc
  obtain ⟨G₂, hG₂d, hG₂e, -, hG₂x, -, hG₂inj, hG₂up, hG₂low, hG₂real⟩ :=
    ConformalImageFull.IsMapOut.exists_reflection_full hA hφ h2d hqA
  rw [e2d] at hG₂d hG₂e hG₂inj hG₂up hG₂low hG₂real
  have hqB : (q : ℂ) ∈ ball (q : ℂ) d := mem_ball_self hd
  have hG₂q : G₂ q = (p : ℂ) := by
    rw [hG₂x, fwdMap_add_eq_limUnder hW₂ ht₂ huq]
    apply Complex.ext <;> simp [hpdef, hfq, huqim]
  have hG₂ne : deriv G₂ q ≠ 0 := QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_ball hG₂d hG₂inj hqB
  set ρ : ℝ := 1 / 48 * d * ‖deriv G₂ q‖ with hρdef
  have hρ : 0 < ρ := by have := norm_pos_iff.2 hG₂ne; positivity
  have hcov' : ball (p : ℂ) ρ ⊆ G₂ '' ball (q : ℂ) d := by
    have := QuantumZipper.CA.Koebe.ball_subset_image_koebe hG₂d hG₂inj
    have hk : QuantumZipper.CA.Koebe.koebeCovConst = 1 / 48 := rfl
    rwa [hk, hG₂q] at this
  have hGK : ∀ z ∈ ball (q : ℂ) d, ∀ k ∈ K, G₂ z ≠ φ k := by
    intro z hz k hk heq
    have hkA : k ∉ A := fun hkA => Set.disjoint_left.1 (h.disjoint_A_K ⟨hT.le, le_rfl⟩) hkA hk
    have hkH : k ∈ H := (QuantumZipper.fwdHull_mono).2 T hk
    have hφk : 0 < (φ k).im := hφ.1.2.mapsTo ⟨hkH, hkA⟩
    have hzim : 0 < z.im := by
      by_contra hc
      rcases (not_lt.1 hc).lt_or_eq with hneg | hzero
      · have := hG₂low z hz hneg; rw [heq] at this; linarith
      · have := hG₂real z hz hzero; rw [heq] at this; linarith
    have hzA : z ∉ A := fun hzA =>
      Set.disjoint_left.1 hqA (ball_subset_ball (by linarith) hz) hzA
    rw [hG₂e ⟨hz, hzim⟩] at heq
    have := hφ.1.2.injOn ⟨hzim, hzA⟩ ⟨hkH, hkA⟩ heq
    subst this
    exact Set.disjoint_left.1 hqK (ball_subset_ball (by linarith) hz) hk
  have hpK : Disjoint (ball (p : ℂ) ρ) (fwdHull W' (a T)) := by
    rw [h.img T ⟨hT.le, le_rfl⟩, Set.disjoint_left]
    rintro w hw ⟨k, hk, rfl⟩
    obtain ⟨z, hz, hzw⟩ := hcov' hw
    exact hGK z hz k hk hzw
  have hp0far : ρ ≤ |p0 - p| := by
    by_contra hcon
    rw [not_le] at hcon
    have hmem : (p0 : ℂ) ∈ ball (p : ℂ) ρ := by
      rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hcon
    obtain ⟨z, hz, hzw⟩ := hcov' hmem
    have hzim : z.im = 0 := by
      rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
      · have := hG₂low z hz hneg; rw [hzw] at this; simp at this
      · exact hzero
      · have := hG₂up z hz hpos; rw [hzw] at this; simp at this
    have hzy : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hzim])
    rw [hzy] at hz hzw
    obtain ⟨uy, huy⟩ := halive₂ z.re hz
    have hyq := abs_sub_lt_of_mem_ball hz
    have hG₂y := refl_eq_fwdMap_of_real hW₂ ht₂ hG₂d hG₂e hz huy
    rw [hG₂y, fwdMap_eq_of_isForwardSol hW₂ huy ht₂mem] at hzw
    have hre := congrArg Complex.re hzw
    simp only [Complex.add_re, Complex.ofReal_re, hp0def] at hre
    have hyx : z.re ≠ x₁ := by
      intro he; rw [he] at hyq; linarith [abs_sub_comm x₁ q]
    rcases lt_or_gt_of_ne hyx with hlt | hgt
    · have hord := QuantumZipper.F1.isForwardSol_lt_of_lt ht₂ hlt huy hu0 t₂ ht₂mem
      linarith
    · have hord := QuantumZipper.F1.isForwardSol_lt_of_lt ht₂ hgt hu0 huy t₂ ht₂mem
      linarith
  -- the image chain at clock `a(s)`
  set τ := a s with hτdef
  have hτ0 : 0 ≤ τ := (h.mapsTo_clock_Icc hs).1
  have hτT : τ ≤ a T := (h.mapsTo_clock_Icc hs).2
  have hpKτ : Disjoint (ball (p : ℂ) ρ) (fwdHull W' τ) :=
    hpK.mono_right ((QuantumZipper.fwdHull_mono).1 hτT)
  have hW'0ne : ∀ y : ℝ, (y : ℂ) ∈ ball (p : ℂ) (ρ / 2) → y ≠ W' 0 := by
    intro y hy hyW
    have := abs_sub_lt_of_mem_ball hy
    rw [hyW, hW'0] at this
    linarith
  have hkoebe := le_norm_fwdMap_real hW'c hτ0 hρ hpKτ hW'0ne
  obtain ⟨vp, hvp⟩ := exists_isForwardSol_of_disjoint_ball_gen hW'c
    (hW'0ne p (mem_ball_self (by linarith))) hτ0 hρ hpKτ
  refine ⟨⟨vp, hvp⟩, ?_⟩
  have hτmem : τ ∈ Icc (0 : ℝ) τ := ⟨hτ0, le_rfl⟩
  have hvpim : (vp τ).im = 0 := im_eq_zero_of_isForwardSol_real hW'c hvp hτmem
  -- the chain rule at `q`
  obtain ⟨δp, hδp, hlowp, hpdisc⟩ := exists_aliveDisc_self hvp hτ0
  have hfp : HasDerivAt (fwdMap W' τ) (deriv (fwdMap W' τ) p) (G₂ q) := by
    rw [hG₂q]
    exact (hasDerivAt_fwdMap_aliveDisc hW'c hvp hδp hlowp hpdisc hτmem).differentiableAt.hasDerivAt
  have hG₂q' : HasDerivAt G₂ (deriv G₂ q) q :=
    (hG₂d.differentiableAt (isOpen_ball.mem_nhds hqB)).hasDerivAt
  have hĜ : HasDerivAt (fun z => fwdMap W' τ (G₂ z) + W' τ)
      (deriv (fwdMap W' τ) p * deriv G₂ q) q :=
    (hfp.comp (q : ℂ) hG₂q').add_const ((W' τ : ℝ) : ℂ)
  have hĜqreal : (fwdMap W' τ (G₂ q) + W' τ).im = 0 := by
    rw [hG₂q, fwdMap_eq_of_isForwardSol hW'c hvp hτmem]; simp [hvpim]
  -- the union hull and its mapping-out function
  set Ks := fwdHull W₁ s with hKsdef
  have hKsK : Ks ⊆ K := (QuantumZipper.fwdHull_mono).1 hs.2
  have hKs : IsHPHull Ks := isHPHull_fwdHull hW₁ hs.1
  have hKsA : IsHPHull (Ks ∪ A) :=
    hKs.union_of_disjoint_closure hA (h.disj.symm.mono_left (closure_mono hKsK))
  have himgs : φ '' ((Ks ∪ A) \ A) = fwdHull W' τ := by
    rw [h.img s hs]
    congr 1
    ext z; constructor
    · rintro ⟨hz, hzA⟩
      rcases hz with hz | hz
      · exact hz
      · exact absurd hz hzA
    · intro hz
      exact ⟨Or.inl hz, fun hzA => Set.disjoint_left.1 (h.disjoint_A_K hs) hzA hz⟩
  have hgC : IsMapOut (φ '' ((Ks ∪ A) \ A)) (fun w => fwdMap W' τ w + W' τ) := by
    rw [himgs]; exact isMapOut_fwdMap_gen hW'c hτ0
  have hgK := IsMapOut.comp hA hKsA subset_union_right hφ hgC
  have hsubU : Ks ∪ A ⊆ H₁ ∪ H₂ := union_subset_union (hKsK.trans hK₁) hK₂
  have hML := re_deriv_le_of_subset hKsA hU hsubU hgK hgU hd hqd hĜ.differentiableAt
    (hGUd.differentiableAt (isOpen_ball.mem_nhds hqB)) hĜqreal (hGUreal q hqB (by simp))
    (fun z hz => by
      show fwdMap W' τ (G₂ z) + W' τ = ((fun w => fwdMap W' τ w + W' τ) ∘ φ) z
      rw [hG₂e hz]; rfl) hGUe
  rw [hĜ.deriv] at hML
  -- combine
  have hmle : m ≤ ‖deriv (fwdMap W' τ) p‖ * ‖deriv G₂ q‖ := by
    refine hML.trans ((Complex.re_le_norm _).trans ?_)
    rw [norm_mul]
  refine le_trans ?_ hkoebe
  rw [hρdef]
  have hdm : d * m ≤ d * (‖deriv (fwdMap W' τ) p‖ * ‖deriv G₂ q‖) :=
    mul_le_mul_of_nonneg_left hmle hd.le
  nlinarith [hdm]

/-! ### The separation of the two image tips -/

/-- In the two-curve setting the starting point of curve `1` is alive for curve `2`, and the image driver starts at
its image. -/
theorem ImgData.exists_start_alive {W₁ W₂ : ℝ → ℝ} {t₂ T : ℝ} {a W' : ℝ → ℝ}
    (h : ImgData W₁ (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W') (hW₂ : Continuous W₂)
    (ht₂ : 0 ≤ t₂) (hne : W₁ 0 ≠ W₂ 0) :
    ∃ u0, IsForwardSol W₂ ((W₁ 0 : ℝ) : ℂ) t₂ u0 ∧ W' 0 = (u0 t₂).re + W₂ t₂ := by
  have h0K : ((W₁ 0 : ℝ) : ℂ) ∈ closure (fwdHull W₁ T) := start_mem_closure_fwdHull h.cont h.pos
  have h0A : ((W₁ 0 : ℝ) : ℂ) ∉ closure (fwdHull W₂ t₂) := fun h0 => Set.disjoint_left.1 h.disj h0 h0K
  obtain ⟨ε₀, hε₀, hε₀A⟩ : ∃ ε > 0, Disjoint (ball ((W₁ 0 : ℝ) : ℂ) ε) (fwdHull W₂ t₂) := by
    rw [Metric.mem_closure_iff] at h0A
    push Not at h0A
    obtain ⟨ε, hε, hεA⟩ := h0A
    refine ⟨ε, hε, Set.disjoint_left.2 fun z hz hzA => ?_⟩
    have := hεA z hzA
    rw [mem_ball, dist_comm] at hz
    linarith
  obtain ⟨u0, hu0⟩ := exists_isForwardSol_of_disjoint_ball_gen hW₂ hne ht₂ hε₀ hε₀A
  refine ⟨u0, hu0, ?_⟩
  have ht₂mem : t₂ ∈ Icc (0 : ℝ) t₂ := ⟨ht₂, le_rfl⟩
  have hu0im : (u0 t₂).im = 0 := im_eq_zero_of_isForwardSol_real hW₂ hu0 ht₂mem
  have ht2 : Tendsto (fun z => fwdMap W₂ t₂ z + W₂ t₂) (𝓝[H] ((W₁ 0 : ℝ) : ℂ))
      (𝓝 ((((u0 t₂).re + W₂ t₂ : ℝ)) : ℂ)) := by
    have := (tendsto_fwdMap_of_isForwardSol hW₂ ht₂ hu0).add (tendsto_const_nhds (x := ((W₂ t₂ : ℝ) : ℂ)))
    have e0 : u0 t₂ + ((W₂ t₂ : ℝ) : ℂ) = ((((u0 t₂).re + W₂ t₂ : ℝ)) : ℂ) := by
      apply Complex.ext <;> simp [hu0im]
    rw [e0] at this; exact this
  exact_mod_cast h.W'_zero_eq ht2

/-- The tip `W₂(t₂)` of the frozen curve is alive for the image chain when `K₁(T)` keeps a clearance `r` from it in
curve `2`'s chart. -/
theorem ImgData.exists_tip_alive {W₁ W₂ : ℝ → ℝ} {t₂ T : ℝ} {a W' : ℝ → ℝ}
    (h : ImgData W₁ (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W') {r : ℝ} (hr : 0 < r)
    (hcl : ∀ z ∈ fwdHull W₁ T, r ≤ ‖fwdMap W₂ t₂ z‖) (hne : W₂ t₂ ≠ W' 0) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    ∃ v, IsForwardSol W' ((W₂ t₂ : ℝ) : ℂ) (a s) v := by
  have hτ0 : 0 ≤ a s := (h.mapsTo_clock_Icc hs).1
  have hζK : Disjoint (ball ((W₂ t₂ : ℝ) : ℂ) r) (fwdHull W' (a s)) := by
    rw [h.img s hs, Set.disjoint_left]
    rintro w hw ⟨k, hk, rfl⟩
    have h1 := hcl k ((QuantumZipper.fwdHull_mono).1 hs.2 hk)
    rw [mem_ball, dist_eq_norm] at hw
    have e : fwdMap W₂ t₂ k + ((W₂ t₂ : ℝ) : ℂ) - ((W₂ t₂ : ℝ) : ℂ) = fwdMap W₂ t₂ k := by ring
    rw [e] at hw; linarith
  exact exists_isForwardSol_of_disjoint_ball_gen h.contW' hne hτ0 hr hζK

/-- **(D9), separation `E` of the image tips, frozen curve on the right.** If `W₁ 0 < q < W₂ 0`, the image of the
frozen tip lies at least `γ` to the right of the image driver: `γ ≤ f̃_{a(s)}(W₂(t₂)) = A_{2,0} − A_{1,0}`. -/
theorem exists_le_re_fwdMap_tip_right {H₁ H₂ : Set ℂ} (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂)
    (hsep : Disjoint (closure H₁) (closure H₂)) {q d : ℝ} (hd : 0 < d)
    (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)) :
    ∃ γ > 0, ∀ (W₁ W₂ : ℝ → ℝ) (t₂ T : ℝ) (a W' : ℝ → ℝ) (r : ℝ),
      ImgData W₁ (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W' →
      Continuous W₂ → 0 ≤ t₂ → ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ → W₁ 0 < q → q < W₂ 0 →
      fwdHull W₁ T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ → 0 < r → (∀ z ∈ fwdHull W₁ T, r ≤ ‖fwdMap W₂ t₂ z‖) →
      ∀ s ∈ Icc (0 : ℝ) T, γ ≤ (fwdMap W' (a s) (W₂ t₂)).re := by
  obtain ⟨γ, hγ, hcore⟩ := exists_le_norm_fwdMap_protected hH₁ hH₂ hsep hd hqH
  refine ⟨γ, hγ, ?_⟩
  intro W₁ W₂ t₂ T a W' r h hW₂ ht₂ hW₂H hx₁q hqW hK₁ hK₂ hr hcl s hs
  obtain ⟨⟨vp, hvp⟩, hle⟩ := hcore W₁ W₂ t₂ T a W' h hW₂ ht₂ hW₂H hK₁ hK₂ s hs
  obtain ⟨u0, hu0, hW'0⟩ := h.exists_start_alive hW₂ ht₂ (by linarith)
  have h2d : 0 < 2 * d := by linarith
  obtain ⟨uq, huq⟩ := exists_isForwardSol_of_disjoint_ball_gen hW₂ (show q ≠ W₂ 0 by linarith) ht₂ h2d
    (hqH.mono_right (hK₂.trans subset_union_right))
  have ht₂mem : t₂ ∈ Icc (0 : ℝ) t₂ := ⟨ht₂, le_rfl⟩
  have hord₂ := QuantumZipper.F1.isForwardSol_lt_of_lt ht₂ hx₁q hu0 huq t₂ ht₂mem
  have hqneg := QuantumZipper.re_neg_isForwardSol_real hW₂ ht₂ huq hqW t₂ ht₂mem
  rw [fwdMap_eq_of_isForwardSol hW₂ huq ht₂mem] at hvp hle
  set p : ℝ := (uq t₂).re + W₂ t₂ with hpdef
  have hp0p : W' 0 < p := by rw [hW'0, hpdef]; linarith
  have hpζ : p < W₂ t₂ := by rw [hpdef]; linarith
  have hτ0 : 0 ≤ a s := (h.mapsTo_clock_Icc hs).1
  have hτmem : a s ∈ Icc (0 : ℝ) (a s) := ⟨hτ0, le_rfl⟩
  have hvpim : (vp (a s)).im = 0 := im_eq_zero_of_isForwardSol_real h.contW' hvp hτmem
  have hvppos : 0 < (vp (a s)).re :=
    QuantumZipper.re_pos_isForwardSol_real h.contW' hτ0 hvp hp0p (a s) hτmem
  obtain ⟨vζ, hvζ⟩ := h.exists_tip_alive hr hcl (by linarith) hs
  have hord := QuantumZipper.F1.isForwardSol_lt_of_lt hτ0 hpζ hvp hvζ (a s) hτmem
  rw [fwdMap_eq_of_isForwardSol h.contW' hvp hτmem] at hle
  rw [fwdMap_eq_of_isForwardSol h.contW' hvζ hτmem]
  have hnorm : ‖vp (a s)‖ = (vp (a s)).re := by
    have : vp (a s) = (((vp (a s)).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hvpim])
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using hvppos)]
    simp
  rw [hnorm] at hle
  linarith

/-- **(D9), separation `E` of the image tips, frozen curve on the left.** If `W₂ 0 < q < W₁ 0`, the image of the
frozen tip lies at least `γ` to the left of the image driver: `γ ≤ −f̃_{a(s)}(W₂(t₂)) = A_{1,0} − A_{2,0}`. -/
theorem exists_le_neg_re_fwdMap_tip_left {H₁ H₂ : Set ℂ} (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂)
    (hsep : Disjoint (closure H₁) (closure H₂)) {q d : ℝ} (hd : 0 < d)
    (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)) :
    ∃ γ > 0, ∀ (W₁ W₂ : ℝ → ℝ) (t₂ T : ℝ) (a W' : ℝ → ℝ) (r : ℝ),
      ImgData W₁ (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W' →
      Continuous W₂ → 0 ≤ t₂ → ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ → W₂ 0 < q → q < W₁ 0 →
      fwdHull W₁ T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ → 0 < r → (∀ z ∈ fwdHull W₁ T, r ≤ ‖fwdMap W₂ t₂ z‖) →
      ∀ s ∈ Icc (0 : ℝ) T, γ ≤ -(fwdMap W' (a s) (W₂ t₂)).re := by
  obtain ⟨γ, hγ, hcore⟩ := exists_le_norm_fwdMap_protected hH₁ hH₂ hsep hd hqH
  refine ⟨γ, hγ, ?_⟩
  intro W₁ W₂ t₂ T a W' r h hW₂ ht₂ hW₂H hW₂q hqx₁ hK₁ hK₂ hr hcl s hs
  obtain ⟨⟨vp, hvp⟩, hle⟩ := hcore W₁ W₂ t₂ T a W' h hW₂ ht₂ hW₂H hK₁ hK₂ s hs
  obtain ⟨u0, hu0, hW'0⟩ := h.exists_start_alive hW₂ ht₂ (by linarith)
  have h2d : 0 < 2 * d := by linarith
  obtain ⟨uq, huq⟩ := exists_isForwardSol_of_disjoint_ball_gen hW₂ (show q ≠ W₂ 0 by linarith) ht₂ h2d
    (hqH.mono_right (hK₂.trans subset_union_right))
  have ht₂mem : t₂ ∈ Icc (0 : ℝ) t₂ := ⟨ht₂, le_rfl⟩
  have hord₂ := QuantumZipper.F1.isForwardSol_lt_of_lt ht₂ hqx₁ huq hu0 t₂ ht₂mem
  have hqpos := QuantumZipper.re_pos_isForwardSol_real hW₂ ht₂ huq hW₂q t₂ ht₂mem
  rw [fwdMap_eq_of_isForwardSol hW₂ huq ht₂mem] at hvp hle
  set p : ℝ := (uq t₂).re + W₂ t₂ with hpdef
  have hp0p : p < W' 0 := by rw [hW'0, hpdef]; linarith
  have hpζ : W₂ t₂ < p := by rw [hpdef]; linarith
  have hτ0 : 0 ≤ a s := (h.mapsTo_clock_Icc hs).1
  have hτmem : a s ∈ Icc (0 : ℝ) (a s) := ⟨hτ0, le_rfl⟩
  have hvpim : (vp (a s)).im = 0 := im_eq_zero_of_isForwardSol_real h.contW' hvp hτmem
  have hvpneg : (vp (a s)).re < 0 :=
    QuantumZipper.re_neg_isForwardSol_real h.contW' hτ0 hvp hp0p (a s) hτmem
  obtain ⟨vζ, hvζ⟩ := h.exists_tip_alive hr hcl (by linarith) hs
  have hord := QuantumZipper.F1.isForwardSol_lt_of_lt hτ0 hpζ hvζ hvp (a s) hτmem
  rw [fwdMap_eq_of_isForwardSol h.contW' hvp hτmem] at hle
  rw [fwdMap_eq_of_isForwardSol h.contW' hvζ hτmem]
  have hnorm : ‖vp (a s)‖ = -(vp (a s)).re := by
    have : vp (a s) = (((vp (a s)).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hvpim])
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by simpa using hvpneg)]
    simp
  rw [hnorm] at hle
  linarith

/-! ### The own derivative factor from below: the other time -/

/-- A uniform separation of two sets gives disjoint closures. -/
theorem disjoint_closure_of_le_norm_sub {S₁ S₂ : Set ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ S₂, ∀ z ∈ S₁, 2 * δ ≤ ‖a - z‖) : Disjoint (closure S₁) (closure S₂) := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  obtain ⟨b, hb, hbz⟩ := Metric.mem_closure_iff.1 hz1 (δ / 2) (by linarith)
  obtain ⟨a, ha, haz⟩ := Metric.mem_closure_iff.1 hz2 (δ / 2) (by linarith)
  have h1 := hsep a ha b hb
  rw [dist_eq_norm] at hbz haz
  have := norm_sub_le_norm_sub_add_norm_sub a z b
  rw [norm_sub_rev a z] at this
  linarith

/-- **(D9), the own derivative factor `A_{1,1}` from below.** Fix enclosures `H₁, H₂` at mutual distance `≥ 2δ` and a
real `q` with `B(q, 2d)` missing `H₁ ∪ H₂`. There is `γ > 0` such that: whenever curve `1` (driver `W₁`, start
`W₁ 0 < q`) has hull `K₁(s) ⊆ H₁`, curve `2` (driver `W₂`, start `W₂ 0 > q`) has hull `K₂(t₂) ⊆ H₂`, and `ImgData` is the
conformal-image data of curve `2` growing on `[0, t₂]` in the complement of `K₁(s)`, then the boundary derivative at
`W₁(s)` of **every** Schwarz reflection `G` of **every** mapping-out function `R` of `g^{(1)}_s(K₂(t₂))` satisfies
`e^{−2t₂/γ²} ≤ |G'(W₁(s))|`. (Along the other time `v ∈ [0, t₂]`, `G'(W₁(s))` is the derivative at `W₁(s)` of the image
chain of curve `2`, whose logarithm has derivative `−2A²_{2,1}/E²` with `A_{2,1} ≤ 1` and `E ≥ γ` by the tip separation.)
The derivative of the reflected own-time map `ownExt` at the driver is such a `G'(W₁(s))`. -/
theorem exists_exp_le_norm_deriv_refl_own {H₁ H₂ : Set ℂ} (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂)
    {δ : ℝ} (hδ : 0 < δ) (hsepδ : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖) {q d : ℝ} (hd : 0 < d)
    (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)) :
    ∃ γ > 0, ∀ (W₁ W₂ : ℝ → ℝ) (s t₂ : ℝ) (a₂ W₂' : ℝ → ℝ),
      ImgData W₂ (fwdHull W₁ s) (fun z => fwdMap W₁ s z + W₁ s) t₂ a₂ W₂' →
      Continuous W₁ → 0 ≤ s → ((W₁ 0 : ℝ) : ℂ) ∈ closure H₁ → ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ →
      W₁ 0 < q → q < W₂ 0 → fwdHull W₁ s ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
      ∀ (R G : ℂ → ℂ) (ε : ℝ), IsMapOut ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t₂) R → 0 < ε →
        DifferentiableOn ℂ G (ball (W₁ s : ℂ) ε) → EqOn G R (ball (W₁ s : ℂ) ε ∩ H) →
        Real.exp (-(2 / γ ^ 2 * t₂)) ≤ ‖deriv G (W₁ s)‖ := by
  have hsepδ' : ∀ a ∈ H₁, ∀ z ∈ H₂, 2 * δ ≤ ‖a - z‖ := fun a ha z hz => by
    rw [norm_sub_rev]; exact hsepδ z hz a ha
  have hsep : Disjoint (closure H₁) (closure H₂) := disjoint_closure_of_le_norm_sub hδ hsepδ
  have hqH' : Disjoint (ball (q : ℂ) (2 * d)) (H₂ ∪ H₁) := by rwa [union_comm]
  obtain ⟨γ, hγ, hleft⟩ := exists_le_neg_re_fwdMap_tip_left hH₂ hH₁ hsep.symm hd hqH'
  obtain ⟨r₁, hr₁, hcl₁⟩ := exists_le_norm_fwdMap_uniform hH₁ hH₂.2.1 hH₂.1 hδ hsepδ
  obtain ⟨r₂, hr₂, hcl₂⟩ := exists_le_norm_fwdMap_uniform hH₂ hH₁.2.1 hH₁.1 hδ hsepδ'
  refine ⟨γ, hγ, ?_⟩
  intro W₁ W₂ s t₂ a₂ W₂' h hW₁ hs hW₁H hW₂H hx₁q hqx₂ hK₁ hK₂ R G ε hR hε hGd hGR
  have hW₂ := h.cont
  have ht₂ := h.pos
  have hsmem : s ∈ Icc (0 : ℝ) s := ⟨hs, le_rfl⟩
  have ht₂mem : t₂ ∈ Icc (0 : ℝ) t₂ := ⟨ht₂.le, le_rfl⟩
  -- clearances
  have hc₁ : ∀ z ∈ fwdHull W₂ t₂, r₁ ≤ ‖fwdMap W₁ s z‖ := fun z hz =>
    hcl₁ W₁ hW₁ hW₁H s hK₁ s hsmem z (hK₂ hz)
  have hclr : ∀ v ∈ Icc (0 : ℝ) t₂, Disjoint (ball (W₂ v : ℂ) r₂)
      ((fun z => fwdMap W₂ v z + W₂ v) '' fwdHull W₁ s) := fun v hv =>
    OwnData.disjoint_ball_of_le_norm fun z hz => hcl₂ W₂ hW₂ hW₂H t₂ hK₂ v hv z (hK₁ hz)
  -- the separation of the tips, in the transposed configuration
  have hgap : ∀ v ∈ Icc (0 : ℝ) t₂, γ ≤ ‖fwdMap W₂' (a₂ v) (W₁ s)‖ := fun v hv =>
    (hleft W₂ W₁ s t₂ a₂ W₂' r₁ h hW₁ hs hW₁H hx₁q hqx₂ hK₂ hK₁ hr₁ hc₁ v hv).trans
      ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
  -- the tip `W₁(s)` is alive for the image chain of curve `2`
  obtain ⟨u0, hu0, hW₂'0⟩ := h.exists_start_alive hW₁ hs (by linarith)
  have hu0pos := QuantumZipper.re_pos_isForwardSol_real hW₁ hs hu0 (by linarith) s hsmem
  obtain ⟨vζ, hvζ⟩ := h.exists_tip_alive hr₁ hc₁ (by rw [hW₂'0]; intro h'; linarith) ht₂mem
  have hode := h.exp_neg_le_norm_deriv_fwdMap_image hr₂ hclr hvζ hγ hgap ht₂mem
  -- identification of the derivative
  set τ := a₂ t₂ with hτdef
  have hτ0 : 0 ≤ τ := (h.mapsTo_clock_Icc ht₂mem).1
  have hτmem : τ ∈ Icc (0 : ℝ) τ := ⟨hτ0, le_rfl⟩
  have hgt : IsMapOut ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t₂) (fun w => fwdMap W₂' τ w + W₂' τ) := by
    rw [← h.img t₂ ht₂mem]; exact isMapOut_fwdMap_gen h.contW' hτ0
  have hEhull : IsHPHull ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t₂) := by
    rw [← h.img t₂ ht₂mem]; exact isHPHull_fwdHull h.contW' hτ0
  have hReq := IsMapOut.eqOn hEhull hR hgt
  obtain ⟨δζ, hδζ, hlowζ, hζdisc⟩ := exists_aliveDisc_self hvζ hτ0
  have hfd : DifferentiableAt ℂ (fwdMap W₂' τ) (W₁ s) :=
    (hasDerivAt_fwdMap_aliveDisc h.contW' hvζ hδζ hlowζ hζdisc hτmem).differentiableAt
  have hxB : ((W₁ s : ℝ) : ℂ) ∈ ball ((W₁ s : ℝ) : ℂ) ε := mem_ball_self hε
  have hGx : DifferentiableAt ℂ G (W₁ s) := hGd.differentiableAt (isOpen_ball.mem_nhds hxB)
  set ε' := min ε r₁ with hε'def
  have hε' : 0 < ε' := lt_min hε hr₁
  have hupper : ∀ e ∈ Ioo (0 : ℝ) ε', G ((W₁ s : ℂ) + (e : ℂ) * I) =
      fwdMap W₂' τ ((W₁ s : ℂ) + (e : ℂ) * I) + W₂' τ := by
    intro e he
    have hnorm : ‖((W₁ s : ℂ) + (e : ℂ) * I) - (W₁ s : ℂ)‖ = e := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos he.1]
    have hzH : (W₁ s : ℂ) + (e : ℂ) * I ∈ H := by
      show 0 < ((W₁ s : ℂ) + (e : ℂ) * I).im
      simp [he.1]
    have hzB : (W₁ s : ℂ) + (e : ℂ) * I ∈ ball ((W₁ s : ℝ) : ℂ) ε := by
      rw [mem_ball, dist_eq_norm, hnorm]; exact he.2.trans_le (min_le_left _ _)
    have hzE : (W₁ s : ℂ) + (e : ℂ) * I ∉ (fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t₂ := by
      rintro ⟨k, hk, hkz⟩
      have h1 := hc₁ k hk
      have h2 : ‖fwdMap W₁ s k‖ = e := by
        rw [← hnorm, ← hkz]; congr 1; push_cast; ring
      have h3 : e < r₁ := he.2.trans_le (min_le_right _ _)
      linarith
    rw [hGR ⟨hzB, hzH⟩, hReq ⟨hzH, hzE⟩]
  have hGval : G (W₁ s) = fwdMap W₂' τ (W₁ s) + W₂' τ := by
    have hGc : Tendsto G (𝓝[H] ((W₁ s : ℝ) : ℂ)) (𝓝 (G (W₁ s))) :=
      hGx.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hgc : Tendsto (fun w => fwdMap W₂' τ w + W₂' τ) (𝓝[H] ((W₁ s : ℝ) : ℂ))
        (𝓝 (fwdMap W₂' τ (W₁ s) + W₂' τ)) :=
      ((hfd.add_const ((W₂' τ : ℝ) : ℂ)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ w in 𝓝[H] ((W₁ s : ℝ) : ℂ), G w = fwdMap W₂' τ w + W₂' τ := by
      have hball : ball ((W₁ s : ℝ) : ℂ) ε' ∈ 𝓝 ((W₁ s : ℝ) : ℂ) := ball_mem_nhds _ hε'
      filter_upwards [inter_mem_nhdsWithin H hball] with w hw
      have hwH : w ∈ H := hw.1
      have hwB : w ∈ ball ((W₁ s : ℝ) : ℂ) ε := ball_subset_ball (min_le_left _ _) hw.2
      have hwE : w ∉ (fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t₂ := by
        rintro ⟨k, hk, hkz⟩
        have h1 := hc₁ k hk
        have hw1 := hw.2
        rw [mem_ball, dist_eq_norm, ← hkz] at hw1
        have e2 : fwdMap W₁ s k + ((W₁ s : ℝ) : ℂ) - ((W₁ s : ℝ) : ℂ) = fwdMap W₁ s k := by ring
        rw [e2] at hw1
        linarith [hw1.trans_le (min_le_right ε r₁)]
      rw [hGR ⟨hwB, hwH⟩, hReq ⟨hwH, hwE⟩]
    have hne : (𝓝[H] ((W₁ s : ℝ) : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
    exact tendsto_nhds_unique (hGc.congr' hev) hgc
  have hderiv := deriv_eq_of_eq_upper hε' hGx (hfd.add_const ((W₂' τ : ℝ) : ℂ)) hGval hupper
  rw [hderiv, deriv_add_const]
  exact hode.1

/-! ### Marks: the clock, mutual distances, and the frozen curve's boundary derivative -/

/-- **The clock is `1`-Lipschitz** when `E_t` keeps a clearance from the driver: `a(s) ≤ s` (`ȧ = A²_{1,1} ≤ 1`). -/
theorem ImgData.clock_le {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ}
    (h : ImgData W A φ T a W') {r : ℝ} (hr : 0 < r)
    (hclr : ∀ t ∈ Icc (0 : ℝ) T, Disjoint (ball (W t : ℂ) r) ((fun z => fwdMap W t z + W t) '' A))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) : a s ≤ s := by
  choose c hc0 hc1 hcder using fun t (ht : t ∈ Icc (0 : ℝ) T) => h.exists_rate_le_one hr ht (hclr t ht)
  set c' : ℝ → ℝ := fun t => if ht : t ∈ Icc (0 : ℝ) T then c t ht else 0 with hc'def
  have hd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt a (c' t) (Icc 0 T) t := by
    intro t ht; simp only [hc'def, ht, ↓reduceDIte]; exact hcder t ht
  have hb : ∀ t ∈ Ico (0 : ℝ) T, ‖c' t‖ ≤ 1 := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self ht
    simp only [hc'def, ht', ↓reduceDIte, Real.norm_eq_abs, abs_of_nonneg (hc0 t ht')]
    exact hc1 t ht'
  have := norm_image_sub_le_of_norm_deriv_le_segment' hd hb s hs
  rw [h.a0, sub_zero, sub_zero, one_mul, Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

/-- **(D9) for the mutual factors `C_{mn}`.** Two points alive for the image chain up to `a(T)`, whose images stay at
distance `≥ γ` from the image driver, keep their mutual distance up to the factor `e^{±2a(s)/γ²}`: by the linear
identity `f̃(ζ₂) − f̃(ζ₁) = (ζ₂ − ζ₁) exp(−∫ 2/(f̃(ζ₂) f̃(ζ₁)))`. -/
theorem ImgData.norm_fwdMap_sub_bounds {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ}
    (h : ImgData W A φ T a W') {ζ₁ ζ₂ : ℂ} {v₁ v₂ : ℝ → ℂ} (hv₁ : IsForwardSol W' ζ₁ (a T) v₁)
    (hv₂ : IsForwardSol W' ζ₂ (a T) v₂) {γ : ℝ} (hγ : 0 < γ)
    (hgap₁ : ∀ s ∈ Icc (0 : ℝ) T, γ ≤ ‖fwdMap W' (a s) ζ₁‖)
    (hgap₂ : ∀ s ∈ Icc (0 : ℝ) T, γ ≤ ‖fwdMap W' (a s) ζ₂‖) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    ‖ζ₂ - ζ₁‖ * Real.exp (-(2 / γ ^ 2 * a s)) ≤ ‖fwdMap W' (a s) ζ₂ - fwdMap W' (a s) ζ₁‖ ∧
      ‖fwdMap W' (a s) ζ₂ - fwdMap W' (a s) ζ₁‖ ≤ ‖ζ₂ - ζ₁‖ * Real.exp (2 / γ ^ 2 * a s) := by
  have hW'c := h.contW'
  have hτ := h.mapsTo_clock_Icc hs
  set τ := a s with hτdef
  have hτmem : τ ∈ Icc (0 : ℝ) (a T) := hτ
  -- every clock time below `τ` is `a(s')` for some `s' ≤ s`
  have hlow : ∀ σ ∈ Icc (0 : ℝ) τ, γ ≤ ‖v₁ σ‖ ∧ γ ≤ ‖v₂ σ‖ := by
    intro σ hσ
    have hcont : ContinuousOn a (Icc 0 s) := h.contA.mono (Icc_subset_Icc_right hs.2)
    obtain ⟨s', hs', hs'σ⟩ := intermediate_value_Icc hs.1 hcont (by rw [h.a0]; exact hσ)
    have hs'T : s' ∈ Icc (0 : ℝ) T := ⟨hs'.1, hs'.2.trans hs.2⟩
    have hσT : σ ∈ Icc (0 : ℝ) (a T) := ⟨hσ.1, hσ.2.trans hτ.2⟩
    rw [← fwdMap_eq_of_isForwardSol hW'c hv₁ hσT, ← fwdMap_eq_of_isForwardSol hW'c hv₂ hσT, ← hs'σ]
    exact ⟨hgap₁ s' hs'T, hgap₂ s' hs'T⟩
  have hid := QuantumZipper.FwdHolo.sol_sub_eq hv₁ hv₂ τ hτmem
  rw [← fwdMap_eq_of_isForwardSol hW'c hv₁ hτmem, ← fwdMap_eq_of_isForwardSol hW'c hv₂ hτmem] at hid
  rw [hid, norm_mul, Complex.norm_exp]
  set I := ∫ σ in (0 : ℝ)..τ, 2 / (v₂ σ * v₁ σ) with hIdef
  have hI : ‖I‖ ≤ 2 / γ ^ 2 * τ := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := τ) (C := 2 / γ ^ 2)
      (f := fun σ => 2 / (v₂ σ * v₁ σ)) (fun σ hσ => by
        rw [uIoc_of_le hτ.1] at hσ
        obtain ⟨h1, h2⟩ := hlow σ ⟨hσ.1.le, hσ.2⟩
        rw [norm_div, norm_mul, Complex.norm_two]
        have hp : 0 < ‖v₂ σ‖ * ‖v₁ σ‖ := mul_pos (hγ.trans_le h2) (hγ.trans_le h1)
        rw [div_le_div_iff₀ hp (by positivity)]
        nlinarith [mul_le_mul h2 h1 hγ.le (norm_nonneg _)])
    rwa [sub_zero, abs_of_nonneg hτ.1] at this
  have hre : |(-I).re| ≤ 2 / γ ^ 2 * τ := by
    rw [Complex.neg_re, abs_neg]; exact (Complex.abs_re_le_norm _).trans hI
  rw [abs_le] at hre
  exact ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hre.1) (norm_nonneg _),
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hre.2) (norm_nonneg _)⟩

/-- **(D9) for the frozen curve's boundary derivative at a protected real point.** If `B(p, ρ)` misses the enclosure
`H₂`, there is `m > 0` such that for every driver `W` with `K_t ⊆ H₂` and `W 0 ≠ p`, the boundary derivative
`g_t'(p) = f_t'(p)` is real with `m ≤ g_t'(p) ≤ 1` (`m` = the boundary derivative at `p` of a reflection of `g_{H₂}`,
by monotonicity in the hull). -/
theorem exists_deriv_fwdMap_real_bounds {H₂ : Set ℂ} (hH₂ : IsHPHull H₂) {p ρ : ℝ} (hρ : 0 < ρ)
    (hpH : Disjoint (ball (p : ℂ) ρ) H₂) :
    ∃ m > 0, ∀ W : ℝ → ℝ, Continuous W → ∀ t : ℝ, 0 ≤ t → fwdHull W t ⊆ H₂ →
      (∀ y : ℝ, (y : ℂ) ∈ ball (p : ℂ) (ρ / 2) → y ≠ W 0) →
      (deriv (fwdMap W t) p).im = 0 ∧ m ≤ (deriv (fwdMap W t) p).re ∧ (deriv (fwdMap W t) p).re ≤ 1 := by
  obtain ⟨g₂, hg₂⟩ := hH₂.exists_isMapOut
  obtain ⟨G₂, hG₂d, hG₂e, -, -, -, hG₂inj, -, -, hG₂real⟩ :=
    ConformalImageFull.IsMapOut.exists_reflection_full hH₂ hg₂ hρ hpH
  have hρ2 : 0 < ρ / 2 := by linarith
  have hpd : Disjoint (ball (p : ℂ) (ρ / 2)) H₂ := hpH.mono_left (ball_subset_ball (by linarith))
  obtain ⟨-, hm⟩ := deriv_refl_re_pos hg₂ hρ2 hG₂d hG₂inj hG₂e hG₂real hpd
  refine ⟨_, hm, ?_⟩
  intro W hW t ht hKH h0
  have hd : Disjoint (ball (p : ℂ) ρ) (fwdHull W t) := hpH.mono_right hKH
  have hpB : (p : ℂ) ∈ ball (p : ℂ) (ρ / 2) := mem_ball_self hρ2
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_disjoint_ball_gen hW (h0 p hpB) ht hρ hd
  have hgt := isMapOut_fwdMap_gen hW ht
  obtain ⟨G, hGd, hGg, -, hGx, -, hGinj, -, -, hGreal⟩ :=
    ConformalImageFull.IsMapOut.exists_reflection_full (isHPHull_fwdHull hW ht) hgt hρ hd
  have hGx' : G p = fwdMap W t p + W t := by rw [hGx, fwdMap_add_eq_limUnder hW ht hv]
  obtain ⟨δ, hδ, hlow, hx⟩ := exists_aliveDisc_self hv ht
  have hfd : DifferentiableAt ℂ (fwdMap W t) p :=
    (hasDerivAt_fwdMap_aliveDisc hW hv hδ hlow hx ⟨ht, le_rfl⟩).differentiableAt
  have hGdx : DifferentiableAt ℂ G p := hGd.differentiableAt (isOpen_ball.mem_nhds hpB)
  have hupper : ∀ ε ∈ Ioo (0 : ℝ) (ρ / 2), G ((p : ℂ) + (ε : ℂ) * I) = fwdMap W t ((p : ℂ) + (ε : ℂ) * I) + W t := by
    intro ε hε
    have hzB : (p : ℂ) + (ε : ℂ) * I ∈ ball (p : ℂ) (ρ / 2) := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hε.1]
      exact hε.2
    have hzH : (p : ℂ) + (ε : ℂ) * I ∈ H := by
      show 0 < ((p : ℂ) + (ε : ℂ) * I).im
      simp [hε.1]
    exact hGg ⟨hzB, hzH⟩
  have hderiv : deriv G p = deriv (fwdMap W t) p := by
    rw [deriv_eq_of_eq_upper hρ2 hGdx (hfd.add_const ((W t : ℝ) : ℂ)) hGx' hupper, deriv_add_const]
  obtain ⟨hGim, -⟩ := deriv_refl_re_pos hgt hρ2 hGd hGinj hGg hGreal
    (hd.mono_left (ball_subset_ball (by linarith)))
  have hle1 : (deriv G p).re ≤ (deriv id (p : ℂ)).re := by
    refine re_deriv_le_of_im_le hρ2 hGdx differentiableAt_id (hGreal _ hpB (by simp)) (by simp) fun ε hε => ?_
    have hzB : (p : ℂ) + (ε : ℂ) * I ∈ ball (p : ℂ) (ρ / 2) := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hε.1]
      exact hε.2
    have hzH : (p : ℂ) + (ε : ℂ) * I ∈ H := by
      show 0 < ((p : ℂ) + (ε : ℂ) * I).im
      simp [hε.1]
    have hzK : (p : ℂ) + (ε : ℂ) * I ∉ fwdHull W t := fun hK =>
      Set.disjoint_left.1 hd (ball_subset_ball (by linarith) hzB) hK
    rw [hGg ⟨hzB, hzH⟩]
    exact hgt.im_le (isHPHull_fwdHull hW ht) ⟨hzH, hzK⟩
  have hML := re_deriv_le_of_subset (isHPHull_fwdHull hW ht) hH₂ hKH hgt hg₂ hρ2 hpd hGdx
    (hG₂d.differentiableAt (isOpen_ball.mem_nhds hpB)) (hGreal _ hpB (by simp)) (hG₂real _ hpB (by simp))
    hGg hG₂e
  rw [hderiv] at hGim hle1 hML
  rw [deriv_id, Complex.one_re] at hle1
  exact ⟨hGim, hML, hle1⟩

end InteractingSLE.ZhanGT4
