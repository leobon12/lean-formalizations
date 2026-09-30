/-
Copyright (c) 2026 The quantum-zipper authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: quantum-zipper (CA-H4U, EXT-CA node U4, boundary limits of the inverse map)
-/
import QuantumZipper.Proofs.Complex.UniformizerBdry
import QuantumZipper.Proofs.Complex.UniformizerComp
import QuantumZipper.Proofs.Complex.CaraExt
import QuantumZipper.Proofs.Complex.CaraBdryFold
import QuantumZipper.Proofs.Complex.CaraBdrySurj

/-!
# Boundary limits of the inverse conformal map at `0` and `∞` (EXT-CA node U4, part 2)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 "U", node U4.  Let `ψ : ℍ → D = leftComponent η`
be a holomorphic bijection (U3) with inverse `φ₀`.  In the disk model `cayley ∘ ψ`, the
Carathéodory extension (C3, `continuousOn_extension`) takes each of the values `cayley 0 = -1` and
`1 = cayley ∞` exactly once on `ℝ ∪ {∞}` (C6 `eq_of_isPreconnected_diff`, with the connectedness
of `E \ {q}` from `UniformizerBdry`, and C7 `frontier_eq_insert_range`).  A compactness argument in
the closed unit disk (every cluster value `p` of `cayley ∘ φ₀` at the boundary point satisfies
`F(p) = q`, hence is the unique preimage) gives

* `exists_boundary_limits`: `cayley (φ₀ z) → ζ₀` as `z → 0` in `D`, and `cayley (φ₀ z) → ζinf`
  as `z → ∞` in `D`, for two *distinct* points `ζ₀, ζinf` of the unit circle.

What is left for `IsNormalizedUniformizer` is the Möbius normalization sending `ζ₀ ↦ -1` and
`ζinf ↦ 1` (see `handoff/CA-H4U.md`).

## Sources

The compactness ("subsequence") argument of the blueprint's U4 sketch; Pommerenke, *Boundary
Behaviour of Conformal Maps* (Springer 1992), Thm 2.6 (Carathéodory: the extension is a
homeomorphism of the closures when the boundary is a Jordan curve) is the classical form; here
only injectivity at the two points `q = -1, 1` is available and suffices.  **Own proof** of the
compactness step (cost rule of `AGENT_GUIDE.md`).
-/

noncomputable section

open Set Metric Filter Bornology
open scoped Topology

namespace QuantumZipper.CA.Uniformizer

variable {η : ℝ → ℂ}

/-- Abstract cluster lemma: if `p` is a cluster value of `T` along `l`, `T ∈ S` eventually,
`g → y` along `𝓝[S] p` and `g ∘ T → q` along `l`, then `y = q`. -/
theorem eq_of_mapClusterPt {α : Type*} {l : Filter α} {T : α → ℂ} {S : Set ℂ} {g : ℂ → ℂ}
    {p q y : ℂ} (hp : MapClusterPt p l T) (hS : ∀ᶠ x in l, T x ∈ S)
    (hg : Tendsto g (𝓝[S] p) (𝓝 y)) (hq : Tendsto (fun x => g (T x)) l (𝓝 q)) : y = q := by
  by_contra hne
  obtain ⟨U, V, hU, hV, hUV⟩ := t2_separation_nhds hne
  obtain ⟨W, hW, hWS⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hg hU)
  obtain ⟨x, hxW, hxS, hxV⟩ :=
    ((mapClusterPt_iff_frequently.1 hp W hW).and_eventually (hS.and (hq hV))).exists
  exact Set.disjoint_left.1 hUV (hWS ⟨hxW, hxS⟩) hxV

theorem norm_cayley_ofReal (x : ℝ) : ‖cayley (x : ℂ)‖ = 1 := by
  have h : cayley (x : ℂ) ∈ sphere (0 : ℂ) 1 := by
    rw [← cayley_image_real]; exact Or.inl ⟨x, by simp, rfl⟩
  simpa using h

theorem cayleyInv_real_of_norm_eq_one {p : ℂ} (hp : ‖p‖ = 1) :
    (((cayleyInv p).re : ℝ) : ℂ) = cayleyInv p := by
  refine Complex.ext (by simp) ?_
  rw [Complex.ofReal_im, im_cayleyInv, hp]
  simp

/-- **Boundary limit of the inverse map** at a boundary point `q` of `cayley '' D` whose preimage
under the extension is unique. -/
theorem tendsto_cayley_comp_inv {ψ φ₀ F : ℂ → ℂ} {wInf : ℂ}
    (hφb : MapsTo φ₀ (leftComponent η) H) (hinv : LeftInvOn ψ φ₀ (leftComponent η))
    (hEq : EqOn F (cayley ∘ ψ) H) (hF : ContinuousOn F Hbar)
    (hInf : Tendsto (cayley ∘ ψ) (cobounded ℂ ⊓ 𝓟 H) (𝓝 wInf))
    (hMaps : MapsTo (cayley ∘ ψ) H (ball 0 1))
    {q : ℂ} (hq1 : ‖q‖ = 1)
    (hC6 : (∀ x y : ℝ, F x = q → F y = q → x = y) ∧ (wInf = q → ∀ x : ℝ, F x ≠ q))
    (hfr : q ∈ insert wInf (range fun x : ℝ => F x))
    {l : Filter ℂ} (hlD : ∀ᶠ z in l, z ∈ leftComponent η) (hl : Tendsto cayley l (𝓝 q)) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ((ζ = 1 ∧ wInf = q) ∨ (ζ ≠ 1 ∧ F (cayleyInv ζ) = q)) ∧
      Tendsto (fun z => cayley (φ₀ z)) l (𝓝 ζ) := by
  -- values of `cayley ∘ φ₀` lie in the open disk, and `F ∘ cayleyInv ∘ cayley ∘ φ₀ = cayley`
  have hball : ∀ᶠ z in l, cayley (φ₀ z) ∈ ball (0 : ℂ) 1 :=
    hlD.mono fun z hz => cayley_mem_ball (hφb hz)
  have hcomp : Tendsto (fun z => F (cayleyInv (cayley (φ₀ z)))) l (𝓝 q) := by
    refine hl.congr' (hlD.mono fun z hz => ?_)
    have hH := hφb hz
    show cayley z = F (cayleyInv (cayley (φ₀ z)))
    rw [cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt hH)), hEq hH]
    simp only [Function.comp_apply, hinv hz]
  have hkey : ∀ (S : Set ℂ) (p y : ℂ), MapClusterPt p l (fun z => cayley (φ₀ z)) →
      (∀ᶠ z in l, cayley (φ₀ z) ∈ S) →
      Tendsto (fun w => F (cayleyInv w)) (𝓝[S] p) (𝓝 y) → y = q :=
    fun S p y hp hS hg => eq_of_mapClusterPt hp hS hg hcomp
  -- the candidate limit point
  obtain ⟨ζ, hζ1, hζ, hζuniq⟩ : ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
      ((ζ = 1 ∧ wInf = q) ∨ (ζ ≠ 1 ∧ F (cayleyInv ζ) = q)) ∧
      ((wInf = q → ζ = 1) ∧ ∀ x : ℝ, F x = q → ζ = cayley x) := by
    rcases hfr with hw | ⟨x₀, hx₀⟩
    · refine ⟨1, by simp, Or.inl ⟨rfl, hw.symm⟩, fun _ => rfl, fun x hx => ?_⟩
      exact absurd hx (hC6.2 hw.symm x)
    · have hx0I : (x₀ : ℂ) + Complex.I ≠ 0 := add_I_ne_zero_of_im_nonneg (by simp)
      refine ⟨cayley x₀, norm_cayley_ofReal x₀, Or.inr ⟨cayley_ne_one hx0I, ?_⟩,
        fun hw => absurd hx₀ (hC6.2 hw x₀), fun x hx => by rw [hC6.1 x x₀ hx hx₀]⟩
      rw [cayleyInv_cayley hx0I]; exact hx₀
  refine ⟨ζ, hζ1, hζ, ?_⟩
  refine (isCompact_closedBall (0 : ℂ) 1).tendsto_nhds_of_unique_mapClusterPt
    (hball.mono fun z hz => ball_subset_closedBall hz) fun p hp hcl => ?_
  by_cases hp1 : p = 1
  · -- cluster value `1`: then `wInf = q`
    subst hp1
    have hw : wInf = q := by
      refine hkey (ball 0 1) 1 wInf hcl hball ?_
      have h1 : Tendsto cayleyInv (𝓝[ball 0 1] 1) (cobounded ℂ ⊓ 𝓟 H) := by
        refine tendsto_inf.2 ⟨tendsto_cayleyInv_nhdsNE_one.mono_left
          (nhdsWithin_mono _ fun w hw => ne_one_of_mem_unitBall hw), ?_⟩
        exact tendsto_principal.2 (eventually_mem_nhdsWithin.mono fun w hw => cayleyInv_mem_H hw)
      refine (hInf.comp h1).congr' (eventually_mem_nhdsWithin.mono fun w hw => ?_)
      exact (hEq (cayleyInv_mem_H hw)).symm
    exact (hζuniq.1 hw).symm
  · -- cluster value `p ≠ 1`: then `F (cayleyInv p) = q`
    have hpS : p ∈ closedBall (0 : ℂ) 1 \ {1} := ⟨hp, hp1⟩
    have hFp : F (cayleyInv p) = q := by
      refine hkey (closedBall 0 1 \ {1}) p _ hcl
        (hball.mono fun z hz => ⟨ball_subset_closedBall hz, ne_one_of_mem_unitBall hz⟩) ?_
      have hc : ContinuousWithinAt (fun w => F (cayleyInv w)) (closedBall 0 1 \ {1}) p :=
        (hF _ (cayleyInv_mem_Hbar hp)).comp
          (continuousOn_cayleyInv.continuousAt (isOpen_ne.mem_nhds hp1)).continuousWithinAt
          fun w hw => cayleyInv_mem_Hbar hw.1
      exact hc.tendsto
    rcases (mem_closedBall_zero_iff.1 hp).lt_or_eq with hlt | heq
    · -- interior point: `F (cayleyInv p) ∈ ball 0 1`, impossible on the circle
      have hH : cayleyInv p ∈ H := cayleyInv_mem_H (mem_ball_zero_iff.2 hlt)
      have := hMaps hH
      rw [← hEq hH, hFp, mem_ball_zero_iff, hq1] at this
      exact absurd this (lt_irrefl 1)
    · have hx := cayleyInv_real_of_norm_eq_one heq
      have := hζuniq.2 _ (by rw [hx]; exact hFp)
      rw [hx, cayley_cayleyInv hp1] at this
      exact this.symm

theorem neBot_cobounded_inf_leftComponent (hη : IsSimpleChord η) :
    (cobounded ℂ ⊓ 𝓟 (leftComponent η)).NeBot := by
  rw [inf_principal_neBot_iff]
  intro U hU
  have hb : IsBounded Uᶜ := isBounded_def.2 (by rwa [compl_compl])
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hb
  have hx : -(|R| + 2) < (0 : ℝ) := by linarith [abs_nonneg R]
  obtain ⟨z, hzD, hzd⟩ :=
    Metric.mem_closure_iff.1 (ofReal_mem_closure_leftComponent hη hx) 1 one_pos
  refine ⟨z, ?_, hzD⟩
  by_contra hzU
  have h1 := hR z hzU
  have h2 : ‖(((-(|R| + 2) : ℝ)) : ℂ)‖ = |R| + 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hx, neg_neg]
  have h3 := norm_sub_norm_le (((-(|R| + 2) : ℝ)) : ℂ) z
  rw [dist_eq_norm] at hzd
  linarith [le_abs_self R]

/-- **U4 (boundary limits).** For a holomorphic bijection `ψ : ℍ → D = leftComponent η` with
inverse `φ₀`, the map `cayley ∘ φ₀` has limits `ζ₀` at `0` and `ζinf` at `∞` (within `D`), two
distinct points of the unit circle. -/
theorem exists_boundary_limits (hη : IsSimpleChord η) {ψ φ₀ : ℂ → ℂ}
    (hψb : BijOn ψ H (leftComponent η)) (hψd : DifferentiableOn ℂ ψ H)
    (hφb : MapsTo φ₀ (leftComponent η) H) (hinv : LeftInvOn ψ φ₀ (leftComponent η)) :
    ∃ ζ₀ ζinf : ℂ, ‖ζ₀‖ = 1 ∧ ‖ζinf‖ = 1 ∧ ζ₀ ≠ ζinf ∧
      Tendsto (fun z => cayley (φ₀ z)) (𝓝[leftComponent η] 0) (𝓝 ζ₀) ∧
      Tendsto (fun z => cayley (φ₀ z)) (cobounded ℂ ⊓ 𝓟 (leftComponent η)) (𝓝 ζinf) := by
  have h := carHyp_cayley_comp hη hψb hψd
  obtain ⟨F, hEq, hF, -, wInf, -, hInf⟩ := Car.continuousOn_extension h (ulc_thetaCurve hη)
  have hfr := Car.frontier_eq_insert_range h hEq hF hInf
  have hMaps : MapsTo (cayley ∘ ψ) H (ball 0 1) := fun z hz => h.bdd (h.bij.mapsTo hz)
  have hnotΩ : ∀ w : ℂ, ‖w‖ = 1 → w ∉ cayley '' leftComponent η := fun w hw hwΩ => by
    have := h.bdd hwΩ
    rw [mem_ball_zero_iff, hw] at this
    exact lt_irrefl 1 this
  have hc0 : ContinuousAt cayley 0 := (differentiableAt_cayley (by simp)).continuousAt
  -- `-1` and `1` are boundary points of `cayley '' D`
  have hm1 : (-1 : ℂ) ∈ frontier (cayley '' leftComponent η) := by
    rw [h.isOpen.frontier_eq]
    refine ⟨?_, hnotΩ _ (by simp)⟩
    rw [← cayley_zero]
    exact mem_closure_image hc0 (zero_mem_closure_leftComponent hη)
  have hp1 : (1 : ℂ) ∈ frontier (cayley '' leftComponent η) := by
    rw [h.isOpen.frontier_eq]
    refine ⟨?_, hnotΩ _ (by simp)⟩
    haveI := neBot_cobounded_inf_leftComponent hη
    exact mem_closure_of_tendsto (tendsto_cayley_cobounded.mono_left inf_le_left)
      (eventually_inf_principal.2 (Eventually.of_forall fun z hz => mem_image_of_mem cayley hz))
  have hC0 := Car.eq_of_isPreconnected_diff h hEq hF hInf
    (isPreconnected_thetaCurve_diff_cayley_zero hη)
  rw [cayley_zero] at hC0
  have hC1 := Car.eq_of_isPreconnected_diff h hEq hF hInf (isPreconnected_thetaCurve_diff_one hη)
  obtain ⟨ζ₀, hζ₀1, hζ₀, hlim₀⟩ := tendsto_cayley_comp_inv hφb hinv hEq hF hInf hMaps
    (q := -1) (by simp) hC0 (hfr ▸ hm1) self_mem_nhdsWithin
    (by simpa [cayley_zero] using hc0.tendsto.mono_left nhdsWithin_le_nhds)
  obtain ⟨ζinf, hζinf1, hζinf, hliminf⟩ := tendsto_cayley_comp_inv hφb hinv hEq hF hInf hMaps
    (q := 1) (by simp) hC1 (hfr ▸ hp1) (mem_inf_of_right (mem_principal_self _))
    (tendsto_cayley_cobounded.mono_left inf_le_left)
  refine ⟨ζ₀, ζinf, hζ₀1, hζinf1, ?_, hlim₀, hliminf⟩
  rintro rfl
  rcases hζ₀ with ⟨h1, hw1⟩ | ⟨h1, hF1⟩ <;> rcases hζinf with ⟨h2, hw2⟩ | ⟨h2, hF2⟩
  · rw [hw1] at hw2; norm_num at hw2
  · exact h2 h1
  · exact h1 h2
  · rw [hF1] at hF2; norm_num at hF2

end QuantumZipper.CA.Uniformizer
