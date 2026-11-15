import InteractingSLE.Foundations.Topology.SimplyConnected
import QuantumZipper.Proofs.Complex.CaraBdrySurj
import QuantumZipper.Proofs.Complex.CaraExt
import QuantumZipper.Proofs.Complex.UniformizerBdry

/-!
# Continuous boundary extension onto complements of locally connected sets

Packet GEO-CARA of `planning/INFRA-GEO.md` §4 (`Topology/PathComplement`), first part.

The extension theorem for a conformal map `ψ : ℍ → U` onto a domain whose boundary lies in
`ℝ ∪ K`, for a compact uniformly locally connected `K ⊆ ℍ̄`
(`exists_continuousOn_extension_of_ulc`).
It is Pommerenke's continuity theorem ([Pom] C. Pommerenke, *Boundary Behaviour of Conformal Maps*,
Springer 1992, Thm 2.1, (iv) ⇒ (i), printed pp. 20–22), in the half-plane form proved by
QuantumZipper (`QuantumZipper.CA.Car.continuousOn_extension`, node C3), applied in the bounded model
`cayley(U)` with the closed set `E = 𝕋 ∪ cayley(K)` in the role of Pommerenke's `ℂ \ G`. The
normalization `ψ(z) → ∞` as `z → ∞` makes the extension finite at the real points: the boundary
value `1 = cayley(∞)` is attained only at `∞` because `E \ {1}` is connected (QuantumZipper's
C6, `eq_of_isPreconnected_diff`, which is [Pom] Prop. 2.5 and Thm 2.6, pp. 23–24).

## Main results

* `ulc_image_of_leftInvOn`, `ulc_image_cayley`: uniform local connectedness (QuantumZipper's
  `Topo.ULC`, [Pom] p. 19 (1)) is carried along maps with continuous inverses on compact sets.
* `ulc_of_locallyConnectedSpace`, `locallyConnectedSpace_of_ulc`: for compact (resp. bounded)
  planar sets, `Topo.ULC` is equivalent to Mathlib's `LocallyConnectedSpace`.
* `exists_continuousOn_extension_of_ulc`: the extension theorem.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open QuantumZipper.CA.Topo (ULC)

namespace InteractingSLE

/-! ### The Cayley transform on `ℍ̄` -/

theorem cayley_ne_one_of_mem_Hbar {z : ℂ} (hz : z ∈ Hbar) : cayley z ≠ 1 :=
  QuantumZipper.CA.cayley_ne_one (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg hz)

theorem continuousOn_cayley_Hbar : ContinuousOn cayley Hbar :=
  QuantumZipper.CA.continuousOn_cayley.mono fun _ hz =>
    QuantumZipper.CA.ne_neg_I_iff.2 (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg hz)

theorem cayleyInv_cayley_of_mem_Hbar {z : ℂ} (hz : z ∈ Hbar) : cayleyInv (cayley z) = z :=
  QuantumZipper.CA.cayleyInv_cayley (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg hz)

/-! ### Uniform local connectedness -/

/-- Uniform local connectedness is carried along a map that is continuous on a compact set `K`
and has a left inverse continuous on the image. -/
theorem ulc_image_of_leftInvOn {K : Set ℂ} {f g : ℂ → ℂ} (hK : IsCompact K)
    (hf : ContinuousOn f K) (hg : ContinuousOn g (f '' K)) (hgf : LeftInvOn g f K)
    (hKu : ULC K) : ULC (f '' K) := by
  intro ε hε
  have hKc : IsCompact (f '' K) := hK.image_of_continuousOn hf
  obtain ⟨η, hη, hηu⟩ :=
    Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hf) ε hε
  obtain ⟨δ₁, hδ₁, hu⟩ := hKu (η / 2) (half_pos hη)
  obtain ⟨δ, hδ, hδu⟩ :=
    Metric.uniformContinuousOn_iff.1 (hKc.uniformContinuousOn_of_continuous hg) δ₁ hδ₁
  refine ⟨δ, hδ, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
  have hab' : dist a b < δ₁ := by
    have := hδu _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rwa [hgf ha, hgf hb] at this
  obtain ⟨β, hβK, hβc, haβ, hbβ, hβd⟩ := hu a ha b hb hab'
  refine ⟨f '' β, image_mono hβK, hβc.image _ (hf.mono hβK), mem_image_of_mem _ haβ,
    mem_image_of_mem _ hbβ, ?_⟩
  refine Metric.diam_le_of_forall_dist_le hε.le ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have hxy : dist x y < η := by
    have := dist_le_diam_of_mem (hK.isBounded.subset hβK) hx hy
    linarith
  exact (hηu x (hβK hx) y (hβK hy) hxy).le

/-- Uniform local connectedness is carried along the Cayley transform on compact subsets of
`ℍ̄`. -/
theorem ulc_image_cayley {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar) (hKu : ULC K) :
    ULC (cayley '' K) := by
  refine ulc_image_of_leftInvOn hK (continuousOn_cayley_Hbar.mono hKH)
    (QuantumZipper.CA.continuousOn_cayleyInv.mono ?_)
    (fun z hz => cayleyInv_cayley_of_mem_Hbar (hKH hz)) hKu
  rintro _ ⟨z, hz, rfl⟩
  exact cayley_ne_one_of_mem_Hbar (hKH hz)

/-- A compact locally connected planar set is uniformly locally connected (Newman's
characterization, [Pom] p. 19). -/
theorem ulc_of_locallyConnectedSpace {E : Set ℂ} (hE : IsCompact E) [LocallyConnectedSpace E] :
    ULC E := by
  refine QuantumZipper.CA.Topo.ULC.of_isCompact_of_forall hE fun x hx ε hε => ?_
  set V : Set E := {y | dist (y : ℂ) x < ε / 2} with hV
  have hVo : IsOpen V := isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const
  have hxV : (⟨x, hx⟩ : E) ∈ V := show dist x x < ε / 2 by rw [dist_self]; positivity
  set W := connectedComponentIn V ⟨x, hx⟩ with hW
  have hWo : IsOpen W := hVo.connectedComponentIn
  obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.1 hWo ⟨x, hx⟩ (mem_connectedComponentIn hxV)
  refine ⟨ρ, hρ, fun a ha hax => ⟨Subtype.val '' W, by rintro _ ⟨y, -, rfl⟩; exact y.2,
    isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn,
    ⟨⟨x, hx⟩, mem_connectedComponentIn hxV, rfl⟩,
    ⟨⟨a, ha⟩, hρW (show dist (⟨a, ha⟩ : E) ⟨x, hx⟩ < ρ from hax), rfl⟩, ?_⟩⟩
  refine Metric.diam_le_of_forall_dist_le hε.le ?_
  rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
  have hy' : y ∈ V := connectedComponentIn_subset _ _ hy
  have hz' : z ∈ V := connectedComponentIn_subset _ _ hz
  simp only [hV, mem_ofPred_eq] at hy' hz'
  calc dist (y : ℂ) z ≤ dist (y : ℂ) x + dist (z : ℂ) x := dist_triangle_right _ _ _
    _ ≤ ε := by linarith

/-- A bounded uniformly locally connected planar set is locally connected. -/
theorem locallyConnectedSpace_of_ulc {E : Set ℂ} (hEb : Bornology.IsBounded E) (hE : ULC E) :
    LocallyConnectedSpace E := by
  refine locallyConnectedSpace_iff_connected_subsets.2 fun x U hU => ?_
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨δ, hδ, hδu⟩ := hE (ε / 2) (half_pos hε)
  set W : Set ℂ := connectedComponentIn (E ∩ ball (x : ℂ) ε) x with hW
  have hxW : (x : ℂ) ∈ E ∩ ball (x : ℂ) ε := ⟨x.2, mem_ball_self hε⟩
  have hWE : W ⊆ E := (connectedComponentIn_subset _ _).trans inter_subset_left
  refine ⟨Subtype.val ⁻¹' W, ?_, ?_, ?_⟩
  · refine Metric.mem_nhds_iff.2 ⟨min δ ε, lt_min hδ hε, fun y hy => ?_⟩
    have hy' : dist (y : ℂ) x < min δ ε := hy
    obtain ⟨β, hβE, hβc, hyβ, hxβ, hβd⟩ :=
      hδu y y.2 x x.2 (hy'.trans_le (min_le_left _ _))
    have hsub : β ⊆ E ∩ ball (x : ℂ) ε := fun b hb => ⟨hβE hb, mem_ball.2 (by
      have := dist_le_diam_of_mem (hEb.subset hβE) hb hxβ
      linarith)⟩
    exact hβc.subset_connectedComponentIn hxβ hsub hyβ
  · rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, image_preimage_eq_of_subset
      (by rw [Subtype.range_coe]; exact hWE)]
    exact isPreconnected_connectedComponentIn
  · intro y hy
    exact hεU ((connectedComponentIn_subset _ _ hy).2)

/-! ### The extension theorem -/

open QuantumZipper.CA in
/-- **Continuous boundary extension** ([Pom] Thm 2.1, (iv) ⇒ (i), pp. 20–22, half-plane form).
Let `U ⊆ ℍ` be open with `∂U ⊆ ℝ ∪ K` and `U ∩ K = ∅`, where `K ⊆ ℍ̄` is compact and uniformly
locally connected and `ℝ ∪ K` is connected. A conformal bijection `ψ : ℍ → U` with `ψ(z) → ∞` as
`z → ∞` extends to a map `F`, continuous on `ℍ̄`, with real boundary values in `∂U`, and with
`F(z) → ∞` as `z → ∞` in `ℍ̄` (so `F` is a continuous map of the compactified closed half-plane).

Proof: QuantumZipper's C3 in the bounded model `cayley(U)` with `E = 𝕋 ∪ cayley(K)` (closed,
ULC, `∂ cayley(U) ⊆ E ⊆ ℂ \ cayley(U)`); the limit at `∞` is `cayley ∞ = 1`; since
`E \ {1} = cayley(ℝ ∪ K)` is connected, C6 shows that the extension never takes the value `1` on
`ℝ`, so `cayleyInv` of it is finite and continuous. -/
theorem exists_continuousOn_extension_of_ulc {U K : Set ℂ} (hUo : IsOpen U) (hUH : U ⊆ H)
    (hUfr : frontier U ⊆ {z : ℂ | z.im = 0} ∪ K) (hUK : Disjoint U K)
    (hK : IsCompact K) (hKH : K ⊆ Hbar) (hKu : ULC K)
    (hKc : IsPreconnected ({z : ℂ | z.im = 0} ∪ K)) {ψ : ℂ → ℂ}
    (hψ : IsConformalBijection ψ H U)
    (hψi : Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (Bornology.cobounded ℂ)) :
    ∃ F : ℂ → ℂ, EqOn F ψ H ∧ ContinuousOn F Hbar ∧ MapsTo F (Hbar \ H) (frontier U) ∧
      Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ) := by
  set D := cayley '' U with hD
  set E := sphere (0 : ℂ) 1 ∪ cayley '' K with hE
  have hUHb : U ⊆ Hbar := hUH.trans QuantumZipper.H_subset_Hbar
  have hinv : LeftInvOn cayleyInv cayley U := fun z hz => cayleyInv_cayley_of_mem_Hbar (hUHb hz)
  have hDo : IsOpen D := cayleyOPH.isOpen_image_of_subset_source hUo fun z hz =>
    ne_neg_I_iff.2 (add_I_ne_zero_of_im_nonneg (hUHb hz))
  have hKcpt : IsCompact (cayley '' K) :=
    hK.image_of_continuousOn (continuousOn_cayley_Hbar.mono hKH)
  have hEc : IsCompact E := (isCompact_sphere 0 1).union hKcpt
  have hEu : ULC E := Topo.ULC.union_of_isCompact_of_isClosed (isCompact_sphere 0 1)
    hKcpt.isClosed (Topo.ULC.sphere 0 1) (ulc_image_cayley hK hKH hKu)
  have hcar : Car.CarHyp (cayley ∘ ψ) D E 1 := by
    refine ⟨(differentiableOn_cayley_Hbar.mono hUHb).comp hψ.1 hψ.2.mapsTo,
      ((Uniformizer.cayley_injOn_Hbar.mono hUHb).bijOn_image).comp hψ.2, hDo, ?_,
      hEc.isClosed, ?_, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact cayley_mem_ball (hUH hz)
    · rw [hDo.frontier_eq]
      rintro w ⟨hwc, hwD⟩
      have hwB : w ∈ closedBall (0 : ℂ) 1 := closure_minimal
        (by rintro _ ⟨z, hz, rfl⟩; exact ball_subset_closedBall (cayley_mem_ball (hUH hz)))
        isClosed_closedBall hwc
      by_cases hs : ‖w‖ = 1
      · exact Or.inl (mem_sphere_zero_iff_norm.2 hs)
      have hwb : w ∈ ball (0 : ℂ) 1 :=
        mem_ball_zero_iff.2 (lt_of_le_of_ne (mem_closedBall_zero_iff.1 hwB) hs)
      have hw1 : w ≠ 1 := Uniformizer.ne_one_of_mem_unitBall hwb
      have hzw : cayley (cayleyInv w) = w := cayley_cayleyInv hw1
      have hzc : cayleyInv w ∈ closure U := by
        have := mem_closure_image (continuousOn_cayleyInv.continuousAt (isOpen_ne.mem_nhds hw1)) hwc
        rwa [hinv.image_image] at this
      have hzU : cayleyInv w ∉ U := fun h => hwD ⟨_, h, hzw⟩
      have hzfr : cayleyInv w ∈ frontier U := by rw [hUo.frontier_eq]; exact ⟨hzc, hzU⟩
      rcases hUfr hzfr with hr | hk
      · exfalso
        have : w ∈ sphere (0 : ℂ) 1 := by
          rw [← hzw, ← Uniformizer.cayley_image_real]; exact Or.inl ⟨_, hr, rfl⟩
        exact hs (mem_sphere_zero_iff_norm.1 this)
      · exact Or.inr ⟨_, hk, hzw⟩
    · rintro w (hw | ⟨k, hk, rfl⟩) ⟨z, hz, hzw⟩
      · have h1 := cayley_mem_ball (hUH hz)
        rw [hzw, mem_ball_zero_iff] at h1
        rw [mem_sphere_zero_iff_norm] at hw
        linarith
      · exact hUK.ne_of_mem hz hk (Uniformizer.cayley_injOn_Hbar (hUHb hz) (hKH hk) hzw)
    · rintro w (hw | ⟨k, hk, rfl⟩)
      · exact sphere_subset_closedBall hw
      · exact cayley_mem_closedBall (hKH hk)
  obtain ⟨Fψ, hEq, hFc, hFfr, wInf, -, hInf⟩ := Car.continuousOn_extension hcar hEu
  have hInf1 : Tendsto (cayley ∘ ψ) (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 1) :=
    tendsto_cayley_cobounded.comp hψi
  have hw1 : wInf = 1 := by
    have := Car.neBot_cobounded_inf_H
    exact tendsto_nhds_unique hInf hInf1
  subst hw1
  have hRH : {z : ℂ | z.im = 0} ⊆ Hbar := fun z (hz : z.im = 0) => show 0 ≤ z.im from hz.ge
  have hE1 : E \ {1} = cayley '' ({z : ℂ | z.im = 0} ∪ K) := by
    rw [image_union, ← Uniformizer.sphere_diff_one, hE, union_sdiff_distrib]
    congr 1
    exact sdiff_singleton_eq_self fun ⟨k, hk, h⟩ => cayley_ne_one_of_mem_Hbar (hKH hk) h
  have hEpc : IsPreconnected (E \ {1}) := by
    rw [hE1]
    exact hKc.image _ (continuousOn_cayley_Hbar.mono (union_subset hRH hKH))
  have C6 := Car.eq_of_isPreconnected_diff hcar hEq hFc hInf hEpc
  have hreal : ∀ z : ℂ, z.im = 0 → z = ((z.re : ℝ) : ℂ) := fun z hz =>
    Complex.ext (by simp) (by simp [hz])
  have hne1 : ∀ z ∈ Hbar, Fψ z ≠ 1 := by
    intro z hz
    rcases (show (0 : ℝ) ≤ z.im from hz).eq_or_lt with h0 | hpos
    · rw [hreal z h0.symm]; exact C6.2 rfl z.re
    · rw [hEq hpos]
      exact Uniformizer.ne_one_of_mem_unitBall (cayley_mem_ball (hUH (hψ.2.mapsTo hpos)))
  refine ⟨cayleyInv ∘ Fψ, fun z hz => ?_, ?_, ?_, ?_⟩
  · show cayleyInv (Fψ z) = ψ z
    rw [hEq hz]; exact cayleyInv_cayley_of_mem_Hbar (hUHb (hψ.2.mapsTo hz))
  · exact continuousOn_cayleyInv.comp hFc fun z hz => hne1 z hz
  · rintro z ⟨hzb, hzH⟩
    have h0 : z.im = 0 := le_antisymm (not_lt.1 hzH) hzb
    have hfr : Fψ z ∈ frontier D := by rw [hreal z h0]; exact hFfr z.re
    have hw1 := hne1 z hzb
    rw [hDo.frontier_eq] at hfr
    rw [hUo.frontier_eq]
    refine ⟨?_, fun hU => hfr.2 ⟨_, hU, cayley_cayleyInv hw1⟩⟩
    have := mem_closure_image (continuousOn_cayleyInv.continuousAt (isOpen_ne.mem_nhds hw1)) hfr.1
    rwa [hinv.image_image] at this
  · have hR : Tendsto Fψ (Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | z.im = 0}) (𝓝 1) := by
      have h1 := Car.tendsto_extension_cocompact hEq hFc hInf
      have h2 : Tendsto (fun z : ℂ => z.re) (Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | z.im = 0})
          (cocompact ℝ) := by
        rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
        refine (tendsto_norm_cobounded_atTop.mono_left inf_le_left).congr' ?_
        filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
        rw [Real.norm_eq_abs]; exact (Complex.abs_re_eq_norm.2 hz).symm
      refine (h1.comp h2).congr' ?_
      filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
      simp only [Function.comp_apply]
      rw [← hreal z hz]
    have hH : Tendsto Fψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 1) := by
      refine hInf.congr' ?_
      filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz using (hEq hz).symm
    have hsplit : Hbar = H ∪ {z : ℂ | z.im = 0} := by
      ext z
      simp only [QuantumZipper.Hbar, QuantumZipper.H, mem_ofPred_eq, mem_union]
      constructor
      · intro h; rcases h.eq_or_lt with h | h
        · exact Or.inr h.symm
        · exact Or.inl h
      · rintro (h | h)
        · exact h.le
        · exact h.ge
    have hHbar : Tendsto Fψ (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (𝓝[≠] 1) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · rw [hsplit, ← sup_principal, inf_sup_left]; exact hH.sup hR
      · filter_upwards [mem_inf_of_right (mem_principal_self Hbar)] with z hz using hne1 z hz
    exact tendsto_cayleyInv_nhdsNE_one.comp hHbar

end InteractingSLE
