/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FcLocal

/-!
# Jordan coordinates of pockets opening at the flow seed: properness, collars and aliveness

Packet PROVE-R6-FACE2. Ports of `R6Safe.jordan_mem_ball_of_mem_ball`, `R6Safe.continuousOn_invFunOn_jordan`,
`R6Safe.exists_halfDisc_subset_image` and of `R6FcTrace`/`R6FcLocal`'s alive lemmas to an unbounded Jordan domain with
`Sec6.IsJordanCoordInf` (`ψ → ∞` at `∞`; no finite pole). The bounded proofs used compactness of `C̄`; here a sequence
either has a bounded subsequence (compactness of closed balls) or tends to `∞`, where `ψ` tends to `∞`.

* `jordanInf_mem_ball_of_mem_ball`, `continuousOn_invFunOn_jordanInf`, `exists_halfDisc_subset_imageInf`;
* `jordan_comp_extInf`, `exists_ball_subset_of_aliveInf`, `notMem_closure_of_ball_subsetInf`,
  `inter_ball_subset_of_noncornerInf`;
* `alive_iff_of`: the aliveness equivalence of `R6FcLocal.alive_iff` from the four one-chart facts, for any shapes.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.R6Fc

variable {C : Set ℂ} {y₀ : ℂ} {ψ : ℂ → ℂ}

/-- **Properness of a Jordan coordinate at infinity**: for `p ∈ C̄` and `ε > 0`, every point of `C̄` whose coordinate
is close enough to `ψ p` is `ε`-close to `p`. -/
theorem jordanInf_mem_ball_of_mem_ball (hψ : Sec6.IsJordanCoordInf C y₀ ψ) {p : ℂ} (hp : p ∈ closure C) {ε : ℝ}
    (hε : 0 < ε) : ∃ r > 0, ∀ z ∈ closure C, ψ z ∈ ball (ψ p) r → z ∈ ball p ε := by
  obtain ⟨hcont, hinj, -, -, -, -, hinf⟩ := hψ
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ z ∈ closure C, ψ z ∈ ball (ψ p) (1 / ((n : ℝ) + 1)) ∧ z ∉ ball p ε :=
    fun n => hcon _ (by positivity)
  choose z hzK hzψ hzp using hseq
  have hψlim : Tendsto (fun n => ψ (z n)) atTop (𝓝 (ψ p)) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    have h1 := mem_ball.1 (hzψ n)
    have h2 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      gcongr
    linarith
  by_cases hfreq : ∃ R : ℝ, ∃ᶠ n in atTop, ‖z n‖ ≤ R
  · obtain ⟨R, hR⟩ := hfreq
    obtain ⟨φ, hφ, hφR⟩ := Filter.extraction_of_frequently_atTop hR
    have hK : IsCompact (closedBall (0 : ℂ) R ∩ closure C) := (isCompact_closedBall 0 R).inter_right isClosed_closure
    obtain ⟨a, haK, φ', hφ', hlim⟩ := hK.tendsto_subseq (x := fun n => z (φ n))
      (fun n => ⟨mem_closedBall_zero_iff.2 (hφR n), hzK (φ n)⟩)
    have hamem : a ∉ ball p ε :=
      isOpen_ball.isClosed_compl.mem_of_tendsto hlim (Eventually.of_forall fun n => hzp (φ (φ' n)))
    have hwithin : Tendsto (fun n => z (φ (φ' n))) atTop (𝓝[closure C] a) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => hzK _⟩
    have h2 := ((hcont a haK.2).tendsto).comp hwithin
    have heq : ψ a = ψ p := tendsto_nhds_unique h2 (hψlim.comp (hφ.comp hφ').tendsto_atTop)
    exact hamem (hinj haK.2 hp heq ▸ mem_ball_self hε)
  · push Not at hfreq
    have hnorm : Tendsto (fun n => ‖z n‖) atTop atTop :=
      tendsto_atTop.2 fun R => (hfreq R).mono fun n hn => hn.le
    have hcob : Tendsto z atTop (cobounded ℂ ⊓ 𝓟 (closure C)) :=
      tendsto_inf.2 ⟨tendsto_norm_atTop_iff_cobounded.1 hnorm, tendsto_principal.2 (Eventually.of_forall hzK)⟩
    have h := tendsto_norm_cobounded_atTop.comp (hinf.comp hcob)
    exact not_tendsto_atTop_of_tendsto_nhds hψlim.norm h

/-- **The inverse of a Jordan coordinate at infinity is continuous on `ℍ`.** -/
theorem continuousOn_invFunOn_jordanInf (hψ : Sec6.IsJordanCoordInf C y₀ ψ) :
    ContinuousOn (Function.invFunOn ψ C) H := by
  have hbij := hψ.2.2.2.1.2
  rw [Metric.continuousOn_iff]
  intro w hw ε hε
  have hp : Function.invFunOn ψ C w ∈ C := Function.invFunOn_mem (hbij.surjOn hw)
  have hpw : ψ (Function.invFunOn ψ C w) = w := Function.invFunOn_eq (hbij.surjOn hw)
  obtain ⟨r, hr, hball⟩ := jordanInf_mem_ball_of_mem_ball hψ (subset_closure hp) hε
  refine ⟨r, hr, fun w' hw' hd => ?_⟩
  have hp' : Function.invFunOn ψ C w' ∈ C := Function.invFunOn_mem (hbij.surjOn hw')
  have hpw' : ψ (Function.invFunOn ψ C w') = w' := Function.invFunOn_eq (hbij.surjOn hw')
  exact hball _ (subset_closure hp') (by rw [hpw', hpw]; exact hd)

/-- **The collar of a contained domain along a shared wall** (pocket opening at the flow seed). -/
theorem exists_halfDisc_subset_imageInf (hψ : Sec6.IsJordanCoordInf C y₀ ψ) {U M : Set ℂ} (hUo : IsOpen U)
    (hUC : U ⊆ C) (hM : IsClosed M) (hfr : frontier U ∩ C ⊆ M) {p : ℂ} (hpU : p ∈ closure U) (hpC : p ∈ closure C)
    (hpM : p ∉ M) : ∃ r > 0, H ∩ ball (ψ p) r ⊆ ψ '' U := by
  have hbij := hψ.2.2.2.1.2
  obtain ⟨δ, hδ, hδM⟩ := Metric.isOpen_iff.1 hM.isOpen_compl p hpM
  obtain ⟨r, hr, hball⟩ := jordanInf_mem_ball_of_mem_ball hψ hpC hδ
  refine ⟨r, hr, ?_⟩
  set D := H ∩ ball (ψ p) r with hD
  set S := Function.invFunOn ψ C '' D with hS
  have hDH : D ⊆ H := inter_subset_left
  have hSpre : IsPreconnected S :=
    (((convex_halfSpace_gt Complex.imLm.isLinear 0 : Convex ℝ H).inter (convex_ball _ _)).isPreconnected).image _
      ((continuousOn_invFunOn_jordanInf hψ).mono hDH)
  have hSC : ∀ w ∈ D, Function.invFunOn ψ C w ∈ C := fun w hw => Function.invFunOn_mem (hbij.surjOn hw.1)
  have hSψ : ∀ w ∈ D, ψ (Function.invFunOn ψ C w) = w := fun w hw => Function.invFunOn_eq (hbij.surjOn hw.1)
  have hSsub : S ⊆ U ∪ (closure U)ᶜ := by
    rintro _ ⟨w, hw, rfl⟩
    have hzC := hSC w hw
    have hzb : Function.invFunOn ψ C w ∈ ball p δ :=
      hball _ (subset_closure hzC) (by rw [hSψ w hw]; exact hw.2)
    by_cases hzU : Function.invFunOn ψ C w ∈ U
    · exact Or.inl hzU
    · refine Or.inr fun hcl => hδM hzb ?_
      exact hfr ⟨⟨hcl, by rwa [hUo.interior_eq]⟩, hzC⟩
  have hcontp := hψ.1 p hpC
  obtain ⟨ρ, hρ, hρψ⟩ := Metric.continuousWithinAt_iff.1 hcontp r hr
  obtain ⟨u, huU, hud⟩ := Metric.mem_closure_iff.1 hpU ρ hρ
  have huC := hUC huU
  have huD : ψ u ∈ D := ⟨hbij.mapsTo huC, hρψ (subset_closure huC) (by rw [dist_comm]; exact hud)⟩
  have huS : u ∈ S := ⟨ψ u, huD, hbij.injOn.leftInvOn_invFunOn huC⟩
  have hSU : S ⊆ U := hSpre.subset_left_of_subset_union hUo isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure)) hSsub ⟨u, huS, huU⟩
  intro w hw
  exact ⟨_, hSU ⟨w, hw, rfl⟩, hSψ w hw⟩

/-- `ψ ∘ E₀ = id` on `ℍ̄` (pocket opening at the flow seed). -/
theorem jordan_comp_extInf (hψ : Sec6.IsJordanCoordInf C y₀ ψ) {E₀ : ℂ → ℂ}
    (hE : EqOn E₀ (Function.invFunOn ψ C) H) (hEc : ContinuousOn E₀ Hbar)
    (hEm : MapsTo E₀ Hbar (closure C)) {w : ℂ} (hw : w ∈ Hbar) : ψ (E₀ w) = w := by
  have hbij := hψ.2.2.2.1.2
  have hH : ∀ u ∈ H, ψ (E₀ u) = u := fun u hu => by
    rw [hE hu]; exact Function.invFunOn_eq (hbij.surjOn hu)
  have hcl : w ∈ closure H := by rwa [QuantumZipper.CA.Car.closure_H_eq_Hbar]
  have hE' : Tendsto E₀ (𝓝[H] w) (𝓝 (E₀ w)) := ((hEc w hw).mono QuantumZipper.H_subset_Hbar).tendsto
  have hE'' : Tendsto E₀ (𝓝[H] w) (𝓝[closure C] (E₀ w)) :=
    tendsto_nhdsWithin_iff.2 ⟨hE', eventually_nhdsWithin_of_forall fun u hu =>
      hEm (QuantumZipper.H_subset_Hbar hu)⟩
  have hlim := ((hψ.1 _ (hEm hw)).tendsto).comp hE''
  have hid : Tendsto (fun u => ψ (E₀ u)) (𝓝[H] w) (𝓝 w) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (eventually_nhdsWithin_of_forall fun u hu => (hH u hu).symm)
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  exact tendsto_nhds_unique hlim hid

/-- An alive point has a neighbourhood in the current domain (pocket opening at the flow seed). -/
theorem exists_ball_subset_of_aliveInf (hψ : Sec6.IsJordanCoordInf C y₀ ψ) {K : Set ℂ} {p : ℂ}
    (hp : p ∈ closure C) (hpK : ψ p ∉ closure K) : ∃ ρ > 0, C ∩ ball p ρ ⊆ C ∩ ψ ⁻¹' (H \ K) := by
  obtain ⟨r, hr, hrK⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hpK
  obtain ⟨ρ, hρ, hρψ⟩ := Metric.continuousWithinAt_iff.1 (hψ.1 p hp) r hr
  refine ⟨ρ, hρ, fun z hz => ⟨hz.1, hψ.2.2.2.1.2.mapsTo hz.1, fun hzK => ?_⟩⟩
  exact hrK (hρψ (subset_closure hz.1) (mem_ball.1 hz.2)) (subset_closure hzK)

/-- A neighbourhood in the current domain makes a point alive (pocket opening at the flow seed). -/
theorem notMem_closure_of_ball_subsetInf (hψ : Sec6.IsJordanCoordInf C y₀ ψ) {K : Set ℂ} (hKH : K ⊆ H) {p : ℂ}
    (hp : p ∈ closure C) {ρ : ℝ} (hρ : 0 < ρ) (hsub : C ∩ ball p ρ ⊆ C ∩ ψ ⁻¹' (H \ K)) : ψ p ∉ closure K := by
  have hbij := hψ.2.2.2.1.2
  obtain ⟨r, hr, hball⟩ := jordanInf_mem_ball_of_mem_ball hψ hp hρ
  intro hcl
  obtain ⟨u, huK, hud⟩ := Metric.mem_closure_iff.1 hcl r hr
  have huH : u ∈ H := hKH huK
  have hzC : Function.invFunOn ψ C u ∈ C := Function.invFunOn_mem (hbij.surjOn huH)
  have hzu : ψ (Function.invFunOn ψ C u) = u := Function.invFunOn_eq (hbij.surjOn huH)
  have hzb : Function.invFunOn ψ C u ∈ ball p ρ :=
    hball _ (subset_closure hzC) (by rw [hzu, mem_ball, dist_comm]; exact hud)
  exact (hsub ⟨hzC, hzb⟩).2.2 (by rw [hzu]; exact huK)

/-- Local containment at a non-corner point (pocket opening at the flow seed). -/
theorem inter_ball_subset_of_noncornerInf (hψ : Sec6.IsJordanCoordInf C y₀ ψ) {U : Set ℂ} (hUo : IsOpen U)
    (hUC : U ⊆ C) {p : ℂ} (hpU : p ∈ closure U) (hpC : p ∈ closure C) (hpM : p ∉ closure (frontier U ∩ C)) :
    ∃ ε > 0, C ∩ ball p ε ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := exists_halfDisc_subset_imageInf hψ hUo hUC isClosed_closure subset_closure hpU hpC hpM
  obtain ⟨ε, hε, hεψ⟩ := Metric.continuousWithinAt_iff.1 (hψ.1 p hpC) r hr
  refine ⟨ε, hε, fun w hw => ?_⟩
  have hψw : ψ w ∈ H ∩ ball (ψ p) r :=
    ⟨hψ.2.2.2.1.2.mapsTo hw.1, hεψ (subset_closure hw.1) (mem_ball.1 hw.2)⟩
  obtain ⟨u, huU, hu⟩ := hrU hψw
  rwa [← hψ.2.2.2.1.2.injOn (hUC huU) hw.1 hu]

/-- **Alive for `C` iff alive for `U` near the landing**, from the four one-chart facts at `p` (any shapes). -/
theorem alive_iff_of {C U : Set ℂ} {ψ ψ' : ℂ → ℂ} {K K' : Set ℂ} (hUC : U ⊆ C)
    (hIncl : U ∩ ψ' ⁻¹' (H \ K') ⊆ C ∩ ψ ⁻¹' (H \ K))
    {pF : ℂ} {ε : ℝ} (hΛa : C ∩ ball pF ε ⊆ U) (hΛ : C ∩ ψ ⁻¹' (H \ K) ∩ ball pF ε ⊆ U ∩ ψ' ⁻¹' (H \ K'))
    {p : ℂ} (hp : p ∈ ball pF (ε / 2))
    (hT1C : ψ p ∉ closure K → ∃ ρ > 0, C ∩ ball p ρ ⊆ C ∩ ψ ⁻¹' (H \ K))
    (hT2C : ∀ ρ > 0, C ∩ ball p ρ ⊆ C ∩ ψ ⁻¹' (H \ K) → ψ p ∉ closure K)
    (hT1U : ψ' p ∉ closure K' → ∃ ρ > 0, U ∩ ball p ρ ⊆ U ∩ ψ' ⁻¹' (H \ K'))
    (hT2U : ∀ ρ > 0, U ∩ ball p ρ ⊆ U ∩ ψ' ⁻¹' (H \ K') → ψ' p ∉ closure K') :
    ψ p ∉ closure K ↔ ψ' p ∉ closure K' := by
  have hε : 0 < ε := by
    have := mem_ball.1 hp
    linarith [dist_nonneg (x := p) (y := pF)]
  have hpball : ∀ ρ : ℝ, ∀ z ∈ ball p (min ρ (ε / 2)), z ∈ ball pF ε ∧ z ∈ ball p ρ := fun ρ z hz => by
    have h1 := mem_ball.1 hz
    have h2 := mem_ball.1 hp
    exact ⟨mem_ball.2 (by linarith [dist_triangle z p pF, min_le_right ρ (ε / 2)]),
      mem_ball.2 (lt_of_lt_of_le h1 (min_le_left _ _))⟩
  constructor
  · intro halive
    obtain ⟨ρ, hρ, hρsub⟩ := hT1C halive
    refine hT2U _ (lt_min hρ (half_pos hε)) fun z hz => ?_
    obtain ⟨hzF, hzp⟩ := hpball ρ z hz.2
    exact hΛ ⟨hρsub ⟨hUC hz.1, hzp⟩, hzF⟩
  · intro halive
    obtain ⟨ρ, hρ, hρsub⟩ := hT1U halive
    refine hT2C _ (lt_min hρ (half_pos hε)) fun z hz => ?_
    obtain ⟨hzF, hzp⟩ := hpball ρ z hz.2
    exact hIncl (hρsub ⟨hΛa ⟨hz.1, hzF⟩, hzp⟩)

end InteractingSLE.Sec7.R6Fc
