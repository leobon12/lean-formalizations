import QuantumZipper.Proofs.Zipper.FieldLawler2Circ
import QuantumZipper.Proofs.Zipper.FieldLawler2Flux24Int

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM round 3: Field–Lawler Lemma 3.3 with (2.4), flux form at `C_R`

**Source.** Field–Lawler, EJP 20 (2015), Lemma 3.3 (p. 8, proof p. 11: integrate (4.1) over
`C_R`) with (2.4) (p. 6), as used in the proof of Prop. 3.4 (p. 9):
`Σ_η ℰ_D(C_R, η) ≤ 2 ℰ_D(C_R, C_ε) ≤ c ε/R`.

`fl3_lemma33`: for a finite family of disjoint arcs of `C_ε` inside `D ⊆ ℍ ∩ B(0,R)`, with
harmonic measures `h k` of the arcs, the total inward flux through `C_R` is
`Σ_k fl2FluxR R (h k) ≤ ofReal (128 π ε / R) · ofReal π`. Pointwise (4.1) is `fl2C42Circ`; the
explicit majorant is `fl2_outer_majorant`; one exceptional angle `θ₀` (the tip) is allowed.
Own elementary assembly.
-/

noncomputable section

open MeasureTheory Filter Set Complex Metric
open scoped Topology Real ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- Pointwise bound for the radial derivatives at one angle. -/
theorem fl3_sum_rDer_le {n : ℕ} {R θ K : ℝ} (h : Fin n → ℂ → ℝ) (M : ℂ → ℝ)
    (hM : Tendsto (fun s : ℝ => M (fl2Pt R θ s) / s) (𝓝[>] 0) (𝓝 K))
    (h0 : ∀ k, ∀ᶠ s : ℝ in 𝓝[>] 0, 0 ≤ h k (fl2Pt R θ s))
    (hle : ∀ᶠ s : ℝ in 𝓝[>] 0, ∑ k, h k (fl2Pt R θ s) ≤ M (fl2Pt R θ s)) :
    ∑ k, fl2rDer R (h k) θ ≤ K ∧ ∀ k, 0 ≤ fl2rDer R (h k) θ := by
  classical
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  -- the indices with a limit
  set S : Finset (Fin n) := Finset.univ.filter
    (fun k => ∃ L, Tendsto (fun s : ℝ => h k (fl2Pt R θ s) / s) (𝓝[>] 0) (𝓝 L)) with hS
  have hL : ∀ k ∈ S, ∃ L, Tendsto (fun s : ℝ => h k (fl2Pt R θ s) / s) (𝓝[>] 0) (𝓝 L) :=
    fun k hk => (Finset.mem_filter.1 hk).2
  choose! L hLt using hL
  have hval : ∀ k, fl2rDer R (h k) θ = if k ∈ S then L k else 0 := by
    intro k
    split_ifs with hk
    · exact fl2_rDer_eq (hLt k hk)
    · unfold fl2rDer
      rw [if_neg]
      intro hex
      exact hk (Finset.mem_filter.2 ⟨Finset.mem_univ _, hex⟩)
  have hL0 : ∀ k ∈ S, 0 ≤ L k := by
    intro k hk
    refine ge_of_tendsto (hLt k hk) ?_
    filter_upwards [h0 k, hpos] with s hs hs'
    exact div_nonneg hs hs'.le
  refine ⟨?_, fun k => ?_⟩
  · have hsum : ∑ k, fl2rDer R (h k) θ = ∑ k ∈ S, L k := by
      rw [Finset.sum_congr rfl fun k _ => hval k, Finset.sum_ite_mem, Finset.univ_inter]
    rw [hsum]
    have ht : Tendsto (fun s : ℝ => (∑ k ∈ S, h k (fl2Pt R θ s)) / s) (𝓝[>] 0)
        (𝓝 (∑ k ∈ S, L k)) := by
      refine (tendsto_finsetSum S hLt).congr fun s => ?_
      rw [Finset.sum_div]
    refine le_of_tendsto_of_tendsto ht hM ?_
    have hall : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ k, 0 ≤ h k (fl2Pt R θ s) := eventually_all.2 h0
    filter_upwards [hle, hall, hpos] with s hs hs0 hs'
    refine div_le_div_of_nonneg_right ?_ hs'.le
    calc ∑ k ∈ S, h k (fl2Pt R θ s) ≤ ∑ k, h k (fl2Pt R θ s) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => hs0 k
      _ ≤ M (fl2Pt R θ s) := hs
  · rw [hval k]
    split_ifs with hk
    · exact hL0 k hk
    · exact le_rfl

/-- **Field–Lawler Lemma 3.3 with (2.4)** (flux form at `C_R`). -/
theorem fl3_lemma33 {ε R θ₀ : ℝ} (hε : 0 < ε) (hR : 4 * ε ≤ R) {n : ℕ} {D : Set ℂ}
    {α β : Fin n → ℝ} (hD : IsOpen D) (hDsub : D ⊆ {z | 0 < z.im ∧ ‖z‖ < R})
    (hpD : -(ε : ℂ) ∉ D)
    (hαβ : ∀ k, -π < α k ∧ α k < β k ∧ β k < π)
    (hsub : ∀ k, flCircArc ε (α k) (β k) ⊆ D)
    (hK : ∀ k, ∃ K : Set ℂ, IsConnected K ∧ Disjoint K D ∧ -(ε : ℂ) ∉ K ∧
      (ε : ℂ) * exp (α k * I) ∈ K ∧ (ε : ℂ) * exp (β k * I) ∈ K)
    (hdisj : Pairwise fun i j => Disjoint (flCircArc ε (α i) (β i)) (flCircArc ε (α j) (β j)))
    {h : Fin n → ℂ → ℝ}
    (hh : ∀ k, IsHarmMeas (D \ flCircArc ε (α k) (β k)) (flCircArc ε (α k) (β k)) (h k))
    {w : ℂ → ℝ}
    (hw : IsHarmMeas (D \ ⋃ k, flCircArc ε (α k) (β k)) (⋃ k, flCircArc ε (α k) (β k)) w)
    {u : Fin n → ℂ → ℝ}
    (hu : ∀ k, IsHarmMeas (D \ ⋃ (i) (_ : i ≠ k), flCircArc ε (α i) (β i))
      (⋃ (i) (_ : i ≠ k), flCircArc ε (α i) (β i)) (u k))
    (hin : ∀ θ ∈ Ioo 0 π, θ ≠ θ₀ → ∀ᶠ s : ℝ in 𝓝[>] 0, fl2Pt R θ s ∈ D) :
    ∑ k, fl2FluxR R (h k) ≤ ENNReal.ofReal (128 * π * ε / R) * ENNReal.ofReal π := by
  have hRpos : 0 < R := by linarith
  have hDb : Bornology.IsBounded D :=
    (Metric.isBounded_ball (x := (0 : ℂ)) (r := R)).subset fun z hz => by
      simpa using (hDsub hz).2
  set A : Set ℂ := ⋃ k, flCircArc ε (α k) (β k) with hA
  have hAsph : A ⊆ sphere (0 : ℂ) ε := by
    intro z hz
    obtain ⟨k, hk⟩ := mem_iUnion.1 hz
    obtain ⟨θ, -, rfl⟩ := hk
    simp [Complex.norm_exp_ofReal_mul_I, abs_of_pos hε]
  have hC := fl2C42Circ hε hD hDb hpD hαβ hsub hK hdisj hh hw hu
  -- the region for the majorant
  set U : Set ℂ := D ∩ {z | ε < ‖z‖} with hU
  have hUo : IsOpen U := hD.inter (isOpen_lt continuous_const continuous_norm)
  have hUA : U ⊆ D \ A := fun z hz => ⟨hz.1, fun hzA => by
    have h1 := hAsph hzA
    rw [mem_sphere_zero_iff_norm] at h1
    have h2 : ε < ‖z‖ := hz.2
    linarith⟩
  have hUsub : U ⊆ {z | 0 < z.im ∧ ε < ‖z‖ ∧ ‖z‖ < R} := fun z hz =>
    ⟨(hDsub hz.1).1, hz.2, (hDsub hz.1).2⟩
  have hwU : InnerProductSpace.HarmonicOnNhd w U := fun z hz => hw.harm z (hUA hz)
  have h01 : ∀ z ∈ U, 0 ≤ w z ∧ w z ≤ 1 := fun z hz => hw.mem01 z (hUA hz)
  have hclA : closure A ⊆ sphere (0 : ℂ) ε := closure_minimal hAsph isClosed_sphere
  have hfr : ∀ x₀ ∈ frontier U, ε < ‖x₀‖ → ∀ δ > 0, ∃ ρ > 0, ∀ y ∈ U, dist y x₀ < ρ →
      w y ≤ δ := by
    intro x₀ hx₀ hn δ hδ
    have hx₀D : x₀ ∈ frontier D := by
      rcases (frontier_inter_subset D {z : ℂ | ε < ‖z‖}) hx₀ with h1 | h1
      · exact h1.1
      · exfalso
        have := frontier_lt_subset_eq continuous_const continuous_norm h1.2
        exact (ne_of_lt hn) this
    have hncl : x₀ ∉ closure A := fun h => by
      have := hclA h
      rw [mem_sphere_zero_iff_norm] at this
      exact (ne_of_lt hn) this.symm
    have hfr' : x₀ ∈ frontier (D \ A) := by
      refine ⟨?_, fun hint => ?_⟩
      · have h1 : x₀ ∈ (closure A)ᶜ ∩ closure D := ⟨hncl, hx₀D.1⟩
        have h2 := isClosed_closure.isOpen_compl.inter_closure h1
        refine closure_mono ?_ h2
        intro z hz
        exact ⟨hz.2, fun hzA => hz.1 (subset_closure hzA)⟩
      · have h3 := interior_subset hint
        have h4 : x₀ ∈ D ∩ frontier D := ⟨h3.1, hx₀D⟩
        rw [hD.inter_frontier_eq] at h4
        exact h4
    have ht := hw.zero x₀ hfr' hncl
    obtain ⟨ρ, hρ, hρ'⟩ := Metric.tendsto_nhdsWithin_nhds.1 ht δ hδ
    refine ⟨ρ, hρ, fun y hy hd => ?_⟩
    have := hρ' (hUA hy) hd
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le
  have hmaj := fl2_outer_majorant ε R U w hε hR hUo hUsub hwU h01 hfr
  set M : ℂ → ℝ := fun z => 2 * (32 * π * ε * z.im * (1 / ‖z‖ ^ 2 - 1 / R ^ 2)) with hM
  -- pointwise bound at each good angle
  have hpt : ∀ θ ∈ Ioo 0 π, θ ≠ θ₀ →
      ∑ k, fl2rDer R (h k) θ ≤ 2 * (32 * π * ε * Real.sin θ * (2 * R - 0) / ((R - 0) * R ^ 2))
        ∧ ∀ k, 0 ≤ fl2rDer R (h k) θ := by
    intro θ hθ hne
    have hMt : Tendsto (fun s : ℝ => M (fl2Pt R θ s) / s) (𝓝[>] 0)
        (𝓝 (2 * (32 * π * ε * Real.sin θ * (2 * R - 0) / ((R - 0) * R ^ 2)))) := by
      have := (fl2_maj_rDer_tendsto (ε := ε) (θ := θ) hRpos).const_mul 2
      refine this.congr fun s => ?_
      simp only [hM]
      ring
    have hgood : ∀ᶠ s : ℝ in 𝓝[>] 0, fl2Pt R θ s ∈ U ∧ R / 2 ≤ ‖fl2Pt R θ s‖ := by
      filter_upwards [hin θ hθ hne, Ioo_mem_nhdsGT (show (0 : ℝ) < R / 2 by linarith)]
        with s hs hs'
      have hn : ‖fl2Pt R θ s‖ = R - s := fl2Pt_norm (by linarith [hs'.2])
      refine ⟨⟨hs, ?_⟩, ?_⟩
      · show ε < ‖fl2Pt R θ s‖
        rw [hn]; linarith [hs'.2]
      · rw [hn]; linarith [hs'.2]
    refine fl3_sum_rDer_le h M hMt (fun k => ?_) ?_
    · filter_upwards [hgood] with s hs
      exact (hh k).mem01 _ ⟨hs.1.1, fun hk => (hUA hs.1).2 (mem_iUnion.2 ⟨k, hk⟩)⟩ |>.1
    · filter_upwards [hgood] with s hs
      have h1 := hC _ (hUA hs.1)
      have h2 := hmaj _ hs.1 hs.2
      simp only [hM]
      linarith
  -- integrate
  have hae : ∀ᵐ θ ∂(volume.restrict (Ioo (0 : ℝ) π)),
      ENNReal.ofReal (∑ k, fl2rDer R (h k) θ * R) ≤ ENNReal.ofReal (128 * π * ε / R) := by
    have hne : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ θ₀ := by
      rw [ae_iff]; simp
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hne] with θ hne hθ
    obtain ⟨h1, -⟩ := hpt θ hθ hne
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Finset.sum_mul]
    have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2.le
    have hv : 2 * (32 * π * ε * Real.sin θ * (2 * R - 0) / ((R - 0) * R ^ 2)) * R =
        128 * π * ε * Real.sin θ / R := by
      rw [sub_zero, sub_zero]; field_simp; ring
    calc (∑ k, fl2rDer R (h k) θ) * R
        ≤ 2 * (32 * π * ε * Real.sin θ * (2 * R - 0) / ((R - 0) * R ^ 2)) * R :=
          mul_le_mul_of_nonneg_right h1 hRpos.le
      _ = 128 * π * ε * Real.sin θ / R := hv
      _ ≤ 128 * π * ε / R := by
          refine div_le_div_of_nonneg_right ?_ hRpos.le
          have hp : 0 ≤ 128 * π * ε := by positivity
          calc 128 * π * ε * Real.sin θ ≤ 128 * π * ε * 1 := mul_le_mul_of_nonneg_left hs1 hp
            _ = 128 * π * ε := mul_one _
  have hnn : ∀ θ ∈ Ioo 0 π, θ ≠ θ₀ → ∀ k, 0 ≤ fl2rDer R (h k) θ * R :=
    fun θ hθ hne k => mul_nonneg ((hpt θ hθ hne).2 k) hRpos.le
  unfold fl2FluxR
  refine (fl2_finset_lintegral_le _ Finset.univ _).trans ?_
  calc ∫⁻ θ in Ioo 0 π, ∑ k, ENNReal.ofReal (fl2rDer R (h k) θ * R)
      ≤ ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (128 * π * ε / R) := by
        refine lintegral_mono_ae ?_
        have hne : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ θ₀ := by
          rw [ae_iff]; simp
        filter_upwards [hae, (ae_restrict_iff' measurableSet_Ioo).2
          (Eventually.of_forall fun θ (hθ : θ ∈ Ioo 0 π) => hθ), ae_restrict_of_ae hne]
          with θ h1 hθ hne'
        rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => hnn θ hθ hne' k, ← Finset.sum_mul]
        rw [← Finset.sum_mul] at h1
        exact h1
    _ = ENNReal.ofReal (128 * π * ε / R) * ENNReal.ofReal π := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero]

end FieldLawler
end QuantumZipper
