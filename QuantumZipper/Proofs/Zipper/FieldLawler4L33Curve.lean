import QuantumZipper.Proofs.Zipper.FieldLawler4L33

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM round 4: `fl4_lemma33_loewner` for a general curve

The same statement for any continuous simple-chord-like curve `γ` with `H \ γ(0,t]`
preconnected (used for the mirror image of the trace, which handles crosscuts with negative
feet). Same proof. Source: Field–Lawler, EJP 20 (2015), Lemma 3.3 and (2.4).
-/

noncomputable section

open MeasureTheory Filter Set Complex Metric
open scoped Topology Real ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

theorem fl4_lemma33_curve {γ : ℝ → ℂ}
    {t R ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) (hR : 4 * ε ≤ R)
    (htr0 : γ 0 = 0) (hcont : ContinuousOn (γ) (Icc 0 t))
    (hH : ∀ s ∈ Ioc 0 t, γ s ∈ H) (hpc : IsPreconnected (H \ γ '' Ioc 0 t))
    (hγR : ∀ s ∈ Ico 0 t, ‖γ s‖ < R) (hγt : ‖γ t‖ = R)
    {n : ℕ} {α β : Fin n → ℝ} (hαβ : ∀ k, 0 ≤ α k ∧ α k < β k ∧ β k < π)
    (hend : ∀ k, (ε : ℂ) * exp (α k * I) ∈ γ '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ 0 ≤ z.re} ∧
      (ε : ℂ) * exp (β k * I) ∈ γ '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ 0 ≤ z.re})
    (harc : ∀ k, flCircArc ε (α k) (β k) ⊆ H \ γ '' Ioc 0 t)
    (hdisj : Pairwise fun i j => Disjoint (flCircArc ε (α i) (β i)) (flCircArc ε (α j) (β j)))
    {h : Fin n → ℂ → ℝ}
    (hh : ∀ k, IsHarmMeas (((H \ γ '' Ioc 0 t) ∩ ball 0 R) \ flCircArc ε (α k) (β k)) (flCircArc ε (α k) (β k))
      (h k)) :
    ∑ k, fl2FluxR R (h k) ≤ ENNReal.ofReal (128 * π * ε / R) * ENNReal.ofReal π := by
  classical
  have hεR : ε < R := by linarith
  set K : Set ℂ := γ '' Icc 0 t with hKdef
  set D := ((H \ γ '' Ioc 0 t) ∩ ball 0 R) with hD
  have hKc : IsConnected K := (isConnected_Icc ht).image _ hcont
  have hK0 : (0 : ℂ) ∈ K := ⟨0, ⟨le_rfl, ht⟩, htr0⟩
  -- the connected sets
  set Q : Set ℂ := K ∪ {z : ℂ | z.im ≤ 0 ∧ 0 ≤ z.re} with hQ
  have hQc : IsConnected Q := by
    have hq : IsConnected {z : ℂ | z.im ≤ 0 ∧ 0 ≤ z.re} := by
      refine ⟨⟨0, by simp⟩, ?_⟩
      refine (Convex.isPreconnected ?_)
      intro x hx y hy a b ha hb hab
      simp only [mem_setOf_eq, add_im, add_re, smul_im, smul_re, smul_eq_mul] at hx hy ⊢
      constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]
    exact IsConnected.union ⟨0, hK0, show (0 : ℂ) ∈ {z : ℂ | z.im ≤ 0 ∧ 0 ≤ z.re} by simp⟩ hKc hq
  have hQD : Disjoint Q D := by
    rw [Set.disjoint_left]
    rintro z (hz | hz) hzD
    · obtain ⟨s, hs, rfl⟩ := hz
      rcases eq_or_lt_of_le hs.1 with h0 | h0
      · have := hzD.1.1
        rw [← h0, htr0] at this
        exact lt_irrefl _ (show (0 : ℝ) < 0 by simpa [H] using this)
      · exact hzD.1.2 ⟨s, ⟨h0, hs.2⟩, rfl⟩
    · have := hzD.1.1
      exact absurd hz.1 (not_le.2 this)
  have hQε : -(ε : ℂ) ∉ Q := by
    rintro (h1 | h1)
    · obtain ⟨s, hs, hse⟩ := h1
      rcases eq_or_lt_of_le hs.1 with h0 | h0
      · rw [← h0, htr0] at hse
        have := congrArg Complex.re hse
        simp at this; linarith
      · have := hH s ⟨h0, hs.2⟩
        rw [hse] at this
        exact lt_irrefl _ (show (0 : ℝ) < 0 by simpa [H] using this)
    · have := h1.2
      simp at this; linarith
  have hDsub : D ⊆ {z | 0 < z.im ∧ ‖z‖ < R} := fun z hz =>
    ⟨hz.1.1, by simpa using hz.2⟩
  have hHK : H \ γ '' Ioc 0 t = H \ K := by
    ext z
    constructor
    · rintro ⟨hz, hzK⟩
      refine ⟨hz, ?_⟩
      rintro ⟨s, hs, rfl⟩
      rcases eq_or_lt_of_le hs.1 with h0 | h0
      · rw [← h0, htr0] at hz
        exact lt_irrefl _ (show (0 : ℝ) < 0 by simpa [H] using hz)
      · exact hzK ⟨s, ⟨h0, hs.2⟩, rfl⟩
    · rintro ⟨hz, hzK⟩
      exact ⟨hz, fun ⟨s, hs, e⟩ => hzK ⟨s, Ioc_subset_Icc_self hs, e⟩⟩
  have hDo : IsOpen D := by
    have hKc' : IsClosed K := (isCompact_Icc.image_of_continuousOn hcont).isClosed
    show IsOpen ((H \ γ '' Ioc 0 t) ∩ ball 0 R)
    rw [hHK]
    exact ((isOpen_lt continuous_const Complex.continuous_im).sdiff hKc').inter isOpen_ball
  -- the auxiliary harmonic measures
  have harc' : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      flCircArc ε (α i) (β i) ⊆ H \ γ '' Ioc 0 t := fun i _ => harc i
  have hend' : ∀ (I₀ : Finset (Fin n)), ∀ i ∈ I₀,
      (ε : ℂ) * exp (α i * I) ∈ γ '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0} ∧
      (ε : ℂ) * exp (β i * I) ∈ γ '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0} := by
    intro I₀ i _
    rcases hend i with ⟨h1, h2⟩
    exact ⟨h1.elim Or.inl (fun h => Or.inr h.1), h2.elim Or.inl (fun h => Or.inr h.1)⟩
  have hex : ∀ I₀ : Finset (Fin n), ∃ g : ℂ → ℝ,
      IsHarmMeas (D \ ⋃ i ∈ I₀, flCircArc ε (α i) (β i)) (⋃ i ∈ I₀, flCircArc ε (α i) (β i)) g :=
    fun I₀ => flExist_loewner_arcs ht (by linarith) hcont htr0 I₀
      (fun i _ => (hαβ i).2.1.le) (hend' I₀)
      (flFin_components ht hε hεR hcont htr0 hH hγR hγt hpc I₀ (hend' I₀) (fun i _ => harc i))
  obtain ⟨w, hw⟩ := hex Finset.univ
  have hwU : (⋃ i ∈ (Finset.univ : Finset (Fin n)), flCircArc ε (α i) (β i)) =
      ⋃ k, flCircArc ε (α k) (β k) := by simp
  rw [hwU] at hw
  have hu : ∀ k, ∃ u : ℂ → ℝ, IsHarmMeas (D \ ⋃ (i) (_ : i ≠ k), flCircArc ε (α i) (β i))
      (⋃ (i) (_ : i ≠ k), flCircArc ε (α i) (β i)) u := by
    intro k
    obtain ⟨g, hg⟩ := hex (Finset.univ.erase k)
    have e : (⋃ i ∈ Finset.univ.erase k, flCircArc ε (α i) (β i)) =
        ⋃ (i) (_ : i ≠ k), flCircArc ε (α i) (β i) := by
      ext z; simp
    rw [e] at hg
    exact ⟨g, hg⟩
  choose u hu using hu
  -- the tip angle
  set θ₀ : ℝ := arg (γ t) with hθ₀
  have hRpos : 0 < R := by linarith
  have hKcl : IsClosed K := (isCompact_Icc.image_of_continuousOn hcont).isClosed
  have hin : ∀ θ ∈ Ioo 0 π, θ ≠ θ₀ → ∀ᶠ s : ℝ in 𝓝[>] 0, fl2Pt R θ s ∈ D := by
    intro θ hθ hne
    have hq : fl2Pt R θ 0 ∉ K := by
      rintro ⟨u, hu, hue⟩
      have hn : ‖γ u‖ = R := by
        rw [hue, fl2Pt_norm (by linarith)]; ring
      have hut : u = t := by
        by_contra hne'
        have := hγR u ⟨hu.1, lt_of_le_of_ne hu.2 hne'⟩
        linarith
      apply hne
      rw [hθ₀, ← hut, hue, fl2Pt, sub_zero, Complex.arg_real_mul _ hRpos, Complex.exp_mul_I,
        Complex.arg_cos_add_sin_mul_I ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩]
    have hopen : IsOpen Kᶜ := hKcl.isOpen_compl
    have hcont' : ContinuousAt (fun s : ℝ => fl2Pt R θ s) 0 := by
      unfold fl2Pt; fun_prop
    have hev : ∀ᶠ s : ℝ in 𝓝 0, fl2Pt R θ s ∈ Kᶜ := hcont'.eventually_mem (hopen.mem_nhds hq)
    filter_upwards [nhdsWithin_le_nhds hev, Ioo_mem_nhdsGT hRpos] with s hsK hs
    have hsH : fl2Pt R θ s ∈ H := by
      show 0 < (fl2Pt R θ s).im
      rw [fl2Pt_im]
      exact mul_pos (by linarith [hs.2]) (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
    refine ⟨?_, ?_⟩
    · rw [hHK]; exact ⟨hsH, hsK⟩
    · rw [mem_ball_zero_iff, fl2Pt_norm hs.2.le]; linarith [hs.1]
  refine fl3_lemma33 (θ₀ := θ₀) hε hR hDo hDsub (fun h => ?_) (fun k => ?_) (fun k => ?_)
    (fun k => ⟨Q, hQc, hQD, hQε, (hend k).1, (hend k).2⟩) hdisj hh hw hu hin
  · have := (hDsub h).1
    simp at this
  · exact ⟨by linarith [(hαβ k).1, Real.pi_pos], (hαβ k).2.1, (hαβ k).2.2⟩
  · intro z hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    refine ⟨harc k ⟨θ, hθ, rfl⟩, ?_⟩
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hε]
    exact hεR

end FieldLawler
end QuantumZipper
