import QuantumZipper.Proofs.Complex.KernelTheorem

/-!
# Convergence of the maps from convergence of their inverses (EXT-CA KT2, helper)

`tendstoLocallyUniformlyOn_of_invFunOn`: let `Φ n : Ω n → V` and `Φ∞ : Ω∞ → V` be bijections
onto a fixed open set `V`, with inverses `ψ n`, `ψ∞` holomorphic on `V` and `ψ∞` injective. If
`ψ n → ψ∞` locally uniformly on `V`, then `Φ n → Φ∞` uniformly on every compact `K ⊆ Ω∞` (and
`K ⊆ Ω n` is not needed: `Φ n` is evaluated at points `ψ n v`).

This is the "inverse functions converge" half of the kernel theorem (Pommerenke, *Univalent
Functions* (1975), proof of Thm 1.8 (a), p. 30, which shows `f_n^{-1} → f^{-1}` near each point
by Hurwitz's theorem). We use Hurwitz's theorem (`hurwitz_eventually_exists_eq`, A5) with
moving targets and a compactness argument; this packaging is our own elementary argument.
-/

noncomputable section

open Set Metric Filter Topology Complex Function

namespace QuantumZipper.CA.Kernel

/-- Locally uniform convergence passes to subsequences. -/
theorem tendstoLocallyUniformlyOn_subseq_qz {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {s : Set ℂ}
    (h : TendstoLocallyUniformlyOn F f atTop s) {N : ℕ → ℕ} (hN : StrictMono N) :
    TendstoLocallyUniformlyOn (fun j => F (N j)) f atTop s := by
  rw [Metric.tendstoLocallyUniformlyOn_iff] at h ⊢
  intro ε hε x hx
  obtain ⟨t, ht, hev⟩ := h ε hε x hx
  exact ⟨t, ht, hN.tendsto_atTop.eventually hev⟩

/-- An injective map is not locally constant at an interior point. -/
theorem not_eventually_eq_of_injOn_open {ψ : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hψi : InjOn ψ V) {v : ℂ} (hv : v ∈ V) : ¬ ∀ᶠ y in 𝓝 v, ψ y = ψ v := by
  intro h
  obtain ⟨δ, hδ, hδV⟩ := Metric.eventually_nhds_iff.1 (h.and (hV.mem_nhds hv))
  have hy : dist (v + (δ / 2 : ℝ)) v < δ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hδ)]
    linarith
  obtain ⟨h1, h2⟩ := hδV hy
  have := hψi h2 hv h1
  have h3 : ((δ / 2 : ℝ) : ℂ) = 0 := by linear_combination this
  have h4 : δ / 2 = 0 := by exact_mod_cast h3
  linarith

/-- **Convergence of univalent maps from convergence of their inverses.** -/
theorem tendstoUniformlyOn_of_invFunOn {V Ωi K : Set ℂ} {Ω : ℕ → Set ℂ} {Φ : ℕ → ℂ → ℂ}
    {Φi : ℂ → ℂ} (hV : IsOpen V) (hΦb : ∀ n, BijOn (Φ n) (Ω n) V) (hΦib : BijOn Φi Ωi V)
    (hΦic : ∀ z ∈ Ωi, ContinuousAt Φi z)
    (hψd : ∀ n, DifferentiableOn ℂ (invFunOn (Φ n) (Ω n)) V)
    (hψi : InjOn (invFunOn Φi Ωi) V)
    (hlim : TendstoLocallyUniformlyOn (fun n => invFunOn (Φ n) (Ω n)) (invFunOn Φi Ωi) atTop V)
    (hKc : IsCompact K) (hKΩ : K ⊆ Ωi) :
    TendstoUniformlyOn Φ Φi atTop K := by
  set ψ := fun n => invFunOn (Φ n) (Ω n) with hψ
  set ψi := invFunOn Φi Ωi with hψi'
  have hinv : ∀ n, InvOn (ψ n) (Φ n) (Ω n) V := fun n => (hΦb n).invOn_invFunOn
  have hinvi : InvOn ψi Φi Ωi V := hΦib.invOn_invFunOn
  by_contra hnot
  rw [Metric.tendstoUniformlyOn_iff] at hnot
  push Not at hnot
  obtain ⟨ε, hε, hfreq⟩ := hnot
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop hfreq
  choose x hxK hxε using hP
  obtain ⟨z, hzK, σ, hσ, hxz⟩ := hKc.tendsto_subseq hxK
  have hN : StrictMono (φ ∘ σ) := hφ.comp hσ
  -- the moving-target sequence `ψ (N j) - (x (σ j) - z) → ψi`
  have hF := tendstoLocallyUniformlyOn_sub_const (tendstoLocallyUniformlyOn_subseq_qz hlim hN)
    (u := fun j => x (σ j) - z) (w := 0) (by simpa using (hxz.sub_const z))
  have hF' : TendstoLocallyUniformlyOn (fun j v => ψ ((φ ∘ σ) j) v - (x (σ j) - z)) ψi atTop V :=
    hF.congr_right fun v _ => by simp [hψi']
  have hzΩ : z ∈ Ωi := hKΩ hzK
  have hvV : Φi z ∈ V := hΦib.mapsTo hzΩ
  have hψz : ψi (Φi z) = z := hinvi.1 hzΩ
  have hnw : ¬ ∀ᶠ y in 𝓝 (Φi z), ψi y = z := by
    have := not_eventually_eq_of_injOn_open hV hψi hvV
    rwa [hψz] at this
  have hHur := hurwitz_eventually_exists_eq hV
    (fun j => ((hψd ((φ ∘ σ) j)).sub_const _)) hF' hvV hψz hnw (half_pos hε)
  have hcont : Tendsto (fun j => Φi (x (σ j))) atTop (𝓝 (Φi z)) := (hΦic z hzΩ).tendsto.comp hxz
  obtain ⟨j, hj1, hj2⟩ := (hHur.and ((Metric.tendsto_nhds.1 hcont) (ε / 2) (half_pos hε))).exists
  obtain ⟨v, hvV', hvb, hveq⟩ := hj1
  have hψv : ψ ((φ ∘ σ) j) v = x (σ j) := by linear_combination hveq
  have hΦv : Φ (φ (σ j)) (x (σ j)) = v := by
    rw [← hψv]; exact (hinv _).2 hvV'
  have := hxε (σ j)
  rw [hΦv] at this
  rw [mem_ball] at hvb
  have := dist_triangle (Φi (x (σ j))) (Φi z) v
  rw [dist_comm v] at hvb
  linarith

end QuantumZipper.CA.Kernel
