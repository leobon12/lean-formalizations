import QuantumZipper.Proofs.Thm18.G1Reduce
import QuantumZipper.Proofs.Thm18.G1RegLogDeriv
import QuantumZipper.Proofs.Complex.KernelChordRight
import QuantumZipper.Proofs.Complex.CaraBdry
import QuantumZipper.Proofs.Loewner.CoreArc3b
import QuantumZipper.Proofs.RS.GenerationBasic
import QuantumZipper.Proofs.RS.KoebeLoewnerTime

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-HOLDER, step 1 (D3): factoring the side map through a forward Loewner map

For a simple chord `η` whose hulls are the initial arcs of the Loewner chain driven by `W`, a side
component `D = sideDom η left`, its inverse normalized uniformizer `ψ = φ⁻¹ : ℍ → D` with a
continuous extension `ψe` to `Hbar`, and `ρ > 0`, we find an integer time `n` such that
`F = f_n ∘ ψe` (`f_n = fwdMap W n`) is a bounded-near-`[-ρ,ρ]`, injective holomorphic self-map of
`ℍ` with `ψ = f̂_n ∘ F` and `Im F(z) → 0` as `z → t ∈ (-ρ, ρ)`
(**`exists_fwd_factor`**, deterministic).

Sources: the Loewner facts (`f_n` is a conformal map of `ℍ \ K_n` onto `ℍ`, inverted by `f̂_n`,
and `K_n = η(0,n]`) are Rohde–Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), §2
(Prop. 2.1), available in the repo as `FwdHolo.*`, `RS.fwdMapInv_*`. The frontier fact
`∂D ∩ ℍ ⊆ η` is `CA.Uniformizer.mem_leftComponent_of_mem_closure`. The localization argument
itself is an **own argument** (handoff/G1-HOLDER.md step 1; no written proof of the whole-chord
statement was found): `ψe([-ρ,ρ])` is bounded, `‖η s‖ → ∞`, so for large `n` the points
`ψe(t)` (`t` real) lie in `ℝ ∪ η(0,n]`, i.e. outside `ℍ \ K_n`; then the image under `f̂_n` of the
compact set `{ε ≤ Im w, ‖w‖ ≤ M}` stays away from `ψe(t)`, which forces `Im F → 0`.
-/

open Set Filter Metric Function
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

/-- The side domain `D = sideDom η left` of a simple chord is open, contained in `ℍ \ η[0,∞)`, and
relatively closed there. -/
theorem sideDom_topo_facts {η : ℝ → ℂ} (hη : IsSimpleChord η) (left : Bool) :
    IsOpen (sideDom η left) ∧ sideDom η left ⊆ H \ η '' Ici 0 ∧
      ∀ w ∈ closure (sideDom η left), w ∈ H → w ∉ η '' Ici 0 → w ∈ sideDom η left := by
  cases left
  · rw [show sideDom η false = rightComponent η from rfl]
    refine ⟨CA.Kernel.isOpen_rightComponent_qz hη, fun z hz => hz.1, fun w hw hwH hwK => ?_⟩
    have hpre : rightComponent η =
        CA.Uniformizer.refl ⁻¹' leftComponent (CA.Uniformizer.refl ∘ η) := by
      ext z; exact CA.Uniformizer.mem_rightComponent_iff
    rw [hpre] at hw ⊢
    have hw' := CA.Uniformizer.continuous_refl.closure_preimage_subset _ hw
    exact CA.Uniformizer.mem_leftComponent_of_mem_closure
      (CA.Uniformizer.isSimpleChord_refl_comp hη) hw'
      (CA.Uniformizer.refl_mem_slit_iff.2 ⟨hwH, hwK⟩)
  · rw [show sideDom η true = leftComponent η from rfl]
    exact ⟨CA.Uniformizer.isOpen_leftComponent hη, fun z hz => hz.1, fun w hw hwH hwK =>
      CA.Uniformizer.mem_leftComponent_of_mem_closure hη hw ⟨hwH, hwK⟩⟩

theorem ofReal_mem_Hbar_loew (t : ℝ) : (t : ℂ) ∈ Hbar := by
  show (0 : ℝ) ≤ (t : ℂ).im
  simp

/-- **D3 (Loewner factorization of a side map).** See the module docstring. -/
theorem exists_fwd_factor {W : ℝ → ℝ} {η : ℝ → ℂ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hη : IsSimpleChord η) (hK : ∀ t : ℝ, 0 ≤ t → fwdHull W t = η '' Set.Ioc 0 t)
    {left : Bool} {φ : ℂ → ℂ} (hφ : IsNormalizedUniformizer (sideDom η left) φ)
    {ψe : ℂ → ℂ} (hc : ContinuousOn ψe Hbar)
    (heq : Set.EqOn (Function.invFunOn φ (sideDom η left)) ψe H)
    (ρ : ℝ) :
    ∃ n : ℕ, Set.MapsTo (fun z => fwdMap W n (ψe z)) H H ∧
      Set.InjOn (fun z => fwdMap W n (ψe z)) H ∧
      DifferentiableOn ℂ (fun z => fwdMap W n (ψe z)) H ∧
      (∀ z ∈ H, fwdMapInv W n (fwdMap W n (ψe z)) = ψe z) ∧
      (∃ M : ℝ, ∀ z ∈ H, ‖z‖ < ρ → ‖fwdMap W n (ψe z)‖ ≤ M) ∧
      ∀ t : ℝ, |t| < ρ → Filter.Tendsto (fun z => (fwdMap W n (ψe z)).im)
        (nhdsWithin (t : ℂ) H) (nhds 0) := by
  classical
  obtain ⟨hDo, hDsub, hDcl⟩ := sideDom_topo_facts hη left
  obtain ⟨hψd, -, -, hψmaps⟩ := G1.invFunOn_props hDo hφ
  have hψinj := G1.injOn_invFunOn_of_uniformizer hφ
  set D := sideDom η left with hDdef
  set ψ := Function.invFunOn φ D with hψdef
  have hφψ : ∀ z ∈ H, φ (ψ z) = z := fun z hz => hφ.1.surjOn.rightInvOn_invFunOn hz
  -- the bound `L` of `ψe` on `Hbar ∩ closedBall 0 ρ`
  have hKc : IsCompact (Hbar ∩ closedBall (0 : ℂ) ρ) :=
    (isCompact_closedBall 0 ρ).inter_left isClosed_Hbar
  obtain ⟨L, hL⟩ := hKc.exists_bound_of_continuousOn (hc.mono inter_subset_left)
  -- the time `n`
  obtain ⟨N, hN⟩ := eventually_atTop.1 (tendsto_atTop.1 hη.2.2.2.2 (L + 1))
  obtain ⟨n, hnN, hn1⟩ : ∃ n : ℕ, N ≤ (n : ℝ) ∧ (1 : ℝ) ≤ n :=
    ⟨⌈max N 1⌉₊, (le_max_left _ _).trans (Nat.le_ceil _),
      (le_max_right _ _).trans (Nat.le_ceil _)⟩
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hKn : fwdHull W n = η '' Ioc 0 n := hK n hn0
  have hKsub : fwdHull W n ⊆ η '' Ici 0 := by
    rw [hKn]; exact image_mono fun x hx => mem_Ici.2 hx.1.le
  have hψK : ∀ z ∈ H, ψe z ∈ H \ fwdHull W n := fun z hz => by
    rw [← heq hz]
    have h := hDsub (hψmaps hz)
    exact ⟨h.1, fun h' => h.2 (hKsub h')⟩
  have hψed : DifferentiableOn ℂ ψe H := hψd.congr (fun z hz => (heq hz).symm)
  have hclH : ∀ t : ℝ, (t : ℂ) ∈ closure H := fun t => by
    rw [CA.Car.closure_H_eq_Hbar]; exact ofReal_mem_Hbar_loew t
  have hlim : ∀ t : ℝ, Tendsto ψe (𝓝[H] (t : ℂ)) (𝓝 (ψe t)) := fun t =>
    ((hc (t : ℂ) (ofReal_mem_Hbar_loew t)).mono H_subset_Hbar).tendsto
  -- key boundary fact: `ψe t ∉ ℍ \ K_n` for real `|t| ≤ ρ`
  have hkey : ∀ t : ℝ, |t| ≤ ρ → ψe t ∉ H \ fwdHull W n := by
    intro t ht hp
    have hNe : (𝓝[H] (t : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hclH t)
    have hpcl : ψe t ∈ closure D := by
      have h1 : ψe t ∈ closure (ψe '' H) :=
        mem_closure_of_tendsto (hlim t)
          (eventually_mem_nhdsWithin.mono fun z hz => mem_image_of_mem _ hz)
      refine closure_mono ?_ h1
      rintro _ ⟨z, hz, rfl⟩
      rw [← heq hz]
      exact hψmaps hz
    have hpnot : ψe t ∉ η '' Ici 0 := by
      rintro ⟨s, hs, hse⟩
      rcases (mem_Ici.1 hs).eq_or_lt with h0 | hpos
      · have h := hp.1
        rw [← hse, ← h0, hη.1] at h
        exact absurd h (by simp [H])
      · by_cases hsn : s ≤ n
        · exact hp.2 (by rw [hKn]; exact ⟨s, ⟨hpos, hsn⟩, hse⟩)
        · have h1 := hN s (hnN.trans (not_le.1 hsn).le)
          have h2 := hL (t : ℂ) ⟨ofReal_mem_Hbar_loew t, by
            simpa [mem_closedBall, dist_zero_right] using ht⟩
          rw [hse] at h1
          linarith
    have hpD : ψe t ∈ D := hDcl _ hpcl hp.1 hpnot
    have hφc : ContinuousAt φ (ψe t) :=
      (hφ.2.1.differentiableAt (hDo.mem_nhds hpD)).continuousAt
    have hψlim : Tendsto ψ (𝓝[H] (t : ℂ)) (𝓝 (ψe t)) :=
      (hlim t).congr' (eventually_mem_nhdsWithin.mono fun z hz => (heq hz).symm)
    have h1 : Tendsto (fun z => φ (ψ z)) (𝓝[H] (t : ℂ)) (𝓝 (φ (ψe t))) :=
      hφc.tendsto.comp hψlim
    have h2 : Tendsto (fun z => φ (ψ z)) (𝓝[H] (t : ℂ)) (𝓝 (t : ℂ)) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).congr'
        (eventually_mem_nhdsWithin.mono fun z hz => (hφψ z hz).symm)
    have heqt := tendsto_nhds_unique h1 h2
    have hH := hφ.1.mapsTo hpD
    rw [heqt] at hH
    exact absurd hH (by simp [H])
  -- the bound on `F`
  obtain ⟨Mw, hMw⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := (n : ℝ))).exists_bound_of_continuousOn hW.continuousOn
  set M : ℝ := 24 * Mw + 8 * Real.sqrt n + L with hMdef
  have hbd : ∀ z ∈ H, ‖z‖ < ρ → ‖fwdMap W n (ψe z)‖ ≤ M := by
    intro z hz hzρ
    have h1 := CoreArc.norm_fwdMap_sub_le_uniform hW hW0 (by linarith : (0 : ℝ) < n)
      (fun s hs => by simpa [Real.norm_eq_abs] using hMw s hs) (hψK z hz)
    have h2 := hL z ⟨H_subset_Hbar hz, by
      simpa [mem_closedBall, dist_zero_right] using hzρ.le⟩
    calc ‖fwdMap W n (ψe z)‖ = ‖(fwdMap W n (ψe z) - ψe z) + ψe z‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖fwdMap W n (ψe z) - ψe z‖ + ‖ψe z‖ := norm_add_le _ _
      _ ≤ M := by rw [hMdef]; linarith
  refine ⟨n, fun z hz => FwdHolo.mapsTo_fwdMap hW hn0 (hψK z hz), ?_, ?_,
    fun z hz => RS.fwdMapInv_fwdMap hW hW0 hn0 (hψK z hz), ⟨M, hbd⟩, ?_⟩
  · intro z hz w hw h
    have h' := FwdHolo.injOn_fwdMap hW hn0 (hψK z hz) (hψK w hw) h
    rw [← heq hz, ← heq hw] at h'
    exact hψinj hz hw h'
  · exact (FwdHolo.differentiableOn_fwdMap hW hn0).comp hψed (fun z hz => hψK z hz)
  · intro t ht
    rw [Metric.tendsto_nhds]
    intro ε hε
    set Kε : Set ℂ := {w | ε ≤ w.im} ∩ closedBall 0 M with hKεdef
    have hKεc : IsCompact Kε :=
      (isCompact_closedBall 0 M).inter_left (isClosed_le continuous_const Complex.continuous_im)
    have hKεH : Kε ⊆ H := fun w hw => show 0 < w.im from lt_of_lt_of_le hε hw.1
    have hCc : IsCompact (fwdMapInv W n '' Kε) :=
      hKεc.image_of_continuousOn ((RS.differentiableOn_fwdMapInv hW hW0 hn0).continuousOn.mono hKεH)
    have hpC : ψe t ∉ fwdMapInv W n '' Kε := by
      rintro ⟨w, hw, hwe⟩
      exact hkey t ht.le (hwe ▸ RS.fwdMapInv_mem_compl_fwdHull hW hW0 hn0 (hKεH hw))
    have hev1 : ∀ᶠ z in 𝓝[H] (t : ℂ), ψe z ∉ fwdMapInv W n '' Kε :=
      (hlim t).eventually (hCc.isClosed.isOpen_compl.mem_nhds hpC)
    have hev2 : ∀ᶠ z in 𝓝[H] (t : ℂ), z ∈ H := self_mem_nhdsWithin
    have hev3 : ∀ᶠ z in 𝓝[H] (t : ℂ), ‖z‖ < ρ :=
      nhdsWithin_le_nhds ((isOpen_lt continuous_norm continuous_const).mem_nhds
        (by simpa using ht))
    filter_upwards [hev1, hev2, hev3] with z h1 h2 h3
    have hpos : 0 < (fwdMap W n (ψe z)).im := FwdHolo.mapsTo_fwdMap hW hn0 (hψK z h2)
    have hlt : (fwdMap W n (ψe z)).im < ε := by
      by_contra hge
      exact h1 ⟨_, ⟨not_lt.1 hge, by
        simpa [mem_closedBall, dist_zero_right] using hbd z h2 h3⟩,
        RS.fwdMapInv_fwdMap hW hW0 hn0 (hψK z h2)⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
    exact hlt

end G1RC
end Thm18Asm
end QuantumZipper
