import QuantumZipper.Proofs.Field.PairAffBox

/-!
# PAIR-AFF: affine-uniform continuum limits of circle-regularized pairings

For a free boundary GFF modulo constants `X` (`IsFreeGFFModConstH`) and `η` with bounded density
supported in a compact subset of `{Im ≥ δ}` (`PairLim.Setup`), put, for `t : ℝ`, `b > 0`,

  `affPair x η s (t, b) = ∫ evalReg x (fc(u, s)) d(η ∘ aff(t,b)⁻¹)(u)`,  `aff(t,b) w = t + b w`,

the circle-regularized pairing of `x` with the affine image of `η`, and let `affLim x η (t, b)`
be its limit as `s → 0⁺` (`limUnder`). Then

* `ae_tendstoLocallyUniformlyOn_affPair`: almost surely, `affPair (X ω) η s → affLim (X ω) η`
  as `s → 0⁺`, **locally uniformly in `(t, b) ∈ ℝ × (0, ∞)`**, and the limit is continuous there;
* `ae_affLim_eq`: for each fixed `(t, b)`, almost surely `affLim (X ω) η (t, b) = X ω (η.map aff)`.

(The raw values `X ω (η.map (aff t b))` are only determined up to a null set for each `(t, b)`, so
the identification cannot hold simultaneously for all `(t, b)` in general; `affLim` is the
continuous version.)

Route: `exists_aff_modification` (`PairAffBox`) on the dilation windows `(1/(n+1), n+1)`, the
Heine–Cantor uniform continuity of the continuous modification on compacts
(`Continuous.tendstoUniformly`), and `tendstoLocallyUniformlyOn_iUnion`.

Source: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
§3.1, Prop. 3.1 (joint continuity of the circle-average process by Kolmogorov–Čentsov);
Revuz–Yor Ch. I Thm. (2.1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Real Topology

namespace QuantumZipper
namespace PairLim

open SmoothConv

variable {M : ℝ≥0} {R δ : ℝ} {η : Measure ℂ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The circle-regularized pairing of `x` with the affine image `η ∘ aff(t,b)⁻¹` at radius `s`. -/
def affPair (x : FieldSample) (η : Measure ℂ) (s : ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ u, evalReg x (foldedCircle u s) ∂(η.map (aff p.1 p.2))

/-- Its limit as `s → 0⁺` (junk value if it does not exist). -/
def affLim (x : FieldSample) (η : Measure ℂ) (p : ℝ × ℝ) : ℝ :=
  limUnder (𝓝[>] 0) fun s => affPair x η s p

/-- Dilation windows. -/
def win (n : ℕ) : Set (ℝ × ℝ) := univ ×ˢ Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)

theorem isOpen_win (n : ℕ) : IsOpen (win n) := isOpen_univ.prod isOpen_Ioo

theorem exists_mem_win {p : ℝ × ℝ} (hp : 0 < p.2) : ∃ n, p ∈ win n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max p.2 p.2⁻¹)
  refine ⟨n, trivial, ?_, by linarith [le_max_left p.2 p.2⁻¹]⟩
  rw [one_div, inv_lt_comm₀ (by positivity) hp]
  linarith [le_max_right p.2 p.2⁻¹]

theorem iUnion_win : ⋃ n, win n = univ ×ˢ Ioi (0 : ℝ) := by
  ext p
  simp only [mem_iUnion]
  constructor
  · rintro ⟨n, -, h, -⟩
    exact ⟨trivial, lt_trans (by positivity) h⟩
  · rintro ⟨-, hp⟩
    exact exists_mem_win hp

/-- **PAIR-AFF (A).** Almost surely, the circle-regularized pairings with the affine images
`η ∘ aff(t,b)⁻¹` converge as `s → 0⁺`, locally uniformly in `(t, b) ∈ ℝ × (0, ∞)`, to a
continuous limit. -/
theorem ae_tendstoLocallyUniformlyOn_affPair [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) (hS : Setup M R δ η) :
    ∀ᵐ ω ∂P, ContinuousOn (affLim (X ω) η) (univ ×ˢ Ioi 0) ∧
      TendstoLocallyUniformlyOn (affPair (X ω) η) (affLim (X ω) η) (𝓝[>] 0)
        (univ ×ˢ Ioi 0) := by
  have H := fun n : ℕ => exists_aff_modification hX hS (b₀ := 1 / ((n : ℝ) + 1))
    (b₁ := (n : ℝ) + 1) (by positivity)
  choose W hWc _ hWeq using H
  filter_upwards [ae_all_iff.2 hWeq] with ω hω
  have hn : ∀ n : ℕ, TendstoLocallyUniformlyOn (affPair (X ω) η)
      (fun p => W n (vec3 (0, p.1, p.2)) ω) (𝓝[>] 0) (win n) ∧
      EqOn (affLim (X ω) η) (fun p => W n (vec3 (0, p.1, p.2)) ω) (win n) := by
    intro n
    set f : ℝ → ℝ × ℝ → ℝ := fun s p => W n (vec3 (s, p.1, p.2)) ω with hf
    have hfc : Continuous (Function.uncurry f) := (hWc n ω).comp continuous_vec3
    have hδ : 0 < min (1 / ((n : ℝ) + 1) * δ) 1 := lt_min (by have := hS.pos; positivity) one_pos
    have hev : ∀ᶠ s in 𝓝[>] 0, EqOn (affPair (X ω) η s) (f s) (win n) := by
      filter_upwards [Ioo_mem_nhdsGT hδ] with s hs p hp
      exact hω n s hs p.1 p.2 hp.2
    have hT : TendstoLocallyUniformlyOn (affPair (X ω) η) (f 0) (𝓝[>] 0) (win n) := by
      refine (tendstoLocallyUniformlyOn_iff_forall_isCompact (isOpen_win n)).2
        fun K hK hKc => ?_
      have : CompactSpace K := isCompact_iff_compactSpace.1 hKc
      have h1 : TendstoUniformly (fun s (k : K) => f s k) (fun k => f 0 k) (𝓝 0) :=
        Continuous.tendstoUniformly (fun s (k : K) => f s k)
          (hfc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) 0
      have h2 : TendstoUniformlyOn f (f 0) (𝓝 0) K :=
        tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.2 h1
      have h3 : TendstoUniformlyOn f (f 0) (𝓝[>] 0) K := fun u hu =>
        (h2 u hu).filter_mono nhdsWithin_le_nhds
      exact h3.congr (hev.mono fun s hs => (hs.mono hK).symm)
    refine ⟨hT, fun p hp => ?_⟩
    exact (hT.tendsto_at hp).limUnder_eq
  have hcont : ∀ n : ℕ, Continuous fun p : ℝ × ℝ => W n (vec3 (0, p.1, p.2)) ω := fun n =>
    (hWc n ω).comp (continuous_vec3.comp (continuous_const.prodMk continuous_id))
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨n, hpn⟩ := exists_mem_win hp.2
    have he : (fun p : ℝ × ℝ => W n (vec3 (0, p.1, p.2)) ω) =ᶠ[𝓝 p] affLim (X ω) η :=
      eventually_of_mem ((isOpen_win n).mem_nhds hpn) fun q hq => ((hn n).2 hq).symm
    exact ((hcont n).continuousAt.congr he).continuousWithinAt
  · rw [← iUnion_win]
    exact tendstoLocallyUniformlyOn_iUnion isOpen_win fun n =>
      (hn n).1.congr_right (hn n).2.symm

end PairLim
end QuantumZipper
