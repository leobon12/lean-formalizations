import QuantumZipper.Proofs.Complex.KernelChord
import QuantumZipper.Proofs.Complex.KernelChordInv
import QuantumZipper.Loewner.Curves

/-!
# KT2: the chord version of the Carathéodory kernel theorem (statement and reduction)

Statement fixed by DECISIONS D7. For a simple chord `η`, the *left-normalized uniformizer* of
the left component `D₁ = leftComponent η` is a normalized uniformizer `φ : D₁ → ℍ`
(`IsNormalizedUniformizer`: `0 ↦ 0`, `∞ ↦ ∞`) with boundary value `φ(−1) = −1`
(`IsLeftUniformizer`). **KT2** (`ChordKernelTheoremLeft`): if simple chords `η n → η` uniformly
on `[0,∞)` in the chordal (spherical) metric (`SphereUniformConv`), then the left-normalized
uniformizers converge with their inverses: `φ_n⁻¹ → φ⁻¹` locally uniformly on `ℍ`, and every
compact `K ⊆ D₁` lies in `D₁(η n)` for large `n` with `φ_n → φ` uniformly on `K`.

Proof route (D7): the doubled domain `leftDoubled η = D₁ ∪ conj D₁ ∪ (−∞,0)` is mapped by the
Schwarz reflection `Φ` of `φ` onto `ℂ \ [0,∞)` with `Φ(−1) = −1`, `Φ'(−1) > 0`; the doubled
domains converge to `leftDoubled η` in the sense of kernel convergence with respect to `−1`;
Pommerenke's kernel theorem (KT1, *Boundary Behaviour of Conformal Maps* (1992), Thm 1.8, p. 14)
in the model form `kernel_theorem_slitNeg` gives `Φ_n⁻¹ → Φ⁻¹` on `ℂ \ [0,∞)`, and
`tendstoUniformlyOn_of_invFunOn` gives `Φ_n → Φ` on compacts. Restricting to `ℍ` gives KT2.

`chordKernelTheoremLeft_of` proves KT2 from the two geometric inputs, stated precisely as
`LeftReflection` (Schwarz reflection of the left-normalized uniformizer) and
`LeftDoubledKernel` (kernel convergence of doubled domains under sphere-uniform convergence),
which remain to be proved.
-/

noncomputable section

open Set Metric Filter Topology Complex Function
open scoped ComplexOrder

namespace QuantumZipper.CA.Kernel

/-- The doubled left domain `D₁ ∪ conj D₁ ∪ (−∞,0)` of a chord (D7). -/
def leftDoubled (η : ℝ → ℂ) : Set ℂ :=
  leftComponent η ∪ (starRingEnd ℂ) '' leftComponent η ∪ {z : ℂ | z.im = 0 ∧ z.re < 0}

/-- `φ` is the left-normalized uniformizer of the chord `η` (D7): a normalized uniformizer of
`leftComponent η` onto `ℍ` (`0 ↦ 0`, `∞ ↦ ∞`) with boundary value `φ(−1) = −1`. -/
def IsLeftUniformizer (η : ℝ → ℂ) (φ : ℂ → ℂ) : Prop :=
  IsNormalizedUniformizer (leftComponent η) φ ∧
    Tendsto φ (𝓝[leftComponent η] (-1)) (𝓝 (-1))

/-- The chordal distance on `ℂ ⊆ Ĉ`: `2|z − w| / (√(1+|z|²) √(1+|w|²))`. -/
def chordalDist (z w : ℂ) : ℝ :=
  2 * ‖z - w‖ / (Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2))

/-- `η n → η` uniformly on `[0,∞)` in the chordal metric of the Riemann sphere. -/
def SphereUniformConv (η : ℕ → ℝ → ℂ) (ηi : ℝ → ℂ) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ≥ (0 : ℝ), chordalDist (η n t) (ηi t) < ε

/-- **KT2** (chord version of the Carathéodory kernel theorem, left component; D7). -/
def ChordKernelTheoremLeft : Prop :=
  ∀ (η : ℕ → ℝ → ℂ) (ηi : ℝ → ℂ) (φ : ℕ → ℂ → ℂ) (φi : ℂ → ℂ),
    (∀ n, IsSimpleChord (η n)) → IsSimpleChord ηi → SphereUniformConv η ηi →
    (∀ n, IsLeftUniformizer (η n) (φ n)) → IsLeftUniformizer ηi φi →
    TendstoLocallyUniformlyOn (fun n => invFunOn (φ n) (leftComponent (η n)))
        (invFunOn φi (leftComponent ηi)) atTop H ∧
      ∀ K : Set ℂ, IsCompact K → K ⊆ leftComponent ηi →
        (∀ᶠ n in atTop, K ⊆ leftComponent (η n)) ∧ TendstoUniformlyOn φ φi atTop K

/-- **Input R (Schwarz reflection).** The left-normalized uniformizer extends, by
`Φ z = conj (φ (conj z))` on `conj D₁` and by its (real) boundary values on `(−∞,0)`, to a
conformal map of the doubled domain onto `ℂ \ [0,∞)` with `Φ(−1) = −1`, `Φ'(−1) > 0`. -/
def LeftReflection : Prop :=
  ∀ (η : ℝ → ℂ) (φ : ℂ → ℂ), IsSimpleChord η → IsLeftUniformizer η φ →
    ∃ Φ : ℂ → ℂ, IsOpen (leftDoubled η) ∧ DifferentiableOn ℂ Φ (leftDoubled η) ∧
      BijOn Φ (leftDoubled η) slitNeg ∧ Φ (-1) = -1 ∧ 0 < deriv Φ (-1) ∧
      EqOn Φ φ (leftComponent η)

/-- **Input K (kernel convergence of doubled domains).** Sphere-uniform convergence of simple
chords implies kernel convergence of the doubled left domains with respect to `−1`
(Pommerenke, p. 13). -/
def LeftDoubledKernel : Prop :=
  ∀ (η : ℕ → ℝ → ℂ) (ηi : ℝ → ℂ), (∀ n, IsSimpleChord (η n)) → IsSimpleChord ηi →
    SphereUniformConv η ηi →
    KernelConvergesTo (fun n => leftDoubled (η n)) (leftDoubled ηi) (-1)

theorem neg_one_mem_leftDoubled (η : ℝ → ℂ) : (-1 : ℂ) ∈ leftDoubled η :=
  Or.inr ⟨by simp, by simp⟩

theorem leftComponent_subset_leftDoubled (η : ℝ → ℂ) : leftComponent η ⊆ leftDoubled η :=
  fun _ hz => Or.inl (Or.inl hz)

theorem mem_leftComponent_of_mem_leftDoubled {η : ℝ → ℂ} {z : ℂ} (hz : z ∈ leftDoubled η)
    (hzH : z ∈ H) : z ∈ leftComponent η := by
  rcases hz with (hz | ⟨w, hw, rfl⟩) | ⟨h0, -⟩
  · exact hz
  · have h1 : 0 < w.im := leftComponent_subset_H η hw
    have h2 : 0 < ((starRingEnd ℂ) w).im := hzH
    rw [conj_im] at h2
    linarith
  · have : 0 < z.im := hzH
    linarith

theorem H_subset_slitNeg : H ⊆ slitNeg := fun z hz => by
  show -z ∈ slitPlane
  rw [mem_slitPlane_iff]
  right
  have : 0 < z.im := hz
  simp only [neg_im]
  linarith

/-- On `ℍ`, the inverse of the doubled map is the inverse of `φ`. -/
theorem invFunOn_doubled_eq {D Ω : Set ℂ} {φ Φ : ℂ → ℂ} (hDΩ : D ⊆ Ω)
    (hφ : BijOn φ D H) (hΦ : BijOn Φ Ω slitNeg) (hEq : EqOn Φ φ D) {v : ℂ} (hv : v ∈ H) :
    invFunOn Φ Ω v = invFunOn φ D v := by
  have h1 : ∃ z ∈ D, φ z = v := hφ.surjOn hv
  have h2 : ∃ z ∈ Ω, Φ z = v := hΦ.surjOn (H_subset_slitNeg hv)
  apply hΦ.injOn (invFunOn_mem h2) (hDΩ (invFunOn_mem h1))
  rw [invFunOn_eq h2, hEq (invFunOn_mem h1), invFunOn_eq h1]

/-- Compacts of the kernel lie in the domains eventually (Pommerenke, p. 13). -/
theorem KernelConvergesTo.eventually_subset {G : ℕ → Set ℂ} {D : Set ℂ} {w₀ : ℂ}
    (hker : KernelConvergesTo G D w₀) (hD : D ≠ {w₀}) {K : Set ℂ} (hKc : IsCompact K)
    (hKD : K ⊆ D) : ∀ᶠ n in atTop, K ⊆ G n := by
  obtain ⟨hi, -⟩ := hker
  have hi := hi.resolve_left hD
  choose! U hU hev using hi.2.2.2.2
  obtain ⟨t, htK, hcov⟩ := hKc.elim_nhds_subcover U fun x hx => hU x (hKD hx)
  have : ∀ᶠ n in atTop, ∀ x ∈ t, U x ⊆ G n :=
    (eventually_all_finset t).2 fun x hx => hev x (hKD (htK x hx))
  filter_upwards [this] with n hn y hy
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (hcov hy)
  exact hn x hx hyx

/-- **KT2 from the two geometric inputs.** -/
theorem chordKernelTheoremLeft_of (hR : LeftReflection) (hK : LeftDoubledKernel) :
    ChordKernelTheoremLeft := by
  intro η ηi φ φi hη hηi hconv hφ hφi
  choose Φ hΩo hΦd hΦb hΦ0 hΦ' hΦeq using fun n => hR (η n) (φ n) (hη n) (hφ n)
  obtain ⟨Φi, hΩio, hΦid, hΦib, hΦi0, hΦi', hΦieq⟩ := hR ηi φi hηi hφi
  have hker := hK η ηi hη hηi hconv
  have hlim := kernel_theorem_slitNeg hΩo hΦd hΦb (fun n => neg_one_mem_leftDoubled _) hΦ0
    hΦ' hΩio hΦid hΦib (neg_one_mem_leftDoubled _) hΦi0 hΦi' hker
  refine ⟨?_, fun K hKc hKD => ?_⟩
  · refine ((hlim.mono H_subset_slitNeg).congr fun n v hv => ?_).congr_right fun v hv => ?_
    · exact invFunOn_doubled_eq (leftComponent_subset_leftDoubled _) (hφ n).1.1 (hΦb n)
        (hΦeq n) hv
    · exact invFunOn_doubled_eq (leftComponent_subset_leftDoubled _) hφi.1.1 hΦib hΦieq hv
  · have hne : leftDoubled ηi ≠ {(-1 : ℂ)} := by
      intro h
      have h2 : (-2 : ℂ) ∈ leftDoubled ηi := Or.inr ⟨by simp, by simp⟩
      rw [h, mem_singleton_iff] at h2
      norm_num at h2
    have hKΩ : K ⊆ leftDoubled ηi := hKD.trans (leftComponent_subset_leftDoubled _)
    have hev : ∀ᶠ n in atTop, K ⊆ leftComponent (η n) := by
      filter_upwards [hker.eventually_subset hne hKc hKΩ] with n hn z hz
      exact mem_leftComponent_of_mem_leftDoubled (hn hz) (leftComponent_subset_H _ (hKD hz))
    refine ⟨hev, ?_⟩
    have hψd : ∀ n, DifferentiableOn ℂ (invFunOn (Φ n) (leftDoubled (η n))) slitNeg := by
      intro n v hv
      obtain ⟨z, hz, rfl⟩ := (hΦb n).surjOn hv
      exact (Koebe.hasDerivAt_invFunOn_of_injOn (hΩo n) (hΦd n) (hΦb n).injOn hz)
        |>.differentiableAt.differentiableWithinAt
    have hψi : InjOn (invFunOn Φi (leftDoubled ηi)) slitNeg :=
      (hΦib.symm hΦib.invOn_invFunOn.symm).injOn
    have hU := tendstoUniformlyOn_of_invFunOn isOpen_slitNeg hΦb hΦib
      (fun z hz => (hΦid.differentiableAt (hΩio.mem_nhds hz)).continuousAt) hψd hψi hlim hKc hKΩ
    refine (hU.congr ?_).congr_right fun z hz => hΦieq (hKD hz)
    filter_upwards [hev] with n hn z hz
    exact hΦeq n (hn hz)

end QuantumZipper.CA.Kernel
