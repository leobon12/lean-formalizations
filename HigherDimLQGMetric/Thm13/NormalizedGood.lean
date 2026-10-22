import HigherDimLQGMetric.Thm13.LawTransfer

/-! A21(1)–(4) for every realization of the normalized LGF law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l8_exists_normalized_good
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ)
    (hLen : L8LengthLimitInput)
    (hL7f : ∀ d ξ κ, L7f_determined d ξ κ)
    (h36 : L8Lemma36TruncInput)
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hMarkov : DMarkovRd) (hShell : ShellDecouplingFun)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d),
        IsNormalizedLGF h P →
        (∀ᵐ ω ∂P,
          (l8_patch hd hκ ξ (εs ∘ φ) (fun n => hεs (φ n)) (h ω)).IsLength ∧
          IsProperFn (l8_patch hd hκ ξ (εs ∘ φ)
            (fun n => hεs (φ n)) (h ω)).1) ∧
        (∀ᵐ ω ∂P, Tendsto
          (fun n => lfppSeq κ ξ (εs ∘ φ) (h ω) n) atTop
          (𝓝 (l8_patch hd hκ ξ (εs ∘ φ)
            (fun n => hεs (φ n)) (h ω)).1)) ∧
        (∀ᵐ ω ∂P, ∃ hD :
          (l8_patch hd hκ ξ (εs ∘ φ) (fun n => hεs (φ n)) (h ω)).IsLength,
          ∀ f : C(Rd d, ℝ),
            l8_patch hd hκ ξ (εs ∘ φ) (fun n => hεs (φ n))
              (addFun (h ω) f) =
              weylMetric ξ f
                (l8_patch hd hκ ξ (εs ∘ φ)
                  (fun n => hεs (φ n)) (h ω)) hD) := by
  obtain ⟨φ, hφ, Ω, mΩ, P, hP, h₀, Dh, hh₀, _hDm, _hgood,
    _hdet, _hstable, hW, hae⟩ :=
    l8_exists_weyl_coupling hL6a hLen hL7f h36 hd ξ κ hκ hB2
      hMarkov hShell εs hεs hεt
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := hP
  have hεφt : Tendsto (εs ∘ φ) atTop (𝓝 0) :=
    hεt.comp hφ.tendsto_atTop
  refine ⟨φ, hφ, ?_⟩
  intro Ω' _ P' _ h' hh'
  let D : DistRd d → ContMetric d :=
    l8_patch hd hκ ξ (εs ∘ φ) (fun n => hεs (φ n))
  have hDm : Measurable D :=
    l8_measurable_patch hd hκ ξ (εs ∘ φ) (fun n => hεs (φ n))
  obtain ⟨hlen, hconv⟩ := l8_normalized_good_of_coupling hd κ hκ ξ
    (εs ∘ φ) (fun n => hεs (φ n)) P h₀ Dh hh₀ hae hW P' h' hh'
  have hproper := l8_ae_proper_of_ae_lfpp_limit hL6a hd κ hκ ξ hB2
    (εs ∘ φ) (fun n => hεs (φ n)) hεφt P' h' hh' D hDm hconv
  have hgood : ∀ᵐ ω ∂P', (D (h' ω)).IsLength ∧
      IsProperFn (D (h' ω)).1 := by
    filter_upwards [hlen, hproper] with ω hlenω hproperω
    exact ⟨hlenω, hproperω⟩
  have hW' := l8_ae_patch_addFun_eq_weyl h36 hd κ hκ ξ l2c_trunc
    (εs ∘ φ) (fun n => hεs (φ n)) hεφt P' h' (D ∘ h') hh'
    hgood hconv
  exact ⟨hgood, hconv, hW'⟩

/-- The all-realizations good event used by the remaining A21 steps. -/
def L8NormalizedGood {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d),
    IsNormalizedLGF h P →
    (∀ᵐ ω ∂P,
      (l8_patch hd hκ ξ εs hεs (h ω)).IsLength ∧
      IsProperFn (l8_patch hd hκ ξ εs hεs (h ω)).1) ∧
    (∀ᵐ ω ∂P, Tendsto
      (fun n => lfppSeq κ ξ εs (h ω) n) atTop
      (𝓝 (l8_patch hd hκ ξ εs hεs (h ω)).1)) ∧
    (∀ᵐ ω ∂P, ∃ hD :
      (l8_patch hd hκ ξ εs hεs (h ω)).IsLength,
      ∀ f : C(Rd d, ℝ),
        l8_patch hd hκ ξ εs hεs (addFun (h ω) f) =
          weylMetric ξ f (l8_patch hd hκ ξ εs hεs (h ω)) hD)

theorem l8_exists_normalized_good'
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ)
    (hLen : L8LengthLimitInput)
    (hL7f : ∀ d ξ κ, L7f_determined d ξ κ)
    (h36 : L8Lemma36TruncInput)
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hMarkov : DMarkovRd) (hShell : ShellDecouplingFun)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      L8NormalizedGood hd hκ ξ (εs ∘ φ) (fun n => hεs (φ n)) :=
  l8_exists_normalized_good hL6a hLen hL7f h36 hd ξ κ hκ hB2
    hMarkov hShell εs hεs hεt

end HigherDimLQGMetric
