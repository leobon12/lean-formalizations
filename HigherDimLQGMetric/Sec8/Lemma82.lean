import HigherDimLQGMetric.Sec8.FavBorel
import HigherDimLQGMetric.Sec8.Perturb

/-!
# Lemma 8.2: finite perturbations at selected traps

The local configuration identity and the unchanged sphere normalizers are
assembled here on a common full-probability event.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Filter Topology
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- All site normalizers and the macroscopic normalizer are unchanged by a
finite separated perturbation, on one full-probability event. -/
theorem lemma82_normalizers {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (ξ Q : ℝ) {f : ℕ → C(Rd d, ℝ)} {J : ℕ}
    (hsupp : ∀ i < J, tsupport (f i) ⊆ ann (0 : Rd d) 1 3)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : 3 * r ≤ R)
    {Z : Finset (Rd d × ℕ)} (hJ : ∀ site ∈ Z, site.2 < J)
    (hcenter : ∀ site ∈ Z, ‖site.1‖ < 5 * R)
    (hsep : ∀ site ∈ Z, ∀ site' ∈ Z, site' ≠ site →
      10 * r ≤ ‖site'.1 - site.1‖) :
    ∀ᵐ ω ∂P,
      macroS ξ Q (addFun (h ω) (F_Z f r Z)) R = macroS ξ Q (h ω) R ∧
      ∀ site ∈ Z,
        sNorm ξ Q (addFun (h ω) (F_Z f r Z)) r site.1 =
          sNorm ξ Q (h ω) r site.1 ∧
        sNorm ξ Q (addFun (h ω) (bumpAt (f site.2) r site.1)) r site.1 =
          sNorm ξ Q (h ω) r site.1 := by
  have hmacro := hh.ae_exists_tendsto_sphereAvgSeq hd
    (mul_pos (by norm_num : (0 : ℝ) < 8) hR) 0
  have hsites : ∀ᵐ ω ∂P, ∀ site ∈ Z,
      sNorm ξ Q (addFun (h ω) (F_Z f r Z)) r site.1 =
        sNorm ξ Q (h ω) r site.1 ∧
      sNorm ξ Q (addFun (h ω) (bumpAt (f site.2) r site.1)) r site.1 =
        sNorm ξ Q (h ω) r site.1 := by
    refine (Filter.eventually_all_finset Z).2 fun site hsite => ?_
    filter_upwards [hh.ae_exists_tendsto_sphereAvgSeq hd hr site.1] with ω hlim
    obtain ⟨a, ha⟩ := hlim
    have hsep' : ∀ q ∈ Z, q ≠ site → 10 * r ≤ ‖q.1 - site.1‖ :=
      fun q hq hne => hsep site hsite q hq hne
    constructor
    · simp only [sNorm, lemma82_sphereAvg_site (h ω) hsupp hr hsite hJ hsep' ha]
    · simp only [sNorm, lemma82_sphereAvg_single (h ω) hsupp (hJ site hsite)
        hr site.1 ha]
  filter_upwards [hmacro, hsites] with ω hlim hsite
  obtain ⟨a, ha⟩ := hlim
  constructor
  · simp only [macroS, lemma82_sphereAvg_macro (h ω) hsupp hr hrR hJ hcenter ha]
  · exact hsite

/-- Lemma 8.2 at a finite labeled set: the normalizers and every trap
configuration agree with the corresponding single-bump field. Subtracting
the perturbation after adding it is a literal distribution identity. -/
theorem lemma82 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hd : 3 ≤ d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    {f : ℕ → C(Rd d, ℝ)} {J : ℕ}
    (hsupp : ∀ i < J, tsupport (f i) ⊆ ann (0 : Rd d) 1 3)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : 3 * r ≤ R)
    {x y : Rd d} {colour : Fin d → ℤ}
    {Z : Finset (Rd d × ℕ)}
    (hZ : IsSec8LabeledSet d J r R x y colour Z) :
    ∀ᵐ ω ∂P,
      macroS ξ Q (addFun (h ω) (F_Z f r Z)) R = macroS ξ Q (h ω) R ∧
      (∀ site ∈ Z,
        sNorm ξ Q (addFun (h ω) (F_Z f r Z)) r site.1 =
          sNorm ξ Q (h ω) r site.1 ∧
        sNorm ξ Q (addFun (h ω) (bumpAt (f site.2) r site.1)) r site.1 =
          sNorm ξ Q (h ω) r site.1 ∧
        config (D (addFun (h ω) (F_Z f r Z)))
          (Dt (addFun (h ω) (F_Z f r Z)))
          (sNorm ξ Q (addFun (h ω) (F_Z f r Z)) r site.1) r site.1 =
        config (D (addFun (h ω) (bumpAt (f site.2) r site.1)))
          (Dt (addFun (h ω) (bumpAt (f site.2) r site.1)))
          (sNorm ξ Q (addFun (h ω) (bumpAt (f site.2) r site.1)) r site.1)
            r site.1) ∧
      addFun (addFun (h ω) (F_Z f r Z)) (-F_Z f r Z) = h ω := by
  have hJ : ∀ site ∈ Z, site.2 < J := by
    intro site hsite
    obtain ⟨_, _, _, _, _, _, hlabel⟩ := hZ.1 site hsite
    exact hlabel
  have hcenter : ∀ site ∈ Z, ‖site.1‖ < 5 * R := by
    intro site hsite
    obtain ⟨_, _, _, hc, _, _, _⟩ := hZ.1 site hsite
    exact hc
  have hsep : ∀ site ∈ Z, ∀ site' ∈ Z, site' ≠ site →
      10 * r ≤ ‖site'.1 - site.1‖ := by
    intro site hsite site' hsite' hne
    exact hZ.separated (by omega : 1 ≤ d) hr hsite' hsite hne
  have hnorm := lemma82_normalizers P h (by omega : 2 ≤ d) hh ξ Q hsupp hr hR hrR
    hJ hcenter hsep
  have hcfg : ∀ᵐ ω ∂P, ∀ site ∈ Z,
      config (D (addFun (h ω) (F_Z f r Z)))
        (Dt (addFun (h ω) (F_Z f r Z)))
        (sNorm ξ Q (addFun (h ω) (F_Z f r Z)) r site.1) r site.1 =
      config (D (addFun (h ω) (bumpAt (f site.2) r site.1)))
        (Dt (addFun (h ω) (bumpAt (f site.2) r site.1)))
        (sNorm ξ Q (addFun (h ω) (bumpAt (f site.2) r site.1)) r site.1)
          r site.1 := by
    refine (Filter.eventually_all_finset Z).2 fun site hsite => ?_
    exact lemma82_config P h (by omega : 2 ≤ d) hh hD hDt hsupp hr
      hsite hJ (fun q hq hne => hsep site hsite q hq hne)
  filter_upwards [hnorm, hcfg] with ω hnorm hcfg
  refine ⟨hnorm.1, ?_, addFun_F_Z_sub (h ω) f r Z⟩
  intro site hsite
  exact ⟨(hnorm.2 site hsite).1, (hnorm.2 site hsite).2, hcfg site hsite⟩

end HigherDimLQGMetric
