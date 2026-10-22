import HigherDimLQGContinuity.Frame.Bessel

/-!
# Pairing frame VII: existence

Packet N3 (NA4 Details (a) A2, steps 7–9; blueprint Part C `c:prop-frame`, steps 6–7). Target of the packet:

`exists_pairingFrame : ∀ {d}, 3 ≤ d → Nonempty (PairingFrame d)`.

With the Lusin–Souslin inverse `T₀` of `Φ = frameCoord` on the good set `𝒢` (`exists_frameInv`):
`T(ω) = T₀(π(ω))` and `good = π⁻¹(Φ(𝒢))`. Then
* `stdP(good) = (π_* stdP)(Φ(𝒢)) = (Φ_* μ)(Φ(𝒢)) ≥ μ(𝒢) = 1` (`map_frameCoord_normLGFLaw`, `normLGFLaw_frameGood`);
* `T_* stdP = (T₀)_* (π_* stdP) = (T₀ ∘ Φ)_* μ = μ` (`T₀ ∘ Φ = id` on `𝒢`), so `T` is a normalized LGF
  (`frame_isNormalizedLGF_of_map_eq`);
* for `ω ∈ good`, `T(ω) = g ∈ 𝒢` with `Φ(g) = π(ω)`; for `v` finitely supported, `g + f_v ∈ 𝒢` and
  `Φ(g + f_v) = π(ω) + π(v) = π(ω + v)`, so `ω + v ∈ good` and `T(ω + v) = g + f_v`;
* the Bessel clause is `frame_bessel` with `C_b = 2 + log 2 + |sphEnergy d|`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The normalized-LGF property transfers across equality of laws (the statement and proof of HDLM's
`l8_isNormalizedLGF_of_map_eq`, `Thm13/Coupling.lean`, restated here to keep the `Thm13` block out of the import
closure of the frame). -/
theorem frame_isNormalizedLGF_of_map_eq {d : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'} {h : Ω → DistRd d} {h' : Ω' → DistRd d}
    (hm : Measurable h) (hh' : IsNormalizedLGF h' P') (e : P.map h = P'.map h') :
    IsNormalizedLGF h P := by
  have hid : IsWholeSpaceLGF (id : DistRd d → DistRd d) (P.map h) := by
    rw [e]
    exact hh'.1.map_id
  refine ⟨⟨hm, ⟨fun I => ?_⟩, fun φ => ?_, fun φ ψ => ?_⟩, ?_⟩
  · have hF : Measurable fun g : DistRd d => I.restrict fun φ : TestRd0 d => g φ.1 :=
      measurable_pi_iff.2 fun _ => measurable_distOn_apply _
    refine ⟨(hF.comp hm).aemeasurable, ?_⟩
    have h1 : IsGaussian ((P.map h).map fun g : DistRd d =>
        I.restrict fun φ : TestRd0 d => g φ.1) :=
      (hid.gaussian.hasGaussianLaw I).isGaussian_map
    rw [Measure.map_map hF hm] at h1
    exact h1
  · have h1 : ∫ g, g φ.1 ∂(P.map h) = 0 := hid.centered φ
    rw [integral_map hm.aemeasurable
      (measurable_distOn_apply φ.1).aestronglyMeasurable] at h1
    exact h1
  · have h1 : cov[fun g : DistRd d => g φ.1,
        fun g : DistRd d => g ψ.1; P.map h] = logCovRd φ.1 ψ.1 :=
      hid.covariance_eq φ ψ
    rw [covariance_map (measurable_distOn_apply φ.1).aestronglyMeasurable
      (measurable_distOn_apply ψ.1).aestronglyMeasurable hm.aemeasurable] at h1
    exact h1
  · have hs : MeasurableSet {g : DistRd d | sphereAvg g 1 0 = 0} :=
      measurableSet_eq_fun (measurable_sphereAvg_left 1 0) measurable_const
    have h1 : ∀ᵐ g ∂(P.map h), sphereAvg g 1 0 = 0 := by
      rw [e]
      exact (ae_map_iff hh'.1.measurable.aemeasurable hs).2 hh'.2
    exact (ae_map_iff hm.aemeasurable hs).1 h1

/-- **A pairing frame exists** (Part C `c:prop-frame`; NA4 A2): for `d ≥ 3` there is a coordinate realization of the
normalized LGF on `(ℝ^ℕ, stdP)` whose finitely supported coordinate shifts are shifts by the bounded continuous
frame vectors `e_j`, with Bessel's inequality for compactly supported Hölder-regular probability measures. -/
theorem exists_pairingFrame {d : ℕ} (hd : 3 ≤ d) : Nonempty (PairingFrame d) := by
  have : NeZero d := ⟨by omega⟩
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have hspec := normLGFLaw_spec d hd2
  have := hspec.1
  obtain ⟨hGm, T₀, hT₀m, hT₀⟩ := exists_frameInv (d := d) hd1
  set good : Set GaussianLQG.Coord := frameProj d ⁻¹' (frameCoord d '' frameGood d) with hgood_def
  set T : GaussianLQG.Coord → DistRd d := fun ω => T₀ (frameProj d ω) with hT_def
  have hTm : Measurable T := hT₀m.comp measurable_frameProj
  -- the law of `T`
  have hlaw : GaussianLQG.stdP.map T = (normLGFLaw d).map id := by
    rw [show T = T₀ ∘ frameProj d from rfl, ← Measure.map_map hT₀m measurable_frameProj,
      ← map_frameCoord_normLGFLaw hd2, Measure.map_map hT₀m measurable_frameCoord]
    refine Measure.map_congr ?_
    filter_upwards [ae_mem_frameGood hd2] with g hg
    exact hT₀ g hg
  -- the good set
  have hgood_meas : MeasurableSet good := measurable_frameProj hGm
  have hgood : GaussianLQG.stdP good = 1 := by
    have e1 : GaussianLQG.stdP good =
        (GaussianLQG.stdP.map (frameProj d)) (frameCoord d '' frameGood d) :=
      (Measure.map_apply measurable_frameProj hGm).symm
    rw [e1, ← map_frameCoord_normLGFLaw hd2, Measure.map_apply measurable_frameCoord hGm]
    refine le_antisymm prob_le_one ?_
    rw [← normLGFLaw_frameGood hd2]
    exact measure_mono (subset_preimage_image _ _)
  -- frame shifts
  have hshift : ∀ ω ∈ good, ∀ v : ℕ →₀ ℝ, GaussianLQG.shiftBy ω v ∈ good ∧
      T (GaussianLQG.shiftBy ω v) = addFun (T ω) (frameFunRd (frameE d) v) := by
    intro ω hω v
    obtain ⟨g, hg, hgω⟩ := hω
    have hTω : T ω = g := by
      show T₀ (frameProj d ω) = g
      rw [← hgω, hT₀ g hg]
    have hg' := addFun_frameE_mem_frameGood hg v
    have hc : frameCoord d (addFun g (frameFunRd (frameE d) v)) =
        frameProj d (GaussianLQG.shiftBy ω v) := by
      rw [frameCoord_addFun_frameE, hgω, GaussianLQG.shiftBy, frameProj_add]
    refine ⟨⟨_, hg', hc⟩, ?_⟩
    show T₀ (frameProj d (GaussianLQG.shiftBy ω v)) = _
    rw [← hc, hT₀ _ hg', hTω]
  exact ⟨{ e := frameE d
           bdd := fun j => exists_abs_framePot_le (frameGS d j) (integral_frameGS j)
           T := T
           measurable_T := hTm
           normalized := frame_isNormalizedLGF_of_map_eq hTm hspec.2.1 hlaw
           good := good
           measurableSet_good := hgood_meas
           ae_good := (prob_compl_eq_zero_iff hgood_meas).2 hgood
           shift_mem := fun ω hω v => (hshift ω hω v).1
           shift := fun ω hω v => (hshift ω hω v).2
           Cb := frameCb d
           one_le_Cb := one_le_frameCb d
           bessel := fun ν _ S B σ hS hB hσ _ hsupp hball n =>
             frame_bessel hd2 ν hS hB hσ hsupp hball n }⟩

end HigherDimLQGContinuity
