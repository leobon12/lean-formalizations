/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6LMeanChain
import InteractingSLE.Spec.Supplement.GW2JDetR4Contact
import InteractingSLE.Spec.Supplement.BW1InEndDetBase

/-!
# GW2's joint (Det): the relative configuration with the counterflow retained

Packet PROVE-GW2-FABLE. GB9, p. 525 ("Before a new flow prefix first meets the retained counterflow, the conditional
exploration has its full canonical word in this joint chart"). The deterministic configuration behind the mean
identification is the one already proved for GB6 (`Supp8.GB6LMean.exists_isRelConfigOff_gb6_hull`), with the two
curves exchanged: `Supp8.Q3Rel.isRetainedChartOff_relMap` and `Supp8.Q3Rel.isRelConfigOff_gb6` hold for an arbitrary
retained driver with a Loewner trace that does not return to its base.

* `exists_frozen_generatingTrace`: a driver with a generating trace before a lifetime `Tα`, frozen after a time
  `t₂ ∈ (t₁, Tα)`, is a globally continuous driver with a generating trace on `[0, ∞)`, agreeing with the given
  driver and trace on `[0, t₂]` (the flow line of GW2 may reach a continuation threshold, so its lifetime is finite);
* `lt_firstContactTime_of_prefix`: a first contact time only sees the prefix of the moving curve;
* **`exists_isRelConfigOff_gw2_hull`**: for a counterflow `(w, γ)` of infinite lifetime with an interior tip at `s`
  that does not return to `0`, and a flow `(wα, α)` before its first contact with the inverted counterflow prefix:
  the relative chain of the (frozen) flow in the chart `relMap w s` of the retained counterflow, the hull identities
  at every earlier flow time (`GB6LMean.HullsUpTo`), and `Supp8.Q3Rel.IsRelConfigOff` for every admissible triple of
  words.

Deterministic. Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd)

namespace InteractingSLE.Theorem14.GW2Fb

open Supp8.GB6 (relMap relInv relClock firstContactTime sphereInv)
open Supp8.Q3Rel (invHull relLog relBad IsRelConfigOff)
open Supp8.GB6LMean (HullsUpTo)

/-! ### Freezing a driver before its lifetime -/

/-- **A driver frozen before its lifetime has a generating trace on `[0, ∞)`.** Let `α` be a generating trace of the
driver `wα` (continuous before `Tα`, from `0`) and `t₁ < Tα`. Then for some `t₂ ∈ (t₁, Tα)` there are a globally
continuous driver `w'` from `0` and a generating trace `α'` of `w'` with infinite lifetime, agreeing with `wα` and
`α` on `[0, t₂]`. -/
theorem exists_frozen_generatingTrace {wα : ℝ≥0 → ℝ} {Tα : ℝ≥0∞} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace wα Tα α) (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα}) (hwα0 : wα 0 = 0)
    {t₁ : ℝ≥0} (ht₁ : (t₁ : ℝ≥0∞) < Tα) :
    ∃ (w' : ℝ≥0 → ℝ) (α' : ℝ≥0 → ℂ) (t₂ : ℝ≥0), t₁ < t₂ ∧ (t₂ : ℝ≥0∞) < Tα ∧ Continuous w' ∧ w' 0 = 0 ∧
      IsGeneratingTrace w' ⊤ α' ∧ (∀ u ≤ t₂, w' u = wα u) ∧ ∀ u ≤ t₂, α' u = α u := by
  obtain ⟨t₃, ht₁t₃, ht₃⟩ := exists_real_btwn_of_lt ht₁
  set T2 : ℝ := ((t₁ : ℝ) + t₃) / 2 with hT2def
  have h1 : (t₁ : ℝ) < T2 := by rw [hT2def]; linarith
  have h2 : T2 < t₃ := by rw [hT2def]; linarith
  have hT20 : 0 ≤ T2 := (NNReal.coe_nonneg t₁).trans h1.le
  have ht₃0 : 0 ≤ t₃ := hT20.trans h2.le
  set W₃ : ℝ → ℝ := frozenDrive wα t₃ with hW₃
  have hW₃c : Continuous W₃ := continuous_frozenDrive_of_lt hwα ht₃
  have hW₃0 : W₃ 0 = 0 := by rw [hW₃, frozenDrive_zero ht₃0, hwα0]
  have hext := (hα.isLoewnerTraceLT ht₃).isLoewnerTrace_ext hW₃c hW₃0 hT20 h2
  set U : ℝ → ℝ := YuanCorollary13.extDrive W₃ T2 with hUdef
  set αr : ℝ → ℂ := YuanCorollary13.extTrace W₃ (fun r : ℝ => α r.toNNReal) T2 with hαrdef
  have hU : Continuous U := YuanCorollary13.continuous_extDrive hW₃c
  have hU0 : U 0 = 0 := YuanCorollary13.extDrive_zero hW₃0 hT20
  have hUnn : ∀ x : ℝ, U (x.toNNReal : ℝ) = U x := fun x => by
    by_cases hx : 0 ≤ x
    · rw [Real.coe_toNNReal _ hx]
    · have hx' : x ≤ 0 := (not_le.1 hx).le
      have e1 : min (min x T2) t₃ ≤ 0 := (min_le_left _ _).trans ((min_le_left _ _).trans hx')
      rw [Real.toNNReal_of_nonpos hx', NNReal.coe_zero, hU0]
      simp only [hUdef, YuanCorollary13.extDrive, hW₃, frozenDrive, Real.toNNReal_of_nonpos e1, hwα0]
  refine ⟨fun u => U u, fun u => αr u, T2.toNNReal, Real.lt_toNNReal_iff_coe_lt.2 h1, ?_,
    hU.comp NNReal.continuous_coe, ?_, BW1In.isGeneratingTrace_of_isLoewnerTrace hUnn hext,
    fun u hu => ?_, fun u hu => ?_⟩
  · show ENNReal.ofReal T2 < Tα
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal h2.le) ht₃
  · show U ((0 : ℝ≥0) : ℝ) = 0
    rw [NNReal.coe_zero, hU0]
  · have hu' : (u : ℝ) ≤ T2 := (Real.le_toNNReal_iff_coe_le hT20).1 hu
    show U (u : ℝ) = wα u
    rw [hUdef, YuanCorollary13.extDrive_eq hu', hW₃,
      frozenDrive_eq ⟨NNReal.coe_nonneg u, hu'.trans h2.le⟩, Real.toNNReal_coe]
  · have hu' : (u : ℝ) ≤ T2 := (Real.le_toNNReal_iff_coe_le hT20).1 hu
    show αr (u : ℝ) = α u
    rw [hαrdef, YuanCorollary13.extTrace_eq hu', Real.toNNReal_coe]

/-! ### First contact only sees the prefix of the moving curve -/

/-- If two curves agree on `[0, t₂]` and the first is, at a time `t₁ < t₂`, strictly before its first contact with
a set, so is the second. -/
theorem lt_firstContactTime_of_prefix {X : Type*} {η η' : ℝ≥0 → X} {A : Set X} {t₁ t₂ : ℝ≥0}
    (h12 : t₁ < t₂) (heq : ∀ u ≤ t₂, η' u = η u) (ht₁ : (t₁ : ℝ≥0∞) < firstContactTime η A) :
    (t₁ : ℝ≥0∞) < firstContactTime η' A := by
  have hmin : (t₁ : ℝ≥0∞) < min (t₂ : ℝ≥0∞) (firstContactTime η A) :=
    lt_min (ENNReal.coe_lt_coe.2 h12) ht₁
  refine lt_of_lt_of_le hmin ?_
  unfold firstContactTime
  refine le_iInf₂ fun u hu => ?_
  by_cases hut : u ≤ t₂
  · rw [heq u hut] at hu
    exact (min_le_right _ _).trans (iInf₂_le u hu)
  · exact (min_le_left _ _).trans (ENNReal.coe_le_coe.2 (not_le.1 hut).le)

/-! ### The configuration -/

/-- **GW2's relative configuration with the counterflow retained** (GB9, p. 525; the mirror image of
`Supp8.GB6LMean.exists_isRelConfigOff_gb6_hull`). Let `γ` be a generating trace of the counterflow driver `w`
(continuous, from `0`, infinite lifetime) with an interior tip at `s` and no return to `0` on `(0, s]`, and let `α` be
a generating trace of the flow driver `wα` before its lifetime `Tα`. For flow times `0 < t < t₁ < Tα` with `t₁` before
the first contact of `α` with the inverted counterflow prefix, there are a frozen flow driver `w'` with a generating
trace `α'` on `[0, ∞)`, agreeing with the flow on `[0, t₂]` for some `t₂ > t₁`, and a relative chain `(Wr, ηr)` with

* positive relative clock and the hull identity `Ψ(K_t) = K̃_{a(t)}` at `t` and at every earlier flow time
  (`Ψ = relMap w s`, `a = relClock w s w'`),
* `Supp8.Q3Rel.IsRelConfigOff` in the flow's frame, with the retained set `invHull w s` (the inverted counterflow
  hull), for every triple of words with the side-word and flowed-word properties. -/
theorem exists_isRelConfigOff_gw2_hull {w wα : ℝ≥0 → ℝ} {Tα : ℝ≥0∞} {γ α : ℝ≥0 → ℂ} {s : ℝ≥0}
    (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0) (hsH : γ s ∈ H)
    (hNR : ∀ v : ℝ≥0, 0 < v → v ≤ s → γ v ≠ 0)
    (hα : IsGeneratingTrace wα Tα α) (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα}) (hwα0 : wα 0 = 0)
    {t t₁ : ℝ≥0} (ht0 : 0 < t) (htt₁ : t < t₁) (ht₁T : (t₁ : ℝ≥0∞) < Tα)
    (ht₁ : (t₁ : ℝ≥0∞) < firstContactTime (fun u => (α u : OnePoint ℂ))
      ((fun u => sphereInv (γ u : OnePoint ℂ)) '' Icc 0 s)) :
    ∃ (w' : ℝ≥0 → ℝ) (α' : ℝ≥0 → ℂ) (t₂ : ℝ≥0), t₁ < t₂ ∧ (t₂ : ℝ≥0∞) < Tα ∧ Continuous w' ∧ w' 0 = 0 ∧
      IsGeneratingTrace w' ⊤ α' ∧ (∀ u ≤ t₂, w' u = wα u) ∧ (∀ u ≤ t₂, α' u = α u) ∧
      ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
        0 < relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => w' r.toNNReal) t ∧
        relMap (fun r : ℝ => w r.toNNReal) s '' fwdHull (fun r : ℝ => w' r.toNNReal) t =
          fwdHull Wr (relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => w' r.toNNReal) t) ∧
        HullsUpTo (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => w' r.toNNReal) Wr t ∧
        ∀ (χ lam : ℝ) (β₀ βE βu : ℝ → ℝ) (S₀ SE Su : Finset ℝ) (G₀ GE G v : ℂ → ℝ),
          IsBoundedHarmonicExtension β₀ S₀ G₀ → IsBoundedHarmonicExtension βE SE GE →
          IsBoundedHarmonicExtension βu Su G →
          Supp8.BHMean.IsSideWord βE SE (fwdMapInv (fun r : ℝ => w' r.toNNReal) t)
            (fwdHull (fun r : ℝ => w' r.toNNReal) t) lam →
          Supp8.BHMean.IsSideWord βu Su
            (fwdMapInv Wr (relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => w' r.toNNReal) t))
            (fwdHull Wr (relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => w' r.toNNReal) t)) lam →
          Supp8.BHMean.IsFlowedWord βu β₀ Su S₀
            (fwdMapInv Wr (relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => w' r.toNNReal) t))
            (fwdHull Wr (relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => w' r.toNNReal) t)) →
          (∀ z, v z = G (fwdMap Wr (relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => w' r.toNNReal) t)
              (relMap (fun r : ℝ => w r.toNNReal) s z)) -
            χ * ((logDerivFwd Wr (relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => w' r.toNNReal) t)
              (relMap (fun r : ℝ => w r.toNNReal) s z)).im + (relLog (fun r : ℝ => w r.toNNReal) s z).im)) →
          IsRelConfigOff (invHull (fun r : ℝ => w r.toNNReal) s) (relMap (fun r : ℝ => w r.toNNReal) s)
            (relInv (fun r : ℝ => w r.toNNReal) s) (relLog (fun r : ℝ => w r.toNNReal) s)
            (relBad (fun r : ℝ => w r.toNNReal) s) (fun r : ℝ => w' r.toNNReal) Wr
            (fun r : ℝ => α' r.toNNReal) ηr t
            (relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => w' r.toNNReal) t) χ lam
            β₀ βE βu S₀ SE Su G₀ GE G v := by
  obtain ⟨w', α', t₂, h12, ht₂T, hw'c, hw'0, hα', hweq, hαeq⟩ :=
    exists_frozen_generatingTrace hα hwα hwα0 ht₁T
  have hNR' : ∀ v ∈ Ioc (0 : ℝ) s, (fun r : ℝ => γ r.toNNReal) v ≠ 0 := fun v hv =>
    hNR v.toNNReal (Real.toNNReal_pos.2 hv.1) (Real.toNNReal_le_iff_le_coe.2 hv.2)
  have hcontact : (t₁ : ℝ≥0∞) < firstContactTime (fun u => sphereInv (α' u : OnePoint ℂ))
      ((fun u => (γ u : OnePoint ℂ)) '' Icc 0 s) := by
    rw [GW2JDetR4.firstContactTime_sphereInv α' γ s]
    exact lt_firstContactTime_of_prefix h12 (fun u hu => by rw [hαeq u hu]) ht₁
  exact ⟨w', α', t₂, h12, ht₂T, hw'c, hw'0, hα', hweq, hαeq,
    Supp8.GB6LMean.exists_isRelConfigOff_gb6_hull (wα := w) (Tα := ⊤) (α := γ) (s := s)
      (U := fun r : ℝ => w r.toNNReal) (αr := fun r : ℝ => γ r.toNNReal) (t₂ := (s : ℝ) + 1)
      hγ hw.continuousOn hw0 ENNReal.coe_lt_top hsH (hw.comp continuous_real_toNNReal)
      (by simp only [Real.toNNReal_zero, hw0]) (isLoewnerTrace_of_isGeneratingTrace hγ) hNR'
      (lt_add_one _) (fun r _ => rfl) hα' hw'c hw'0 ht0 htt₁ hcontact⟩

end InteractingSLE.Theorem14.GW2Fb
