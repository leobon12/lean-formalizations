/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdFstShift
import InteractingSLE.Spec.Supplement.OrdFstSided

/-!
# Leaf 3, the first continuation: its canonical clock and the slit sides of a later line

Packet PROVE-T15-ORDDET3 (Theorem 1.5's leaf 3, `RLC.RetOrdDetFstStatement`; supplement p. 497, Lemma G7 for the first
current tip).

* `canonRetPath_shift`, `canonRetLife_shift`: the canonical retained clock from the seed `c` is the translate by `c` of
  the canonical clock of the chart shifted by `c` from the seed `0`;
* **`exists_ordContFst_facts`** (pathwise): the canonical retained clock of the FIRST continuation (stopped at its first
  new contact with the retained union only, real contacts allowed), read in the chart shifted to the first tip, has a
  continuous driver `W` generating it from `0`, and at every continuation time its capacity time `Q` and its chart
  images `ψ₀(γ([0, Q]) + tipPos) = η₁([u, u + t])`, `ψ₀(γ(Q) + tipPos) = η₁(u + t)` are those required by
  `OrdDet.retChart_trans_fst` (`Supp7.isRetCont_fst`, `RetAux79.canonRetPath_facts`); the seed is `tipPos`;
* **`exists_slitSideFst_of_lt`** (deterministic): at a later line `(u + t, r)` of the first continuation, every open
  interval inside the two slit images contains a point `y` whose later shifted chart image `ψ₁(y + τ₁)` is an interior
  point of the first prefix, off the second prefix and off the later first tip (the first-path analogue of
  `OrdDet.exists_slitSide_of_lt`, PROVE-T15-ORDDET2's dense form);
* **`slitHeightsFst_of_dense`**: with the SIDED outer word `IsRetainedWordFst` at the later pair, the recentred later
  word has the canonical new-side heights `∓λ − θ₁χ` on the two slit images (left slit `−λ − θ₁χ`, right slit
  `λ − θ₁χ`) off its jumps.

For Theorem 1.5; deterministic (R43/R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE

namespace RLC

namespace OrdDet

open Supp7 Restart MartChar.RealFlow

/-! ### The canonical clock from a translated seed -/

theorem canonRetPath_shift (D : Set ℂ) (φ : ℂ → ℂ) (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (a : ℝ≥0) (K : Set ℂ) (c : ℝ)
    (s : ℝ≥0) :
    canonRetPath D φ η ζ a K c s = canonRetPath D (fun z => φ z - c) η ζ a K 0 s + c := by
  simp only [canonRetPath, ofReal_zero, sub_zero, add_zero]

theorem canonRetLife_shift (D : Set ℂ) (φ : ℂ → ℂ) (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (a : ℝ≥0) (K : Set ℂ) (c : ℝ) :
    canonRetLife D φ η ζ a K c = canonRetLife D (fun z => φ z - c) η ζ a K 0 := by
  simp only [canonRetLife, ofReal_zero, sub_zero]

/-! ### The canonical clock of the first continuation -/

/-- **The canonical retained clock of the first continuation at an ordinary retained pair** (pathwise; see the module
docstring). `η` is a good path agreeing with the first data path on `[0, u]`; the first tip is interior, off the
second prefix, adherent to the active domain and not revisited before `u`. The chart path is the canonical clock of the
chart shifted by `tipPos` from the seed `0`; with `canonRetPath_shift` it is the canonical clock from the seed
`tipPos` minus `tipPos`. -/
theorem exists_ordContFst_facts {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω} (hd : d.IsMeasGood) {ω : Ω}
    (hω : ω ∈ d.E) {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} (hp : IsPathGood η ζ x) (hα : ∀ s ≤ d.u, d.η₁ ω s = η s)
    (huζ : (d.u : ℝ≥0∞) < ζ) (hpH : d.η₁ ω d.u ∈ H) (hpO : d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r)
    (hcl : d.η₁ ω d.u ∈ closure (activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r))
    (hne₁ : ∀ s < d.u, d.η₁ ω s ≠ d.η₁ ω d.u) :
    ∃ W : ℝ≥0 → ℝ, Continuous W ∧ W 0 = 0 ∧
      IsGeneratingTrace W (canonRetLife (d.D ω) (fun z => d.fwd ω z - tipPos d d.η₁ ω) η ζ d.u
          (η '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r) 0)
        (canonRetPath (d.D ω) (fun z => d.fwd ω z - tipPos d d.η₁ ω) η ζ d.u
          (η '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r) 0) ∧
      InjOn (canonRetPath (d.D ω) (fun z => d.fwd ω z - tipPos d d.η₁ ω) η ζ d.u
          (η '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r) 0)
        {s | (s : ℝ≥0∞) ≤ canonRetLife (d.D ω) (fun z => d.fwd ω z - tipPos d d.η₁ ω) η ζ d.u
          (η '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r) 0} ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < contLife η ζ d.u (η '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r) →
        let Q := (chartClock (contPath (d.D ω) (fun z => d.fwd ω z - tipPos d d.η₁ ω) η d.u
          (contLife η ζ d.u (η '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r))) t).toNNReal
        0 < Q ∧ (Q : ℝ≥0∞) < canonRetLife (d.D ω) (fun z => d.fwd ω z - tipPos d d.η₁ ω) η ζ d.u
          (η '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r) 0 ∧
        (fun s => d.inv ω (canonRetPath (d.D ω) (fun z => d.fwd ω z - tipPos d d.η₁ ω) η ζ d.u
            (η '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r) 0 s + tipPos d d.η₁ ω)) '' Icc 0 Q =
          η '' Icc d.u (d.u + t) ∧
        d.inv ω (canonRetPath (d.D ω) (fun z => d.fwd ω z - tipPos d d.η₁ ω) η ζ d.u
            (η '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r) 0 Q + tipPos d d.η₁ ω) = η (d.u + t) := by
  have hg := hd.good ω (RetData.E_subset_G hω)
  obtain ⟨⟨x₀, hx₀⟩, hC⟩ := hd.isRetChart hω
  have hφ : ∃ x₀ : ℝ, ∀ z, d.fwd ω z =
      ConformalImage.mapOut (fillH (prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r)) z - x₀ :=
    ⟨x₀, fun z => by
      show d.g ω z - d.shift ω = _
      rw [hx₀, RetData.g, RetData.K_of_mem hω]⟩
  obtain ⟨w₁, hw₁, hR⟩ := isRetCont_fst hg hC hφ hp hα huζ hpH hpO hcl hne₁
  -- the seed is `tipPos`
  have hDω : d.D ω = activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r := hd.D_of_mem hω
  have htp : tipPos d d.η₁ ω = w₁ := by
    have hNe : (𝓝[d.D ω] (d.η₁ ω d.u)).NeBot := by
      rw [hDω]; exact mem_closure_iff_nhdsWithin_neBot.1 hcl
    show (limUnder (𝓝[d.D ω] (d.η₁ ω d.u)) (d.fwd ω)).re = w₁
    rw [hDω] at hNe ⊢
    rw [hw₁.limUnder_eq, ofReal_re]
  -- the domain and the stop set
  have hKc : IsClosed (prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r) := (isCompact_prefixSet' hg.1 hg.2.1).isClosed
  have hK : d.η₂ ω '' Icc 0 d.r ∪ η '' Icc 0 d.u = η '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r := union_comm _ _
  have hD : H \ fillH (d.η₂ ω '' Icc 0 d.r ∪ η '' Icc 0 d.u) = d.D ω := by
    rw [hDω, activeDomain_eq hKc, prefixSet, image_congr fun s hs => hα s hs.2, hK]
  obtain ⟨W, hWc, hW0, hgen, hinj, hfacts⟩ := RetAux79.canonRetPath_facts hR
  rw [hD, hK] at hgen hinj hfacts
  rw [htp]
  refine ⟨W, hWc, hW0, hgen, hinj, fun t ht0 htV => ?_⟩
  obtain ⟨-, hQlt, hQpos, himg, htip⟩ := hfacts t htV.le
  exact ⟨hQpos ht0, hQlt htV, himg, htip⟩

/-! ### The slit sides of a later line of the first continuation -/

/-- **The slit sides of a later line of the first continuation, dense form** (see the module docstring). Data `d`
(cutoffs `(u, r)`) and `d'` (cutoffs `(u + t, r)`), a sample of both chart events, a chart path `γ` of the first
continuation from the seed `τ₀` (generated by a continuous `W` from `0`, injective, `0 < Q <` its lifetime, tracing
`η₁([u, u + t])` through `w ↦ ψ₀(w + τ₀)` and ending at the later first tip), and the shifted transition (III-a)
`ψ₁(w + τ₁) = ψ₀(f_Q⁻¹ w + τ₀)` on `ℍ` (`retChart_trans_fst`). Every open interval inside the two slit images contains
a point `y` with `ψ₁(y + τ₁)` an interior point of the first prefix, off the second prefix and off the later first
tip. -/
theorem exists_slitSideFst_of_lt {Ω : Type*} [MeasurableSpace Ω] {d d' : RetData Ω} (hd : d.IsMeasGood)
    (hd' : d'.IsMeasGood) {t : ℝ≥0} {ω : Ω} (hω : ω ∈ d.E) (hω' : ω ∈ d'.E) {τ₀ τ₁ : ℝ} {W : ℝ≥0 → ℝ}
    {γ : ℝ≥0 → ℂ} {ζc : ℝ≥0∞} {Q : ℝ≥0} (hg : IsGeneratingTrace W ζc γ) (hWc : Continuous W) (hW0 : W 0 = 0)
    (hinj : InjOn γ {s | (s : ℝ≥0∞) ≤ ζc}) (hQ : (Q : ℝ≥0∞) < ζc)
    (himg : (fun s => d.inv ω (γ s + τ₀)) '' Icc 0 Q = d.η₁ ω '' Icc d.u (d.u + t))
    (htip : d.inv ω (γ Q + τ₀) = d.η₁ ω (d.u + t))
    (hIIIa : ∀ w ∈ H, d'.inv ω (w + τ₁) = d.inv ω (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w + τ₀))
    {a b : ℝ} (hab : a < b)
    (hslit : Ioo a b ⊆ Ioo (-rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q) 0 ∪
      Ioo 0 (rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q)) :
    ∃ y ∈ Ioo a b, d'.inv ω (y + τ₁) ∈ H ∧ d'.inv ω (y + τ₁) ∈ d.η₁ ω '' Icc 0 (d.u + t) ∧
      d'.inv ω (y + τ₁) ≠ d.η₁ ω (d.u + t) ∧ d'.inv ω (y + τ₁) ∉ d.η₂ ω '' Icc 0 d.r := by
  set w' : ℝ → ℝ := fun s => W s.toNNReal with hw'
  have hQr : (0 : ℝ) ≤ Q := Q.coe_nonneg
  -- the global model of the chart path
  obtain ⟨Wg, γg, T', hQT', hWgc, hWg0, hγg, hWeq, hγeq⟩ :=
    Sec7.ReverseArc.exists_global_model hg hWc.continuousOn hW0 hQ
  have hWeqQ : EqOn w' Wg (Icc 0 (Q : ℝ)) := fun r hr => (hWeq r ⟨hr.1, hr.2.trans hQT'.le⟩).symm
  have hΦeq : fwdMapInv w' Q = fwdMapInv Wg Q := fwdMapInv_eq_of_eqOn hQr hQT' fun r hr => (hWeq r hr).symm
  have hWQ : W Q = Wg Q := by
    rw [hWeq Q ⟨hQr, hQT'.le⟩, Real.toNNReal_coe]
  have hRR : rightImg (fun s : ℝ => W s.toNNReal) 0 Q = rightImg Wg 0 Q :=
    Sec7.Lemma71B.rightImg_congr hWgc hQr hWeqQ 0
  have hRL : rightImg (fun s : ℝ => -W s.toNNReal) 0 Q = rightImg (fun s => -Wg s) 0 Q :=
    Sec7.Lemma71B.rightImg_congr hWgc.neg hQr (fun r hr => by
      show -W r.toNNReal = -Wg r
      rw [show W r.toNNReal = w' r from rfl, hWeqQ hr]) 0
  rw [hWQ, hRR, hRL] at hslit
  have hγQ : γg Q = γ Q := by rw [hγeq Q ⟨hQr, hQT'.le⟩, Real.toNNReal_coe]
  have himgg : γg '' Icc 0 (Q : ℝ) = γ '' Icc 0 Q := by
    rw [image_congr (fun r hr => hγeq r ⟨hr.1, hr.2.trans hQT'.le⟩), image_toNNReal_Icc γ hQr,
      Real.toNNReal_coe]
  have hi : InjOn γg (Icc 0 (Q : ℝ)) := by
    intro s hs s' hs' he
    have hle : ∀ x ∈ Icc (0 : ℝ) Q, ((x.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζc := fun x hx =>
      (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hx.2)).trans hQ.le
    rw [hγeq s ⟨hs.1, hs.2.trans hQT'.le⟩, hγeq s' ⟨hs'.1, hs'.2.trans hQT'.le⟩] at he
    have := hinj (hle s hs) (hle s' hs') he
    rw [← Real.coe_toNNReal s hs.1, ← Real.coe_toNNReal s' hs'.1, this]
  -- the middle chart points land on the chart path, and some of them in `ℍ`
  set Φ := extendFrom H (fwdMapInv Wg Q) with hΦdef
  have hmid : ∀ z ∈ Ioo a b, Φ z ∈ γg '' Icc 0 (Q : ℝ) := by
    intro z hz
    have h1 := le_rightImg hWgc 0 hQr
    have h2 : -Wg Q ≤ rightImg (fun s => -Wg s) 0 Q := le_rightImg (w := fun s => -Wg s) hWgc.neg 0 hQr
    rcases hslit hz with h | h
    · exact Sec7.Lemma71P.mem_image_of_mid hγg hWgc hWg0 hQr h.1 (by linarith [h.2])
    · exact Sec7.Lemma71P.mem_image_of_mid hγg hWgc hWg0 hQr (by linarith [h.1]) h.2
  obtain ⟨z, hz, hzH⟩ := Sec7.Lemma71P.exists_mem_H_of_lt hγg hWgc hWg0 hQr hi
    (fun a' b' hab' hsub => exists_im_ne_zero_of_lt hγg hWgc hWg0 hab' hsub) hab hmid
  have hz0 : z ≠ 0 := by
    rcases hslit hz with h | h
    · exact h.2.ne
    · exact h.1.ne'
  -- the two charts
  have hG := hd.good ω (RetData.E₀_subset_G (RetData.E_subset_E₀ hω))
  have h0₂ : (d.η₂ ω 0).im = 0 := hG.2.2.2.2.2.1
  have hC := (hd.isRetChart hω).2
  have hC' := (hd'.isRetChart hω').2
  have hΦc : ContinuousOn Φ Hbar := (hγg.hasBdryLimits hWgc hWg0 hQr).continuousOn
  have hΦm : MapsTo Φ Hbar Hbar := fun x hx => Sec7.Lemma71P.extendFrom_mem_Hbar hγg hWgc hWg0 hQr hx
  have hHbar : ∀ v : ℂ, v ∈ Hbar → ∀ y : ℝ, v + y ∈ Hbar := fun v hv y =>
    show 0 ≤ (v + y).im by simpa using (show 0 ≤ v.im from hv)
  have hHadd : ∀ v : ℂ, v ∈ H → ∀ y : ℝ, v + y ∈ H := fun v hv y =>
    show 0 < (v + y).im by simpa using (show 0 < v.im from hv)
  have hc₁ : ContinuousOn (fun w => d'.inv ω (w + τ₁)) Hbar :=
    hC'.continuousOn_inv.comp (continuousOn_id.add continuousOn_const) fun v hv => hHbar v hv τ₁
  have hc₀ : ContinuousOn (fun w => d.inv ω (Φ w + τ₀)) Hbar :=
    hC.continuousOn_inv.comp ((hΦc.add continuousOn_const)) fun v hv => hHbar _ (hΦm hv) τ₀
  have hψ : EqOn (fun w => d'.inv ω (w + τ₁)) (fun w => d.inv ω (Φ w + τ₀)) Hbar := by
    refine Set.EqOn.of_subset_closure (s := H) (fun w hw => ?_) hc₁ hc₀ QuantumZipper.H_subset_Hbar
      (by rw [closure_H])
    show d'.inv ω (w + τ₁) = d.inv ω (Φ w + τ₀)
    rw [hIIIa w hw, hΦdef, ZhanGT4.extendFrom_eq_fwdMapInv hWgc hWg0 hQr hw, hΦeq]
  have hzHb : ((z : ℝ) : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hψz : d'.inv ω ((z : ℂ) + τ₁) = d.inv ω (Φ z + τ₀) := hψ hzHb
  have hΦzH : Φ z + τ₀ ∈ H := hHadd _ hzH τ₀
  -- the image lies in the stop-line active domain and on the new piece
  have hD : d.inv ω (Φ z + τ₀) ∈ activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r := (hC.bijOn h0₂).mapsTo hΦzH
  obtain ⟨hDH, -, hD₂⟩ := notMem_of_mem_activeDomain hD
  rw [himgg] at hmid
  have hnew : d.inv ω (Φ z + τ₀) ∈ d.η₁ ω '' Icc d.u (d.u + t) := by
    obtain ⟨s', hs', hs'z⟩ := hmid z hz
    rw [← himg, ← hs'z]
    exact ⟨s', hs', rfl⟩
  refine ⟨z, hz, ?_, ?_, ?_, ?_⟩
  · rw [hψz]; exact hDH
  · rw [hψz]; exact image_mono (Icc_subset_Icc_left zero_le) hnew
  · rw [hψz, ← htip]
    intro he
    by_cases hγH : γ Q + τ₀ ∈ H
    · have hΦγ : Φ z = γg Q := by
        rw [hγQ]
        have := (hC.bijOn h0₂).injOn hΦzH hγH he
        exact add_right_cancel this
      exact hz0 (by exact_mod_cast Sec7.Lemma71P.eq_zero_of_extendFrom_eq_tip hγg hWgc hWg0 hQr hi hΦγ)
    · exact hC.inv_notMem h0₂ (γ Q + τ₀) hγH (he ▸ hD)
  · rw [hψz]; exact hD₂

/-- **The slit heights of the first continuation from density and the sided outer word.** If every open interval
inside the two slit images `(ℓ, 0)`, `(0, ϱ)` contains a point `y` sent by `w ↦ ψ(w + τ)` to an interior point of the
first prefix, off the second prefix and off the first tip, then a word with the sided outer word `IsRetainedWordFst`
relative to `τ` has, recentred at `τ`, the canonical new-side heights of the first path on the slit images off its
jumps. -/
theorem slitHeightsFst_of_dense {κ θ₁ : ℝ} {α β : ℝ≥0 → ℂ} {a b : ℝ≥0} {ψ : ℂ → ℂ} {τ : ℝ} {c : BoundaryWord}
    (hw : IsRetainedWordFst κ θ₁ α a β b ψ τ c) {ℓ ϱ : ℝ}
    (hside : ∀ a' b' : ℝ, a' < b' → Ioo a' b' ⊆ Ioo ℓ 0 ∪ Ioo 0 ϱ → ∃ y ∈ Ioo a' b',
      ψ (y + τ) ∈ H ∧ ψ (y + τ) ∈ α '' Icc 0 a ∧ ψ (y + τ) ≠ α a ∧ ψ (y + τ) ∉ β '' Icc 0 b) :
    (∀ y ∉ ((Exist.StagedLaw.BoundaryWord.shiftW τ c).jumps : Set ℝ), ℓ < y → y < 0 →
        (Exist.StagedLaw.BoundaryWord.shiftW τ c).fn y = -sleLambda κ - θ₁ * QuantumZipper.chiC κ) ∧
      (∀ y ∉ ((Exist.StagedLaw.BoundaryWord.shiftW τ c).jumps : Set ℝ), 0 < y → y < ϱ →
        (Exist.StagedLaw.BoundaryWord.shiftW τ c).fn y = sleLambda κ - θ₁ * QuantumZipper.chiC κ) := by
  set c' := Exist.StagedLaw.BoundaryWord.shiftW τ c with hc'
  have hgood : ∀ y : ℝ, ψ (y + τ) ∈ H → ψ (y + τ) ∈ α '' Icc 0 a → ψ (y + τ) ≠ α a →
      ψ (y + τ) ∉ β '' Icc 0 b →
      (y < 0 → c'.fn y = -sleLambda κ - θ₁ * QuantumZipper.chiC κ) ∧
        (0 < y → c'.fn y = sleLambda κ - θ₁ * QuantumZipper.chiC κ) := by
    intro y hH hα htip hβ
    have hψ : ψ ((y + τ : ℝ) : ℂ) = ψ (y + τ) := by push_cast; rfl
    rw [← hψ] at hH hα htip hβ
    obtain ⟨hL, hR⟩ := hw (y + τ) hH htip hα hβ
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hc', Exist.StagedLaw.BoundaryWord.fn_shiftW]; exact hL (by linarith)
    · rw [hc', Exist.StagedLaw.BoundaryWord.fn_shiftW]; exact hR (by linarith)
  have hloc : ∀ y ∉ (c'.jumps : Set ℝ), ∃ ε > 0, ∀ z : ℝ, dist z y < ε → c'.fn z = c'.fn y := fun y hy =>
    Metric.eventually_nhds_iff.1 (c'.isPiecewiseConstantBoundaryData y (by exact_mod_cast hy))
  refine ⟨fun y hy hℓ hy0 => ?_, fun y hy hy0 hϱ => ?_⟩
  · obtain ⟨ε, hε, hεy⟩ := hloc y hy
    obtain ⟨y', hy', hH, hα, htip, hβ⟩ := hside (max ℓ (y - ε)) y (max_lt hℓ (by linarith))
      (fun z hz => Or.inl ⟨(le_max_left _ _).trans_lt hz.1, hz.2.trans hy0⟩)
    have hd : dist y' y < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right ℓ (y - ε), hy'.1, hy'.2]
    rw [← hεy y' hd]
    exact (hgood y' hH hα htip hβ).1 (hy'.2.trans hy0)
  · obtain ⟨ε, hε, hεy⟩ := hloc y hy
    obtain ⟨y', hy', hH, hα, htip, hβ⟩ := hside y (min ϱ (y + ε)) (lt_min hϱ (by linarith))
      (fun z hz => Or.inr ⟨hy0.trans hz.1, hz.2.trans_le (min_le_left _ _)⟩)
    have hd : dist y' y < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [min_le_right ϱ (y + ε), hy'.1, hy'.2]
    rw [← hεy y' hd]
    exact (hgood y' hH hα htip hβ).2 (hy0.trans hy'.1)

end OrdDet

end RLC

end InteractingSLE
