/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71PBranch
import InteractingSLE.Spec.Sec7.Lemma71NMain

/-!
# Lemma 7.1's (CS), geometric half, almost surely on every pocket construction

Packet PROVE-LEMMA71P (specification Remark 6.7, `source/spec/p145-192.md` L566–L590; Lemma 7.1,
`source/spec/p193-240.md` L576–L606; supplement §2.3). On every pocket construction over a three-curve space
(`Lemma72B.IsThreeCurveSpace`, `Lemma71K.IsPocketConstruction`) with capacity data `G, M, Y`
(`Lemma71L.exists_capData`) and a branch shift that is almost surely the inherited branch, at every capacity time `t`,
almost surely on `{t < capLife}`, at every chart point `x` of `(L_t − W_t, 0) ∪ (0, R_t − W_t)` (in the coordinates of
`Lemma71N.PocketCurveSideStatement`):

* (CS-a) the inverse chart of the active component lands at a middle-curve point `γ(s)` with `s` strictly before the
  capacity stop `τ_t`; hence `γ(s) ∈ A ∪ ℝ` and the complete union `AL` lies in `A` near `γ(s)`;
* (CS-branch) for every driver `W^γ` generating `γ` and every `q` with `s < q ≤ τ_t`,
  `pocketLift ∘ pocketInv − Im log g^γ_q′ ∘ pocketInv → 0`;
* (CS-G) the seed function `pocketG` tends to `−λ` (`x < 0`) or `λ` (`x > 0`).

Main result: **`ae_curveSideGeom`**. With CS-prob (`vL + u₀ + χ · Im log g^γ_q′ → ∓λ` approaching `γ(s)` from the
corresponding side, for rational `q > s`; packet PROVE-LEMMA71Q) this gives `Lemma71N.PocketCurveSideStatement`:
`vL + u₀ − Gl = (vL + u₀ + χ Im log g^γ_q′) − G + χ (pocketLift − Im log g^γ_q′)`, for one rational `q ∈ (s, τ_t]`.
No named input; R43/R48: nothing here uses Theorems 1.2–1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Lemma71P

open QuantumZipper (H Hbar chiC fwdMap fwdMapInv fwdHull logDerivFwd)
open QuantumZipper.CA (cayley cayleyInv)
open Lemma71C Lemma71K Lemma71L Sec6 LocalSets
open MartChar Lemma71M Lemma71E Lemma71D Coupling Lemma71G
open Lemma71N (IsPocketFrame IsPocketBranch)

/-! ### Generating traces of the three curves -/

/-- A flow line from `0` with infinite lifetime almost surely has a driver generating it on `[0, ∞)`. -/
theorem ae_exists_isGeneratingTrace {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {κ θ : ℝ} {bd : ℝ → ℝ}
    {J : Finset ℝ} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine κ bd J 0 θ P h η ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ∀ᵐ ω ∂P, ∃ W' : ℝ≥0 → ℝ, IsGeneratingTrace W' ⊤ (η ω) := by
  obtain ⟨_, _, W, _, _, _, -, -, htr⟩ := hfl
  filter_upwards [htr, hζ] with ω h1 h2
  refine ⟨fun t => W t ω, ?_⟩
  rw [h2] at h1
  simpa only [Complex.ofReal_zero, sub_zero] using h1

/-! ### The pathwise pocket data -/

section Seg

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ θ₁ θ₂ a b : ℝ}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}
  {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}

/-- **Almost surely the pocket data of the middle curve hold** (`IsPocketSeg`, with the visit clock), together with
the good event `PocketGood`. -/
theorem ae_isPocketSeg (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    (hpc : IsPocketConstruction P β α γ C c γ') :
    ∀ᵐ ω ∂P, PocketGood β α γ C c γ' ω ∧ ∃ (a' b' : ℝ) (Ψ : ℂ → ℂ),
      IsPocketSeg (β ω) (α ω) (γ ω) (C ω) (c ω) Ψ a' b' (γ' ω) (visitClock (γ ω) (closure (cayley '' C ω))) := by
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, hβ62, hα62, hγ62, hae⟩ := hS'
  obtain ⟨-, -, him3, -, -, -, -⟩ := Lemma71G.IsLemma62Curve.three hβ62 hα62 hγ62
  have hpc' := hpc
  obtain ⟨hC, -, hconf, hdom, -, -, -, hlog, hbetw, hfr, hsegc, -, hmark⟩ := hpc'
  filter_upwards [ae_pocketGood hS hpc, hae, hbetw, hfr, hmark] with ω hg hω hbω hfrω hmω
  obtain ⟨-, -, -, -, -, -, hβα, hsβ, hsα, hsγ, hord, -, -⟩ := hω
  obtain ⟨a', b', Ψ, hMk, hΨc, hΨi, hΨH, hΨ0, hΨtop, hΨe, hseg, hrange⟩ := hmω
  have hF : IsPocketFrame (β ω) (α ω) (C ω) (c ω) Ψ a' b' :=
    ⟨hsβ, hsα, hβα, hbω, hMk, hconf ω, hdom ω, hΨc, hΨi, hΨH, hΨ0, hΨtop, hΨe, hfrω⟩
  have hCo : IsOpen (C ω) := (hC ω).1
  have hCH : C ω ⊆ H := (hC ω).2.2.2
  have hγH : ∀ t, γ ω t ∈ Hbar := fun t => him3 2 ω t
  obtain ⟨hvc, hcay, -, -, -⟩ := hg.visit hCo hCH (hconf ω) (hdom ω) hγH
  obtain ⟨-, hκm, hκ0, -, -, -⟩ := hvc
  have hγα : Disjoint (range (γ ω)) (rightSideOf (range (α ω))) := by
    have h := hord.right_middle
    rwa [Lemma71I.arcRange_realPath, Lemma71I.arcRange_realPath] at h
  exact ⟨hg, a', b', Ψ, ⟨hF, hsγ, hγα, hlog ω, hsegc ω, hseg, hrange, hκm, hκ0, hcay⟩⟩

omit mΩ in
/-- **The capacity stopping time is the visit-clock time of the capacity inverse** at positive capacity times (the
equality case of `Lemma71N.capTime_le_visit`). -/
theorem capTime_eq_visit {G : (Hist × Hist) × ℂ → ℂ} {M : Set ((Hist × Hist) × ℂ)} {Y : Hist × Hist → ℂ}
    {ω : Ω} (hg : PocketGood β α γ C c γ' ω) (hCo : IsOpen (C ω)) (hCH : C ω ⊆ H)
    (hc : (c ω).IsConformal) (hdom : ((c ω).dom : Set ℂ) = C ω) (hγH : ∀ t, γ ω t ∈ Hbar)
    (hγc : Continuous (γ ω)) (hΓ : IsSegCurve (γ' ω))
    (hMiff : ∀ z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω) (hGeq : ∀ z ∈ C ω, G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : Y (outerHist β α ω) = closePt α C ω) {t : ℝ≥0} (ht0 : 0 < t) (htl : (t : ℝ≥0∞) < capLife (γ' ω)) :
    capTime G M Y β α γ t ω = ENNReal.ofReal (visitClock (γ ω) (closure (cayley '' C ω)) (capInv (γ' ω) t)) := by
  obtain ⟨hvc, -, -, hD1, -⟩ := hg.visit hCo hCH hc hdom hγH
  rw [← hYeq] at hD1
  have hFc : ContinuousOn (c ω).1 (C ω) := by rw [← hdom]; exact hc.differentiableOn_fwd.continuousOn
  have htl' : ENNReal.ofReal (t : ℝ) < capLife (γ' ω) := by rwa [ENNReal.ofReal_coe_nnreal]
  exact capRule_eq_visitClock hMiff hGeq hCo hFc hγc hΓ hvc hD1 (NNReal.coe_pos.2 ht0) htl'

end Seg

/-! ### The main statement -/

section Main

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ θ₁ θ₂ a b : ℝ}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}
  {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}

/-- **Lemma 7.1's (CS), geometric half (CS-a, CS-branch, CS-G), almost surely.** On every pocket construction over a
three-curve space with capacity data and a branch shift that is almost surely the inherited branch, at every capacity
time `t`, almost surely on `{t < capLife}`: at every chart point `x ∈ (L_t − W_t, 0) ∪ (0, R_t − W_t)` there is a
middle-curve time `s` strictly before the capacity stop `τ_t = capTime G M Y β α γ t` such that

* the inverse chart of the active component tends to `γ(s)` at `x`, `γ(s) ∈ A ∪ ℝ`, and `AL ∩ B(γ(s), r) ⊆ A` for some
  `r > 0` (`A` the explored set of the stopped three curves, `AL` that of the complete three curves);
* for every driver `W^γ` generating `γ` on `[0, ∞)` and every `q` with `s < q ≤ τ_t`,
  `pocketLift ∘ pocketInv − Im log g^γ_q′ ∘ pocketInv → 0` at `x` (the shifted chart, `a' = 0`);
* `pocketG → −λ` at `x < 0` and `→ λ` at `x > 0` (marks `cpf2RhoL κ θ₂`, `cpf2RhoR κ θ₁`, `a' = 0`). -/
theorem ae_curveSideGeom (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    (hpc : IsPocketConstruction P β α γ C c γ') {G : (Hist × Hist) × ℂ → ℂ} {M : Set ((Hist × Hist) × ℂ)}
    {Y : Hist × Hist → ℂ} (hMiff : ∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z) (hYeq : ∀ ω, Y (outerHist β α ω) = closePt α C ω)
    {n : Ω → ℤ} (hN : ∀ᵐ ω ∂P, IsPocketBranch (β ω) (α ω) (c ω) (n ω)) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < capLife (γ' ω) → ∀ x : ℝ,
      (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL 0 t ω - segDriver (γ' ω) t < x ∧ x < 0) ∨
        (0 < x ∧ x < geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR 0 t ω - segDriver (γ' ω) t) →
      ∃ s : ℝ≥0, (s : ℝ≥0∞) < capTime G M Y β α γ t ω ∧
        Tendsto (pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t) (𝓝[H] (x : ℂ))
          (𝓝 (γ ω s)) ∧
        γ ω s ∈ explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω ∪
          {z : ℂ | z.im = 0} ∧
        (∃ r > 0, explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω ∩ ball (γ ω s) r ⊆
          explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω) ∧
        (∀ Wγ : ℝ≥0 → ℝ, IsGeneratingTrace Wγ ⊤ (γ ω) → ∀ q : ℝ≥0, s < q →
          (q : ℝ≥0∞) ≤ capTime G M Y β α γ t ω →
          Tendsto (fun y => pocketLift (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t
              (pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t y) -
            (logDerivFwd (fun r : ℝ => Wγ r.toNNReal) q
              (pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t y)).im) (𝓝[H] (x : ℂ))
            (𝓝 0)) ∧
        Tendsto (pocketG κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁)
            (fun s => segDriver (γ' ω) s)
            (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
            (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) t 0) (𝓝[H] (x : ℂ))
          (𝓝 (if x < 0 then -sleLambda κ else sleLambda κ)) := by
  have hS' := hS
  obtain ⟨-, -, -, hβfl, hαfl, -, hβ62, hα62, hγ62, hae⟩ := hS'
  obtain ⟨hc3, -, him3, -, -, -, -⟩ := Lemma71G.IsLemma62Curve.three hβ62 hα62 hγ62
  have hpc' := hpc
  obtain ⟨hC, -, hconf, hdom, -, -, -, -, -, -, hsegc, -, -⟩ := hpc'
  have hζβ : ∀ᵐ ω ∂P, ζβ ω = ⊤ := hae.mono fun ω hω => hω.1
  have hζα : ∀ᵐ ω ∂P, ζα ω = ⊤ := hae.mono fun ω hω => hω.2.1
  filter_upwards [ae_isPocketSeg hS hpc, hN, ae_exists_isGeneratingTrace hβfl hζβ,
    ae_exists_isGeneratingTrace hαfl hζα] with ω ⟨hg, a', b', Ψ, hP⟩ hNω ⟨Wβ, htrβ⟩ ⟨Wα, htrα⟩ htl x hx
  set w : ℝ≥0 → ℝ := fun s => segDriver (γ' ω) s with hwdef
  have hCo : IsOpen (C ω) := (hC ω).1
  have hCH : C ω ⊆ H := (hC ω).2.2.2
  have hγc : Continuous (γ ω) := hc3 2 ω
  have hγH : ∀ t, γ ω t ∈ Hbar := fun t => him3 2 ω t
  -- the setting at time `t`
  obtain ⟨W, hW, hW0, hWe, η, hη, hηe⟩ := exists_loewnerTrace hP.seg htl
  have hT : IsTSetting (β ω) (α ω) (γ ω) (C ω) (c ω) Ψ a' b' (γ' ω)
      (visitClock (γ ω) (closure (cayley '' C ω))) (n ω) W η t := ⟨hP, hNω, htl, hW, hW0, hWe, hη, hηe⟩
  have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
  -- the middle chart points
  have hWt : w t = W t := by
    have := hWe ⟨ht0, le_rfl⟩
    simp only [Ito.rpath, Real.toNNReal_coe] at this
    exact this.symm
  have hR' : RealFlow.rightImg (Ito.rpath w) 0 t = RealFlow.rightImg W 0 t :=
    Lemma71B.rightImg_congr hW ht0 (fun r hr => (hWe hr).symm) 0
  have hL' : RealFlow.rightImg (fun s => -Ito.rpath w s) 0 t = RealFlow.rightImg (fun s => -W s) 0 t :=
    Lemma71B.rightImg_congr hW.neg ht0 (fun r hr => by show -Ito.rpath w r = -W r; rw [hWe hr]) 0
  have hvL : (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω) 0 t - w t = midL W t := by
    have e : (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω) 0 t =
        -RealFlow.rightImg (fun s => -Ito.rpath (fun s => segDriver (γ' ω) s) s) 0 t := by
      simp only [geomL, LP.twoSeedXL, neg_zero]
      rfl
    rw [e, hL', hWt]
    rfl
  have hvR : (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) 0 t - w t = midR W t := by
    have e : (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) 0 t =
        RealFlow.rightImg (Ito.rpath fun s => segDriver (γ' ω) s) 0 t := by
      simp only [geomR, LP.twoSeedXR]
      rfl
    rw [e, hR', hWt]
    rfl
  have hxm : midL W t < x ∧ x < midR W t ∧ x ≠ 0 := by
    have hmL := midL_nonpos hW ht0
    have hmR := midR_nonneg hW ht0
    rcases hx with hx | hx
    · refine ⟨?_, by linarith [hx.2], hx.2.ne⟩
      have := hx.1; rw [← hvL]; exact this
    · refine ⟨by linarith [hx.1], ?_, hx.1.ne'⟩
      have := hx.2; rw [← hvR]; exact this
  obtain ⟨hxL, hxR, hx0⟩ := hxm
  -- CS-a
  obtain ⟨σ, hσ, hTσ, u, hu0, hut, -, -⟩ := hT.exists_land hxL hxR hx0
  have htpos : 0 < t := by
    rcases eq_zero_or_pos t with h0 | h0
    · exfalso
      have hd := PocketTraversal.isDrivenCurve_of_isSegCurve hP.seg
      rw [h0, NNReal.coe_zero, hd.capInv_of_nonpos le_rfl] at hut
      linarith
    · exact h0
  have hτ := capTime_eq_visit (G := G) (M := M) (Y := Y) hg hCo hCH (hconf ω) (hdom ω) hγH hγc hP.seg (hMiff ω)
    (hGeq ω) (hYeq ω) htpos htl
  have hτ' : capTime G M Y β α γ t ω = (hT.capT : ℝ≥0∞) := by
    rw [hτ, ← hT.capT_eq, ENNReal.ofReal_coe_nnreal]
  obtain ⟨-, -, hinv, -⟩ := tChart_facts (hconf ω) hP.seg htl hW hW0 hWe (n ω)
  have hTσ' : Tendsto (pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t) (𝓝[H] (x : ℂ))
      (𝓝 (γ ω σ)) := hTσ.congr' (eventually_nhdsWithin_of_forall fun y hy => (hinv y hy).symm)
  refine ⟨σ, by rw [hτ']; exact_mod_cast hσ, hTσ', ?_, ?_, ?_, ?_⟩
  · rw [Three.explored_threeStops]
    by_cases hσH : γ ω σ ∈ H
    · exact Or.inl ⟨Or.inr ⟨σ, by rw [hτ']; exact_mod_cast hσ.le, rfl⟩, hσH⟩
    · exact Or.inr (le_antisymm (not_lt.1 hσH) (hγH σ))
  · obtain ⟨ρ, hρ, hball⟩ := Lemma71N.exists_ball_tail hP.hγ hσ
    refine ⟨ρ, hρ, ?_⟩
    rw [Three.explored_threeTop, Three.explored_threeStops]
    rintro z ⟨⟨(hz | hz) | ⟨v, rfl⟩, hzH⟩, hzb⟩
    · exact ⟨Or.inl (Or.inl hz), hzH⟩
    · exact ⟨Or.inl (Or.inr hz), hzH⟩
    · have hv : v < hT.capT := by
        by_contra hle
        exact hball v (not_lt.1 hle) hzb
      exact ⟨Or.inr ⟨v, by rw [hτ']; exact_mod_cast hv.le, rfl⟩, hzH⟩
  · intro Wγ htrγ q hsq hqτ
    have hqT : q ≤ hT.capT := by rw [hτ'] at hqτ; exact_mod_cast hqτ
    exact hT.tendsto_pocketLift_sub htrβ htrα htrγ hxL hxR hx0 hTσ' hsq hqT
  · refine tendsto_pocketG_mid κ (cpf2RhoL κ θ₂) (cpf2RhoR κ θ₁) w _ _ t ?_ ?_ hx
    · rw [hvL]; exact midL_nonpos hW ht0
    · rw [hvR]; exact midR_nonneg hW ht0

end Main

/-! ### Assembly with the probabilistic half -/

section Assembly

theorem coe_coe_nnrat (q : ℚ≥0) : (((q : ℝ≥0)) : ℝ) = ((q : ℚ) : ℝ) := by
  rw [NNRat.cast_def, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast, Rat.cast_def, NNRat.num_coe,
    NNRat.den_coe]
  push_cast
  rfl

/-- A nonnegative rational strictly after `s` and not after `τ`, when `s < τ`. -/
theorem exists_nnrat_btwn {s : ℝ≥0} {τ : ℝ≥0∞} (hs : (s : ℝ≥0∞) < τ) :
    ∃ q : ℚ≥0, s < (q : ℝ≥0) ∧ (((q : ℝ≥0)) : ℝ≥0∞) ≤ τ := by
  obtain ⟨r, hr0, hsr, hrτ⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hs
  have h : (((r.toNNRat : ℚ≥0) : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal r := by
    rw [ENNReal.ofReal]
    congr 1
    ext
    rw [coe_coe_nnrat, Rat.coe_toNNRat r hr0, Real.coe_toNNReal _ (by exact_mod_cast hr0)]
  refine ⟨r.toNNRat, ?_, by rw [h]; exact hrτ.le⟩
  rw [← ENNReal.coe_lt_coe, h]
  exact hsr

/-- **`PocketCurveSide` from its geometric and probabilistic halves** (pathwise algebra:
`vL + u₀ − (G − k·lift) = (vL + u₀ + k·Lq) − G + k·(lift − Lq)`, at one rational time `q ∈ (s, τ]`). -/
theorem pocketCurveSide_of_parts {A AL : Set ℂ} {vL u₀ : ℂ → ℝ} {Finv : ℂ → ℂ} {Gs lift : ℂ → ℝ}
    {Lq : ℝ≥0 → ℂ → ℝ} {γ : ℝ≥0 → ℂ} {τ : ℝ≥0∞} {xL xR lam k : ℝ}
    (hgeom : ∀ x : ℝ, (xL < x ∧ x < 0) ∨ (0 < x ∧ x < xR) → ∃ s : ℝ≥0, (s : ℝ≥0∞) < τ ∧
      Tendsto Finv (𝓝[H] (x : ℂ)) (𝓝 (γ s)) ∧ γ s ∈ A ∪ {z : ℂ | z.im = 0} ∧
      (∃ r > 0, AL ∩ ball (γ s) r ⊆ A) ∧
      (∀ q : ℝ≥0, s < q → (q : ℝ≥0∞) ≤ τ →
        Tendsto (fun y => lift (Finv y) - Lq q (Finv y)) (𝓝[H] (x : ℂ)) (𝓝 0)) ∧
      Tendsto Gs (𝓝[H] (x : ℂ)) (𝓝 (if x < 0 then -lam else lam)))
    (hprob : ∀ x : ℝ, (xL < x ∧ x < 0) ∨ (0 < x ∧ x < xR) → ∀ s : ℝ≥0,
      Tendsto Finv (𝓝[H] (x : ℂ)) (𝓝 (γ s)) → (s : ℝ≥0∞) < τ → ∀ q : ℚ≥0, s < (q : ℝ≥0) →
      (((q : ℝ≥0)) : ℝ≥0∞) ≤ τ →
      Tendsto (fun y => vL (Finv y) + u₀ (Finv y) + k * Lq q (Finv y)) (𝓝[H] (x : ℂ))
        (𝓝 (if x < 0 then -lam else lam))) :
    Lemma71N.PocketCurveSide A AL vL u₀ Finv (fun y => Gs y - k * lift (Finv y)) xL xR := by
  intro x hx
  obtain ⟨s, hsτ, hland, hA, hAL, hbr, hG⟩ := hgeom x hx
  obtain ⟨q, hsq, hqτ⟩ := exists_nnrat_btwn hsτ
  refine ⟨γ s, hland, hA, hAL, ?_⟩
  have h1 := hprob x hx s hland hsτ q hsq hqτ
  have h2 := hbr q hsq hqτ
  have h := (h1.sub hG).add (h2.const_mul k)
  rw [sub_self, mul_zero, add_zero] at h
  refine h.congr fun y => ?_
  ring

open LQGMetric (DistOn TestOn) in
/-- **Named input (CS-prob): the probabilistic half of (CS)** (Remark 6.7; packet PROVE-LEMMA71Q): on every pocket
construction over a three-curve space with capacity data and an almost surely inherited branch shift, at every
capacity time `t` and for every version `gL` of the mean of the complete three curves, almost surely on
`{t < capLife}`, for every harmonic representative `vL` of `gL`, every driver `W^γ` generating `γ`, every middle chart
point `x` at which the inverse chart of the active component lands at `γ(s)` with `s` before the capacity stop, and
every rational `q ∈ (s, τ_t]`: `vL + u₀ + χ · Im log g^γ_q′ → −λ` (`x < 0`) or `λ` (`x > 0`) along the inverse chart
(Proposition 3.8/3.9 and the single-curve heights of `γ([0, q])`, approached from the corresponding side of `γ`). -/
def PocketCurveProbStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ a b : ℝ, θ₁ < 0 → 0 < θ₂ →
    sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a → sleLambda κ - θ₁ * chiC κ ≤ b →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β α γ : Ω → ℝ≥0 → ℂ) (ζβ ζα ζγ : Ω → ℝ≥0∞),
      Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ →
    ∀ (C : Ω → Set ℂ) (c : Ω → Chart) (γ' : Ω → ℝ → ℂ), IsPocketConstruction P β α γ C c γ' →
    ∀ (G : (Hist × Hist) × ℂ → ℂ) (M : Set ((Hist × Hist) × ℂ)) (Y : Hist × Hist → ℂ),
      Measurable G → MeasurableSet M → Measurable Y → (∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω) →
      (∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z) → (∀ ω, Y (outerHist β α ω) = closePt α C ω) →
    ∀ n : Ω → ℤ, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n →
      (∀ᵐ ω ∂P, IsPocketBranch (β ω) (α ω) (c ω) (n ω)) →
    ∀ (t : ℝ≥0) (gL : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL →
      ∀ᵐ ω ∂P, (t : ℝ≥0∞) < capLife (γ' ω) → ∀ vL : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd vL (H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) →
        (∀ ψ : TestOn upperHalfPlaneOpens,
          tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω → gL ω ψ = ∫ x, vL x * ψ x) →
        ∀ Wγ : ℝ≥0 → ℝ, IsGeneratingTrace Wγ ⊤ (γ ω) →
        ∀ x : ℝ, (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL 0 t ω - segDriver (γ' ω) t < x ∧ x < 0) ∨
            (0 < x ∧ x < geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR 0 t ω - segDriver (γ' ω) t) →
        ∀ s : ℝ≥0, Tendsto (pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t) (𝓝[H] (x : ℂ))
            (𝓝 (γ ω s)) →
          (s : ℝ≥0∞) < capTime G M Y β α γ t ω → ∀ q : ℚ≥0, s < (q : ℝ≥0) →
          (((q : ℝ≥0)) : ℝ≥0∞) ≤ capTime G M Y β α γ t ω →
          Tendsto (fun y => vL (pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t y) +
              u₀ (pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t y) +
              chiC κ * (logDerivFwd (fun r : ℝ => Wγ r.toNNReal) ((q : ℝ≥0) : ℝ)
                (pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t y)).im) (𝓝[H] (x : ℂ))
            (𝓝 (if x < 0 then -sleLambda κ else sleLambda κ))

/-- **(CS) from its probabilistic half**: `Lemma71N.PocketCurveSideStatement` follows from
`PocketCurveProbStatement` and the geometric half proved here (`ae_curveSideGeom`, `pocketCurveSide_of_parts`). -/
theorem pocketCurveSideStatement_of_prob (hprob : PocketCurveProbStatement.{u}) :
    Lemma71N.PocketCurveSideStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ a b hθ₁ hθ₂ ha hb Ω _ P _ h u₀ β α γ ζβ ζα ζγ hS C c γ' hpc G M Y hG hM hY hMiff hGeq hYeq
    n hn hN t gL hgL
  have hgeom := ae_curveSideGeom hS hpc hMiff hGeq hYeq hN t
  have hpr := hprob κ hκ hκ4 θ₁ θ₂ a b hθ₁ hθ₂ ha hb P h u₀ β α γ ζβ ζα ζγ hS C c γ' hpc G M Y hG hM hY hMiff hGeq
    hYeq n hn hN t gL hgL
  have hS' := hS
  obtain ⟨-, -, -, -, -, hγfl, -, -, -, hae⟩ := hS'
  have hζγ : ∀ᵐ ω ∂P, ζγ ω = ⊤ := hae.mono fun ω hω => hω.2.2.1
  filter_upwards [hgeom, hpr, ae_exists_isGeneratingTrace hγfl hζγ] with ω hgω hpω ⟨Wγ, htrγ⟩ htl vL hvL hgvL
  refine pocketCurveSide_of_parts (Lq := fun q z => (logDerivFwd (fun r : ℝ => Wγ r.toNNReal) q z).im)
    (fun x hx => ?_) (fun x hx s hland hsτ q hsq hqτ => hpω htl vL hvL hgvL Wγ htrγ x hx s hland hsτ q hsq hqτ)
  obtain ⟨s, hsτ, hland, hA, hAL, hbr, hG⟩ := hgω htl x hx
  exact ⟨s, hsτ, hland, hA, hAL, hbr Wγ htrγ, hG⟩

end Assembly

end InteractingSLE.Sec7.Lemma71P
