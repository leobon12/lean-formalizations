/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLvPinchUse
import InteractingSLE.Spec.Supplement.SBTail2EraseStep
import InteractingSLE.Spec.Supplement.SBLwShift
import InteractingSLE.Spec.Supplement.SBLxSucc

/-!
# SB2(1)'s chain record at one horizon: the geometric clauses

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half). The geometric clauses of the S2 chain record
(`Lv.IsSB2LineChain` / the per-time `Tc.IsSB2LineChainAt`) at ONE sample, in the coordinates shifted by the upper
seed `u`, from:

* the retained prefix path `p` from `u` (`Lx.IsPrefixPath`, almost surely `Lv.ae_isPrefixPath_launch`);
* the shifted launch chart as a left entry chart, with a boundary map `g`;
* S1 for the upper flow up to a physical horizon `T` (`IsOneSided A η T`, from `SB2LaunchProblem.one_sided`);
* the entrance `T_L = firstVisit η ζ L` before `T`, with no common arc with `A` and no real arc on `(T_L, T)`.

Results:

* `firstVisit_eq_of_injective`: the visit time of an injective witness that agrees with the flow before the horizon
  is the flow's first visit;
* `exists_shifted_witness`: S1's witness translated by `−u` (a proper curve from `0`, prefix on its closed right
  side, equal to `η − u` up to `T`);
* `IsSB2RelChain.mono`: a relative chain on `[0, S₁]` is one on every `[0, S₀]`, `S₀ ≤ S₁`;
* **`exists_geomRecord`**: the shifted prefix path, the witness `β'` with its visit time `t_L = T_L`, the proper
  S2 lift `γ`, the agreement with `η − u` before `t_L + S₁`, one relative chain `(Wr, ηr)` for every `S₀ < S₁`, and no
  real arc on `(0, S₁)`, for every `0 < S₁` with `T_L + S₁ < T`. One application of
  `Lv.exists_relConfig_of_path_of_finite` at a horizon beyond `S₁` gives a single chain (no gluing).

Deterministic in the data; nothing here replaces a source statement (S1 and the arc conditions are hypotheses, as in
`exists_relConfig_of_path_of_finite`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Tc

open Lv

/-! ### The first visit of an injective witness -/

/-- **The visit time of an injective witness is the flow's first visit**: if `β'` is injective, agrees with `η − u`
before the horizon `T`, and visits `L − u` at `t_L < T` with `t_L ≤ ζ`, then `t_L` is the first visit of `L` by `η`
before `ζ`. -/
theorem firstVisit_eq_of_injective {β' η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {u : ℝ} {L : ℂ} {T tL : ℝ≥0}
    (hinj : Function.Injective β') (hagree : ∀ t : ℝ≥0, t < T → β' t = η t - u) (hvis : β' tL = L - u)
    (htT : tL < T) (htζ : (tL : ℝ≥0∞) ≤ ζ) : ((tL : ℝ≥0) : ℝ≥0∞) = firstVisit η ζ L := by
  have hηL : η tL = L := by
    have h := hagree tL htT
    rw [hvis] at h
    linear_combination -h
  refine le_antisymm (le_iInf₂ fun s hs => ?_) (iInf₂_le tL ⟨htζ, hηL⟩)
  rcases lt_or_ge s T with hsT | hsT
  · have hβs : β' s = β' tL := by rw [hagree s hsT, hs.2, hvis]
    rw [hinj hβs]
  · exact ENNReal.coe_le_coe.2 (htT.le.trans hsT)

/-! ### The shifted S1 witness -/

/-- **S1's witness in the shifted coordinates**: a proper curve from `0` with the shifted prefix on its closed right
side, equal to `η − u` up to the horizon. -/
theorem exists_shifted_witness {A : Set ℂ} {η : ℝ≥0 → ℂ} {T : ℝ≥0} {u : ℝ} (h : IsOneSided A η T)
    (hη0 : η 0 = u) :
    ∃ β' : ℝ≥0 → ℂ, Supp9B.IsProperCurve β' ∧ β' 0 = 0 ∧
      (fun z => z - (u : ℂ)) '' A ⊆ Supp9B.closedRightSide β' ∧ ∀ t ≤ T, β' t = η t - u := by
  obtain ⟨β', ⟨hc, hi, him, hp, he⟩, hA⟩ := Erase.isOneSided_add_real h (-u)
  have he' : ∀ t ≤ T, β' t = η t - u := fun t ht => by
    rw [he t ht]; push_cast; ring
  refine ⟨β', ⟨hc, hi, him, hp⟩, by rw [he' 0 zero_le, hη0, sub_self], ?_, he'⟩
  have e : (fun z => z - (u : ℂ)) '' A = (· + ((-u : ℝ) : ℂ)) '' A := by
    refine image_congr fun z _ => ?_
    push_cast; ring
  rw [e]
  exact hA

/-! ### Monotonicity of the relative chain -/

/-- **A relative chain on `[0, S₁]` is a relative chain on every `[0, S₀]`, `S₀ ≤ S₁`.** -/
theorem IsSB2RelChain.mono {A : Set ℂ} {c : Chart} {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ S₁ : ℝ} {Wr : ℝ → ℝ}
    {ηr : ℝ → ℂ} (h : FinRel.IsSB2RelChain A c β' γ tL S₁ Wr ηr) (hS : S₀ ≤ S₁) :
    FinRel.IsSB2RelChain A c β' γ tL S₀ Wr ηr := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hsub : Icc (0 : ℝ) S₀ ⊆ Icc 0 S₁ := Icc_subset_Icc_right hS
  exact ⟨h1, h2, h3, h4, h5.mono hsub, h6.mono hsub, fun s hs => h7 s (hsub hs)⟩

/-! ### The geometric record at one horizon -/

/-- **The geometric clauses of SB2(1)'s chain record at one horizon** (one sample, shifted coordinates): from the
prefix path `p` from `u`, the shifted launch chart `shiftChart c u m` as a left entry chart with boundary map `g`, S1
up to the horizon `T`, the entrance `T_L < T` and the no-common-arc / no-real-arc conditions on `(T_L, T)`, for every
`0 < S₁` with `T_L + S₁ < T`: the shifted prefix path, the witness with its visit at `t_L = T_L`, the S2 lift, the
agreement with the shifted flow before `t_L + S₁`, one relative chain for all `S₀ < S₁`, no real arc on `(0, S₁)`. -/
theorem exists_geomRecord {p : ℝ → ℂ} {u m : ℝ} {A : Set ℂ} {c : Chart} {g : ℂ → ℂ} {η : ℝ≥0 → ℂ}
    {ζ : ℝ≥0∞} {T : ℝ≥0} (hp : Lx.IsPrefixPath p u A)
    (hc : IsLeftEntryChart ((fun s => p s - u) '' Icc 0 1) (realMin ((fun s => p s - u) '' Icc 0 1))
      (Lw.shiftChart c u m))
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g (Lw.shiftChart c u m).2.1 H)
    (hS1 : IsOneSided A η T) (hη0 : η 0 = u)
    (hvis : firstVisit η ζ (realMin A) < T)
    (hnA : interior {r ∈ Ioo (0 : ℝ) ((T : ℝ) - (firstVisit η ζ (realMin A)).toReal) |
      η ((firstVisit η ζ (realMin A)).toNNReal + r.toNNReal) ∈ closure A} = ∅)
    (hnR : interior {r ∈ Ioo (0 : ℝ) ((T : ℝ) - (firstVisit η ζ (realMin A)).toReal) |
      (η ((firstVisit η ζ (realMin A)).toNNReal + r.toNNReal)).im = 0} = ∅)
    {S₁ : ℝ} (hS₁ : 0 < S₁) (hS₁T : (firstVisit η ζ (realMin A)).toReal + S₁ < T) :
    ∃ (β' γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
      (ContinuousOn (fun s => p s - u) (Icc 0 1) ∧ (fun s => p s - u) 0 = 0 ∧
        (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ ((fun s => p s - u) s).im) ∧
        (∀ z, ((fun s => p s - u) ⁻¹' {z} ∩ Icc 0 1).Finite) ∧
        (fun s => p s - u) '' Icc 0 1 = (fun z => z - (u : ℂ)) '' A) ∧
      (Supp9B.IsProperCurve β' ∧ β' 0 = 0 ∧ (fun s => p s - u) '' Icc 0 1 ⊆ Supp9B.closedRightSide β' ∧
        β' tL = realMin ((fun s => p s - u) '' Icc 0 1) ∧ ((tL : ℝ≥0) : ℝ≥0∞) = firstVisit η ζ (realMin A) ∧
        Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧ ∀ s, g (γ s) = β' (tL + s)) ∧
      (∀ t : ℝ≥0, (t : ℝ) < (tL : ℝ) + S₁ → β' t = η t - u) ∧
      ((∀ S₀ : ℝ, 0 ≤ S₀ → S₀ < S₁ →
          FinRel.IsSB2RelChain ((fun s => p s - u) '' Icc 0 1) (Lw.shiftChart c u m) β' γ tL S₀ Wr ηr) ∧
        interior {r ∈ Ioo (0 : ℝ) S₁ | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅) := by
  obtain ⟨hpc, hp0, hpf, hpH, hpA⟩ := hp
  set p' : ℝ → ℂ := fun s => p s - u with hp'
  set L : ℝ := realMin A with hL
  set TL : ℝ≥0∞ := firstVisit η ζ (realMin A) with hTL
  -- the prefix, shifted
  have hp'c : ContinuousOn p' (Icc 0 1) := hpc.sub continuousOn_const
  have hp'0 : p' 0 = 0 := by simp [hp', hp0]
  have hp'H : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p' s).im := fun s hs => by simpa [hp'] using hpH s hs
  have hp'f : ∀ z, (p' ⁻¹' {z} ∩ Icc 0 1).Finite := fun z => by
    have e : p' ⁻¹' {z} = p ⁻¹' {z + u} := by
      ext s; simp only [mem_preimage, mem_singleton_iff, hp']
      exact ⟨fun h => by rw [← h]; ring, fun h => by rw [h]; ring⟩
    rw [e]; exact hpf (z + u)
  have hp'A : p' '' Icc 0 1 = (fun z => z - (u : ℂ)) '' A := by
    rw [← hpA, image_image]
  -- the realMin of the shifted prefix
  have hAcpt : IsCompact A := hpA ▸ isCompact_Icc.image_of_continuousOn hpc
  have huA : ((u : ℝ) : ℂ) ∈ A := hpA ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, hp0⟩
  have hbdd : BddBelow {x : ℝ | (x : ℂ) ∈ A} := by
    obtain ⟨R, hR⟩ := hAcpt.isBounded.subset_closedBall 0
    refine ⟨-R, fun x hx => ?_⟩
    have h1 := hR hx
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at h1
    linarith [neg_abs_le x]
  have hmin : realMin (p' '' Icc 0 1) = L - u := by
    rw [hp'A]; exact Lw.realMin_image_sub u ⟨u, huA⟩ hbdd
  -- the witness
  obtain ⟨β', hβ', hβ'0, hβ'A, hβ'η⟩ := exists_shifted_witness hS1 hη0
  have hβ'A' : p' '' Icc 0 1 ⊆ Supp9B.closedRightSide β' := hp'A ▸ hβ'A
  -- the entrance: a visit `s < T`, which is the first visit
  obtain ⟨s, hs⟩ := iInf_lt_iff.1 hvis
  obtain ⟨⟨hsζ, hsη⟩, hsT⟩ := iInf_lt_iff.1 hs
  have hsT' : s < T := ENNReal.coe_lt_coe.1 hsT
  have hβs : β' s = ((L : ℂ) - (u : ℂ)) := by rw [hβ'η s hsT'.le, hsη]
  have hβs' : β' s = realMin (p' '' Icc 0 1) := by rw [hβs, hmin]; push_cast; ring
  have hTLs : TL = s :=
    (firstVisit_eq_of_injective hβ'.2.1 (fun t ht => hβ'η t ht.le) hβs hsT' hsζ).symm
  have hTLr : TL.toReal = s := by rw [hTLs]; rfl
  have hTLn : TL.toNNReal = s := by rw [hTLs]; rfl
  have honly : ∀ t : ℝ≥0, β' t = realMin (p' '' Icc 0 1) → t = s := fun t ht =>
    hβ'.2.1 (ht.trans hβs'.symm)
  -- the relative configuration at the horizon `S = T − s`
  set S : ℝ := (T : ℝ) - s with hS
  have hS₁S : S₁ < S := by rw [hS]; rw [hTLr] at hS₁T; linarith
  have hsr : ∀ r : ℝ, r ∈ Ioo (0 : ℝ) S → s + r.toNNReal < T := fun r hr => by
    rw [← NNReal.coe_lt_coe, NNReal.coe_add, Real.coe_toNNReal _ hr.1.le]
    have := hr.2; rw [hS] at this; linarith
  have hclA : IsClosed A := hAcpt.isClosed
  have hcl' : IsClosed (p' '' Icc 0 1) := (isCompact_Icc.image_of_continuousOn hp'c).isClosed
  have hnA' : ∀ t : ℝ≥0, β' t = realMin (p' '' Icc 0 1) →
      interior {r ∈ Ioo (0 : ℝ) S | β' (t + r.toNNReal) ∈ closure (p' '' Icc 0 1)} = ∅ := by
    intro t ht
    rw [honly t ht]
    refine subset_empty_iff.1 (hnA ▸ interior_mono fun r hr => ⟨?_, ?_⟩)
    · rw [hTLr]; exact hr.1
    · have h1 := hr.2
      rw [hcl'.closure_eq, hp'A, hβ'η _ (hsr r hr.1).le] at h1
      obtain ⟨z, hz, hze⟩ := h1
      rw [hTLn, hclA.closure_eq]
      have : z = η (s + r.toNNReal) := by linear_combination hze
      exact this ▸ hz
  have hnR' : ∀ t : ℝ≥0, β' t = realMin (p' '' Icc 0 1) →
      interior {r ∈ Ioo (0 : ℝ) S | β' (t + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅ := by
    intro t ht
    rw [honly t ht]
    refine subset_empty_iff.1 (hnR ▸ interior_mono fun r hr => ⟨?_, ?_⟩)
    · rw [hTLr]; exact hr.1
    · have h1 : (β' (s + r.toNNReal)).im = 0 := hr.2
      rw [hβ'η _ (hsr r hr.1).le] at h1
      rw [hTLn]
      simpa using h1
  obtain ⟨tL, γ, htL, -, hγ, hγ0, hlift, Wr, ηr, hchain⟩ :=
    exists_relConfig_of_path_of_finite hp'c hp'0 hp'f hp'H hβ' hβ'0 hβ'A' hc hgc hgi hS₁.le hS₁S hnA' hnR'
  have htLs : tL = s := honly tL htL
  subst htLs
  refine ⟨β', γ, tL, Wr, ηr, ⟨hp'c, hp'0, hp'H, hp'f, hp'A⟩,
    ⟨hβ', hβ'0, hβ'A', htL, hTLs.symm, hγ, hγ0, hlift⟩, fun t ht => hβ'η t ?_,
    ⟨fun S₀ _ hS₀ => IsSB2RelChain.mono hchain hS₀.le, ?_⟩⟩
  · have h1 : (t : ℝ) < T := by rw [hTLr] at hS₁T; linarith
    exact (NNReal.coe_lt_coe.1 h1).le
  · refine subset_empty_iff.1 (hnR' tL htL ▸ interior_mono fun r hr => ⟨⟨hr.1.1, hr.1.2.trans hS₁S⟩, hr.2⟩)

end InteractingSLE.Theorem14.SB.Tc
