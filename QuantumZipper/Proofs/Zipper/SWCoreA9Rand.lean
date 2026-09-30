import QuantumZipper.Proofs.Zipper.SWCoreA9Ev

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A9 (2): offset flow distortion data along the independent Brownian driver

`a9_rand_data`: for a free field `X` and an independent Brownian motion `B`, almost surely, for
every horizon `N + 1` and every rational rectangle `[a₁,a₂] × [b₁,b₂] ⊂ ℍ`: for every `η > 0`,
eventually in `k`, for all rational `q ∈ [0,N+1]`, rational `α ∈ [1,2]` and rational centres `z`
in the rectangle, the smoothed pairings on `fc(z, α 2^{-k}).map f_q⁻¹` converge to the pushed
`evalReg`, which is `η`-close to the round value at radius `α 2^{-k} |(f_q⁻¹)'(z)|`.

Sheffield–Wang (arXiv:1605.06171, proof of Thm 1.4, (3.5)–(3.7)): the radius `ε` is a continuous
parameter there, so the offsets `α 2^{-k}` are in the paper. Own bookkeeping, mirrors
`SWCoreA8Path`/`SWCoreA8Rand` with the radius factor of the D64 family `a7Rad`; only rational
parameters are needed, so no continuity extension is used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace SWCore

open CharFun RegCont

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Offset flow distortion data at rational parameters (radius `α 2^{-k}`, `α ∈ [1,2]`). -/
def A9Data (x : FieldSample) (W : ℝ → ℝ) (T : ℝ) (A B C D : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T →
    ∀ α : ℚ, (α : ℝ) ∈ Icc (1 : ℝ) 2 → ∀ z : ℚ × ℚ, zQ z ∈ rectC A B C D →
      Tendsto (fun j => ∫ u, avgReg x j u
          ∂((foldedCircle (zQ z) ((α : ℝ) * radius k)).map (fwdMapInv W q))) atTop
        (𝓝 (evalReg x ((foldedCircle (zQ z) ((α : ℝ) * radius k)).map (fwdMapInv W q)))) ∧
      |evalReg x ((foldedCircle (zQ z) ((α : ℝ) * radius k)).map (fwdMapInv W q)) -
        evalReg x (foldedCircle (fwdMapInv W q (zQ z))
          ((α : ℝ) * radius k * ‖deriv (fwdMapInv W q) (zQ z)‖))| ≤ η

/-- `A9Data` only depends on the flow maps on `ℍ`. -/
theorem a9Data_congr {x : FieldSample} {W W' : ℝ → ℝ} {T : ℝ} {A B C D : ℝ}
    (hb : 0 < C) (h : ∀ t ∈ Icc (0 : ℝ) T, EqOn (fwdMapInv W t) (fwdMapInv W' t) H)
    (hD : A9Data x W' T A B C D) : A9Data x W T A B C D := by
  intro η hη
  filter_upwards [hD η hη] with k hk q hq α hα z hz
  have hα0 : (0 : ℝ) < α := by linarith [hα.1]
  have hmap : (foldedCircle (zQ z) ((α : ℝ) * radius k)).map (fwdMapInv W q) =
      (foldedCircle (zQ z) ((α : ℝ) * radius k)).map (fwdMapInv W' q) :=
    Measure.map_congr ((TwoPoint.foldedCircle_ae_mem_H _ (mul_pos hα0 (radius_pos k))).mono
      fun u hu => h q hq hu)
  have hzH : zQ z ∈ H := a8_rect_H hb hz
  have hder : deriv (fwdMapInv W q) (zQ z) = deriv (fwdMapInv W' q) (zQ z) :=
    Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (isOpen_H.mem_nhds hzH) fun u hu => h q hq hu)
  rw [hmap, h q hq hzH, hder]
  exact hk q hq α hα z hz

/-- **Pathwise step**: the countable event gives the data for the driver `Wof f`. -/
theorem a9_path (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) {A B C D : ℚ} (hC : (0 : ℝ) < C)
    {f : C(Icc (0 : ℝ) T, ℝ)} (hf0 : Wof κ T hT f 0 = 0) {x : FieldSample}
    (hE : a9Ev κ hT A B C D (f, x)) : A9Data x (Wof κ T hT f) T A B C D := by
  intro η hη
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
  obtain ⟨K₀, hK₀⟩ := hE.1
  obtain ⟨K, hK⟩ := hE.2 n
  refine eventually_atTop.2 ⟨max K₀ K, fun k hk q hq α hα z hz => ?_⟩
  have hα0 : (0 : ℝ) < α := by linarith [hα.1]
  have hzH : zQ z ∈ H := a8_rect_H hC hz
  set ν := (foldedCircle (zQ z) ((α : ℝ) * radius k)).map (fwdMapInv (Wof κ T hT f) q)
    with hν
  have hΦ : ∀ j, a9Phi κ hT j k α q hq.1 (zQ z) (f, x) = ∫ u, avgReg x j u ∂ν := fun j =>
    a9Phi_eq hf0 hq j k hα0 _ x
  have hcs : CauchySeq fun j => ∫ u, avgReg x j u ∂ν := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨J, hJ⟩ := hK₀ k (le_of_max_le_left hk) m
    exact ⟨J, fun j hj => by
      rw [Real.dist_eq, ← hΦ, ← hΦ]
      exact (hJ j hj J le_rfl q hq α hα z hz).trans_lt hm⟩
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  have e : evalReg x ν = L := hL.limUnder_eq
  rw [e, ← a9Rd_eq hf0 hq k α hzH x]
  refine ⟨hL, ?_⟩
  obtain ⟨J, hJ⟩ := hK k (le_of_max_le_right hk)
  have ht := (hL.sub_const (a9Rd κ hT k α q hq.1 (zQ z) (f, x))).abs
  refine (le_of_tendsto ht (eventually_atTop.2 ⟨J, fun j hj => ?_⟩)).trans hn.le
  show |(∫ u, avgReg x j u ∂ν) - _| ≤ _
  rw [← hΦ]
  exact hJ j hj q hq α hα z hz

/-- One horizon and one rectangle. -/
theorem a9_rand_one [IsProbabilityMeasure P] (κ : ℝ) {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (N : ℕ) {a₁ a₂ b₁ b₂ : ℚ} (h12 : (a₁ : ℝ) ≤ a₂) (hb : (0 : ℝ) < b₁) (hb12 : (b₁ : ℝ) ≤ b₂) :
    ∀ᵐ ω ∂P, A9Data (X ω) (drive κ B ω) (((N : ℚ) + 1 : ℚ) : ℝ) a₁ a₂ b₁ b₂ := by
  set Tq : ℚ := (N : ℚ) + 1 with hTq
  have hT' : (0 : ℝ) < (Tq : ℝ) := by rw [hTq]; push_cast; positivity
  set T : ℝ := (Tq : ℝ) with hTdef
  have hT0 : 0 ≤ T := hT'.le
  set E : Set (C(Icc (0 : ℝ) T, ℝ) × FieldSample) :=
    {p | p.1 ∉ GoodP hT0 (1 / 3)} ∪ {p | a9Ev κ hT0 a₁ a₂ b₁ b₂ p} with hE
  have hEm : MeasurableSet E :=
    ((measurableSet_GoodP hT0 (1 / 3)).compl.preimage measurable_fst).union
      (measurableSet_a9Ev κ hT0 a₁ a₂ b₁ b₂)
  have hfib : ∀ f : C(Icc (0 : ℝ) T, ℝ), ∀ᵐ ω ∂P, (f, X ω) ∈ E := by
    intro f
    by_cases hf : f ∈ GoodP hT0 (1 / 3)
    · filter_upwards [a9_fibre hX κ hT0 h12 hb hb12 hf] with ω hω using Or.inr hω
    · exact ae_of_all _ fun ω => Or.inl hf
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hpath : pathOf B =ᵐ[P] pathOf B' := hB'eq.mono fun ω h => funext fun t => (h t).symm
  have hind' : IndepFun (pathC T B' hB'c) X P :=
    indepFun_pathC T (hind.congr hpath (ae_eq_refl _)) hB'c
  have hEae := ae_indep (measurable_pathC T hB'm hB'c) hXm hind' hEm hfib
  filter_upwards [hEae, RegUnif.ae_pathC_good hB hB'c hB'eq hT', hB'eq] with ω hω hgood heq
  set f := pathC T B' hB'c ω with hfdef
  have hf0 : Wof κ T hT0 f 0 = 0 := Wof_zero_of_GoodP hT0 κ hgood
  obtain ⟨hdc, hd0, hEq⟩ := RegUnif.drive_facts κ hB'c hT' heq hf0
  rcases hω with hbad | hev
  · exact absurd hgood hbad
  exact a9Data_congr hb (fun t ht => fwdMapInv_congr hdc hd0 (continuous_Wof κ T hT0 f) hf0 hEq ht)
    (a9_path κ hT0 hb hf0 hev)

/-- **The offset flow distortion data along the Brownian driver**, all horizons and
rectangles, at rational parameters. -/
theorem a9_rand_data [IsProbabilityMeasure P] (κ : ℝ) {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ N : ℕ, ∀ a₁ a₂ b₁ b₂ : ℚ, (a₁ : ℝ) ≤ a₂ → (0 : ℝ) < b₁ → (b₁ : ℝ) ≤ b₂ →
      A9Data (X ω) (drive κ B ω) (((N : ℚ) + 1 : ℚ) : ℝ) a₁ a₂ b₁ b₂ := by
  refine ae_all_iff.2 fun N => ae_all_iff.2 fun a₁ => ae_all_iff.2 fun a₂ =>
    ae_all_iff.2 fun b₁ => ae_all_iff.2 fun b₂ => ?_
  by_cases h : (a₁ : ℝ) ≤ a₂ ∧ (0 : ℝ) < b₁ ∧ (b₁ : ℝ) ≤ b₂
  · filter_upwards [a9_rand_one κ hB hX hind N h.1 h.2.1 h.2.2] with ω hω using
      fun _ _ _ => hω
  · exact ae_of_all _ fun ω h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h

end SWCore
end QuantumZipper
