import QuantumZipper.Proofs.Zipper.SWCoreA8Path
import QuantumZipper.Proofs.LQG.RegularSample

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A8 (5): the flow distortion data along the independent Brownian driver

`a8_rand_data`: for a free field `X` and an independent Brownian motion `B`, almost surely, for
every horizon `N + 1`, every rational rectangle `[a₁,a₂] × [b₁,b₂] ⊂ ℍ`: eventually in `k`, for all
`t ≤ N + 1` and `z` in the rectangle, the smoothed pushed pairings along `f_t⁻¹` (driver
`drive κ B ω`) converge to the pushed `evalReg`, which is continuous in `z`; and for every
`η > 0`, eventually in `k`, the pushed value is `η`-close to the round value.

Proof: conditioning on the path (`CharFun.ae_indep`) of the good continuous version
(`CharFun.exists_good_version`, `pathC`), with the measurable countable event `a8Ev`
(`measurableSet_a8Ev`), its fixed-path fibre (`a8_fibre`, from the D64 primed core) and the
pathwise extension (`a8_path`); the driver agrees with `Wof (pathC …)` on `[0,T]`
(`RegUnif.drive_facts`) and the flow maps with it on `ℍ` (`RegCont.fwdMapInv_congr`).
Same scheme as `F1.xFlowGamUCQStmt_of_fixed` (XFlowUCTr). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace SWCore

open CharFun RegCont

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The conclusion of `a8_rand_data` for one driver, one horizon and one rectangle. -/
def A8Data (x : FieldSample) (W : ℝ → ℝ) (T : ℝ) (a₁ a₂ b₁ b₂ : ℝ) : Prop :=
  (∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) T,
    (∀ z ∈ rectC a₁ a₂ b₁ b₂, Tendsto (fun j => ∫ u, avgReg x j u
        ∂((foldedCircle z (radius k)).map (fwdMapInv W t))) atTop
        (𝓝 (evalReg x ((foldedCircle z (radius k)).map (fwdMapInv W t))))) ∧
    ContinuousOn (fun z => evalReg x ((foldedCircle z (radius k)).map (fwdMapInv W t)))
      (rectC a₁ a₂ b₁ b₂)) ∧
  ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ z ∈ rectC a₁ a₂ b₁ b₂,
    |evalReg x ((foldedCircle z (radius k)).map (fwdMapInv W t)) -
      evalReg x (foldedCircle (fwdMapInv W t z) (radius k * ‖deriv (fwdMapInv W t) z‖))| ≤ η

/-- `A8Data` only depends on the flow maps on `ℍ`. -/
theorem a8Data_congr {x : FieldSample} {W W' : ℝ → ℝ} {T : ℝ} {a₁ a₂ b₁ b₂ : ℝ}
    (hb : 0 < b₁) (h : ∀ t ∈ Icc (0 : ℝ) T, EqOn (fwdMapInv W t) (fwdMapInv W' t) H)
    (hD : A8Data x W' T a₁ a₂ b₁ b₂) : A8Data x W T a₁ a₂ b₁ b₂ := by
  have hmap : ∀ t ∈ Icc (0 : ℝ) T, ∀ (w : ℂ) (k : ℕ),
      (foldedCircle w (radius k)).map (fwdMapInv W t) =
        (foldedCircle w (radius k)).map (fwdMapInv W' t) := fun t ht w k =>
    Measure.map_congr ((TwoPoint.foldedCircle_ae_mem_H w (radius_pos k)).mono fun u hu =>
      h t ht hu)
  have hRH : rectC a₁ a₂ b₁ b₂ ⊆ H := a8_rect_H hb
  have hder : ∀ t ∈ Icc (0 : ℝ) T, ∀ z ∈ H, deriv (fwdMapInv W t) z = deriv (fwdMapInv W' t) z :=
    fun t ht z hz => Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (isOpen_H.mem_nhds hz) fun u hu => h t ht hu)
  obtain ⟨h1, h2⟩ := hD
  refine ⟨h1.mono fun k hk t ht => ⟨fun z hz => ?_, ?_⟩, fun η hη => ?_⟩
  · rw [hmap t ht z k]; exact (hk t ht).1 z hz
  · exact (hk t ht).2.congr fun z _ => by rw [hmap t ht z k]
  · filter_upwards [h2 η hη] with k hk t ht z hz
    rw [hmap t ht z k, h t ht (hRH hz), hder t ht z (hRH hz)]
    exact hk t ht z hz

/-- One horizon and one rectangle. -/
theorem a8_rand_one [IsProbabilityMeasure P] (κ : ℝ) {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (N : ℕ) {a₁ a₂ b₁ b₂ : ℚ} (h12 : (a₁ : ℝ) ≤ a₂) (hb : (0 : ℝ) < b₁) (hb12 : (b₁ : ℝ) ≤ b₂) :
    ∀ᵐ ω ∂P, A8Data (X ω) (drive κ B ω) (((N : ℚ) + 1 : ℚ) : ℝ) a₁ a₂ b₁ b₂ := by
  set Tq : ℚ := (N : ℚ) + 1 with hTq
  have hT' : (0 : ℝ) < (Tq : ℝ) := by rw [hTq]; push_cast; positivity
  set T : ℝ := (Tq : ℝ) with hTdef
  have hT0 : 0 ≤ T := hT'.le
  set E : Set (C(Icc (0 : ℝ) T, ℝ) × FieldSample) :=
    {p | p.1 ∉ GoodP hT0 (1 / 3)} ∪ {p | a8Ev κ hT0 a₁ a₂ b₁ b₂ p} with hE
  have hEm : MeasurableSet E :=
    ((measurableSet_GoodP hT0 (1 / 3)).compl.preimage measurable_fst).union
      (measurableSet_a8Ev κ hT0 a₁ a₂ b₁ b₂)
  have hfib : ∀ f : C(Icc (0 : ℝ) T, ℝ), ∀ᵐ ω ∂P, (f, X ω) ∈ E := by
    intro f
    by_cases hf : f ∈ GoodP hT0 (1 / 3)
    · filter_upwards [a8_fibre hX κ hT0 h12 hb hb12 hf] with ω hω using Or.inr hω
    · exact ae_of_all _ fun ω => Or.inl hf
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hpath : pathOf B =ᵐ[P] pathOf B' := hB'eq.mono fun ω h => funext fun t => (h t).symm
  have hind' : IndepFun (pathC T B' hB'c) X P :=
    indepFun_pathC T (hind.congr hpath (ae_eq_refl _)) hB'c
  have hEae := ae_indep (measurable_pathC T hB'm hB'c) hXm hind' hEm hfib
  filter_upwards [hEae, RegUnif.ae_pathC_good hB hB'c hB'eq hT', hB'eq,
    RegSample.ae_isRegularSample hX] with ω hω hgood heq hreg
  set f := pathC T B' hB'c ω with hfdef
  have hf0 : Wof κ T hT0 f 0 = 0 := Wof_zero_of_GoodP hT0 κ hgood
  obtain ⟨hdc, hd0, hEq⟩ := RegUnif.drive_facts κ hB'c hT' heq hf0
  rcases hω with hbad | hev
  · exact absurd hgood hbad
  obtain ⟨F, hF⟩ := hreg
  have hpd := a8_path κ (Tq := Tq) hT0 h12 hb hb12 hf0 hF hev
  exact a8Data_congr hb (fun t ht => fwdMapInv_congr hdc hd0 (continuous_Wof κ T hT0 f) hf0 hEq ht)
    hpd

/-- **The flow distortion data along the Brownian driver**, all horizons and rectangles. -/
theorem a8_rand_data [IsProbabilityMeasure P] (κ : ℝ) {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ N : ℕ, ∀ a₁ a₂ b₁ b₂ : ℚ, (a₁ : ℝ) ≤ a₂ → (0 : ℝ) < b₁ → (b₁ : ℝ) ≤ b₂ →
      A8Data (X ω) (drive κ B ω) (((N : ℚ) + 1 : ℚ) : ℝ) a₁ a₂ b₁ b₂ := by
  refine ae_all_iff.2 fun N => ae_all_iff.2 fun a₁ => ae_all_iff.2 fun a₂ =>
    ae_all_iff.2 fun b₁ => ae_all_iff.2 fun b₂ => ?_
  by_cases h : (a₁ : ℝ) ≤ a₂ ∧ (0 : ℝ) < b₁ ∧ (b₁ : ℝ) ≤ b₂
  · filter_upwards [a8_rand_one κ hB hX hind N h.1 h.2.1 h.2.2] with ω hω using
      fun _ _ _ => hω
  · exact ae_of_all _ fun ω h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h

end SWCore
end QuantumZipper
