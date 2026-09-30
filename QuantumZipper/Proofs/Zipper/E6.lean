import QuantumZipper.Proofs.Zipper.E6Omega
import QuantumZipper.Statements.ConfigLaw

/-!
# E6: length stationarity of `P_*` (abstract core)

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §E6; paper: Sheffield arXiv:1012.4797, proof of
Theorem 1.8, PDF p. 70 ("Since x was sampled uniformly from quantum measure ... must be invariant
under the operation of unzipping by a fixed quantity of quantum boundary length"). The paper gives
no details; this is the blueprint's argument (own formalization):

* `ℓ₀ := ℓ₁ e^{−C/2}`; the Palm point `x` is shifted left by `ν̃`-length `ℓ₀`
  (`ν̃ = ν + Leb|_{(−∞,−δ−1]}`, `E6Basic`), A6 (`PalmShift.ps_det_left`) costs `4ℓ₀` per `ω`;
* the identity `Z_C C̄_x ≈ zipLenDown γ ℓ₁ (Z_C C̄_{x_{ℓ₀}})` (hypothesis `hId`);
* the bad set costs `ℓ₀ + E[1{ν[−δ−1,−δ] ≤ ℓ₀} ν[−δ,0]] → 0`;
* E5 (hypothesis `hE5`, abstract form of `EPLAN2.E5Stmt`) at radii `R` and `R'`, and B5
  locality of `zipLenDown γ ℓ₁` (hypothesis `LocalAbs`), then `C → ∞`.

Everything random is abstract here: `ν` is a kernel (the Palm measure `nuPalm`, via NU-KER),
`hit ω` the collided points (`τ_x < T`), `z ω = zeroMinus V T`, `zc C ω x` the zoomed collided
configuration of E5, `c'` a sample of `P_*`, `loc R` the local data map of S5-TV.
The conclusion `e6_core` is the equality of all local laws (`∫⁻ Γ ∘ loc R`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper.E6

open PalmShift

/-- Configurations. -/
abbrev Cfg := FieldSample × (ℝ → ℝ)

variable {Ω : Type*} [MeasurableSpace Ω] {Ω' : Type*} [MeasurableSpace Ω']
  {L : Type*} [MeasurableSpace L]

/-- The un-normalized Palm integral of `f` over the collided points of `[−δ, 0]`. -/
def palmZ (P : Measure Ω) (ν : Kernel Ω ℝ) (δ : ℝ) (hit : Ω → Set ℝ) (zc : Ω → ℝ → Cfg)
    (f : Cfg → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, (hit ω).indicator (fun x => f (zc ω x)) x ∂ν ω ∂P

/-- `p = E ν{x ∈ [−δ,0] : τ_x < T}` (E5's `pm`). -/
def pmass (P : Measure Ω) (ν : Kernel Ω ℝ) (δ : ℝ) (hit : Ω → Set ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ν ω {x | x ∈ Icc (-δ) 0 ∧ x ∈ hit ω} ∂P

/-- Abstract E5 (the two-sided `ℝ≥0∞` TV-local form of `EPLAN2.E5Stmt`, with `nuPalm` a kernel). -/
def E5Abs (P : Measure Ω) (ν : Kernel Ω ℝ) (δ : ℝ) (hit : Ω → Set ℝ) (zc : ℝ → Ω → ℝ → Cfg)
    (P' : Measure Ω') (c' : Ω' → Cfg) (loc : ℕ → Cfg → L) : Prop :=
  ∀ R : ℕ, ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ C in atTop, ∀ Γ : L → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
    palmZ P ν δ hit (zc C) (fun y => Γ (loc R y)) ≤
        pmass P ν δ hit * ∫⁻ ω', Γ (loc R (c' ω')) ∂P' + η ∧
      pmass P ν δ hit * ∫⁻ ω', Γ (loc R (c' ω')) ∂P' ≤
        palmZ P ν δ hit (zc C) (fun y => Γ (loc R y)) + η

/-- Measurability of the inner Palm integral. -/
lemma measurable_inner (ν : Kernel Ω ℝ) [IsSFiniteKernel ν] (δ : ℝ) (hit : Ω → Set ℝ)
    (hHm : MeasurableSet {p : Ω × ℝ | p.2 ∈ hit p.1}) {f : Ω → ℝ → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) :
    Measurable fun ω => ∫⁻ x in Icc (-δ) 0, (hit ω).indicator (f ω) x ∂ν ω := by
  refine Measurable.setLIntegral_kernel_prod_right ?_ measurableSet_Icc
  have : Function.uncurry (fun ω => (hit ω).indicator (f ω)) =
      {p : Ω × ℝ | p.2 ∈ hit p.1}.indicator (Function.uncurry f) := by
    funext p; simp only [Function.uncurry, indicator]; rfl
  rw [this]; exact hf.indicator hHm

/-- The tail term `D(ℓ) = E[1{ν[−δ−1,−δ] ≤ ℓ} ν[−δ,0]]` is small for small `ℓ`. -/
lemma e6_D_small (P : Measure Ω) (ν : Kernel Ω ℝ) [IsSFiniteKernel ν] (δ : ℝ)
    (hpos : ∀ᵐ ω ∂P, ∀ x y, x < y → 0 < ν ω (Ioo x y))
    (hmass : ∫⁻ ω, ν ω (Icc (-δ) 0) ∂P ≠ ∞) {u : ℝ≥0∞} (hu : 0 < u) :
    ∃ ℓs : ℝ≥0, 0 < ℓs ∧
      ∫⁻ ω, {ω | ν ω (Icc (-δ - 1) (-δ)) ≤ ℓs}.indicator (fun ω => ν ω (Icc (-δ) 0)) ω ∂P ≤ u := by
  set m := P.withDensity fun ω => ν ω (Icc (-δ) 0)
  have hmeas1 : Measurable fun ω => ν ω (Icc (-δ - 1) (-δ)) := ν.measurable_coe measurableSet_Icc
  set s : ℕ → Set Ω := fun n => {ω | ν ω (Icc (-δ - 1) (-δ)) ≤ ((1 : ℝ≥0) / (n + 1) : ℝ≥0)}
  have hs : ∀ n, MeasurableSet (s n) := fun n => measurableSet_le hmeas1 measurable_const
  have hanti : Antitone s := by
    intro n k hnk ω hω
    refine (show ν ω (Icc (-δ - 1) (-δ)) ≤ _ from hω).trans (ENNReal.coe_le_coe.mpr ?_)
    gcongr
  have hfin : m (s 0) ≠ ∞ := by
    rw [withDensity_apply _ (hs 0)]
    exact ne_top_of_le_ne_top hmass (setLIntegral_le_lintegral _ _)
  have hlim := tendsto_measure_iInter_atTop (μ := m) (fun n => (hs n).nullMeasurableSet) hanti
    ⟨0, hfin⟩
  have hnull : m (⋂ n, s n) = 0 := by
    refine withDensity_absolutelyContinuous P _ ?_
    refine measure_mono_null (t := {ω | ¬ ∀ x y, x < y → 0 < ν ω (Ioo x y)}) ?_ (ae_iff.mp hpos)
    intro ω hω hgood
    have h0 : ν ω (Icc (-δ - 1) (-δ)) = 0 := by
      refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      refine (mem_iInter.mp hω n).trans ?_
      simp only [zero_add, ENNReal.coe_le_coe]
      rw [← NNReal.coe_le_coe]; push_cast; exact hn.le
    have := hgood (-δ - 1) (-δ) (by linarith)
    exact absurd (h0 ▸ measure_mono (μ := ν ω) Ioo_subset_Icc_self) (not_le.mpr this)
  rw [hnull] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hu)).exists
  refine ⟨(1 : ℝ≥0) / (n + 1), by positivity, ?_⟩
  rw [lintegral_indicator (hs n)]
  simpa [m, withDensity_apply _ (hs n)] using hn.le

/-- The tail term `D(ℓ)`. -/
def tailD (P : Measure Ω) (ν : Kernel Ω ℝ) (δ : ℝ) (ℓ : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ ω, {ω | ν ω (Icc (-δ - 1) (-δ)) ≤ ℓ}.indicator (fun ω => ν ω (Icc (-δ) 0)) ω ∂P

lemma tailD_mono (P : Measure Ω) (ν : Kernel Ω ℝ) (δ : ℝ) {ℓ ℓ' : ℝ≥0} (h : ℓ ≤ ℓ') :
    tailD P ν δ ℓ ≤ tailD P ν δ ℓ' := by
  refine lintegral_mono fun ω => indicator_le_indicator_of_subset (fun ω' hω' => ?_) (by simp) ω
  exact (show ν ω' (Icc (-δ - 1) (-δ)) ≤ _ from hω').trans (by exact_mod_cast h)

end QuantumZipper.E6
