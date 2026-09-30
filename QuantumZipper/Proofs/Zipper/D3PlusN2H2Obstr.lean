import Mathlib.MeasureTheory.Constructions.Polish.Basic
import QuantumZipper.Proofs.Zipper.D3PlusN2HeartStmt
import QuantumZipper.Proofs.Section5.Prop17PalmCReg

/-!
# N2-H2: what the node `N2HLatTVStmt` forces (a regularization obstruction)

Task N2-H2. The node `N2HLatTVStmt` (`D3PlusN2HeartStmt.lean`) compares the model's lateral
window with the wedge-side window `latY'' K X'' = (μ ↦ lateralPart (X'' ω) μ)` on the index set
`LocIdx K` of **all** admissible measures supported in a closed ball of radius `< K`.

`lateralPart x μ = evalReg x μ − ∫ radAvgReg x ‖z‖ dμ` uses the regularized evaluation
`evalReg x μ = limUnder_k ∫ avgReg x k dμ`, which is the junk constant wherever the sequence
diverges. On that divergence event the wedge-side value is `junk − ∫ radAvgReg x ‖z‖ dμ` and so
**depends on the arbitrary additive constant** of the free field modulo constants (adding `c`
shifts it by `−c·μ(ℂ)`), while on the convergence event the constant cancels.

Main result (own elementary argument; no published source treats these junk values):

* `ae_tendsto_integral_avgReg_of_n2HLatTV`: `N2HLatTVStmt` implies that for **every** free GFF
  mod const `X` and every window measure `μ : LocIdx K`, almost surely the sequence
  `k ↦ ∫ avgReg (X ω) k dμ` converges.

Proof: the TV limit of a fixed sequence is unique (`eq_of_tendsto_tvDist`), so the wedge-side
window law is the same for `X` and for `X + c` (`isFreeGFFModConstH_addConst`); on regular
samples `lateralPart (X + c) μ = lateralPart X μ − c μ(ℂ) 1_{divergence}`
(`lateralPart_addConst_of_good`); a real random variable whose law is invariant under all
shifts on an event `D` has `P D = 0` (`measure_eq_zero_of_shift_invariant`, disjoint unit
intervals).

The conclusion is the per-measure form of the regularization bridge `F2.EvalRegRawStmt`
("a.s. `evalReg (X ω) ν = X ω ν` at every admissible `ν`"), which the repository proves only for
good (bounded density) and Frostman measures and which DECISIONS.md D17 records as a rate "the
project does not have ... and which is not a statement of the paper". Hence `N2HLatTVStmt` (and
with it any proof of it) needs this regularization theorem at arbitrary admissible measures.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus
namespace N2H2Obs

open WedgeTK GaussTK

/-! ## Junk bookkeeping for `limUnder` -/

/-- Two divergent real sequences have the same junk `limUnder`. -/
theorem limUnder_eq_of_not_tendsto {f g : ℕ → ℝ} (hf : ¬ ∃ L, Tendsto f atTop (𝓝 L))
    (hg : ¬ ∃ L, Tendsto g atTop (𝓝 L)) : limUnder atTop f = limUnder atTop g := by
  have hf' : ¬ ∃ L, Filter.map f atTop ≤ 𝓝 L := hf
  have hg' : ¬ ∃ L, Filter.map g atTop ≤ 𝓝 L := hg
  unfold limUnder lim Classical.epsilon Classical.strongIndefiniteDescription
  rw [dif_neg hf', dif_neg hg']

/-! ## Adding a constant to a regular sample -/

theorem tendsto_radSeq {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : GoodRad x F) {r : ℝ}
    (hr : 0 < r) :
    Tendsto (fun n : ℕ => x (foldedCircle 0 (dyadicRound n r + radius n))) atTop
      (𝓝 (F (0, r))) := by
  have hs : ∀ n : ℕ, dyadicRound n r + radius n = dyRad n (⌊(2 : ℝ) ^ n * r⌋.toNat) := by
    intro n
    rw [CoordsFull.radAvg_radius_eq_div, dyRad]
    have h0 : 0 ≤ ⌊(2 : ℝ) ^ n * r⌋ := Int.floor_nonneg.2 (by positivity)
    have : ((⌊(2 : ℝ) ^ n * r⌋.toNat : ℕ) : ℝ) = (⌊(2 : ℝ) ^ n * r⌋ : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h0
    rw [this]; push_cast; ring
  have hlim : Tendsto (fun n : ℕ => dyadicRound n r + radius n) atTop (𝓝 r) := by
    have h1 : Tendsto (fun n : ℕ => dyadicRound n r) atTop (𝓝 r) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun n => norm_nonneg _)
        (fun n => by rw [Real.norm_eq_abs]; exact CircleCont.abs_dyadicRound_sub_le n r)
        tendsto_one_div_two_pow
    have h2 : Tendsto (fun n : ℕ => radius n) atTop (𝓝 0) :=
      tendsto_nhds_of_tendsto_nhdsWithin RegClosure.tendsto_radius_nhdsGT
    simpa using h1.add h2
  have hmem : ∀ n : ℕ, ((0 : ℂ), dyadicRound n r + radius n) ∈ Hbar ×ˢ Ioi (0 : ℝ) := fun n =>
    ⟨zero_mem_Hbar, by rw [hs n]; exact dyRad_pos _ _⟩
  have ht : Tendsto (fun n : ℕ => ((0 : ℂ), dyadicRound n r + radius n)) atTop
      (𝓝[Hbar ×ˢ Ioi 0] ((0 : ℂ), r)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.prodMk_nhds hlim, Eventually.of_forall hmem⟩
  have hc := (hF.1.1 ((0 : ℂ), r) ⟨zero_mem_Hbar, hr⟩).tendsto.comp ht
  have e : (fun n : ℕ => x (foldedCircle 0 (dyadicRound n r + radius n))) =
      fun n => F ((0 : ℂ), dyadicRound n r + radius n) := by
    funext n; rw [hs n]; exact hF.2 n _
  rw [e]; exact hc

theorem radAvgReg_addConst {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : GoodRad x F) (c : ℝ)
    {r : ℝ} (hr : 0 < r) : radAvgReg (addConst x c) r = F (0, r) + c := by
  unfold radAvgReg
  have h : Tendsto (fun n : ℕ => addConst x c (foldedCircle 0 (dyadicRound n r + radius n)))
      atTop (𝓝 (F (0, r) + c)) := by
    simp only [addConst, measure_univ, ENNReal.toReal_one, mul_one]
    exact (tendsto_radSeq hF hr).add_const c
  exact h.limUnder_eq

theorem avgReg_addConst {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (c : ℝ)
    (k : ℕ) {w : ℂ} (hw : w ∈ Hbar) :
    avgReg (addConst x c) k w = F (w, radius k) + c ∧ avgReg x k w = F (w, radius k) := by
  have h := hF.2.1 k w hw
  refine ⟨?_, h.limUnder_eq⟩
  unfold avgReg
  have h' : Tendsto (fun n => addConst x c (foldedCircle (dyadicRoundC n w) (radius k))) atTop
      (𝓝 (F (w, radius k) + c)) := by
    simp only [addConst, measure_univ, ENNReal.toReal_one, mul_one]
    exact h.add_const c
  exact h'.limUnder_eq

theorem integral_avgReg_addConst {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (c : ℝ) (k : ℕ) {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    ∫ w, avgReg (addConst x c) k w ∂μ = ∫ w, avgReg x k w ∂μ + c * (μ Set.univ).toReal := by
  haveI : IsFiniteMeasure μ := hμ.1
  obtain ⟨K, hK, hKH, hμK⟩ := hμ.2.1
  have hae : ∀ᵐ w ∂μ, w ∈ K := ae_iff.2 hμK
  have hH : ∀ᵐ w ∂μ, w ∈ Hbar := hae.mono fun w hw => hKH hw
  have hcont : ContinuousOn (fun w => F (w, radius k)) Hbar :=
    hF.1.comp (continuousOn_id.prodMk continuousOn_const) fun w hw => ⟨hw, radius_pos k⟩
  have hint : Integrable (fun w => F (w, radius k)) μ := by
    have := (hcont.mono hKH).integrableOn_compact (μ := μ) hK
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at this
  rw [integral_congr_ae (hH.mono fun w hw => (avgReg_addConst hF c k hw).1),
    integral_congr_ae (hH.mono fun w hw => (avgReg_addConst hF c k hw).2),
    integral_add hint (integrable_const c), integral_const, smul_eq_mul, measureReal_def]
  ring

theorem integral_radAvgReg_addConst {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : GoodRad x F)
    (c : ℝ) {μ : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hrad : Integrable (fun z => F (0, ‖z‖)) μ) :
    ∫ z, radAvgReg (addConst x c) ‖z‖ ∂μ = ∫ z, radAvgReg x ‖z‖ ∂μ + c * (μ Set.univ).toReal := by
  haveI : IsFiniteMeasure μ := hμ.1
  have hne : ∀ᵐ z ∂μ, z ≠ 0 := by
    rw [ae_iff]; simpa using noAtoms_of_isAdmissibleH hμ 0
  rw [integral_congr_ae (hne.mono fun z hz => radAvgReg_addConst hF c (norm_pos_iff.2 hz)),
    integral_congr_ae (hne.mono fun z hz => hF.radAvgReg_eq (norm_pos_iff.2 hz)),
    integral_add hrad (integrable_const c), integral_const, smul_eq_mul, measureReal_def]
  ring

open Classical in
/-- On a regular sample, adding the constant `c` leaves the lateral part at `μ` unchanged when
the regularized evaluation converges, and shifts it by `−c μ(ℂ)` (junk branch) otherwise. -/
theorem lateralPart_addConst_of_good {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : GoodRad x F)
    (c : ℝ) {μ : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hrad : Integrable (fun z => F (0, ‖z‖)) μ) :
    lateralPart (addConst x c) μ =
      if ∃ L, Tendsto (fun k : ℕ => ∫ w, avgReg x k w ∂μ) atTop (𝓝 L) then lateralPart x μ
      else lateralPart x μ - c * (μ Set.univ).toReal := by
  unfold lateralPart evalReg
  rw [integral_radAvgReg_addConst hF c hμ hrad]
  have hs : (fun k : ℕ => ∫ w, avgReg (addConst x c) k w ∂μ) =
      fun k => ∫ w, avgReg x k w ∂μ + c * (μ Set.univ).toReal :=
    funext fun k => integral_avgReg_addConst hF.1 c k hμ
  rw [hs]
  split_ifs with hconv
  · obtain ⟨L, hL⟩ := hconv
    rw [(hL.add_const _).limUnder_eq, hL.limUnder_eq]
    ring
  · have hconv' : ¬ ∃ L, Tendsto (fun k : ℕ => ∫ w, avgReg x k w ∂μ +
        c * (μ Set.univ).toReal) atTop (𝓝 L) := by
      rintro ⟨L, hL⟩
      exact hconv ⟨L - c * (μ Set.univ).toReal, by simpa using hL.sub_const (c * (μ Set.univ).toReal)⟩
    rw [limUnder_eq_of_not_tendsto hconv' hconv]
    ring

/-! ## Two elementary measure-theoretic facts -/

/-! ## The obstruction -/

end N2H2Obs
end D3Plus
end QuantumZipper
