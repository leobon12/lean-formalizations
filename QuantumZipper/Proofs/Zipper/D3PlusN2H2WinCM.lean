import QuantumZipper.Proofs.Zipper.D3PlusN2RWin
import QuantumZipper.Proofs.Zipper.D3PlusLSCZLoc
import QuantumZipper.Proofs.Zipper.D3PlusIRich
import QuantumZipper.Proofs.Zipper.D3PlusN2HeartMix
import QuantumZipper.Proofs.Zipper.D3PlusN2Cutoff
import QuantumZipper.Proofs.Zipper.D3PlusIMarkov

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2-H2 on the restricted index: the Cameron–Martin step (task N2H2-HARMWIN)

Reduces the model-side H2 node `N2H2HarmWinStmt` (`D3PlusN2RWin.lean`, Decision D36) to the
representation node `N2H2WinReprStmt` below, proving the whole Cameron–Martin / Markov part:

  `n2H2HarmWin_of_repr : N2H2WinReprStmt → N2H2HarmWinStmt`.

## The route (Duplantier–Miller–Sheffield, arXiv:1409.7055, proof of Prop. 4.7(ii), pp. 77–78)

Write the free field on the half-disc as `X = Z + h_X` (Markov decomposition, node L2), `Z` the
local field (`locZField X r`), `h_X` harmonic, `Z ⊥ h_X` (`K3.indep_markovZ_outside`). At scale
`a` the window of `X` is the window of `Z` shifted by the harmonic part; modulo the additive
constant `h_X(0)` (killed by the lateral part) the shift is `h = h_X − h_X(0)`, harmonic near `0`
and vanishing there. For fixed `ε` and all small `a`, both windows are one measurable map `G` of
the `ε`-local data of `Z` (resp. of `Z` plus the outside-measurable shift `b`), so by
independence and TV duality (`lscz_lintegral_shift_le`)

  `TV(law window(Z), law window(X)) ≤ E[min(1, TV(law Z|_ε, law Z|_ε + ∫ h_ω))]`,

and the right side tends to `0` as `ε → 0⁺` by the local Cameron–Martin bound
(`d3PlusIN2FixCMLoc_of_parts cmIncrStmt_holds n2Cutoff_holds`: Berestycki–Powell,
arXiv:2004.04720, Lemmas 3.12, 3.14, p. 79; cutoff energy `O(ε²)`, D24) and dominated
convergence for lower integrals (`tendsto_lintegral_of_ae_tendsto_nonmeas`). This is the argument
of `lscZeroGen_locFieldFull` (`D3PlusLSCZMain.lean`) with a random, a.s. admissible correction.

## The open representation node `N2H2WinReprStmt`

It collects the non-probabilistic bookkeeping of the step (all standard, see its docstring):
the harmonic part `hd` (`d3PlusN2HarmPart_holds` minus its value at `0`), the outside-measurable
shift `b` on the `ε`-local measures (`b μ = X(bal μ) − X(P_0)` at circles), and for small `a` the
measurable reader `G` (locality of `evalReg`/`lateralPart`: they read only dyadic folded circles
eventually inside `ball 0 ε`) with the a.s. identities on the model and the free side.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- The law of a measurable map, on a measurable set, as a lower integral of an indicator. -/
theorem map_apply_eq_lintegral_indicator_win {Ω β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] {P : Measure Ω} {f : Ω → β} (hf : Measurable f) {A : Set β}
    (hA : MeasurableSet A) : P.map f A = ∫⁻ ω, A.indicator 1 (f ω) ∂P := by
  rw [Measure.map_apply hf hA, ← lintegral_indicator_one (hf hA)]
  refine lintegral_congr fun ω => ?_
  by_cases h : f ω ∈ A
  · simp [h, Set.indicator_of_mem, Set.mem_preimage]
  · simp [h, Set.indicator_of_notMem, Set.mem_preimage]

/-- **TV of an independently shifted local reading** (Markov independence + TV duality;
`lscz_lintegral_shift_le` with an a.s. shift identity). -/
theorem tvDist_map_shift_le_win {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {r ε : ℝ}
    (hr : 0 < r) {E : Type*} [MeasurableSpace E] {G : (LocIdx ε → ℝ) → E} (hG : Measurable G)
    {b : Ω → LocIdx ε → ℝ} (hb : Measurable[K3.outsideSigma X 0 r] b)
    (sh : Ω → LocIdx ε → ℝ) (hsh : ∀ᵐ ω ∂P, ∀ v, G (v + b ω) = G (v + sh ω)) :
    TV.tvDist (P.map fun ω => G (resField ε (locZField X r ω)))
      (P.map fun ω => G (resField ε (locZField X r ω) + b ω)) ≤
    ∫⁻ ω, min (TV.tvDist (P.map fun ω' => resField ε (locZField X r ω'))
      (P.map fun ω' => resField ε (locZField X r ω') + sh ω)) 1 ∂P := by
  classical
  have hm : K3.outsideSigma X 0 r ≤ ‹MeasurableSpace Ω› :=
    (K3.outsideSigma_le_freeIncrSigma X 0 r).trans (freeIncrSigma_le hX)
  have hZ : Measurable (localZ X r) := measurable_localZ hX hr
  have hind : Indep (MeasurableSpace.comap (localZ X r) inferInstance)
      (K3.outsideSigma X 0 r) P := by
    have hL2 := K3.indep_markovZ_outside (t := 0) hX hr
    rw [← comap_localZ] at hL2
    exact hL2
  set ℓ : (LocIdx r → ℝ) → LocIdx ε → ℝ := fun s => resField ε (extLoc r s) with hℓ_def
  have hℓ : Measurable ℓ := (measurable_resField ε).comp (measurable_extLoc r)
  set a : Ω → LocIdx ε → ℝ := fun _ => 0 with ha_def
  have ha : Measurable[K3.outsideSigma X 0 r] a := measurable_const
  set sh' : Ω → LocIdx ε → ℝ := fun ω =>
    if (∀ v, G (v + a ω + b ω) = G (v + sh ω + a ω)) then sh ω else b ω with hsh'_def
  have hsh' : ∀ ω v, G (v + a ω + b ω) = G (v + sh' ω + a ω) := by
    intro ω v
    by_cases h : ∀ v, G (v + a ω + b ω) = G (v + sh ω + a ω)
    · simp only [hsh'_def, if_pos h]
      exact h v
    · simp only [hsh'_def, if_neg h]
      rw [add_right_comm]
  have hae : ∀ᵐ ω ∂P, sh' ω = sh ω := by
    filter_upwards [hsh] with ω hω
    have h : ∀ v, G (v + a ω + b ω) = G (v + sh ω + a ω) := fun v => by
      simpa [ha_def] using hω v
    simp only [hsh'_def, if_pos h]
  have hW : Measurable fun ω => resField ε (locZField X r ω) := hℓ.comp hZ
  have hWM : Measurable fun ω => G (resField ε (locZField X r ω)) := hG.comp hW
  have hWMb : Measurable fun ω => G (resField ε (locZField X r ω) + b ω) :=
    hG.comp (hW.add (hb.mono hm le_rfl))
  have hT : ∫⁻ ω, min (TV.tvDist (P.map fun ω' => ℓ (localZ X r ω'))
      (P.map fun ω' => ℓ (localZ X r ω') + sh' ω)) 1 ∂P =
      ∫⁻ ω, min (TV.tvDist (P.map fun ω' => resField ε (locZField X r ω'))
        (P.map fun ω' => resField ε (locZField X r ω') + sh ω)) 1 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω hω
    rw [hω]
    rfl
  have e1 : ∀ A : Set (E), (fun ω => A.indicator 1 (G (ℓ (localZ X r ω) + a ω + b ω))) =
      fun ω => A.indicator (1 : E → ℝ≥0∞) (G (resField ε (locZField X r ω) + b ω)) := by
    intro A
    funext ω
    simp only [ha_def, add_zero]
    rfl
  have e0 : ∀ A : Set (E), (fun ω => A.indicator 1 (G (ℓ (localZ X r ω) + a ω))) =
      fun ω => A.indicator (1 : E → ℝ≥0∞) (G (resField ε (locZField X r ω))) := by
    intro A
    funext ω
    simp only [ha_def, add_zero]
    rfl
  refine tvDist_le_of_forall_le (fun A hA => ?_) (fun A hA => ?_)
  all_goals
    have hΦ : Measurable[(K3.outsideSigma X 0 r).prod inferInstance]
        fun p : Ω × E => A.indicator (1 : E → ℝ≥0∞) p.2 :=
      (measurable_one.indicator hA).comp
        (@measurable_snd Ω E (K3.outsideSigma X 0 r) _)
    have h1 : ∀ p : Ω × E, A.indicator (1 : E → ℝ≥0∞) p.2 ≤ 1 := fun p => by
      by_cases h : p.2 ∈ A <;> simp [h]
    obtain ⟨k1, k2⟩ := lscz_lintegral_shift_le hm hZ hind hℓ hG ha hb sh' hsh' hΦ h1
    rw [map_apply_eq_lintegral_indicator_win hWM hA,
      map_apply_eq_lintegral_indicator_win hWMb hA, ← e1, ← e0, ← hT]
  · exact k2
  · exact k1

end D3Plus
end QuantumZipper
