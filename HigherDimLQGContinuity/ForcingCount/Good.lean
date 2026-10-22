import HigherDimLQGContinuity.ForcingCount.Bumps
import HigherDimLQGMetric.Sec8.Geod
import HigherDimLQGMetric.Sec10.Lemma101
import HigherDimLQGMetric.Metric.WeylAxioms

/-!
# The almost-sure good event of the count

Packet Q9. Part B `b:lem-lowmult`/`b:lem-upcount` work "on the a.s. event where Lemma `b:lem-site-normal` holds for all
sites of the catalogue and all (finitely many) `f_Z`, all metrics `ρ^D_{H ± f_Z}`, `ρ^E_{H ± f_Z}` are length metrics
with canonical geodesics, and axiom (III) holds". This file defines that event (`CountGood`) and proves that it has
full `pinLaw d 10`-measure (`ae_countGood`), from the strong axioms (I) and (III), the library's properness of
subcritical strong metrics (`lemma27_proper` through `lemma101`) with its bounded-Weyl transfer
(`sec8_proper_of_bounded_weyl`), and the a.s. convergence of sphere averages of the whole-space LGF.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-- All labelled sites of a catalogue: `𝒵 × Λ`. -/
def countUnivSites (K : CountData d) (𝔆 : Catalogue d) : Finset (Rd d × K.cat.Label) :=
  𝔆.Z ×ˢ (@Finset.univ K.cat.Label K.cat.fintypeLabel)

/-- The good properties of one input field: length metrics, a canonical geodesic of the primary, and Weyl scaling
(axiom (III)) of both normalized metrics for all continuous functions and open sets. -/
def q9GoodInput (K : CountData d) (H : DistRd d) : Prop :=
  (rho K.D H).IsLength ∧ (rho K.E H).IsLength ∧ (∃ γ, IsConstSpeedGeod (rho K.D H) K.x K.y γ) ∧
    (∀ (g : C(Rd d, ℝ)) (U : Set (Rd d)), IsOpen U → ∀ u v : Rd d,
      (rho K.D (addFun H g)).internal U u v = weylScaleOn K.ξ g (rho K.D H) U u v) ∧
    (∀ (g : C(Rd d, ℝ)) (U : Set (Rd d)), IsOpen U → ∀ u v : Rd d,
      (rho K.E (addFun H g)).internal U u v = weylScaleOn K.η g (rho K.E H) U u v)

/-- The good event of the count: every modified field `H ± f_W` (`W ⊆ 𝒵 × Λ`) is a good input, and the sphere averages
of `H` converge at every site of the catalogue. -/
def CountGood (K : CountData d) (𝔆 : Catalogue d) (H : DistRd d) : Prop :=
  (∀ W ∈ (countUnivSites K 𝔆).powerset, q9GoodInput K (addFun H (selBump K 𝔆.s W)) ∧
      q9GoodInput K (addFun H (-selBump K 𝔆.s W))) ∧
    ∀ z ∈ 𝔆.Z, ∃ a, Tendsto (sphereAvgSeq H 𝔆.s z) atTop (𝓝 a)

theorem q9_isLength_rho {D : DistRd d → ContMetric d} {H : DistRd d} (h : (D H).IsLength) :
    (rho D H).IsLength :=
  ContMetric.isLength_smul _ h

theorem q9_rho_internal_weyl {D : DistRd d → ContMetric d} {ξ : ℝ} {X : DistRd d} {g : C(Rd d, ℝ)}
    {U : Set (Rd d)} {u v : Rd d}
    (h : (D (addFun X g)).internal U u v = weylScaleOn ξ g (D X) U u v) :
    (rho D (addFun X g)).internal U u v = weylScaleOn ξ g (rho D X) U u v := by
  unfold rho
  rw [ContMetric.internal_smul, h, weylScaleOn_smul]

/-- Every input `H + f` with a bounded deterministic `f` is good, `pinLaw d 10`-a.s. -/
theorem q9_ae_goodInput (hd : 3 ≤ d) (K : CountData d) (hξ : 0 < K.ξ)
    (hQ : Real.sqrt (2 * d) < distExp d K.ξ)
    (hD : IsStrongExpMetric d K.ξ (distExp d K.ξ) K.D) (hE : IsStrongExpMetric d K.η (distExp d K.η) K.E)
    {f : C(Rd d, ℝ)} {B : ℝ} (hf : ∀ x, |f x| ≤ B) :
    ∀ᵐ H ∂(pinLaw d 10), q9GoodInput K (addFun H f) := by
  have hd2 : 2 ≤ d := by omega
  have := isProbabilityMeasure_pinLaw (d := d) hd2 10
  have hh : IsWholeSpaceLGF (id : DistRd d → DistRd d) (pinLaw d 10) :=
    (isWholeSpaceLGF_pinLaw hd2 (by norm_num : (0 : ℝ) < 10)).1
  have hh' : IsLGFPlusCont (fun H : DistRd d => addFun (id H) f) (pinLaw d 10) :=
    hh.isLGFPlusCont.addFun measurable_const
  have hsharp := lemma101 hd2 hξ hD
  filter_upwards [hD.length _ _ hh', hE.length _ _ hh', hD.length _ _ hh.isLGFPlusCont,
    lemma27_proper hd hξ hQ hsharp (pinLaw d 10) id hh, hD.weyl _ _ hh.isLGFPlusCont,
    hD.ae_internal_eq_weylScaleOn hh', hE.ae_internal_eq_weylScaleOn hh'] with
    H hlD hlE hl0 hprop hwD0 hwD hwE
  simp only [id_eq] at hlD hlE hl0 hprop hwD0 hwD hwE
  refine ⟨q9_isLength_rho hlD, q9_isLength_rho hlE, ?_, fun g U hU u v => q9_rho_internal_weyl (hwD g U hU u v),
    fun g U hU u v => q9_rho_internal_weyl (hwE g U hU u v)⟩
  have : ProperSpace (K.D H).Space := hprop
  have hW : IsWeylOf K.ξ f (K.D H) (K.D (addFun H f)) := fun u v => (hwD0 f u v).symm
  have ha : ∀ x, -(K.ξ * B) ≤ K.ξ * f x := by
    intro x
    have h1 := (abs_le.1 (hf x)).1
    nlinarith
  have hb : ∀ x, K.ξ * f x ≤ K.ξ * B := by
    intro x
    have h1 := (abs_le.1 (hf x)).2
    nlinarith
  have : ProperSpace (K.D (addFun H f)).Space :=
    sec8_proper_of_bounded_weyl (K.D H) _ hl0 K.ξ f hW ha hb
  obtain ⟨γ, hγ⟩ := sec8_exists_constSpeedGeod _ hlD K.x K.y
  exact ⟨γ, (isConstSpeedGeodFn_smul_iff _ _ _ _ _ (Real.exp_pos _)).2 hγ⟩

theorem abs_selBump_le (K : CountData d) (hM : 0 ≤ K.M) (hprof : ∀ ℓ x, 0 ≤ K.cat.prof ℓ x ∧ K.cat.prof ℓ x ≤ 1)
    (s : ℝ) (W : Finset (Rd d × K.cat.Label)) (x : Rd d) : |selBump K s W x| ≤ W.card * K.M := by
  rw [abs_of_nonneg (selBump_nonneg hM (fun ℓ x => (hprof ℓ x).1) s W x), selBump_apply]
  calc ∑ p ∈ W, q9Bump (K.cat.prof p.2) K.M p.1 s x ≤ ∑ _p ∈ W, K.M :=
        Finset.sum_le_sum fun p _ => q9Bump_le hM (fun x => (hprof p.2 x).2) _ _ _
    _ = W.card * K.M := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The good event has full measure.** -/
theorem ae_countGood (hd : 3 ≤ d) (K : CountData d) (𝔆 : Catalogue d) (hs : 0 < 𝔆.s) (hξ : 0 < K.ξ)
    (hQ : Real.sqrt (2 * d) < distExp d K.ξ)
    (hD : IsStrongExpMetric d K.ξ (distExp d K.ξ) K.D) (hE : IsStrongExpMetric d K.η (distExp d K.η) K.E)
    (hM : 0 ≤ K.M) (hprof : ∀ ℓ x, 0 ≤ K.cat.prof ℓ x ∧ K.cat.prof ℓ x ≤ 1) :
    ∀ᵐ H ∂(pinLaw d 10), CountGood K 𝔆 H := by
  have hd2 : 2 ≤ d := by omega
  have hh : IsWholeSpaceLGF (id : DistRd d → DistRd d) (pinLaw d 10) :=
    (isWholeSpaceLGF_pinLaw hd2 (by norm_num : (0 : ℝ) < 10)).1
  have h1 : ∀ᵐ H ∂(pinLaw d 10), ∀ W ∈ (countUnivSites K 𝔆).powerset,
      q9GoodInput K (addFun H (selBump K 𝔆.s W)) ∧ q9GoodInput K (addFun H (-selBump K 𝔆.s W)) := by
    refine (Finset.eventually_all _).2 fun W _ => ?_
    have hp := q9_ae_goodInput hd K hξ hQ hD hE (f := selBump K 𝔆.s W) (abs_selBump_le K hM hprof 𝔆.s W)
    have hn := q9_ae_goodInput hd K hξ hQ hD hE (f := -selBump K 𝔆.s W) (B := W.card * K.M)
      (fun x => by
        simpa only [ContinuousMap.neg_apply, abs_neg] using abs_selBump_le K hM hprof 𝔆.s W x)
    filter_upwards [hp, hn] with H h1 h2 using ⟨h1, h2⟩
  have h2 : ∀ᵐ H ∂(pinLaw d 10), ∀ z ∈ 𝔆.Z, ∃ a, Tendsto (sphereAvgSeq H 𝔆.s z) atTop (𝓝 a) :=
    (Finset.eventually_all _).2 fun z _ => by
      simpa only [id_eq] using hh.ae_exists_tendsto_sphereAvgSeq hd2 hs z
  filter_upwards [h1, h2] with H hH1 hH2 using ⟨hH1, hH2⟩

end HigherDimLQGContinuity
