import QuantumZipper.Proofs.GFF.K3.MixedM6Pre
import QuantumZipper.Proofs.GFF.Existence
import QuantumZipper.Proofs.LQG.KernelIdentities

/-!
# DOM-a by annulus features (decision D34), node AN1: the free annulus features

The localised construction of DOM-a (decision D34) glues the local structure of the mixed field
through the closed span `K3.annulusSpan D S` of the *local annulus features*
`annulusFeat D z s s' = v_{fold_{z,s}} − v_{fold_{z,s'}}` (`K3.rieszVec_annulus'`,
`MixedProj.lean`), over all local balls of `(D, S)`. The free field has the same features:

  `freeAnnFeat z s s' := v̂_{fold_{z,s}} − v̂_{fold_{z,s'}} ∈ HkE`.

**AN1** (`inner_freeAnnFeat`): the two families have the same Gram matrix,

  `⟪freeAnnFeat z s s', freeAnnFeat w t t'⟫ = ⟪annulusFeat D z s s', annulusFeat D w t t'⟫`

for local annuli of `(D, S)`. Hence (`K3.exists_linearIsometry_closure_of_gram`) there is a
linear isometry from the mixed annulus span onto the free one matching the generators.

Proof: the mixed side is `∫ annulusPot z s s' d(fold_{w,t} − fold_{w,t'})` by the universality of
the annulus pairings (`K3.inner_rieszVec_annulusFeat`), the free side is
`kernelCov2 neumannH` (`GFFExist.freeVec_inner`), and `annulusPot = fcPot_s − fcPot_{s'}` is the
difference of the `neumannH`-potentials of the two folded circles (`K3.annulusPot_eq_integral_neumannH`,
`CircleMV.integral_neumannH_foldedCircle`). Own elementary argument from these proved identities.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ComplexConjugate

namespace QuantumZipper

namespace Prop16Asm

open GFFExist K3 KernelId CircleMV

open Classical in
/-- The free annulus feature `v̂_{fold_{z,s}} − v̂_{fold_{z,s'}}` (zero for degenerate data). -/
def freeAnnFeat (z : ℂ) (s s' : ℝ) : HkE :=
  if h : z ∈ Hbar ∧ 0 < s ∧ 0 < s' then
    freeVec ⟨foldedCircle z s, isAdmissibleH_foldedCircle h.1 h.2.1⟩ -
      freeVec ⟨foldedCircle z s', isAdmissibleH_foldedCircle h.1 h.2.2⟩
  else 0

theorem freeAnnFeat_eq {z : ℂ} {s s' : ℝ} (hz : z ∈ Hbar) (hs : 0 < s) (hs' : 0 < s') :
    freeAnnFeat z s s' = freeVec ⟨foldedCircle z s, isAdmissibleH_foldedCircle hz hs⟩ -
      freeVec ⟨foldedCircle z s', isAdmissibleH_foldedCircle hz hs'⟩ := by
  simp [freeAnnFeat, hz, hs, hs']

/-- A continuous function is integrable for a folded circle. -/
theorem integrable_foldedCircle_of_continuous_an {g : ℂ → ℝ} (hg : Continuous g) {w : ℂ}
    (hw : w ∈ Hbar) {t : ℝ} (ht : 0 < t) : Integrable g (foldedCircle w t) := by
  have := (isAdmissibleH_foldedCircle hw ht).1
  have hK : IsCompact (closedBall w t ∩ Hbar) := (isCompact_closedBall w t).inter_right isClosed_Hbar
  have hI : IntegrableOn g (closedBall w t ∩ Hbar) (foldedCircle w t) :=
    hg.continuousOn.integrableOn_compact hK
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem
    (ae_iff.2 (K3.foldedCircle_compl_eq_zero hw ht.le))] at hI

/-- The annulus potential is the difference of the two folded-circle potentials. -/
theorem annulusPot_eq_fcPot_sub {z : ℂ} {s s' : ℝ} (hs : 0 < s) (hss' : s < s') (y : ℂ) :
    annulusPot z s s' y = fcPot s z y - fcPot s' z y := by
  rw [annulusPot_eq_integral_neumannH z y hs hss', integral_neumannH_foldedCircle z y hs,
    integral_neumannH_foldedCircle z y (hs.trans hss')]
  rfl

/-- Integral of the annulus potential against a folded circle, as free covariances. -/
theorem integral_annulusPot_foldedCircle {z w : ℂ} {s s' t : ℝ} (hs : 0 < s) (hss' : s < s')
    (hw : w ∈ Hbar) (ht : 0 < t) :
    ∫ y, annulusPot z s s' y ∂(foldedCircle w t) =
      kernelCov neumannH (foldedCircle w t) (foldedCircle z s) -
        kernelCov neumannH (foldedCircle w t) (foldedCircle z s') := by
  simp_rw [annulusPot_eq_fcPot_sub hs hss']
  rw [integral_sub (integrable_foldedCircle_of_continuous_an (continuous_fcPot hs z) hw ht)
    (integrable_foldedCircle_of_continuous_an (continuous_fcPot (hs.trans hss') z) hw ht)]
  unfold kernelCov
  simp_rw [integral_neumannH_foldedCircle_right' z _ hs,
    integral_neumannH_foldedCircle_right' z _ (hs.trans hss')]

/-- **AN1: the free and the mixed annulus features have the same Gram matrix.** -/
theorem inner_freeAnnFeat {D S : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H)
    (hb : Bornology.IsBounded D) (hS : S ⊆ {z : ℂ | z.im = 0})
    (hpos : ∃ g ∈ mixedSpace D S, 0 < dirichletEnergyOn D g) {z w : ℂ} {s s' R0 t t' R1 : ℝ}
    (hz : LocalBall D S z R0) (hs : 0 < s) (hss' : s < s') (hs'R : s' < R0)
    (hw : LocalBall D S w R1) (ht : 0 < t) (htt' : t < t') (ht'R : t' < R1) :
    ⟪freeAnnFeat z s s', freeAnnFeat w t t'⟫ =
      ⟪annulusFeat D z s s', annulusFeat D w t t'⟫ := by
  have hzH : z ∈ Hbar := hz.1
  have hwH : w ∈ Hbar := hw.1
  have hz' : LocalBall D S z s' :=
    hz.mono hzH (hs.trans hss') (by rw [dist_self]; linarith)
  rw [freeAnnFeat_eq hzH hs (hs.trans hss'), freeAnnFeat_eq hwH ht (ht.trans htt'),
    real_inner_comm, freeVec_inner _ _ _ _ (by simp only [measure_univ])
      (by simp only [measure_univ])]
  rw [← rieszVec_annulus' hD hDH hb hS hw ht htt' ht'R, inner_sub_right,
    real_inner_comm _ (annulusFeat D z s s'), real_inner_comm _ (annulusFeat D z s s'),
    inner_rieszVec_annulusFeat hb hpos
      (isAdmissibleDual_foldedCircle_of_local hD hDH hb hS hw ht (htt'.trans ht'R)) hz' hs hss',
    inner_rieszVec_annulusFeat hb hpos
      (isAdmissibleDual_foldedCircle_of_local hD hDH hb hS hw (ht.trans htt') ht'R) hz' hs hss',
    integral_annulusPot_foldedCircle hs hss' hwH ht,
    integral_annulusPot_foldedCircle hs hss' hwH (ht.trans htt')]
  simp only [kernelCov2]
  ring

end Prop16Asm

end QuantumZipper
