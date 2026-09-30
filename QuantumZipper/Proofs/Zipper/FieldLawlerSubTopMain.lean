import QuantumZipper.Proofs.Zipper.FieldLawlerSubTopEnd
import QuantumZipper.Proofs.Zipper.FieldLawlerSubTopSign
import QuantumZipper.Proofs.Zipper.FieldLawlerSubTopComp
import QuantumZipper.Proofs.Zipper.FieldLawlerSubSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-IMAGETOP: `FLImageTopStmt` from the separation property of the arcs of `H_t ∩ C_ε`

Task FL-IMAGETOP (helper of FL-THM, D75). Field–Lawler, *Escape probability and transience for
SLE*, EJP 20 (2015), proof of Prop. 3.4, p. 9, first display: `D ∩ C_ε = ⋃ⱼ ηⱼ`, `ηⱼ`
crosscuts of `D = H_t`.

`flImageTop_of_sep : FLTopSepStmt → FLImageTopStmt`. Everything in `FLImageTopStmt` is proved
(the family of arcs indexed by `ℕ`, their `Z_t`-images are crosscuts of `ℍ` with real end
points on one side of `0`, pairwise disjoint, in the level set), except the separation input
`FLTopSepStmt`, stated inside `D` itself: every `x ∈ D` with `|x| < ε` lies in a bounded
component of `D \ A` for some maximal arc `A` of `D ∩ C_ε`. This is the planar-topology fact FL
use without comment ("the ηⱼ are crosscuts of D"; the separation of `D` by a crosscut:
Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer 1992, Prop. 2.12, p. 29, together
with the choice of the arc through which `x` leaves `B(0, ε)`).
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- **Remaining input (separation in `D`).** Every point `x` of `D = H_t` with `|x| < ε` lies
in a bounded component of `D \ A` for a maximal arc `A = {ε e^{iθ} : α < θ < β}` of
`D ∩ C_ε`. -/
def FLTopSepStmt : Prop :=
  ∀ (W : ℝ → ℝ), Continuous W → W 0 = 0 →
    ∀ t R ε : ℝ, 0 ≤ t → 0 < R → 0 < ε → ε < R →
    trace W 0 = 0 → ContinuousOn (trace W) (Icc 0 t) → InjOn (trace W) (Icc 0 t) →
    (∀ s ∈ Ioc 0 t, trace W s ∈ H) →
    fwdHull W t = trace W '' Ioc 0 t →
    (∀ s ∈ Ico 0 t, ‖trace W s‖ < R) → ‖trace W t‖ = R →
    ∀ x ∈ H \ fwdHull W t, ‖x‖ < ε →
      ∃ α β : ℝ, α < β ∧ 0 ≤ α ∧ β ≤ π ∧ (∀ θ ∈ Ioo α β, flCirc ε θ ∈ H \ fwdHull W t) ∧
        flCirc ε α ∉ H \ fwdHull W t ∧ flCirc ε β ∉ H \ fwdHull W t ∧
        Bornology.IsBounded
          (connectedComponentIn ((H \ fwdHull W t) \ flCirc ε '' Ioo α β) x)

/-- Boundedness in `D` transfers to the image: `p` lies under the crosscut `Z_t A`. -/
theorem fl_not_mem_hullComp (hc : SideCtx W t F) {ε α β : ℝ} (hab : α < β) {p : ℂ}
    (hbdd : Bornology.IsBounded
      (connectedComponentIn ((H \ fwdHull W t) \ flCirc ε '' Ioo α β) (F p))) :
    p ∉ hullComp (flArc W t ε α β) := by
  rintro ⟨hpS, hunb⟩
  apply hunb
  set K := connectedComponentIn (H \ arcH (flArc W t ε α β)) p with hK
  have hKS : K ⊆ H \ arcH (flArc W t ε α β) := connectedComponentIn_subset _ _
  have hKH : K ⊆ H := hKS.trans sdiff_subset
  have hHb : H ⊆ Hbar := fun z hz => by show (0 : ℝ) ≤ z.im; exact le_of_lt hz
  have hmaps : ∀ u ∈ K, F u ∈ (H \ fwdHull W t) \ flCirc ε '' Ioo α β := by
    intro u hu
    refine ⟨hc.F_mem_dom (hKH hu), ?_⟩
    rintro ⟨θ, hθ, hθe⟩
    apply (hKS hu).2
    have hs : (θ - α) / (β - α) ∈ Ioo (0 : ℝ) 1 := by
      have := sub_pos.2 hab
      constructor
      · exact div_pos (by linarith [hθ.1]) this
      · rw [div_lt_one this]; linarith [hθ.2]
    refine ⟨(θ - α) / (β - α), hs, ?_⟩
    have hang : flAng α β ((θ - α) / (β - α)) = θ := by
      unfold flAng; field_simp [(sub_pos.2 hab).ne']; ring
    show fwdMap W t (flCirc ε (flAng α β ((θ - α) / (β - α)))) = u
    rw [hang, hθe, hc.fwdMap_F (hKH hu)]
  have hFK : F '' K ⊆ connectedComponentIn ((H \ fwdHull W t) \ flCirc ε '' Ioo α β) (F p) :=
    (isPreconnected_connectedComponentIn.image F
      (hc.Fcont.mono (hKH.trans hHb))).subset_connectedComponentIn
      ⟨p, mem_connectedComponentIn hpS, rfl⟩ (image_subset_iff.2 hmaps)
  obtain ⟨M, hM⟩ := hbdd.subset_closedBall 0
  obtain ⟨C, hC⟩ := hc.bound
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := M + C)).subset fun u hu => ?_
  have h1 : ‖F u‖ ≤ M := by simpa using hM (hFK ⟨u, hu, rfl⟩)
  have h2 := hC u (hKH hu)
  have h3 : ‖u‖ ≤ ‖F u‖ + ‖F u - u‖ := by
    have := norm_sub_le (F u) (F u - u)
    simpa using this
  rw [Metric.mem_closedBall, dist_zero_right]
  linarith

/-- **FL-IMAGETOP from the separation input.** -/
theorem flImageTop_of_sep (hsep : FLTopSepStmt) : FLImageTopStmt := by
  intro W hW hW0 t R ε ht hR hε hεR h0 hcont hinj hH hhull hlt heq htip
  have htpos : 0 < t := by
    rcases ht.lt_or_eq with h | h
    · exact h
    · subst h; rw [h0, norm_zero] at heq; linarith
  obtain ⟨F, hc, hrev⟩ := flTop_ctx hW hW0 htpos h0 hcont hinj hH hhull
  have hnc : ∀ a b : ℝ, a < b → ∀ c : ℂ, ¬ ∀ s ∈ Ioo a b, F s = c := hrev.noConst
  set D := H \ fwdHull W t with hDdef
  have hDo : IsOpen D := hc.isOpen_dom
  have hDH : D ⊆ H := sdiff_subset
  set O := flO D ε with hOdef
  have hle : ∀ z ∈ fwdHull W t, ‖z‖ ≤ R := by
    intro z hz
    rw [hhull] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    rcases hs.2.lt_or_eq with h | h
    · exact (hlt s ⟨hs.1.le, h⟩).le
    · rw [h, heq]
  have htH : trace W t ∈ H := hH t ⟨htpos, le_rfl⟩
  -- the components of `O`
  set 𝒞 : Set (Set ℝ) := {I | ∃ θ ∈ O, I = connectedComponentIn O θ} with h𝒞
  have hdisj𝒞 : 𝒞.PairwiseDisjoint id := by
    rintro _ ⟨θ, hθ, rfl⟩ _ ⟨θ', hθ', rfl⟩ hne
    rw [Function.onFun, Set.disjoint_left]
    intro z hz hz'
    exact hne ((connectedComponentIn_eq hz).trans (connectedComponentIn_eq hz').symm)
  have hcount : 𝒞.Countable := hdisj𝒞.countable_of_isOpen
    (fun I ⟨θ, _, hI⟩ => hI ▸ (flO_isOpen hDo).connectedComponentIn)
    (fun I ⟨θ, hθ, hI⟩ => hI ▸ ⟨θ, mem_connectedComponentIn hθ⟩)
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_injective.1 hcount
  classical
  let g : ℕ → Set ℝ := fun j => if h : ∃ c : 𝒞, f c = j then (h.choose : Set ℝ) else ∅
  have hg : ∀ c : 𝒞, g (f c) = c := fun c => by
    have h : ∃ c' : 𝒞, f c' = f c := ⟨c, rfl⟩
    simp only [g, dif_pos h]
    exact congrArg Subtype.val (hf h.choose_spec)
  set S : Set ℕ := range f with hS
  let η : ℕ → ℝ → ℂ := fun j => flArc W t ε (sInf (g j)) (sSup (g j))
  -- properties of the arc of index `j ∈ S`
  have hjS : ∀ j ∈ S, ∃ θ ∈ O, g j = connectedComponentIn O θ := by
    rintro j ⟨⟨I, θ, hθ, hI⟩, rfl⟩
    exact ⟨θ, hθ, (hg _).trans hI⟩
  have hprops : ∀ j ∈ S, sInf (g j) < sSup (g j) ∧ 0 ≤ sInf (g j) ∧ sSup (g j) ≤ π ∧
      (∀ θ ∈ Ioo (sInf (g j)) (sSup (g j)), flCirc ε θ ∈ D) ∧
      flCirc ε (sInf (g j)) ∉ D ∧ flCirc ε (sSup (g j)) ∉ D ∧
      g j = Ioo (sInf (g j)) (sSup (g j)) := by
    intro j hj
    obtain ⟨θ, hθ, hgj⟩ := hjS j hj
    obtain ⟨hI, h0α, hαβ, hβπ, hα, hβ, hin⟩ := flComp_props hDo hDH hθ
    rw [hgj]
    exact ⟨hαβ, h0α, hβπ, fun θ' hθ' => hin θ' (hI ▸ hθ'), hα, hβ, hI⟩
  have hex : ∀ j, ∃ a b : ℝ, j ∈ S → (IsCrosscutH (η j) ∧
      Tendsto (η j) (𝓝[>] 0) (𝓝 (a : ℂ)) ∧ Tendsto (η j) (𝓝[<] 1) (𝓝 (b : ℂ)) ∧
      0 < a * b ∧ arcH (η j) ⊆ {p | ‖fwdMapInv W t p‖ = ε}) := by
    intro j
    by_cases hj : j ∈ S
    · obtain ⟨hαβ, h0α, hβπ, hin, hα, hβ, -⟩ := hprops j hj
      obtain ⟨a, b, hFa, hFb, hcc, hla, hlb, hlev⟩ :=
        flArc_crosscut hc hnc hε hαβ h0α hβπ hin hα hβ
      refine ⟨a, b, fun _ => ⟨hcc, hla, hlb, ?_, hlev⟩⟩
      refine fl_endpoints_sameSide hc hεR htH heq hle hcc.1 hcc.2.2.1 ?_ hla hlb
        (by rw [hFa, flCirc_norm hε]) (by rw [hFb, flCirc_norm hε])
      intro s hs
      have hmem := hin _ (flAng_mem hαβ hs)
      show ‖F (fwdMap W t (flCirc ε (flAng (sInf (g j)) (sSup (g j)) s)))‖ ≤ ε
      rw [hc.F_fwdMap hmem, flCirc_norm hε]
    · exact ⟨0, 0, fun h => absurd h hj⟩
  choose a b hab using hex
  refine ⟨S, η, a, b, fun j hj => hab j hj, ?_, ?_⟩
  · -- pairwise disjoint
    rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩ hne
    have hcc : c ≠ c' := fun h => hne (h ▸ rfl)
    obtain ⟨hαβ, h0α, hβπ, hin, -, -, hI⟩ := hprops _ ⟨c, rfl⟩
    obtain ⟨hαβ', h0α', hβπ', hin', -, -, hI'⟩ := hprops _ ⟨c', rfl⟩
    refine flArc_disjoint hc hε hαβ h0α hβπ hαβ' h0α' hβπ' hin hin' ?_
    rw [← hI, ← hI', hg, hg]
    exact hdisj𝒞 c.2 c'.2 fun h => hcc (Subtype.ext h)
  · -- every point of `Z_t(D ∩ B(0, ε))` lies under some `Z_t ηⱼ`
    intro p hp hpε
    have hFp : F p = fwdMapInv W t p := hc.Feq hp
    obtain ⟨α, β, hαβ, h0α, hβπ, hin, hα, hβ, hbdd⟩ :=
      hsep W hW hW0 t R ε ht hR hε hεR h0 hcont hinj hH hhull hlt heq (F p)
        (hc.F_mem_dom hp) (hFp ▸ hpε)
    have hcomp := flComp_of_maximal hDo hDH hαβ h0α hβπ hin hα hβ
    have hmO : (α + β) / 2 ∈ O :=
      ⟨flCirc_mem_Ioo_of_H ⟨by linarith, by linarith⟩ (hDH (hin _ ⟨by linarith, by linarith⟩)),
        hin _ ⟨by linarith, by linarith⟩⟩
    let c : 𝒞 := ⟨Ioo α β, (α + β) / 2, hmO, hcomp.symm⟩
    refine ⟨f c, ⟨c, rfl⟩, ?_⟩
    have hgc : g (f c) = Ioo α β := hg c
    show p ∉ hullComp (flArc W t ε (sInf (g (f c))) (sSup (g (f c))))
    rw [hgc, csInf_Ioo hαβ, csSup_Ioo hαβ]
    exact fl_not_mem_hullComp hc hαβ hbdd

end FieldLawler
end QuantumZipper
