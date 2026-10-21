import SmallGammaGeodesics.NIC.WhiteNoise
import SmallGammaGeodesics.NIC.TransportCLM
import SmallGammaGeodesics.NIC.Bump
import LQGMetric.Field.MarkovAsmA

/-!
# NIC, part 2 (steps 5–7): weak harmonicity, Weyl's lemma and the harmonic error `K`

Packet P-G2; design D-P2 of `planning/handoffs/P-G1.md` (steps 5–7), GA2 D5 Step 7,
blueprint `lem:nic` Step E.

* `IsWeakHarm T`: `T(−Δf/2π) = 0` for all `f ∈ C_c^∞(U)`; it is tested on the countable family
  `distGen U` (`isWeakHarm_iff`, via `MarkovAsm.lapV` and `injective_distOn_pairings`).
* `harmRep T`: Weyl's harmonic representative `weylFun T` if `T` is weakly harmonic, `0`
  otherwise. It is harmonic on `U` for **every** `T` (`harmonicOnNhd_harmRep`), vanishes off `U`,
  and represents `T` when `T` is weakly harmonic (`integral_harmRep_mul`).
* Measurability: for a measurable family `T ω`, `ω ↦ harmRep (T ω) z` is measurable and
  `(ω, z) ↦ harmRep (T ω) z` is jointly measurable (`measurable_uncurry_of_continuousOn`, a
  Carathéodory argument on `Ω × U` plus the zero extension).
* `NearIdPair.nicDist U h h̄ := (h ∘ τ − h̄)|_U`, i.e. `T φ = ⟨h, τ φ⟩ − ⟨h̄, φ⟩`.
  `NearIdPair.ae_isWeakHarm`: if `⟨h, φ⟩ = W(J φ)` and `⟨h̄, φ⟩ = W(O J φ)` a.s., then `T` is
  a.s. weakly harmonic on any open `U` where `Ψ` is holomorphic: `O J ρ_χ = U_τ J ρ_χ = J τ ρ_χ`
  (`polar_jH_cmTest`, the key identity of part 1).
* `NearIdPair.coupling_of_isWeakHarm`: the coupling `⟨h, τ g⟩ = ⟨h̄, g⟩ + ∫ K g` for every `g`
  supported in `U`; `NearIdPair.harmRep_sub_eq`: `K z − K w = T(ψ_{s,z} − ψ_{s,w})` for the
  scaled radial bumps of `NIC.Bump`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace InnerProductSpace
open scoped RealInnerProductSpace

namespace SmallGammaGeodesics
namespace NIC

open LQGMetric LQGMetric.GFFExist LQGMetric.WhiteNoise LQGMetric.MarkovGerm LQGMetric.MarkovAsm
  LQGMetric.MarkovHarm LQGMetric.MarkovZB LQGMetric.MarkovWeyl2 LQGMetric.MarkovWeyl3

/-! ## Weakly harmonic distributions and their harmonic representatives -/

/-- `T` is weakly harmonic on `U`: `T(−Δf/2π) = 0` for all `f ∈ C_c^∞(U)` -/
def IsWeakHarm {U : Opens ℂ} (T : DistOn U) : Prop :=
  ∀ f : zsSub (U : Set ℂ), T (cmTestOn f) = 0

/-- weak harmonicity is tested on the countable family `distGen U` -/
lemma isWeakHarm_iff {U : Opens ℂ} (T : DistOn U) :
    IsWeakHarm T ↔ ∀ j : ℕ × ℕ, T (lapV U (distGen U j)) = 0 := by
  constructor
  · intro hT j
    rw [← cmTestOn_toZs]
    exact hT _
  · intro hT f
    have hT0 : T.comp (lapV U) = 0 := by
      apply injective_distOn_pairings U
      funext j
      show T (lapV U (distGen U j)) = 0
      exact hT j
    rw [← toZs_ofZs f, cmTestOn_toZs]
    exact congrArg (fun S : DistOn U => S (ofZs f)) hT0

open Classical in
/-- **The harmonic representative**: `weylFun T` if `T` is weakly harmonic, `0` otherwise -/
def harmRep {U : Opens ℂ} (T : DistOn U) : ℂ → ℝ :=
  if IsWeakHarm T then weylFun T else 0

lemma harmRep_of_isWeakHarm {U : Opens ℂ} {T : DistOn U} (hT : IsWeakHarm T) :
    harmRep T = weylFun T := by
  rw [harmRep, ite_eq_left hT]

lemma harmRep_of_not {U : Opens ℂ} {T : DistOn U} (hT : ¬ IsWeakHarm T) : harmRep T = 0 := by
  rw [harmRep, ite_eq_right hT]

/-- `harmRep T` is harmonic on `U` for every `T` -/
lemma harmonicOnNhd_harmRep {U : Opens ℂ} (T : DistOn U) : HarmonicOnNhd (harmRep T) U := by
  by_cases hT : IsWeakHarm T
  · rw [harmRep_of_isWeakHarm hT]
    exact harmonicOnNhd_weylFun T hT
  · rw [harmRep_of_not hT]
    exact harmonicOnNhd_const (0 : ℝ)

lemma weylFun_eq_zero_of_notMem {U : Opens ℂ} (T : DistOn U) {z : ℂ} (hz : z ∉ U) :
    weylFun T z = 0 := by
  have h : ¬ ∃ s, 0 < s ∧ closedBall z s ⊆ U := fun ⟨s, hs, hV⟩ =>
    hz (hV (mem_closedBall_self hs.le))
  rw [weylFun, dite_eq_right h]

lemma harmRep_eq_zero_of_notMem {U : Opens ℂ} (T : DistOn U) {z : ℂ} (hz : z ∉ U) :
    harmRep T z = 0 := by
  by_cases hT : IsWeakHarm T
  · rw [harmRep_of_isWeakHarm hT, weylFun_eq_zero_of_notMem T hz]
  · rw [harmRep_of_not hT]
    rfl

/-- Weyl's lemma: a weakly harmonic `T` is integration against `harmRep T` -/
lemma integral_harmRep_mul {U : Opens ℂ} {T : DistOn U} (hT : IsWeakHarm T) (φ : TestOn U) :
    T φ = ∫ x, harmRep T x * φ x := by
  rw [harmRep_of_isWeakHarm hT]
  exact integral_mul_weylFun T hT φ

/-- `harmRep T z = T ψ_{s,z}` for weakly harmonic `T` and `B̄(z, s) ⊆ U` -/
lemma harmRep_eq_sbumpOn {U : Opens ℂ} {T : DistOn U} (hT : IsWeakHarm T) {z : ℂ} {s : ℝ}
    (hs : 0 < s) (hz : closedBall z s ⊆ U) : harmRep T z = T (sbumpOn hs hz) := by
  rw [harmRep_of_isWeakHarm hT]
  exact weylFun_eq_sbumpOn T hT hs hz

/-! ## Measurability -/

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_weylFun_apply {U : Opens ℂ} {T : Ω → DistOn U}
    (hT : ∀ φ : TestOn U, Measurable fun ω => T ω φ) (z : ℂ) :
    Measurable fun ω => weylFun (T ω) z := by
  by_cases h : ∃ s, 0 < s ∧ closedBall z s ⊆ U
  · have e : (fun ω => weylFun (T ω) z) =
        fun ω => T ω (rbTest h.choose_spec.1 h.choose_spec.2) := by
      funext ω
      rw [weylFun, dite_eq_left h]
    rw [e]
    exact hT _
  · have e : (fun ω => weylFun (T ω) z) = fun _ => 0 := by
      funext ω
      rw [weylFun, dite_eq_right h]
    rw [e]
    exact measurable_const

lemma measurableSet_isWeakHarm {U : Opens ℂ} {T : Ω → DistOn U}
    (hT : ∀ φ : TestOn U, Measurable fun ω => T ω φ) :
    MeasurableSet {ω | IsWeakHarm (T ω)} := by
  have e : {ω | IsWeakHarm (T ω)} = ⋂ j : ℕ × ℕ, {ω | T ω (lapV U (distGen U j)) = 0} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    exact isWeakHarm_iff (T ω)
  rw [e]
  exact MeasurableSet.iInter fun j => measurableSet_eq_fun (hT _) measurable_const

lemma measurable_harmRep_apply {U : Opens ℂ} {T : Ω → DistOn U}
    (hT : ∀ φ : TestOn U, Measurable fun ω => T ω φ) (z : ℂ) :
    Measurable fun ω => harmRep (T ω) z := by
  have e : (fun ω => harmRep (T ω) z) =
      {ω | IsWeakHarm (T ω)}.indicator (fun ω => weylFun (T ω) z) := by
    funext ω
    by_cases h : IsWeakHarm (T ω)
    · rw [indicator_of_mem (show ω ∈ {ω | IsWeakHarm (T ω)} from h), harmRep_of_isWeakHarm h]
    · rw [indicator_of_notMem (show ω ∉ {ω | IsWeakHarm (T ω)} from h), harmRep_of_not h]
      rfl
  rw [e]
  exact (measurable_weylFun_apply hT z).indicator (measurableSet_isWeakHarm hT)

/-- **Joint measurability** of a Carathéodory function on `Ω × U` extended by zero -/
lemma measurable_uncurry_of_continuousOn {U : Set ℂ} (hU : IsOpen U) {K : Ω → ℂ → ℝ}
    (hc : ∀ ω, ContinuousOn (K ω) U) (hm : ∀ z, Measurable fun ω => K ω z)
    (h0 : ∀ ω, ∀ z ∉ U, K ω z = 0) : Measurable fun p : Ω × ℂ => K p.1 p.2 := by
  let u : U → Ω → ℝ := fun z ω => K ω z
  have hu : Measurable (Function.uncurry u) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => (hc ω).domRestrict)
      (fun z => hm z)
  let S : Set (Ω × ℂ) := {p | p.2 ∈ U}
  have hS : MeasurableSet S := measurable_snd hU.measurableSet
  refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
  · have hg : Measurable fun p : S => ((⟨p.1.2, p.2⟩ : U), p.1.1) :=
      ((measurable_snd.comp measurable_subtype_coe).subtype_mk).prodMk
        (measurable_fst.comp measurable_subtype_coe)
    exact hu.comp hg
  · have e : Sᶜ.domRestrict (fun p : Ω × ℂ => K p.1 p.2) = fun _ => 0 := by
      funext p
      exact h0 p.1.1 p.1.2 p.2
    rw [e]
    exact measurable_const

/-- joint measurability of `(ω, z) ↦ harmRep (T ω) z` -/
lemma measurable_harmRep {U : Opens ℂ} {T : Ω → DistOn U}
    (hT : ∀ φ : TestOn U, Measurable fun ω => T ω φ) :
    Measurable fun p : Ω × ℂ => harmRep (T p.1) p.2 :=
  measurable_uncurry_of_continuousOn (K := fun ω => harmRep (T ω)) U.isOpen
    (fun ω => (harmonicOnNhd_harmRep (T ω)).continuousOn) (measurable_harmRep_apply hT)
    (fun ω _ hz => harmRep_eq_zero_of_notMem (T ω) hz)

end Measurability

/-! ## The distribution `T = (h ∘ τ − h̄)|_U` -/

/-- a test function on `ℂ` supported in `U`, viewed in `𝓓(U)` -/
def testOnOf {U : Opens ℂ} (g : TestC) (hg : tsupport (g : ℂ → ℝ) ⊆ U) : TestOn U :=
  ⟨g, g.contDiff, g.hasCompactSupport, hg⟩

lemma extC_testOnOf {U : Opens ℂ} (g : TestC) (hg : tsupport (g : ℂ → ℝ) ⊆ U) :
    extC U (testOnOf g hg) = g := by
  ext x
  rw [coe_extC]
  rfl

namespace NearIdPair

variable (D : NearIdPair)

/-- `X := h ∘ Φ⁻¹` as a distribution: `⟨X, φ⟩ = ⟨h, τ φ⟩` (`τ` is continuous on `𝓓(ℂ)`) -/
def pullDist (h : DistC) : DistC := h.comp D.transportCLM

lemma pullDist_apply (h : DistC) (φ : TestC) : D.pullDist h φ = h (D.transport φ) := rfl

/-- `T := (h ∘ τ − h̄)|_U`, i.e. `T φ = ⟨h, τ φ⟩ − ⟨h̄, φ⟩` -/
def nicDist (U : Opens ℂ) (h hb : DistC) : DistOn U :=
  restrictTo U (D.pullDist h - hb)

lemma nicDist_apply (U : Opens ℂ) (h hb : DistC) (φ : TestOn U) :
    D.nicDist U h hb φ = h (D.transport (extC U φ)) - hb (extC U φ) := rfl

lemma measurable_nicDist_apply {Ω : Type*} [MeasurableSpace Ω] {h hb : Ω → DistC}
    (hh : Measurable h) (hhb : Measurable hb) (U : Opens ℂ) (φ : TestOn U) :
    Measurable fun ω => D.nicDist U (h ω) (hb ω) φ := by
  simp only [nicDist_apply]
  exact ((measurable_distOn_apply _).comp hh).sub ((measurable_distOn_apply _).comp hhb)

/-- **The coupling clause** on the event where `T` is weakly harmonic:
`⟨h, τ g⟩ = ⟨h̄, g⟩ + ∫ K g` for every `g` supported in `U` -/
theorem coupling_of_isWeakHarm {U : Opens ℂ} {h₀ hb₀ : DistC}
    (hT : IsWeakHarm (D.nicDist U h₀ hb₀)) (g : TestC) (hg : tsupport (g : ℂ → ℝ) ⊆ U) :
    h₀ (D.transport g) = hb₀ g + ∫ y, harmRep (D.nicDist U h₀ hb₀) y * g y := by
  have h1 := integral_harmRep_mul hT (testOnOf g hg)
  rw [nicDist_apply, extC_testOnOf] at h1
  have h2 : ∫ x, harmRep (D.nicDist U h₀ hb₀) x * (testOnOf g hg) x =
      ∫ y, harmRep (D.nicDist U h₀ hb₀) y * g y := rfl
  rw [h2] at h1
  linarith

/-- **Increments through the scaled radial bumps**: `K z − K w = T(ψ_{s,z} − ψ_{s,w})` -/
theorem harmRep_sub_eq {U : Opens ℂ} {h₀ hb₀ : DistC} (hT : IsWeakHarm (D.nicDist U h₀ hb₀))
    {z w : ℂ} {s : ℝ} (hs : 0 < s) (hz : closedBall z s ⊆ U) (hw : closedBall w s ⊆ U) :
    harmRep (D.nicDist U h₀ hb₀) z - harmRep (D.nicDist U h₀ hb₀) w =
      h₀ (D.transport (sbumpC hs z - sbumpC hs w)) - hb₀ (sbumpC hs z - sbumpC hs w) := by
  rw [harmRep_eq_sbumpOn hT hs hz, harmRep_eq_sbumpOn hT hs hw, ← map_sub, nicDist_apply]
  have e : extC U (sbumpOn hs hz - sbumpOn hs hw) = sbumpC hs z - sbumpC hs w := by
    ext x
    rw [coe_extC]
    rfl
  rw [e]

/-! ## Weak harmonicity, almost surely -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
  {h hb : Ω → DistC}

/-- `O J ρ_χ = J τ ρ_χ` for `ρ_χ = −Δχ/2π`, `tsupport χ ⊆ U`, `Ψ` holomorphic on `U` -/
lemma wnIsom_testL2_cmTest {U : Set ℂ} (hU : IsOpen U) (hΨ : DifferentiableOn ℂ D.Ψ U)
    (χ : TestC) (hχ : tsupport (χ : ℂ → ℝ) ⊆ U) :
    D.wnIsom (testL2 (cmTest χ)) = testL2 (D.transport (cmTest χ)) := by
  have h := D.wnIsom_testL2 (cmTest0' χ)
  rw [D.polar_jH_cmTest hU hΨ χ hχ, coe_jH, coe_transport0] at h
  exact h

/-- **Step 5: `T` is a.s. weakly harmonic on `U`** -/
theorem ae_isWeakHarm {U : Opens ℂ} (hΨ : DifferentiableOn ℂ D.Ψ U)
    (hae : ∀ φ : TestC, (fun ω => h ω φ) =ᵐ[P] W (testL2 φ))
    (hbae : ∀ φ : TestC, (fun ω => hb ω φ) =ᵐ[P] W (D.wnIsom (testL2 φ))) :
    ∀ᵐ ω ∂P, IsWeakHarm (D.nicDist U (h ω) (hb ω)) := by
  have key : ∀ f : zsSub (U : Set ℂ),
      ∀ᵐ ω ∂P, D.nicDist U (h ω) (hb ω) (cmTestOn f) = 0 := by
    intro f
    have hvec := D.wnIsom_testL2_cmTest U.isOpen hΨ (zsTest f.2) f.2.2.2
    filter_upwards [hae (D.transport (cmTest (zsTest f.2))), hbae (cmTest (zsTest f.2))]
      with ω h1 h2
    rw [nicDist_apply, extC_cmTestOn, h1, h2, hvec, sub_self]
  have hall : ∀ᵐ ω ∂P, ∀ j : ℕ × ℕ,
      D.nicDist U (h ω) (hb ω) (lapV U (distGen U j)) = 0 :=
    ae_all_iff.2 fun j => by
      have := key (toZs (distGen U j))
      rwa [cmTestOn_toZs] at this
  filter_upwards [hall] with ω hω
  exact (isWeakHarm_iff _).2 hω

end NearIdPair

end NIC
end SmallGammaGeodesics
