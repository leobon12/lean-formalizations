import QuantumZipper.Proofs.Thm18.A1RS2Fix

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS2 (2): from the rational Cauchy estimate to the limit at every parameter (deterministic)

**`tendsto_of_ratCauchy`**: if a function `Φ ρ p` satisfies, on every rational box inside
`smearU`, the uniform estimate `|Φ r q − E₀ q| < 1/(n+1)` at the rational parameters `q` and
rational radii `0 < r < 1/(N+1)` (the output of `ae_smear_cauchy_fixed`, after the transfer to the
random driver), and `(p, ρ) ↦ Φ ρ p` is continuous on `smearU × (0, ∞)` and `E₀` on `smearU`, then
`Φ ρ p → E₀ p` as `ρ → 0⁺` at every `p ∈ smearU`.

The same extension from a countable dense set as in `A1RF.ae_flowPhiYc_unifCauchy`
(A1RFLoopFree.lean) and `GenUC.ae_unifConv_all_radii`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace R18
namespace A1RS

theorem denseRange_ratPt : DenseRange ratPt :=
  DenseRange.piMap (X := fun _ : Fin 4 => ℚ) (Y := fun _ => ℝ) (f := fun _ => ((↑) : ℚ → ℝ))
    fun _ => Rat.denseRange_cast

theorem isOpen_smearU : IsOpen smearU :=
  (isOpen_lt continuous_const (continuous_apply 0)).inter
    (isOpen_lt continuous_const (continuous_apply 3))

/-- Every point of `smearU` lies in the interior of a rational box inside `smearU`. -/
theorem exists_ratBox_nhds {p : Fin 4 → ℝ} (hp : p ∈ smearU) :
    ∃ a b : Fin 4 → ℚ, (∀ i, (a i : ℝ) < p i ∧ p i < b i) ∧ GenUC.ratBox a b ⊆ smearU := by
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.1 isOpen_smearU p hp
  have hlo : ∀ i, ∃ q : ℚ, p i - e / 2 < q ∧ (q : ℝ) < p i := fun i =>
    exists_rat_btwn (by linarith)
  have hhi : ∀ i, ∃ q : ℚ, p i < q ∧ (q : ℝ) < p i + e / 2 := fun i =>
    exists_rat_btwn (by linarith)
  choose a ha using hlo
  choose b hb using hhi
  refine ⟨a, b, fun i => ⟨(ha i).2, (hb i).1⟩, fun y hy => hball ?_⟩
  rw [Metric.mem_ball, dist_pi_lt_iff he]
  intro i
  have h := hy i (mem_univ i)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [h.1, h.2, (ha i).1, (hb i).2]

theorem mem_closure_ratPts {a b : Fin 4 → ℚ} {p : Fin 4 → ℝ}
    (hp : ∀ i, (a i : ℝ) < p i ∧ p i < b i) :
    p ∈ closure (ratPt '' {q | ratPt q ∈ GenUC.ratBox a b}) := by
  rw [_root_.mem_closure_iff]
  intro o ho hpo
  have hV : IsOpen (o ∩ Set.pi univ fun i => Ioo (a i : ℝ) (b i)) :=
    ho.inter (isOpen_set_pi finite_univ fun i _ => isOpen_Ioo)
  obtain ⟨q, hq⟩ := denseRange_ratPt.exists_mem_open hV ⟨p, hpo, fun i _ => hp i⟩
  exact ⟨ratPt q, hq.1, q, fun i _ => Ioo_subset_Icc_self (hq.2 i (mem_univ i)), rfl⟩

theorem mem_closure_ratRadii {δ ρ : ℝ} (hρ : 0 < ρ) (hρδ : ρ < δ) :
    ρ ∈ closure (((↑) : ℚ → ℝ) '' {r : ℚ | 0 < r ∧ (r : ℝ) < δ}) := by
  rw [_root_.mem_closure_iff]
  intro o ho hρo
  obtain ⟨r, hr⟩ := (Rat.denseRange_cast (𝕜 := ℝ)).exists_mem_open (ho.inter isOpen_Ioo)
    ⟨ρ, hρo, hρ, hρδ⟩
  exact ⟨r, hr.1, r, ⟨by exact_mod_cast hr.2.1, hr.2.2⟩, rfl⟩

/-- **Extension from rational parameters and radii to all of them.** -/
theorem tendsto_of_ratCauchy {Φ : ℝ → (Fin 4 → ℝ) → ℝ} {E0 : (Fin 4 → ℝ) → ℝ}
    (hC : ∀ a b : Fin 4 → ℚ, GenUC.ratBox a b ⊆ smearU → ∀ n : ℕ, ∃ N : ℕ, ∀ r : ℚ, 0 < r →
      (r : ℝ) < 1 / ((N : ℝ) + 1) → ∀ q : Fin 4 → ℚ, ratPt q ∈ GenUC.ratBox a b →
        |Φ r (ratPt q) - E0 (ratPt q)| < 1 / ((n : ℝ) + 1))
    (hΦc : ContinuousOn (fun z : (Fin 4 → ℝ) × ℝ => Φ z.2 z.1) (smearU ×ˢ Ioi 0))
    (hEc : ContinuousOn E0 smearU) :
    ∀ p ∈ smearU, Tendsto (fun ρ => Φ ρ p) (𝓝[>] 0) (𝓝 (E0 p)) := by
  intro p hp
  obtain ⟨a, b, hpab, hsub⟩ := exists_ratBox_nhds hp
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := hC a b hsub n
  refine ⟨1 / ((N : ℝ) + 1), by positivity, fun {ρ} hρ hρd => ?_⟩
  have hρ0 : 0 < ρ := hρ
  have hρN : ρ < 1 / ((N : ℝ) + 1) := by
    rwa [Real.dist_eq, sub_zero, abs_of_pos hρ0] at hρd
  set E : Set ((Fin 4 → ℝ) × ℝ) := (ratPt '' {q | ratPt q ∈ GenUC.ratBox a b}) ×ˢ
    (((↑) : ℚ → ℝ) '' {r : ℚ | 0 < r ∧ (r : ℝ) < 1 / ((N : ℝ) + 1)}) with hE
  have hES : E ⊆ smearU ×ˢ Ioi 0 := by
    rintro ⟨z1, z2⟩ ⟨⟨q, hq, rfl⟩, ⟨r, hr, rfl⟩⟩
    exact ⟨hsub hq, show (0 : ℝ) < r by exact_mod_cast hr.1⟩
  have hmem : (p, ρ) ∈ closure E := by
    rw [hE, closure_prod_eq]
    exact ⟨mem_closure_ratPts hpab, mem_closure_ratRadii hρ0 hρN⟩
  have hpρ : (p, ρ) ∈ smearU ×ˢ Ioi 0 := ⟨hp, hρ0⟩
  have hg : ContinuousWithinAt (fun z : (Fin 4 → ℝ) × ℝ => |Φ z.2 z.1 - E0 z.1|) E (p, ρ) :=
    (((hΦc _ hpρ).sub ((hEc p hp).comp continuousWithinAt_fst fun z hz => hz.1)).abs).mono hES
  have hle : |Φ ρ p - E0 p| ≤ 1 / ((n : ℝ) + 1) :=
    ContinuousWithinAt.closure_le
      (f := fun z : (Fin 4 → ℝ) × ℝ => |Φ z.2 z.1 - E0 z.1|) (g := fun _ => 1 / ((n : ℝ) + 1)) hmem hg
      continuousWithinAt_const (by
        rintro ⟨z1, z2⟩ ⟨⟨q, hq, rfl⟩, ⟨r, hr, rfl⟩⟩
        exact (hN r hr.1 hr.2 q hq).le)
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hle hn

/-- **Locally uniform version of the extension.** Under the hypotheses of
`tendsto_of_ratCauchy`, `Φ ρ → E₀` locally uniformly on `smearU` as `ρ → 0⁺` (the form needed to
pass the estimate through the rescaling by the canonical scale). -/
theorem tendstoLocallyUniformlyOn_of_ratCauchy {Φ : ℝ → (Fin 4 → ℝ) → ℝ}
    {E0 : (Fin 4 → ℝ) → ℝ}
    (hC : ∀ a b : Fin 4 → ℚ, GenUC.ratBox a b ⊆ smearU → ∀ n : ℕ, ∃ N : ℕ, ∀ r : ℚ, 0 < r →
      (r : ℝ) < 1 / ((N : ℝ) + 1) → ∀ q : Fin 4 → ℚ, ratPt q ∈ GenUC.ratBox a b →
        |Φ r (ratPt q) - E0 (ratPt q)| < 1 / ((n : ℝ) + 1))
    (hΦc : ContinuousOn (fun z : (Fin 4 → ℝ) × ℝ => Φ z.2 z.1) (smearU ×ˢ Ioi 0))
    (hEc : ContinuousOn E0 smearU) :
    TendstoLocallyUniformlyOn Φ E0 (𝓝[>] 0) smearU := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε p hp
  obtain ⟨a, b, hpab, hsub⟩ := exists_ratBox_nhds hp
  set V : Set (Fin 4 → ℝ) := Set.pi univ fun i => Ioo (a i : ℝ) (b i) with hV
  have hVo : IsOpen V := isOpen_set_pi finite_univ fun i _ => isOpen_Ioo
  have hpV : p ∈ V := fun i _ => hpab i
  refine ⟨V, mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds hpV), ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := hC a b hsub n
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / ((N : ℝ) + 1) by positivity)]
    with ρ hρ p' hp'
  have hp'i : ∀ i, (a i : ℝ) < p' i ∧ p' i < b i := fun i => hp' i (mem_univ i)
  have hp'U : p' ∈ smearU := hsub fun i _ => ⟨(hp'i i).1.le, (hp'i i).2.le⟩
  set E : Set ((Fin 4 → ℝ) × ℝ) := (ratPt '' {q | ratPt q ∈ GenUC.ratBox a b}) ×ˢ
    (((↑) : ℚ → ℝ) '' {r : ℚ | 0 < r ∧ (r : ℝ) < 1 / ((N : ℝ) + 1)}) with hE
  have hES : E ⊆ smearU ×ˢ Ioi 0 := by
    rintro ⟨z1, z2⟩ ⟨⟨q, hq, rfl⟩, ⟨r, hr, rfl⟩⟩
    exact ⟨hsub hq, show (0 : ℝ) < r by exact_mod_cast hr.1⟩
  have hmem : (p', ρ) ∈ closure E := by
    rw [hE, closure_prod_eq]
    exact ⟨mem_closure_ratPts hp'i, mem_closure_ratRadii hρ.1 hρ.2⟩
  have hpρ : (p', ρ) ∈ smearU ×ˢ Ioi 0 := ⟨hp'U, hρ.1⟩
  have hg : ContinuousWithinAt (fun z : (Fin 4 → ℝ) × ℝ => |Φ z.2 z.1 - E0 z.1|) E (p', ρ) :=
    (((hΦc _ hpρ).sub ((hEc p' hp'U).comp continuousWithinAt_fst fun z hz => hz.1)).abs).mono
      hES
  have hle : |Φ ρ p' - E0 p'| ≤ 1 / ((n : ℝ) + 1) :=
    ContinuousWithinAt.closure_le
      (f := fun z : (Fin 4 → ℝ) × ℝ => |Φ z.2 z.1 - E0 z.1|) (g := fun _ => 1 / ((n : ℝ) + 1))
      hmem hg continuousWithinAt_const (by
        rintro ⟨z1, z2⟩ ⟨⟨q, hq, rfl⟩, ⟨r, hr, rfl⟩⟩
        exact (hN r hr.1 hr.2 q hq).le)
  rw [dist_comm, Real.dist_eq]
  exact lt_of_le_of_lt hle hn

end A1RS
end R18
end QuantumZipper
