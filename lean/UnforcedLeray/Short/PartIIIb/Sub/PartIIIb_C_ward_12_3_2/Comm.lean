import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.PairFunctionalDual.SolDiv

/-!
# Differentiating the shift-zero equation once: `[∂_l, A₀] = ½∂_l` (source 2525-2537, 2552-2559)

Organizer item `ORG:ward/bg-bootstrap` (design of task `PartIII-b:C/ward/12/3/2/2`).  Source of
record `the November 2 reference manuscript`.

Source 2529-2534: "Since `∂_jA₀w = (A₀ - 1/2)∂_jw` ... Rewrite the differentiated equation as
`A₀D_jw = f_j + ½D_jw`", and 2552-2559: "Inductively, if derivatives through order `k` are in the
graph ... apply the maximal graph to the differentiated equation."  On phase tests this is
`∂_l(L₀ᵗΦ) = L₀ᵗ(∂_lΦ) + ½∂_lΦ` (`[∂_l, y·∇] = ∂_l`).

`l0T_dy_fun` is the one-step lemma in functional form, for any class of tests closed under `∂_l`
(all phase tests, or the solenoidal tests on which the projected equation is tested), any constant
`c` and any right-hand functional `R`: if `⟪L₀ᵗΦ, u⟫ = c⟪Φ, u⟫ + R(Φ)` and `∂_lu = v`, then
`⟪L₀ᵗΦ, v⟫ = (c + ½)⟪Φ, v⟫ - R(∂_lΦ)`.  It applies at every order: iterating it along
`∂_{l₁}, …, ∂_{l_k}` gives the order-`k` equation with constant `c + k/2` and right side
`(-1)^k R(∂_{l_1}⋯∂_{l_k}Φ)` (the step `k → k+1` of source 2552-2559).  `hasPhaseOp_L0T_dy` is the
all-test form with a `Y`-valued right side: `A₀u = F`, `∂_lu = v`, `∂_lF = G` give
`A₀v = ½v + G`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.HessComm

open UnforcedLeray.PhaseSpace

/-- `∂_l(L₀ᵗΦ) = L₀ᵗ(∂_lΦ) + ½∂_lΦ` for a smooth test (`[∂_l, y·∇] = ∂_l`). -/
theorem dy_L0T {ν : ℝ} {Φ : ℝ × Space → CVec3} (hC : ContDiff ℝ ∞ Φ) (l : Fin 3) :
    dy l (UnforcedLeray.B0411.L0T ν Φ) =
      UnforcedLeray.B0411.L0T ν (dy l Φ) + (1 / 2 : ℂ) • dy l Φ := by
  have h := UnforcedLeray.Short.PartIIIb.NearInst.PairDualAux.dy_L0T_add (ν := ν) (μ := 0) hC l
  have e0 : (fun x => UnforcedLeray.B0411.L0T ν Φ x + ((0 : ℝ) : ℂ) • Φ x) =
      UnforcedLeray.B0411.L0T ν Φ := by
    funext x
    simp
  rw [e0] at h
  rw [h]
  funext x
  simp only [UnforcedLeray.B0411.L0T, UnforcedLeray.PhaseSpace.nuLapT, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, Complex.ofReal_zero, zero_smul, add_zero]
  module

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- **One differentiation of a first-order phase equation** (functional form; source 2529-2534,
2552-2559).  Let `T` be a class of phase tests closed under every `∂_l` (all phase tests, or the
solenoidal tests).  If `⟪L₀ᵗΦ, u⟫ = c⟪Φ, u⟫ + R(Φ)` for `Φ ∈ T` and `∂_lu = v` in distributions,
then `⟪L₀ᵗΦ, v⟫ = (c + ½)⟪Φ, v⟫ - R(∂_lΦ)` for `Φ ∈ T`. -/
theorem l0T_dy_fun (ν : ℝ) (T : (ℝ × Space → CVec3) → Prop)
    (hTp : ∀ Φ, T Φ → IsPhaseTest P Φ) (hTd : ∀ Φ, T Φ → ∀ l : Fin 3, T (dy l Φ))
    (l : Fin 3) (c : ℂ) (R : (ℝ × Space → CVec3) → ℂ) {u v : Yq P q}
    (hu : ∀ Φ, T Φ →
      phasePair P q (UnforcedLeray.B0411.L0T ν Φ) u = c * phasePair P q Φ u + R Φ)
    (huv : HasPhaseOp (fun Φ => -dy l Φ) u v) (Φ : ℝ × Space → CVec3) (hΦ : T Φ) :
    phasePair P q (UnforcedLeray.B0411.L0T ν Φ) v =
      (c + 1 / 2) * phasePair P q Φ v - R (dy l Φ) := by
  have hp : IsPhaseTest P Φ := hTp Φ hΦ
  have hC : ContDiff ℝ ∞ Φ := hp.smooth
  have hd : IsPhaseTest P (dy l Φ) := hp.dy l
  have hL0 : IsPhaseTest P (UnforcedLeray.B0411.L0T ν Φ) :=
    UnforcedLeray.B0411.isPhaseTest_L0T hp ν
  have hL0d : IsPhaseTest P (UnforcedLeray.B0411.L0T ν (dy l Φ)) :=
    UnforcedLeray.B0411.isPhaseTest_L0T hd ν
  have hhalf : IsPhaseTest P ((1 / 2 : ℂ) • dy l Φ) := hd.const_smul _
  have h1 := huv _ hL0
  simp only at h1
  rw [dy_L0T hC l, phasePair_neg (hL0d.add hhalf), phasePair_add hL0d hhalf,
    phasePair_const_smul hd] at h1
  have h2 := huv Φ hp
  simp only at h2
  rw [phasePair_neg hd] at h2
  have h3 := hu (dy l Φ) (hTd Φ hΦ l)
  linear_combination (-1 : ℂ) * h1 + (c + 1 / 2) * h2 + (-1 : ℂ) * h3

/-- **The commutator lemma on all phase tests** (source 2529-2534): if `A₀u = F`, `∂_lu = v` and
`∂_lF = G` in distributions (`A₀` the shift-zero operator, transpose `0 + L₀ᵗ`), then
`A₀v = ½v + G`. -/
theorem hasPhaseOp_L0T_dy (ν : ℝ) (l : Fin 3) {u v F G : Yq P q}
    (huF : HasPhaseOp (fun Φ => (0 : ℂ) • Φ + UnforcedLeray.B0411.L0T ν Φ) u F)
    (huv : HasPhaseOp (fun Φ => -dy l Φ) u v)
    (hFG : HasPhaseOp (fun Φ => -dy l Φ) F G) :
    HasPhaseOp (fun Φ => (0 : ℂ) • Φ + UnforcedLeray.B0411.L0T ν Φ) v
      ((1 / 2 : ℂ) • v + G) := by
  have hu : ∀ Φ, IsPhaseTest P Φ →
      phasePair P q (UnforcedLeray.B0411.L0T ν Φ) u =
        (0 : ℂ) * phasePair P q Φ u + phasePair P q Φ F := by
    intro Φ hΦ
    have h := huF Φ hΦ
    simp only [zero_smul, zero_add] at h
    rw [h, zero_mul, zero_add]
  intro Φ hΦ
  have hd : IsPhaseTest P (dy l Φ) := hΦ.dy l
  have key := l0T_dy_fun (P := P) (q := q) ν (IsPhaseTest P) (fun _ h => h)
    (fun _ h l' => h.dy l') l 0 (fun Ψ => phasePair P q Ψ F) hu huv Φ hΦ
  have hG := hFG Φ hΦ
  simp only at hG
  rw [phasePair_neg hd] at hG
  simp only [zero_smul, zero_add]
  rw [key, map_add, map_smul, smul_eq_mul, ← hG]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete.HessComm
