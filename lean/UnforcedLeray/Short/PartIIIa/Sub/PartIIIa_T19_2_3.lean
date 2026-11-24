import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_3
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NullModification
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.TailContinuation.GlobalExistence

/-!
# Part III-a, task `PartIII-a:T19/2/3`: forward Duhamel propagation and Biot-Savart velocity

Source of record: `the November 2 reference manuscript` (SP), lines 3489-3515
(Steps P3-Duhamel and P4: forward Duhamel vorticity propagation and core velocity reconstruction).

## Mathematical structure and decomposition

Given a free causal solution `(b₀, G₀)` of `IsCausalEnergySolution c ν μ 0 F b₀ G₀` and the
global train causal solution `(b_sol, G_sol)` of `IsCausalEnergySolution c ν μ (trainVel tr) F b_sol G_sol`
(supplied by `trainCausalExistence` from `T19_PolyCausal/TailContinuation/GlobalExistence.lean`),
the gain-conjugated core velocity perturbation and its gradient and scalar curl are:
* `corePerturbVel γ ν b₀ b_sol = gainConj γ ν (b_sol - b₀)` (`u₁ = g⁻¹(b_sol - b₀)`),
* `corePerturbGrad γ ν G₀ G_sol = gainConj γ ν (G_sol - G₀)` (`G₁ = g⁻¹(G_sol - G₀)`),
* `corePerturbVort γ ν G₀ G_sol s x = G₁ (s, x) 1 0 - G₁ (s, x) 0 1` (`ω = ∂_q u_{1,η} - ∂_η u_{1,q}`).

Unconditionally proved in this file:
1. `hasWeakCellDerivC_add_realSmul`, `divFree_add_realSmul`: closure of `HasWeakCellDerivC` and
   spatial divergence-freeness on `B0579.cell c` under `φ₀ + a • φ₁`.
2. `corePerturb_divFree`, `corePerturb_weakGrad`: for every `s > 0`, `corePerturbVel` is
   divergence-free on `B0579.cell c` and has weak cell gradient `corePerturbGrad`.
3. `corePerturb_memLp_ae`: for almost every `s ∈ Ioo (0 : ℝ) (coreEnd ν b)`, the slice
   `(corePerturbVel (s, ·), corePerturbGrad (s, ·))` belongs to `L²(B0579.cell c)` (from
   `energyLoc` on compact subintervals `[H/(k+3), H - H/(k+3)] ⊂ (0, H)` via Tonelli).
4. `isCoreCausalSolution_of_nullKeep`: redefining `(corePerturbVel, corePerturbGrad)` to `0` on
   `{p | p.1 ∈ N}` for any measurable null set of ages `N ⊆ ℝ` (`volume N = 0`) preserves
   `IsCoreCausalSolution c ν H μ (trainVel tr) F (b₀ + g • u₁) (G₀ + g • G₁)` for every age
   `s ∈ Ioo (0 : ℝ) H` (since on `s ∈ N` the sum equals `(b₀, G₀)` and off `N` it equals
   `(b_sol, G_sol)`, while `N ×ˢ univ` is null for `volume` and `ageμ c (-3/2)`).
5. `coreDuhamelPropagation_of`: assembles `CoreDuhamelPropagation` from `trainCausalExistence` and
   the two leaf propositions:
   * `CoreBiotSavartSliceBound` (`PartIII-a:T19/2/3/1`, SP 3497-3515): uniqueness of Biot-Savart
     on `B0579.cell c` (`c ≥ 1`) and resulting `H¹(cell c)` bound `≤ (C_BS * xNorm c 9 ω)²` for any
     divergence-free `H¹(cell c)` slice `(u, G)` whose curl `ω = G 1 0 - G 0 1` lies in `X_{9,c}`
     with zero circulation.
   * `CoreDuhamelVorticityBound` (`PartIII-a:T19/2/3/2`, SP 3462-3496): for a.e.
     `s ∈ Ioo (0 : ℝ) (coreEnd ν b)`, the perturbation vorticity
     `ω s = corePerturbVort P.eigenvalue.re ν G₀ G_sol s` lies in `X_{9,c}` with zero circulation
     and satisfies the Duhamel weak-forward clock integral bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## 1. Weak derivative and divergence-free linearity on `B0579.cell c` -/

/-- `HasWeakCellDerivC` is closed under `φ₀ + a • φ₁`, `g₀ + a • g₁` for `a : ℝ`. -/
theorem hasWeakCellDerivC_add_realSmul {c : ℝ} (j : Fin 2) (a : ℝ)
    {φ₀ φ₁ g₀ g₁ : ℝ × ℝ → ℂ}
    (h₀ : HasWeakCellDerivC c j φ₀ g₀) (h₁ : HasWeakCellDerivC c j φ₁ g₁) :
    HasWeakCellDerivC c j (fun x => φ₀ x + a • φ₁ x) (fun x => g₀ x + a • g₁ x) := by
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · obtain ⟨hφ₀, hg₀⟩ := h₀.1 ψ hψ
    obtain ⟨hφ₁, hg₁⟩ := h₁.1 ψ hψ
    refine ⟨?_, ?_⟩
    · refine (hφ₀.add (hφ₁.const_mul (a : ℂ))).congr_fun_ae (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply, Complex.real_smul]
      ring
    · refine (hg₀.add (hg₁.const_mul (a : ℂ))).congr_fun_ae (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply, Complex.real_smul]
      ring
  · obtain ⟨hφ₀, hg₀⟩ := h₀.1 ψ hψ
    obtain ⟨hφ₁, hg₁⟩ := h₁.1 ψ hψ
    have hsplit₁ : ∀ x, (φ₀ x + a • φ₁ x) * (B0579.pd j ψ x : ℂ) =
        φ₀ x * (B0579.pd j ψ x : ℂ) + (a : ℂ) * (φ₁ x * (B0579.pd j ψ x : ℂ)) :=
      fun _ => by simp only [Complex.real_smul]; ring
    have hsplit₂ : ∀ x, (g₀ x + a • g₁ x) * (ψ x : ℂ) =
        g₀ x * (ψ x : ℂ) + (a : ℂ) * (g₁ x * (ψ x : ℂ)) :=
      fun _ => by simp only [Complex.real_smul]; ring
    rw [integral_congr_ae (Eventually.of_forall hsplit₁),
      integral_add hφ₀ (hφ₁.const_mul (a : ℂ)), integral_const_mul,
      integral_congr_ae (Eventually.of_forall hsplit₂),
      integral_add hg₀ (hg₁.const_mul (a : ℂ)), integral_const_mul,
      h₀.2 ψ hψ, h₁.2 ψ hψ]
    ring

/-- `HasWeakCellDerivC` is closed under real scalar multiplication `a • φ`, `a • g`. -/
theorem hasWeakCellDerivC_realSmul {c : ℝ} (j : Fin 2) (a : ℝ)
    {φ g : ℝ × ℝ → ℂ} (h : HasWeakCellDerivC c j φ g) :
    HasWeakCellDerivC c j (fun x => a • φ x) (fun x => a • g x) := by
  have h0 := hasWeakCellDerivC_add_realSmul j a (causalNull_hasWeak_zero c j) h
  simpa only [zero_add] using h0

/-- The spatial divergence-free condition on `B0579.cell c` is preserved under `b₀ + a • u₁`
when `b₀` and `u₁` have weak cell gradients. -/
theorem divFree_add_realSmul {c : ℝ} (a : ℝ)
    {b₀ u₁ : ℝ × ℝ → Fin 2 → ℂ} {G₀ G₁ : ℝ × ℝ → Fin 2 → Fin 2 → ℂ}
    (hdiv₀ : ∀ ψ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c,
        (b₀ x 0 * (B0579.pd 0 ψ x : ℂ) + b₀ x 1 * (B0579.pd 1 ψ x : ℂ)) = 0)
    (hdiv₁ : ∀ ψ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c,
        (u₁ x 0 * (B0579.pd 0 ψ x : ℂ) + u₁ x 1 * (B0579.pd 1 ψ x : ℂ)) = 0)
    (hw₀ : ∀ i j, HasWeakCellDerivC c j (fun x => b₀ x i) (fun x => G₀ x i j))
    (hw₁ : ∀ i j, HasWeakCellDerivC c j (fun x => u₁ x i) (fun x => G₁ x i j)) :
    ∀ ψ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c,
        ((b₀ x 0 + a • u₁ x 0) * (B0579.pd 0 ψ x : ℂ) +
          (b₀ x 1 + a • u₁ x 1) * (B0579.pd 1 ψ x : ℂ)) = 0 := by
  intro ψ hψ
  have hb₀0 := ((hw₀ 0 0).1 ψ hψ).1
  have hb₀1 := ((hw₀ 1 1).1 ψ hψ).1
  have hu₁0 := ((hw₁ 0 0).1 ψ hψ).1
  have hu₁1 := ((hw₁ 1 1).1 ψ hψ).1
  have hA : IntegrableOn (fun x => b₀ x 0 * (B0579.pd 0 ψ x : ℂ) +
      b₀ x 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) := hb₀0.add hb₀1
  have hB : IntegrableOn (fun x => u₁ x 0 * (B0579.pd 0 ψ x : ℂ) +
      u₁ x 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) := hu₁0.add hu₁1
  have hsplit : ∀ x,
      (b₀ x 0 + a • u₁ x 0) * (B0579.pd 0 ψ x : ℂ) +
        (b₀ x 1 + a • u₁ x 1) * (B0579.pd 1 ψ x : ℂ) =
      (b₀ x 0 * (B0579.pd 0 ψ x : ℂ) + b₀ x 1 * (B0579.pd 1 ψ x : ℂ)) +
        (a : ℂ) * (u₁ x 0 * (B0579.pd 0 ψ x : ℂ) + u₁ x 1 * (B0579.pd 1 ψ x : ℂ)) :=
    fun _ => by simp only [Complex.real_smul]; ring
  rw [integral_congr_ae (Eventually.of_forall hsplit),
    integral_add hA (hB.const_mul (a : ℂ)),
    integral_const_mul, hdiv₀ ψ hψ, hdiv₁ ψ hψ]
  ring

/-! ## 2. Core velocity perturbation, gradient, and vorticity -/

/-- Gain-conjugated velocity perturbation `u₁ = g⁻¹(b_sol - b₀)` (SP 3492). -/
def corePerturbVel (γ ν : ℝ) (b₀ b_sol : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) :
    ℝ × (ℝ × ℝ) → Fin 2 → ℂ :=
  gainConj γ ν (fun p i => b_sol p i - b₀ p i)

/-- Gain-conjugated gradient perturbation `G₁ = g⁻¹(G_sol - G₀)` (SP 3492). -/
def corePerturbGrad (γ ν : ℝ) (G₀ G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) :
    ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ :=
  gainConj γ ν (fun p i j => G_sol p i j - G₀ p i j)

/-- Scalar vorticity slice `ω(s, x) = ∂_q u_{1,η} - ∂_η u_{1,q} = G₁(s, x) 1 0 - G₁(s, x) 0 1`
of the core perturbation (SP 3491-3492). -/
def corePerturbVort (γ ν : ℝ) (G₀ G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (s : ℝ) (x : ℝ × ℝ) : ℂ :=
  corePerturbGrad γ ν G₀ G_sol (s, x) 1 0 - corePerturbGrad γ ν G₀ G_sol (s, x) 0 1

theorem measurable_corePerturbVel (γ ν : ℝ)
    {b₀ b_sol : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    (hb₀ : ∀ i, Measurable fun p => b₀ p i) (hb_sol : ∀ i, Measurable fun p => b_sol p i) :
    ∀ i, Measurable fun p => corePerturbVel γ ν b₀ b_sol p i :=
  fun i => measurable_gainConj_vec (fun j => (hb_sol j).sub (hb₀ j)) i

theorem measurable_corePerturbGrad (γ ν : ℝ)
    {G₀ G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hG₀ : ∀ i j, Measurable fun p => G₀ p i j) (hG_sol : ∀ i j, Measurable fun p => G_sol p i j) :
    ∀ i j, Measurable fun p => corePerturbGrad γ ν G₀ G_sol p i j :=
  fun i j => measurable_gainConj (fun i' j' => (hG_sol i' j').sub (hG₀ i' j')) i j

theorem corePerturb_weakGrad {c ν γ : ℝ} {μ : ℂ} {vel₀ vel₁ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    {F₀ F₁ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b₀ b_sol : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G₀ G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hsol₀ : IsCausalEnergySolution c ν μ vel₀ F₀ b₀ G₀)
    (hSol : IsCausalEnergySolution c ν μ vel₁ F₁ b_sol G_sol)
    {s : ℝ} (hs : 0 < s) (i j : Fin 2) :
    HasWeakCellDerivC c j
      (fun x => corePerturbVel γ ν b₀ b_sol (s, x) i)
      (fun x => corePerturbGrad γ ν G₀ G_sol (s, x) i j) := by
  have hsub_u : (fun x => b_sol (s, x) i - b₀ (s, x) i) =
      fun x => b_sol (s, x) i + (-1 : ℝ) • b₀ (s, x) i := by
    funext x; simp only [Complex.real_smul]; push_cast; ring
  have hsub_G : (fun x => G_sol (s, x) i j - G₀ (s, x) i j) =
      fun x => G_sol (s, x) i j + (-1 : ℝ) • G₀ (s, x) i j := by
    funext x; simp only [Complex.real_smul]; push_cast; ring
  have hw_diff : HasWeakCellDerivC c j
      (fun x => b_sol (s, x) i - b₀ (s, x) i)
      (fun x => G_sol (s, x) i j - G₀ (s, x) i j) := by
    rw [hsub_u, hsub_G]
    exact hasWeakCellDerivC_add_realSmul j (-1 : ℝ) (hSol.weakGrad s hs i j) (hsol₀.weakGrad s hs i j)
  exact hasWeakCellDerivC_realSmul j (gainG γ ν s)⁻¹ hw_diff

theorem corePerturb_divFree {c ν γ : ℝ} {μ : ℂ} {vel₀ vel₁ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    {F₀ F₁ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b₀ b_sol : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G₀ G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hsol₀ : IsCausalEnergySolution c ν μ vel₀ F₀ b₀ G₀)
    (hSol : IsCausalEnergySolution c ν μ vel₁ F₁ b_sol G_sol)
    {s : ℝ} (hs : 0 < s) :
    ∀ ψ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c,
        (corePerturbVel γ ν b₀ b_sol (s, x) 0 * (B0579.pd 0 ψ x : ℂ) +
          corePerturbVel γ ν b₀ b_sol (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) = 0 := by
  have hdiv_sub : ∀ ψ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c,
        ((b_sol (s, x) 0 - b₀ (s, x) 0) * (B0579.pd 0 ψ x : ℂ) +
          (b_sol (s, x) 1 - b₀ (s, x) 1) * (B0579.pd 1 ψ x : ℂ)) = 0 := by
    have h := divFree_add_realSmul (-1 : ℝ) (hSol.divFree s hs) (hsol₀.divFree s hs)
      (hSol.weakGrad s hs) (hsol₀.weakGrad s hs)
    intro ψ hψ
    refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (h ψ hψ)
    simp only [Complex.real_smul]; push_cast; ring
  have hw_sub : ∀ i j, HasWeakCellDerivC c j
      (fun x => b_sol (s, x) i - b₀ (s, x) i)
      (fun x => G_sol (s, x) i j - G₀ (s, x) i j) := by
    intro i j
    have h := corePerturb_weakGrad (γ := 0) (ν := ν) hsol₀ hSol hs i j
    simpa [corePerturbVel, corePerturbGrad, gainConj, gainG] using h
  have h0_div : ∀ ψ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c,
        ((0 : ℂ) * (B0579.pd 0 ψ x : ℂ) + (0 : ℂ) * (B0579.pd 1 ψ x : ℂ)) = 0 := by
    intro ψ _; simp
  have h0_w : ∀ _i j : Fin 2, HasWeakCellDerivC c j (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ)) :=
    fun _ j => causalNull_hasWeak_zero c j
  have hsmul := divFree_add_realSmul (gainG γ ν s)⁻¹ h0_div hdiv_sub h0_w hw_sub
  intro ψ hψ
  simpa [corePerturbVel, gainConj, zero_add] using hsmul ψ hψ

/-! ## 3. Almost-everywhere `L²(cell c)` slice regularity of `(corePerturbVel, corePerturbGrad)` -/

private theorem lintegral_slice_lt_top_ae_on_Icc {c s₁ s₂ : ℝ}
    {f : ℝ × (ℝ × ℝ) → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, f p < ⊤) :
    ∀ᵐ s ∂volume, s ∈ Icc s₁ s₂ → ∫⁻ x in B0579.cell c, f (s, x) < ⊤ := by
  rw [lintegral_restrict_prod_eq (Icc s₁ s₂) (B0579.cell c) f hf] at hfin
  have hm : Measurable fun s : ℝ => ∫⁻ x in B0579.cell c, f (s, x) :=
    hf.lintegral_prod_right'
  have hae := ae_lt_top hm hfin.ne
  rwa [ae_restrict_iff' measurableSet_Icc] at hae

private theorem ae_Ioo_of_ae_Icc {H : ℝ} (hH : 0 < H) {P : ℝ → Prop}
    (h : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < H → ∀ᵐ s ∂volume, s ∈ Icc s₁ s₂ → P s) :
    ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) H → P s := by
  have hall : ∀ᵐ s ∂volume, ∀ k : ℕ,
      s ∈ Icc (H / ((k : ℝ) + 3)) (H - H / ((k : ℝ) + 3)) → P s := by
    rw [ae_all_iff]
    intro k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hpos : 0 < H / ((k : ℝ) + 3) := by positivity
    have hle : H / ((k : ℝ) + 3) ≤ H / 3 :=
      div_le_div_of_nonneg_left hH.le (by positivity) (by linarith)
    exact h _ _ hpos (by linarith) (by linarith)
  filter_upwards [hall] with s hs hsIoo
  have hs0 : 0 < s / H := div_pos hsIoo.1 hH
  have hs1 : 0 < (H - s) / H := div_pos (sub_pos.2 hsIoo.2) hH
  obtain ⟨k₁, hk₁⟩ := exists_nat_one_div_lt hs0
  obtain ⟨k₂, hk₂⟩ := exists_nat_one_div_lt hs1
  refine hs (max k₁ k₂) ⟨?_, ?_⟩
  · have hk : (k₁ : ℝ) + 1 ≤ (max k₁ k₂ : ℕ) + 3 := by
      have : (k₁ : ℝ) ≤ (max k₁ k₂ : ℕ) := by exact_mod_cast le_max_left k₁ k₂
      linarith
    have h1 : 1 / (((max k₁ k₂ : ℕ) : ℝ) + 3) < s / H :=
      (one_div_le_one_div_of_le (by positivity) hk).trans_lt hk₁
    have h2 := mul_lt_mul_of_pos_right h1 hH
    rw [one_div_mul_eq_div, div_mul_cancel₀ _ hH.ne'] at h2
    exact h2.le
  · have hk : (k₂ : ℝ) + 1 ≤ (max k₁ k₂ : ℕ) + 3 := by
      have : (k₂ : ℝ) ≤ (max k₁ k₂ : ℕ) := by exact_mod_cast le_max_right k₁ k₂
      linarith
    have h1 : 1 / (((max k₁ k₂ : ℕ) : ℝ) + 3) < (H - s) / H :=
      (one_div_le_one_div_of_le (by positivity) hk).trans_lt hk₂
    have h2 := mul_lt_mul_of_pos_right h1 hH
    rw [one_div_mul_eq_div, div_mul_cancel₀ _ hH.ne'] at h2
    linarith

private theorem memLp_two_of_lintegral_sq_lt_top {c : ℝ} {φ : ℝ × ℝ → ℂ} (hφ : Measurable φ)
    {g : ℝ × ℝ → ℝ} (hg : ∀ x, ‖φ x‖ ^ 2 ≤ g x)
    (hfin : ∫⁻ x in B0579.cell c, ENNReal.ofReal (g x) < ⊤) :
    MemLp φ 2 (volume.restrict (B0579.cell c)) := by
  refine ⟨hφ.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin
  have h2 : ENNReal.toReal 2 = 2 := by norm_num
  rw [h2, ENNReal.rpow_two, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hg x)

private theorem norm_sq_le_vnorm2_sq (a : Fin 2 → ℂ) (i : Fin 2) :
    ‖a i‖ ^ 2 ≤ vnorm2 a ^ 2 := by
  rw [causalLin_vnorm2_sq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖a j‖) (Finset.mem_univ i)

private theorem norm_sq_le_tnorm2_sq (T : Fin 2 → Fin 2 → ℂ) (i j : Fin 2) :
    ‖T i j‖ ^ 2 ≤ tnorm2 T ^ 2 := by
  rw [causalLin_tnorm2_sq]
  calc ‖T i j‖ ^ 2 ≤ ∑ k : Fin 2, ‖T i k‖ ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg ‖T i k‖) (Finset.mem_univ j)
    _ ≤ ∑ l : Fin 2, ∑ k : Fin 2, ‖T l k‖ ^ 2 :=
        Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun k _ => sq_nonneg ‖T l k‖)
          (Finset.mem_univ i)

theorem corePerturb_memLp_ae {c ν γ H : ℝ} (hν : 0 < ν) (hH : 0 < H) {μ : ℂ}
    {vel₀ vel₁ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    {F₀ F₁ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b₀ b_sol : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G₀ G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hsol₀ : IsCausalEnergySolution c ν μ vel₀ F₀ b₀ G₀)
    (hSol : IsCausalEnergySolution c ν μ vel₁ F₁ b_sol G_sol) :
    ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) H →
      (∀ i, MemLp (fun x => corePerturbVel γ ν b₀ b_sol (s, x) i) 2
        (volume.restrict (B0579.cell c))) ∧
      (∀ i j, MemLp (fun x => corePerturbGrad γ ν G₀ G_sol (s, x) i j) 2
        (volume.restrict (B0579.cell c))) := by
  have hDiff := causalSolSub c ν μ vel₁ F₁ F₁ b_sol b_sol G_sol G_sol hSol hSol
  have hmu := measurable_corePerturbVel γ ν hsol₀.measurable hSol.measurable
  have hmG := measurable_corePerturbGrad γ ν hsol₀.gradMeasurable hSol.gradMeasurable
  have hmF : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (vnorm2 (corePerturbVel γ ν b₀ b_sol p) ^ 2 +
        tnorm2 (corePerturbGrad γ ν G₀ G_sol p) ^ 2) :=
    (((causalLin_measurable_vnorm2 hmu).pow_const 2).add
      ((causalLin_measurable_tnorm2 hmG).pow_const 2)).ennreal_ofReal
  have hIcc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < H →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (corePerturbVel γ ν b₀ b_sol p) ^ 2 +
          tnorm2 (corePerturbGrad γ ν G₀ G_sol p) ^ 2) < ⊤ := by
    intro s₁ s₂ hs₁ hs₁₂ _
    have hI₀ := hsol₀.energyLoc s₁ s₂ hs₁ hs₁₂
    have hI₁ := hSol.energyLoc s₁ s₂ hs₁ hs₁₂
    have hX : Measurable fun p : ℝ × (ℝ × ℝ) => vnorm2 (b_sol p) ^ 2 + tnorm2 (G_sol p) ^ 2 :=
      ((causalLin_measurable_vnorm2 hSol.measurable).pow_const 2).add
        ((causalLin_measurable_tnorm2 hSol.gradMeasurable).pow_const 2)
    have hsub_fin : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (fun i => b_sol p i - b₀ p i) ^ 2 +
          tnorm2 (fun i j => G_sol p i j - G₀ p i j) ^ 2) < ⊤ := by
      have hD : ∀ p : ℝ × (ℝ × ℝ),
          vnorm2 (fun i => b_sol p i - b₀ p i) ^ 2 +
            tnorm2 (fun i j => G_sol p i j - G₀ p i j) ^ 2 ≤
          2 * (vnorm2 (b_sol p) ^ 2 + tnorm2 (G_sol p) ^ 2) +
            2 * (vnorm2 (b₀ p) ^ 2 + tnorm2 (G₀ p) ^ 2) := fun p => by
        linarith [causalLin_vnorm2_sub_sq_le (b_sol p) (b₀ p),
          causalLin_tnorm2_sub_sq_le (G_sol p) (G₀ p)]
      have key := causalLin_lintegral_le (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c)) hX hD
      exact lt_of_le_of_lt key (by finiteness)
    set E : ℝ := Real.exp (|γ| / ν)
    have hE0 : 0 ≤ E := Real.exp_nonneg _
    have hS_meas : MeasurableSet (Icc s₁ s₂ ×ˢ B0579.cell c) :=
      measurableSet_Icc.prod (ceP_measurableSet_cell c)
    have hpt : ∀ p ∈ Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (corePerturbVel γ ν b₀ b_sol p) ^ 2 +
          tnorm2 (corePerturbGrad γ ν G₀ G_sol p) ^ 2) ≤
        ENNReal.ofReal (E ^ 2) *
          ENNReal.ofReal (vnorm2 (fun i => b_sol p i - b₀ p i) ^ 2 +
            tnorm2 (fun i j => G_sol p i j - G₀ p i j) ^ 2) := by
      intro p hp
      rw [← ENNReal.ofReal_mul (sq_nonneg E)]
      apply ENNReal.ofReal_le_ofReal
      have hs0 : 0 ≤ p.1 := ( hs₁.le.trans hp.1.1 )
      have hg_ge : Real.exp (-(|γ| / ν)) ≤ gainG γ ν p.1 := (gainG_bounds hν hs0).1
      have hg_pos : 0 < gainG γ ν p.1 := by unfold gainG; exact Real.exp_pos _
      have hginv_le : (gainG γ ν p.1)⁻¹ ≤ E := by
        unfold E
        rw [Real.exp_neg] at hg_ge
        exact inv_le_of_inv_le₀ (Real.exp_pos _) hg_ge
      have hsq_le : ((gainG γ ν p.1)⁻¹) ^ 2 ≤ E ^ 2 :=
        pow_le_pow_left₀ (inv_nonneg.2 hg_pos.le) hginv_le 2
      have hv_eq := ceP_vnorm2_smul_sq (gainG γ ν p.1)⁻¹ (fun i => b_sol p i - b₀ p i)
      have ht_eq := ceP_tnorm2_smul_sq (gainG γ ν p.1)⁻¹ (fun i j => G_sol p i j - G₀ p i j)
      change vnorm2 (fun i => (gainG γ ν p.1)⁻¹ • (b_sol p i - b₀ p i)) ^ 2 +
          tnorm2 (fun i j => (gainG γ ν p.1)⁻¹ • (G_sol p i j - G₀ p i j)) ^ 2 ≤ _
      rw [hv_eq, ht_eq, ← mul_add]
      exact mul_le_mul_of_nonneg_right hsq_le (by positivity)
    calc ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
            ENNReal.ofReal (vnorm2 (corePerturbVel γ ν b₀ b_sol p) ^ 2 +
              tnorm2 (corePerturbGrad γ ν G₀ G_sol p) ^ 2)
        ≤ ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
            ENNReal.ofReal (E ^ 2) *
              ENNReal.ofReal (vnorm2 (fun i => b_sol p i - b₀ p i) ^ 2 +
                tnorm2 (fun i j => G_sol p i j - G₀ p i j) ^ 2) :=
          setLIntegral_mono' hS_meas hpt
      _ = ENNReal.ofReal (E ^ 2) * ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
            ENNReal.ofReal (vnorm2 (fun i => b_sol p i - b₀ p i) ^ 2 +
              tnorm2 (fun i j => G_sol p i j - G₀ p i j) ^ 2) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsub_fin
  have hae_fin : ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) H →
      ∫⁻ x in B0579.cell c,
        ENNReal.ofReal (vnorm2 (corePerturbVel γ ν b₀ b_sol (s, x)) ^ 2 +
          tnorm2 (corePerturbGrad γ ν G₀ G_sol (s, x)) ^ 2) < ⊤ :=
    ae_Ioo_of_ae_Icc hH fun s₁ s₂ hs₁ hs₁₂ hs₂H =>
      lintegral_slice_lt_top_ae_on_Icc hmF (hIcc s₁ s₂ hs₁ hs₁₂ hs₂H)
  filter_upwards [hae_fin] with s hs hsIoo
  have hfin_s := hs hsIoo
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · refine memLp_two_of_lintegral_sq_lt_top
      ((hmu i).comp (measurable_const.prodMk measurable_id))
      (fun x => (norm_sq_le_vnorm2_sq _ i).trans
        (le_add_of_nonneg_right (sq_nonneg (tnorm2 _)))) hfin_s
  · refine memLp_two_of_lintegral_sq_lt_top
      ((hmG i j).comp (measurable_const.prodMk measurable_id))
      (fun x => (norm_sq_le_tnorm2_sq _ i j).trans
        (le_add_of_nonneg_left (sq_nonneg (vnorm2 _)))) hfin_s

/-! ## 4. Null-set modification of `(corePerturbVel, corePerturbGrad)` preserves `IsCoreCausalSolution` -/

/-- Redefining `(corePerturbVel, corePerturbGrad)` to `0` on `{p | p.1 ∈ N}` for any measurable
null set of ages `N ⊆ ℝ` (`volume N = 0`) preserves `IsCoreCausalSolution` for
`(b₀ + g • u₁, G₀ + g • G₁)` on `(0, H)`. -/
theorem isCoreCausalSolution_of_nullKeep {c ν γ H : ℝ} {μ : ℂ}
    {tr : UnforcedLeray.B0140.TrainSol ν c}
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b₀ b_sol : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G₀ G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hsol₀ : IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b₀ G₀)
    (hSol : IsCausalEnergySolution c ν μ (trainVel tr) F b_sol G_sol)
    {N : Set ℝ} (hNmeas : MeasurableSet N) (hN0 : (volume : Measure ℝ) N = 0) :
    IsCoreCausalSolution c ν H μ (trainVel tr) F
      (fun p i => b₀ p i + gainG γ ν p.1 •
        causalNullKeep N (fun q => corePerturbVel γ ν b₀ b_sol q i) p)
      (fun p i j => G₀ p i j + gainG γ ν p.1 •
        causalNullKeep N (fun q => corePerturbGrad γ ν G₀ G_sol q i j) p) := by
  set u₁ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ :=
    fun p i => causalNullKeep N (fun q => corePerturbVel γ ν b₀ b_sol q i) p
  set G₁ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ :=
    fun p i j => causalNullKeep N (fun q => corePerturbGrad γ ν G₀ G_sol q i j) p
  have hmu₁ : ∀ i, Measurable fun p => u₁ p i :=
    fun i => causalNull_measurable hNmeas
      (measurable_corePerturbVel γ ν hsol₀.measurable hSol.measurable i)
  have hmG₁ : ∀ i j, Measurable fun p => G₁ p i j :=
    fun i j => causalNull_measurable hNmeas
      (measurable_corePerturbGrad γ ν hsol₀.gradMeasurable hSol.gradMeasurable i j)
  have hmg : Measurable fun p : ℝ × (ℝ × ℝ) => gainG γ ν p.1 :=
    (ceP_measurable_gainG γ ν).comp measurable_fst
  have hb_off : ∀ p : ℝ × (ℝ × ℝ), p.1 ∉ N → ∀ i,
      b₀ p i + gainG γ ν p.1 • u₁ p i = b_sol p i := by
    intro p hpN i
    have hkeep : u₁ p i = corePerturbVel γ ν b₀ b_sol p i :=
      causalNullKeep_of_mem _ (show p ∈ (Prod.fst ⁻¹' N)ᶜ from hpN)
    rw [hkeep]
    unfold corePerturbVel gainConj
    simp only [Pi.smul_apply]
    have hg_ne : gainG γ ν p.1 ≠ 0 := by unfold gainG; exact (Real.exp_pos _).ne'
    rw [smul_inv_smul₀ hg_ne]
    ring
  have hG_off : ∀ p : ℝ × (ℝ × ℝ), p.1 ∉ N → ∀ i j,
      G₀ p i j + gainG γ ν p.1 • G₁ p i j = G_sol p i j := by
    intro p hpN i j
    have hkeep : G₁ p i j = corePerturbGrad γ ν G₀ G_sol p i j :=
      causalNullKeep_of_mem _ (show p ∈ (Prod.fst ⁻¹' N)ᶜ from hpN)
    rw [hkeep]
    unfold corePerturbGrad gainConj
    simp only [Pi.smul_apply]
    have hg_ne : gainG γ ν p.1 ≠ 0 := by unfold gainG; exact (Real.exp_pos _).ne'
    rw [smul_inv_smul₀ hg_ne]
    ring
  have hb_on : ∀ p : ℝ × (ℝ × ℝ), p.1 ∈ N → ∀ i,
      b₀ p i + gainG γ ν p.1 • u₁ p i = b₀ p i := by
    intro p hpN i
    have hkeep : u₁ p i = 0 :=
      causalNullKeep_of_null _ (show p ∈ Prod.fst ⁻¹' N from hpN)
    simp [hkeep]
  have hG_on : ∀ p : ℝ × (ℝ × ℝ), p.1 ∈ N → ∀ i j,
      G₀ p i j + gainG γ ν p.1 • G₁ p i j = G₀ p i j := by
    intro p hpN i j
    have hkeep : G₁ p i j = 0 :=
      causalNullKeep_of_null _ (show p ∈ Prod.fst ⁻¹' N from hpN)
    simp [hkeep]
  have hZv : (volume : Measure (ℝ × (ℝ × ℝ))) (Prod.fst ⁻¹' N) = 0 :=
    causalNull_volume_null hN0
  have hZa : ageμ c (-3 / 2) (Prod.fst ⁻¹' N) = 0 :=
    causalNull_age_null c (-3 / 2) hNmeas hN0
  have hae_v_b : ∀ᵐ p ∂(volume : Measure (ℝ × (ℝ × ℝ))),
      (fun i => b₀ p i + gainG γ ν p.1 • u₁ p i) = b_sol p := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.2 hZv] with p hp
    exact funext (hb_off p hp)
  have hae_v_G : ∀ᵐ p ∂(volume : Measure (ℝ × (ℝ × ℝ))),
      (fun i j => G₀ p i j + gainG γ ν p.1 • G₁ p i j) = G_sol p := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.2 hZv] with p hp
    exact funext fun i => funext (hG_off p hp i)
  have hae_a_b : ∀ᵐ p ∂(ageμ c (-3 / 2)),
      (fun i => b₀ p i + gainG γ ν p.1 • u₁ p i) = b_sol p := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.2 hZa] with p hp
    exact funext (hb_off p hp)
  refine
    { measurable := fun i => (hsol₀.measurable i).add (hmg.smul (hmu₁ i))
      gradMeasurable := fun i j => (hsol₀.gradMeasurable i j).add (hmg.smul (hmG₁ i j))
      energyLoc := ?_
      zeroEntrance := ?_
      divFree := ?_
      weakGrad := ?_
      integrable := ?_
      weak := ?_ }
  · intro s₁ s₂ hs₁ hs₁₂ _
    refine lt_of_eq_of_lt (MeasureTheory.lintegral_congr_ae ?_) (hSol.energyLoc s₁ s₂ hs₁ hs₁₂)
    filter_upwards [MeasureTheory.ae_restrict_of_ae (s := Icc s₁ s₂ ×ˢ B0579.cell c) hae_v_b,
      MeasureTheory.ae_restrict_of_ae (s := Icc s₁ s₂ ×ˢ B0579.cell c) hae_v_G] with p hbp hGp
    change ENNReal.ofReal (vnorm2 (fun i => b₀ p i + gainG γ ν p.1 • u₁ p i) ^ 2 +
        tnorm2 (fun i j => G₀ p i j + gainG γ ν p.1 • G₁ p i j) ^ 2) = _
    rw [hbp, hGp]
  · obtain ⟨δ, hδ, hfin⟩ := hSol.zeroEntrance
    refine ⟨δ, hδ, lt_of_eq_of_lt (MeasureTheory.lintegral_congr_ae ?_) hfin⟩
    filter_upwards [MeasureTheory.ae_restrict_of_ae (s := Ioo 0 δ ×ˢ univ) hae_a_b] with p hbp
    change ENNReal.ofReal (vnorm2 (fun i => b₀ p i + gainG γ ν p.1 • u₁ p i) ^ 2) = _
    rw [hbp]
  · intro s hs ψ hψ
    by_cases hsN : s ∈ N
    · refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (hsol₀.divFree s hs.1 ψ hψ)
      dsimp only
      rw [hb_on (s, x) hsN 0, hb_on (s, x) hsN 1]
    · refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (hSol.divFree s hs.1 ψ hψ)
      dsimp only
      rw [hb_off (s, x) hsN 0, hb_off (s, x) hsN 1]
  · intro s hs i j
    by_cases hsN : s ∈ N
    · have h0 : (fun x => b₀ (s, x) i + gainG γ ν s • u₁ (s, x) i) = fun x => b₀ (s, x) i :=
        funext fun x => hb_on (s, x) hsN i
      have h0G : (fun x => G₀ (s, x) i j + gainG γ ν s • G₁ (s, x) i j) =
          fun x => G₀ (s, x) i j :=
        funext fun x => hG_on (s, x) hsN i j
      rw [h0, h0G]
      exact hsol₀.weakGrad s hs.1 i j
    · have h1 : (fun x => b₀ (s, x) i + gainG γ ν s • u₁ (s, x) i) = fun x => b_sol (s, x) i :=
        funext fun x => hb_off (s, x) hsN i
      have h1G : (fun x => G₀ (s, x) i j + gainG γ ν s • G₁ (s, x) i j) =
          fun x => G_sol (s, x) i j :=
        funext fun x => hG_off (s, x) hsN i j
      rw [h1, h1G]
      exact hSol.weakGrad s hs.1 i j
  · intro Φ hΦ _
    refine MeasureTheory.Integrable.congr (hSol.integrable Φ hΦ) ?_
    filter_upwards [MeasureTheory.ae_restrict_of_ae (s := Ioi (0 : ℝ) ×ˢ B0579.cell c) hae_v_b]
      with p hbp
    exact (causalNull_flat_congr ν μ (trainVel tr) F Φ b_sol
      (fun q i => b₀ q i + gainG γ ν q.1 • u₁ q i) p (congrFun hbp)).symm
  · intro Φ hΦ _
    have hae_flat :
        flatIntegrand ν μ (trainVel tr) F (fun q i => b₀ q i + gainG γ ν q.1 • u₁ q i) Φ
          =ᵐ[volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)]
        flatIntegrand ν μ (trainVel tr) F b_sol Φ := by
      filter_upwards [MeasureTheory.ae_restrict_of_ae (s := Ioi (0 : ℝ) ×ˢ B0579.cell c) hae_v_b]
        with p hbp
      exact causalNull_flat_congr ν μ (trainVel tr) F Φ b_sol
        (fun q i => b₀ q i + gainG γ ν q.1 • u₁ q i) p (congrFun hbp)
    exact (MeasureTheory.integral_congr_ae hae_flat).trans (hSol.weak Φ hΦ)

/-! ## 5. Leaf statements for `PartIII-a:T19/2/3` (`PartIII-a:T19/2/3/1..2`) -/

/-- **Leaf `PartIII-a:T19/2/3/1` (`CoreBiotSavartSliceBound`, SP lines 3497-3515)**:
Given the Biot-Savart `H¹(cell c)` reconstruction hypothesis (`C_BS`), for any `c ≥ 1` and any
measurable divergence-free `H¹(cell c)` velocity/gradient slice `(u, G)` on `B0579.cell c` whose
weak curl `ω(x) = G x 1 0 - G x 0 1` belongs to `X_{9,c}` with `HasZeroCirculation c ω`, the pair
`(u, G)` coincides a.e. on `B0579.cell c` with the Biot-Savart reconstruction of `ω` (since the
difference `u - u_BS ∈ H¹(cell c)` is divergence-free and curl-free on the cylinder `B0579.cell c`,
so its cylinder Fourier modes vanish, SP 3511-3514), and therefore satisfies the Biot-Savart `H¹`
bound `∫_{cell c} ‖u‖² ≤ (C_BS ‖ω‖_{X_{9,c}})²` and `∫_{cell c} ‖G‖² ≤ (C_BS ‖ω‖_{X_{9,c}})²`. -/
def CoreBiotSavartSliceBound : Prop :=
  ∀ (C_BS : ℝ), 0 ≤ C_BS →
    (∀ (c : ℝ), 1 ≤ c → ∀ (f : ℝ × ℝ → ℂ),
      MemLp f 2 (B0579.cellMeasure c 9) → HasZeroCirculation c f →
      ∃ (u : ℝ × ℝ → Fin 2 → ℂ) (G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ),
        (∀ i, Measurable fun x => u x i) ∧
        (∀ i j, Measurable fun x => G x i j) ∧
        IsBiotSavart c f u ∧
        (∀ i j : Fin 2, HasWeakCellDerivC c j (fun x => u x i) (fun x => G x i j)) ∧
        (∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ≤
          (ENNReal.ofReal C_BS * xNorm c 9 f) ^ (2 : ℝ) ∧
        (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ≤
          (ENNReal.ofReal C_BS * xNorm c 9 f) ^ (2 : ℝ)) →
    ∀ (c : ℝ), 1 ≤ c →
      ∀ (u : ℝ × ℝ → Fin 2 → ℂ) (G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ),
        (∀ i, Measurable fun x => u x i) →
        (∀ i j, Measurable fun x => G x i j) →
        (∀ i, MemLp (fun x => u x i) 2 (volume.restrict (B0579.cell c))) →
        (∀ i j, MemLp (fun x => G x i j) 2 (volume.restrict (B0579.cell c))) →
        (∀ ψ, B0579.IsCylTest c ψ →
          ∫ x in B0579.cell c,
            (u x 0 * (B0579.pd 0 ψ x : ℂ) + u x 1 * (B0579.pd 1 ψ x : ℂ)) = 0) →
        (∀ i j : Fin 2, HasWeakCellDerivC c j (fun x => u x i) (fun x => G x i j)) →
        MemLp (fun x => G x 1 0 - G x 0 1) 2 (B0579.cellMeasure c 9) →
        HasZeroCirculation c (fun x => G x 1 0 - G x 0 1) →
        (∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ≤
            (ENNReal.ofReal C_BS * xNorm c 9 (fun x => G x 1 0 - G x 0 1)) ^ (2 : ℝ) ∧
          (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ≤
            (ENNReal.ofReal C_BS * xNorm c 9 (fun x => G x 1 0 - G x 0 1)) ^ (2 : ℝ)

/-- **Leaf `PartIII-a:T19/2/3/2` (`CoreDuhamelVorticityBound`, SP lines 3462-3496)**:
Forward Duhamel vorticity bound on the core `(0, coreEnd ν b)`:
given the curl duality bound (`C_dual`), for `0 < ν ≤ ν_vort`, BUC train `tr` with core coefficient
bound `A_m` on `(0, coreEnd ν b)` and `ClockBoundAt P 9 b C_clock ν tr`, free causal solution
`(b₀, G₀)` of `F`, and train causal solution `(b_sol, G_sol)` of `F`, the perturbation vorticity
`ω s = corePerturbVort P.eigenvalue.re ν G₀ G_sol s` satisfies for almost every
`s ∈ Ioo (0 : ℝ) (coreEnd ν b)`:
`MemLp (ω s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9)`, `HasZeroCirculation (ν ^ (-2 : ℝ)) (ω s)`, and
the Duhamel clock integral bound
`xNorm c 9 (ω s) ≤ ∫⁻ t in Ioo 0 s, |C_clock| ν^{-M_s} (t/s)^{Re μ} (1 + (s-t)^{-1/2}) C_dual A_m (‖u₀(t)‖₂ + ‖G̃₀(t)‖₂) dt`. -/
def CoreDuhamelVorticityBound : Prop :=
  ∀ (C_dual : ℝ), 0 ≤ C_dual →
    (∀ (c A_m : ℝ), 0 < c → 0 ≤ A_m →
      ∀ (v : ℝ × ℝ → Fin 2 → ℝ), ContDiff ℝ 1 v →
        (∀ x ∈ B0579.cell c, B0579.bracket x ^ (9 : ℝ) * (‖v x‖ + ‖fderiv ℝ v x‖) ≤ A_m) →
        ∀ (u : ℝ × ℝ → Fin 2 → ℂ) (G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ),
          (∀ i, Measurable fun x => u x i) → (∀ i j, Measurable fun x => G x i j) →
          (∫⁻ x in B0579.cell c,
              ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2)) ^
            (1 / 2 : ℝ) ≤
            ENNReal.ofReal (C_dual * A_m) *
              ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ^ (1 / 2 : ℝ) +
                (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ^ (1 / 2 : ℝ)) ∧
          ∀ (f : ℝ × ℝ → ℂ),
            (∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
              (∀ j, HasWeakCellDerivC c j φ (g j)) → h1Norm c 9 φ g ≤ 1 →
              ENNReal.ofReal ‖∫ x in B0579.cell c, f x * φ x‖ ≤
                ∫⁻ x in B0579.cell c,
                  ENNReal.ofReal (vnorm2 (advStretch v u G x) * vnorm2 (fun j => g j x))) →
            negNorm c 9 f ≤
              ENNReal.ofReal (C_dual * A_m) *
                ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ^ (1 / 2 : ℝ) +
                  (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ^ (1 / 2 : ℝ))) →
    ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
      ∀ b : ℝ, 1 ≤ b → ∃ ν_vort : ℝ, 0 < ν_vort ∧
        ∀ ν ∈ Ioc 0 ν_vort, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ μ ∈ K,
          ∀ A_m C_clock : ℝ, 0 ≤ A_m →
            (∀ s ∈ Ioc (0 : ℝ) (coreEnd ν b), ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
              B0579.bracket x ^ (9 : ℝ) * (‖tr.v s x‖ + ‖fderiv ℝ (tr.v s) x‖) ≤ A_m) →
            ClockBoundAt P 9 b C_clock ν tr →
            ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ p i j, F p i j = F p j i) →
              (∀ i j, Measurable fun p => F p i j) →
              tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) < ⊤ →
              ∀ b₀ G₀, IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (fun _ _ _ => 0) F b₀ G₀ →
                ∀ b_sol G_sol,
                  IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (trainVel tr) F b_sol G_sol →
                  ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) (coreEnd ν b) →
                    MemLp (corePerturbVort P.eigenvalue.re ν G₀ G_sol s) 2
                      (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9) ∧
                    HasZeroCirculation (ν ^ (-2 : ℝ))
                      (corePerturbVort P.eigenvalue.re ν G₀ G_sol s) ∧
                    xNorm (ν ^ (-2 : ℝ)) 9 (corePerturbVort P.eigenvalue.re ν G₀ G_sol s) ≤
                      ∫⁻ t in Ioo (0 : ℝ) s,
                        ENNReal.ofReal (|C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) *
                          (t / s) ^ μ.re * (1 + (s - t) ^ (-1 / 2 : ℝ))) *
                          (ENNReal.ofReal (C_dual * A_m) *
                            (unnormSliceVel (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b₀) t +
                              unnormSliceGrad (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G₀) t))

/-! ## 6. Conditional assembly of `CoreDuhamelPropagation` -/

/-- **Conditional assembly of `CoreDuhamelPropagation`** (`PartIII-a:T19/2/3`, SP 3489-3515)
from `CoreBiotSavartSliceBound` and `CoreDuhamelVorticityBound` (together with
`trainCausalExistence` from `GlobalExistence.lean`). -/
theorem coreDuhamelPropagation_of (hBS_slice : CoreBiotSavartSliceBound)
    (hVort : CoreDuhamelVorticityBound) :
    UnforcedLeray.Short.IIIa.CoreDuhamelPropagation := by
  intro C_dual C_BS hC_dual hC_BS hDual hBS P hP K hK b hb1
  obtain ⟨ν_ex, hν_ex, hEx_P⟩ := trainCausalExistence P hP K hK
  obtain ⟨ν_vort, hν_vort, hVort_P⟩ :=
    hVort C_dual hC_dual
      (fun c A_m hc hAm v hv hv_bd u G hu hG => (hDual c A_m hc hAm v hv hv_bd u G hu hG).2)
      P hP K hK b hb1
  set ν_core : ℝ := min (min ν_ex ν_vort) (min (1 / 2) ((2 * b)⁻¹))
  have hν_core : 0 < ν_core :=
    lt_min (lt_min hν_ex hν_vort) (lt_min (by norm_num) (inv_pos.2 (by linarith)))
  refine ⟨ν_core, hν_core,
    fun ν hν tr htr μ hμ A_m C_clock hAm0 hAm hClk F hsym hmeas hfin b₀ G₀ hsol₀ => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν_e : ν ≤ ν_ex := hν.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_v : ν ≤ ν_vort := hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_half : ν ≤ 1 / 2 := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_2b : ν ≤ (2 * b)⁻¹ := hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hH1, hHc, -, -⟩ := coreEnd_bounds hb1 hν0 hν_half hν_2b
  have hH0 : 0 < coreEnd ν b := by linarith
  have hc1 : 1 ≤ ν ^ (-2 : ℝ) := by linarith
  obtain ⟨b_sol, G_sol, hSol⟩ := hEx_P ν ⟨hν0, hν_e⟩ tr htr μ hμ F hsym hmeas hfin
  have hae_vort := hVort_P ν ⟨hν0, hν_v⟩ tr htr μ hμ A_m C_clock hAm0 hAm hClk
    F hsym hmeas hfin b₀ G₀ hsol₀ b_sol G_sol hSol
  have hae_memLp := corePerturb_memLp_ae (γ := P.eigenvalue.re) hν0 hH0 hsol₀ hSol
  set c : ℝ := ν ^ (-2 : ℝ)
  set γ : ℝ := P.eigenvalue.re
  set H : ℝ := coreEnd ν b
  set u₁_raw := corePerturbVel γ ν b₀ b_sol
  set G₁_raw := corePerturbGrad γ ν G₀ G_sol
  set ω_raw := corePerturbVort γ ν G₀ G_sol
  -- Good-slice predicate on `s ∈ Ioo 0 H`
  let goodSlice (s : ℝ) : Prop :=
    s ∈ Ioo (0 : ℝ) H →
      (∀ i, MemLp (fun x => u₁_raw (s, x) i) 2 (volume.restrict (B0579.cell c))) ∧
      (∀ i j, MemLp (fun x => G₁_raw (s, x) i j) 2 (volume.restrict (B0579.cell c))) ∧
      MemLp (ω_raw s) 2 (B0579.cellMeasure c 9) ∧
      HasZeroCirculation c (ω_raw s) ∧
      xNorm c 9 (ω_raw s) ≤
        ∫⁻ t in Ioo (0 : ℝ) s,
          ENNReal.ofReal (|C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) *
            (t / s) ^ μ.re * (1 + (s - t) ^ (-1 / 2 : ℝ))) *
            (ENNReal.ofReal (C_dual * A_m) *
              (unnormSliceVel c (gainConj γ ν b₀) t +
                unnormSliceGrad c (gainConj γ ν G₀) t))
  have hae_good : ∀ᵐ s ∂(volume : Measure ℝ), goodSlice s := by
    filter_upwards [hae_memLp, hae_vort] with s hm hv hs
    exact ⟨(hm hs).1, (hm hs).2, (hv hs).1, (hv hs).2.1, (hv hs).2.2⟩
  obtain ⟨N, hNsub, hNmeas, hN0⟩ :=
    exists_measurable_superset_of_null (MeasureTheory.ae_iff.1 hae_good)
  have hgood_off : ∀ s : ℝ, s ∉ N → goodSlice s := by
    intro s hsN
    by_contra hcon
    exact hsN (hNsub hcon)
  classical
  let W_raw : ℝ → ℝ≥0∞ := fun s => if s ∈ N then 0 else xNorm c 9 (ω_raw s)
  let u₁ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p i => causalNullKeep N (fun q => u₁_raw q i) p
  let G₁ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ :=
    fun p i j => causalNullKeep N (fun q => G₁_raw q i j) p
  have hmu_raw := measurable_corePerturbVel γ ν hsol₀.measurable hSol.measurable
  have hmG_raw := measurable_corePerturbGrad γ ν hsol₀.gradMeasurable hSol.gradMeasurable
  refine ⟨W_raw, u₁, G₁,
    fun i => causalNull_measurable hNmeas (hmu_raw i),
    fun i j => causalNull_measurable hNmeas (hmG_raw i j),
    isCoreCausalSolution_of_nullKeep hsol₀ hSol hNmeas hN0,
    fun s hs => ?_, fun s hs => ?_⟩
  · by_cases hsN : s ∈ N
    · simp [W_raw, hsN]
    · simp only [W_raw, hsN, ↓reduceIte]
      exact ((hgood_off s hsN hs).2.2.2.2)
  · by_cases hsN : s ∈ N
    · have hu0 : ∀ x : ℝ × ℝ, u₁ (s, x) = 0 := by
        intro x; funext i
        exact causalNullKeep_of_null _ (show (s, x) ∈ Prod.fst ⁻¹' N from hsN)
      have hG0 : ∀ x : ℝ × ℝ, G₁ (s, x) = 0 := by
        intro x; funext i j
        exact causalNullKeep_of_null _ (show (s, x) ∈ Prod.fst ⁻¹' N from hsN)
      have hv0 : ∀ x : ℝ × ℝ, vnorm2 (u₁ (s, x)) ^ 2 = 0 := by
        intro x; rw [hu0 x, causalLin_vnorm2_sq]; simp
      have ht0 : ∀ x : ℝ × ℝ, tnorm2 (G₁ (s, x)) ^ 2 = 0 := by
        intro x; rw [hG0 x, causalLin_tnorm2_sq]; simp
      simp [hv0, ht0]
    · simp only [W_raw, hsN, ↓reduceIte]
      have hu_eq : ∀ x : ℝ × ℝ, u₁ (s, x) = u₁_raw (s, x) := by
        intro x; funext i
        exact causalNullKeep_of_mem _ (show (s, x) ∈ (Prod.fst ⁻¹' N)ᶜ from hsN)
      have hG_eq : ∀ x : ℝ × ℝ, G₁ (s, x) = G₁_raw (s, x) := by
        intro x; funext i j
        exact causalNullKeep_of_mem _ (show (s, x) ∈ (Prod.fst ⁻¹' N)ᶜ from hsN)
      simp only [hu_eq, hG_eq]
      obtain ⟨hmu_lp, hmG_lp, hω_lp, hω_circ, -⟩ := hgood_off s hsN hs
      exact hBS_slice C_BS hC_BS hBS c hc1
        (fun x => u₁_raw (s, x)) (fun x => G₁_raw (s, x))
        (fun i => (hmu_raw i).comp (measurable_const.prodMk measurable_id))
        (fun i j => (hmG_raw i j).comp (measurable_const.prodMk measurable_id))
        hmu_lp hmG_lp
        (corePerturb_divFree hsol₀ hSol hs.1)
        (corePerturb_weakGrad hsol₀ hSol hs.1)
        hω_lp hω_circ

end UnforcedLeray.Short.IIIa
