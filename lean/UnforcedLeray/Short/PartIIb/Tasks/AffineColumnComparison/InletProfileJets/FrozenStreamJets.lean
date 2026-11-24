import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_2
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream

/-!
# Part II-b, task `PartII-b:G4/5/2/2/2` (`FrozenStreamJets`)

Source of record: `the November 2 reference manuscript`, lines 2347-2369, 2383-2385.
The frozen streams are `frozenLin i ∘ periodicStream p.mode p.c` with `frozenLin` the continuous
linear functionals `2 Re` and `-2 Im`. Jets of the composition are the jets of the periodized
eigenstream composed with a fixed linear functional; the bounds of `frozenStreamBounds` at orders
`l ≤ j` are merged by taking sums of constants, the largest exponent, and the smallest rate.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint

/-- The two frozen-stream components as continuous real linear functionals on `ℂ`. -/
def frozenLin : Fin 2 → (ℂ →L[ℝ] ℝ) := ![(2 : ℝ) • Complex.reCLM, (-2 : ℝ) • Complex.imCLM]

theorem frozenStream_eq_comp_lin (p : Params) (i : Fin 2) :
    p.frozenStream i = (frozenLin i) ∘ (periodicStream p.mode p.c) := by
  funext x
  fin_cases i <;> simp [Params.frozenStream, frozenLin]

theorem frozenLin_norm_le_sum (i : Fin 2) :
    ‖frozenLin i‖ ≤ ‖frozenLin 0‖ + ‖frozenLin 1‖ := by
  fin_cases i
  · exact le_add_of_nonneg_right (norm_nonneg _)
  · exact le_add_of_nonneg_left (norm_nonneg _)

theorem frozenStreamJets : UnforcedLeray.Short.IIb.FrozenStreamJets := by
  intro lam q hq j
  choose C κ N hC hκ hper using fun l : ℕ => frozenStreamBounds lam q hq l
  obtain ⟨l0, hl0, hmin⟩ := Finset.exists_min_image (Finset.range (j + 1)) κ
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩
  set K : ℝ := ‖frozenLin 0‖ + ‖frozenLin 1‖ with hK
  set S : ℝ := ∑ l ∈ Finset.range (j + 1), C l with hS
  set NN : ℕ := ∑ l ∈ Finset.range (j + 1), N l with hNN
  have hK0 : 0 ≤ K := by positivity
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun l _ => (hC l).le)
  have hpos : 0 < (1 + K) * (1 + S) := by positivity
  refine ⟨(1 + K) * (1 + S), κ l0, NN, hpos, hκ l0, ?_⟩
  intro p hmode hc1 i l hl x
  have hc0 : 0 < p.c := by linarith
  have hlj : l ∈ Finset.range (j + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hl)
  have hCle : C l ≤ 1 + S := by
    have := Finset.single_le_sum (f := C) (fun i _ => (hC i).le) hlj
    linarith
  have hNle : N l ≤ NN := by
    have := Finset.single_le_sum (f := N) (fun i _ => Nat.zero_le (N i)) hlj
    exact this
  have hκle : κ l0 ≤ κ l := hmin l hlj
  have hcomp : ‖iteratedFDeriv ℝ l (p.frozenStream i) x‖ ≤
      ‖frozenLin i‖ * ‖iteratedFDeriv ℝ l (periodicStream q p.c) x‖ := by
    rw [frozenStream_eq_comp_lin, hmode]
    have hPC : ContDiff ℝ ∞ (periodicStream q p.c) := (hper l p.c hc1).1
    rw [ContinuousLinearMap.iteratedFDeriv_comp_left (frozenLin i) hPC.contDiffAt
      (by exact_mod_cast le_top)]
    exact (frozenLin i).norm_compContinuousMultilinearMap_le _
  have hbound := (hper l p.c hc1).2 x
  have hexp : Real.exp (-(κ l * |x.2| / p.c)) ≤ Real.exp (-(κ l0 * |x.2| / p.c)) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    apply div_le_div_of_nonneg_right _ hc0.le
    exact mul_le_mul_of_nonneg_right hκle (abs_nonneg _)
  have hcN : p.c ^ N l ≤ p.c ^ NN := pow_le_pow_right₀ hc1 hNle
  have hE0 : 0 ≤ Real.exp (-(κ l0 * |x.2| / p.c)) := (Real.exp_pos _).le
  have hcNN0 : 0 ≤ p.c ^ NN := pow_nonneg hc0.le _
  have hCl0 : 0 ≤ C l := (hC l).le
  have hfin1 : ‖iteratedFDeriv ℝ l (periodicStream q p.c) x‖ ≤
      C l * p.c ^ NN * Real.exp (-(κ l0 * |x.2| / p.c)) := by
    calc ‖iteratedFDeriv ℝ l (periodicStream q p.c) x‖
        ≤ C l * p.c ^ N l * Real.exp (-(κ l * |x.2| / p.c)) := hbound
      _ ≤ C l * p.c ^ NN * Real.exp (-(κ l0 * |x.2| / p.c)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hcN hCl0)
          hexp (Real.exp_pos _).le (mul_nonneg hCl0 hcNN0)
  have hKl : ‖frozenLin i‖ ≤ K := frozenLin_norm_le_sum i
  have hKn : 0 ≤ ‖frozenLin i‖ := norm_nonneg _
  have hX0 : 0 ≤ C l * p.c ^ NN * Real.exp (-(κ l0 * |x.2| / p.c)) :=
    mul_nonneg (mul_nonneg hCl0 hcNN0) hE0
  have h3 : C l * p.c ^ NN * Real.exp (-(κ l0 * |x.2| / p.c)) ≤
      (1 + S) * p.c ^ NN * Real.exp (-(κ l0 * |x.2| / p.c)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle hcNN0) hE0
  have h1 : ‖frozenLin i‖ ≤ 1 + K := by linarith
  have hfinal : ‖frozenLin i‖ * (C l * p.c ^ NN * Real.exp (-(κ l0 * |x.2| / p.c))) ≤
      (1 + K) * ((1 + S) * p.c ^ NN * Real.exp (-(κ l0 * |x.2| / p.c))) :=
    mul_le_mul h1 h3 hX0 (by linarith)
  calc ‖iteratedFDeriv ℝ l (p.frozenStream i) x‖
      ≤ ‖frozenLin i‖ * ‖iteratedFDeriv ℝ l (periodicStream q p.c) x‖ := hcomp
    _ ≤ ‖frozenLin i‖ * (C l * p.c ^ NN * Real.exp (-(κ l0 * |x.2| / p.c))) :=
        mul_le_mul_of_nonneg_left hfin1 hKn
    _ ≤ (1 + K) * ((1 + S) * p.c ^ NN * Real.exp (-(κ l0 * |x.2| / p.c))) := hfinal
    _ = (1 + K) * (1 + S) * p.c ^ NN * Real.exp (-(κ l0 * |x.2| / p.c)) := by ring

end UnforcedLeray.Short.IIb
