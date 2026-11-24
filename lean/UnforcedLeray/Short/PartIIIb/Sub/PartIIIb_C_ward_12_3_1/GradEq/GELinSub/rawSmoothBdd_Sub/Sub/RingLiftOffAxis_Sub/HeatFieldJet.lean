import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.ProfileDerivBdd

/-!
# Organizer task `PartIII-b:C/ward/12/3/1/2/6/1/3/1/org/1/org/1/7`: `heatFieldJet`

Source of record: `the November 2 reference manuscript` (SP), lines 1310-1313
(`heatParG`, `heatParH` are polynomials in `w = ϱ²` times Gaussian derivatives in `y₃`) and
1323-1325.

The lift `heatField ν R j y = heatParG • hor y + heatParH • e₃` (with `w = y₀² + y₁²`) is a
finite sum of products of the factors `c · y_i`, `c · w^j` and `g_ν^{(n)}(y₂)`. The Gaussian
derivatives are bounded with all their derivatives (`profileDerivBdd`), and on the region
`ϱ² ≤ W` the coordinate factors `y₀`, `y₁` have bounded jets, so every Cartesian derivative of
`heatField ν R j` is bounded there.

Route: the predicate `HeatJetBdd W f` (bounded jets on `ϱ² ≤ W`) is closed under sums, products
of scalar functions (Leibniz `norm_iteratedFDeriv_mul_le`) and multiplication by constant vectors
(`norm_iteratedFDeriv_comp_left`); it holds for constants, for the coordinates `y₀`, `y₁`, and for
`g(y₂)` when `g` has globally bounded derivatives.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set Filter Topology
open scoped ContDiff
open UnforcedLeray UnforcedLeray.Short.IIb

/-- Bounded Cartesian jets of `f` on the region `ϱ² ≤ W`. -/
abbrev HeatJetBdd (W : ℝ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space → F) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, Axi.ϱ y ^ 2 ≤ W → ‖iteratedFDeriv ℝ k f y‖ ≤ C

theorem hfjAdd {W : ℝ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : Space → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (Hf : HeatJetBdd W f) (Hg : HeatJetBdd W g) : HeatJetBdd W (fun y => f y + g y) := by
  intro k
  obtain ⟨Cf, hCf0, hCf⟩ := Hf k
  obtain ⟨Cg, hCg0, hCg⟩ := Hg k
  refine ⟨Cf + Cg, add_nonneg hCf0 hCg0, fun y hy => ?_⟩
  have hfa : ContDiffAt ℝ k f y := hf.contDiffAt.of_le (by exact_mod_cast le_top)
  have hga : ContDiffAt ℝ k g y := hg.contDiffAt.of_le (by exact_mod_cast le_top)
  have e : iteratedFDeriv ℝ k (fun y => f y + g y) y =
      iteratedFDeriv ℝ k f y + iteratedFDeriv ℝ k g y := iteratedFDeriv_add_apply hfa hga
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (hCf y hy) (hCg y hy))

theorem hfjSmulConst {W : ℝ} {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (v : Space)
    (Hf : HeatJetBdd W f) : HeatJetBdd W (fun y => f y • v) := by
  intro k
  obtain ⟨Cf, hCf0, hCf⟩ := Hf k
  set L : ℝ →L[ℝ] Space := (ContinuousLinearMap.id ℝ ℝ).smulRight v with hLdef
  have hfun : (fun y => f y • v) = L ∘ f := by
    funext y
    simp [hLdef]
  refine ⟨‖L‖ * Cf, mul_nonneg (norm_nonneg _) hCf0, fun y hy => ?_⟩
  have hfa : ContDiffAt ℝ ∞ f y := hf.contDiffAt
  rw [hfun]
  refine (L.norm_iteratedFDeriv_comp_left hfa (by exact_mod_cast le_top)).trans ?_
  exact mul_le_mul_of_nonneg_left (hCf y hy) (norm_nonneg _)

theorem hfjMul {W : ℝ} {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (Hf : HeatJetBdd W f) (Hg : HeatJetBdd W g) : HeatJetBdd W (fun y => f y * g y) := by
  intro k
  choose Cf hCf0 hCf using Hf
  choose Cg hCg0 hCg using Hg
  refine ⟨∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) * Cf i) * Cg (k - i),
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCf0 i)) (hCg0 _),
    fun y hy => ?_⟩
  refine (norm_iteratedFDeriv_mul_le hf hg y (by exact_mod_cast le_top)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hCf i y hy) (Nat.cast_nonneg _)) (hCg _ y hy)
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hCf0 i))

theorem hfjConst {W : ℝ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (c : F) :
    HeatJetBdd W (fun _ : Space => c) := by
  intro k
  refine ⟨‖c‖, norm_nonneg _, fun y _ => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [norm_iteratedFDeriv_zero]
  · rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hk) c]
    simp

theorem hfjPow {W : ℝ} {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (Hf : HeatJetBdd W f) (j : ℕ) :
    HeatJetBdd W (fun y => f y ^ j) := by
  induction j with
  | zero =>
    have e : (fun y => f y ^ (0 : ℕ)) = fun _ : Space => (1 : ℝ) := by
      funext y
      simp
    rw [e]
    exact hfjConst 1
  | succ j ih =>
    have e : (fun y => f y ^ (j + 1)) = fun y => f y ^ j * f y := by
      funext y
      ring
    rw [e]
    exact hfjMul (hf.pow j) hf ih Hf

theorem hfjCompProj {W : ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (Hg : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, ‖iteratedFDeriv ℝ k g z‖ ≤ C) (i : Fin 3) :
    HeatJetBdd W (fun y : Space => g (y i)) := by
  intro k
  obtain ⟨Cg, hCg0, hCg⟩ := Hg k
  set P : Space →L[ℝ] ℝ := EuclideanSpace.proj i with hP
  have hfun : (fun y : Space => g (y i)) = g ∘ P := by
    funext y
    rfl
  refine ⟨Cg * ‖P‖ ^ k, mul_nonneg hCg0 (pow_nonneg (norm_nonneg _) _), fun y _ => ?_⟩
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right P hg y (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (hCg (P y)) (pow_nonneg (norm_nonneg _) _)

theorem hfjProfileDerivEq (ν : ℝ) (k : ℕ) : ∀ m : ℕ,
    iteratedDeriv k (UnforcedLeray.B0191.profileDeriv ν m) =
      UnforcedLeray.B0191.profileDeriv ν (m + k) := by
  induction k with
  | zero =>
    intro m
    simp
  | succ k ih =>
    intro m
    have hd : deriv (UnforcedLeray.B0191.profileDeriv ν m) =
        UnforcedLeray.B0191.profileDeriv ν (m + 1) := by
      funext x
      exact (UnforcedLeray.B0191.hasDerivAt_profileDeriv ν m x).deriv
    have hm : m + 1 + k = m + (k + 1) := by omega
    rw [iteratedDeriv_succ', hd, ih (m + 1), hm]

theorem hfjProfileDeriv {ν : ℝ} (hν : 0 < ν) (m : ℕ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, ‖iteratedFDeriv ℝ k (UnforcedLeray.B0191.profileDeriv ν m) z‖ ≤ C := by
  obtain ⟨C, hC⟩ := profileDerivBdd ν hν (m + k)
  refine ⟨|C|, abs_nonneg _, fun z => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hfjProfileDerivEq ν k m, Real.norm_eq_abs]
  exact (hC z).trans (le_abs_self C)

theorem hfjCoord {W : ℝ} (i : Fin 3) (hsq : ∀ y : Space, y i ^ 2 ≤ y 0 ^ 2 + y 1 ^ 2) :
    HeatJetBdd W (fun y : Space => y i) := by
  set L : Space →L[ℝ] ℝ := EuclideanSpace.proj i with hL
  have hfun : (fun y : Space => y i) = ⇑L := by
    funext y
    rfl
  rw [hfun]
  intro k
  refine ⟨|1 + W| + ‖L‖, by positivity, fun y hy => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [norm_iteratedFDeriv_zero]
    have h1 : y i ^ 2 ≤ W := (hsq y).trans (by rw [← Axi.ϱ_sq]; exact hy)
    have h2 : |y i| ≤ 1 + W := by
      nlinarith [sq_nonneg (|y i| - 1), sq_abs (y i), abs_nonneg (y i), sq_nonneg (y i)]
    have h3 : ‖L y‖ = |y i| := by
      rw [Real.norm_eq_abs]
      rfl
    rw [h3]
    have h4 : (1 + W) ≤ |1 + W| := le_abs_self _
    linarith [norm_nonneg L, abs_nonneg (1 + W)]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [← norm_iteratedFDeriv_fderiv]
    have hd : fderiv ℝ (⇑L) = fun _ => L := funext fun x => L.fderiv
    rw [hd]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [norm_iteratedFDeriv_zero]
      exact le_add_of_nonneg_left (abs_nonneg _)
    · rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hm) L]
      simp only [Pi.zero_apply, norm_zero]
      positivity

/-- The radial coefficient `heatParG` of the heat term, in the variables `y`. -/
def hfjA (ν R : ℝ) (j : ℕ) (y : Space) : ℝ :=
  -((R ^ (2 * j + 1))⁻¹) *
    ((y 0 ^ 2 + y 1 ^ 2) ^ j * UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) (y 2))

/-- The axial coefficient `heatParH` of the heat term, in the variables `y`. -/
def hfjB (ν R : ℝ) (j : ℕ) (y : Space) : ℝ :=
  (2 * (j : ℝ) + 2) * (R ^ (2 * j + 1))⁻¹ *
    ((y 0 ^ 2 + y 1 ^ 2) ^ j * UnforcedLeray.B0191.profileDeriv ν (2 * j) (y 2))

theorem hfjField (ν R : ℝ) (j : ℕ) (y : Space) :
    heatField ν R j y = (hfjA ν R j y * y 0) • coordinateVector 0 +
      ((hfjA ν R j y * y 1) • coordinateVector 1 + hfjB ν R j y • Axi.e3) := by
  have hh : Axi.hor y = y 0 • coordinateVector 0 + y 1 • coordinateVector 1 := by
    ext i
    fin_cases i <;> simp [Axi.hor, coordinateVector]
  simp only [heatField, hfjA, hfjB, heatParG, heatParH, hh]
  module

theorem heatFieldJet : UnforcedLeray.Short.PartIIIb.Concrete.HeatFieldJet := by
  intro ν R hν j k W
  have c0 : ContDiff ℝ ∞ (fun y : Space => y 0) := by fun_prop
  have c1 : ContDiff ℝ ∞ (fun y : Space => y 1) := by fun_prop
  have c2 : ContDiff ℝ ∞ (fun y : Space => y 2) := by fun_prop
  have cw : ContDiff ℝ ∞ (fun y : Space => y 0 ^ 2 + y 1 ^ 2) := by fun_prop
  have cwj : ∀ j' : ℕ, ContDiff ℝ ∞ (fun y : Space => (y 0 ^ 2 + y 1 ^ 2) ^ j') :=
    fun j' => cw.pow j'
  have cg : ∀ n : ℕ, ContDiff ℝ ∞ (fun y : Space => UnforcedLeray.B0191.profileDeriv ν n (y 2)) :=
    fun n => (UnforcedLeray.Short.IIb.contDiff_profileDeriv ν n).comp c2
  have h0 : HeatJetBdd W (fun y : Space => y 0) :=
    hfjCoord (W := W) 0 (fun y => le_add_of_nonneg_right (sq_nonneg _))
  have h1 : HeatJetBdd W (fun y : Space => y 1) :=
    hfjCoord (W := W) 1 (fun y => le_add_of_nonneg_left (sq_nonneg _))
  have hw : HeatJetBdd W (fun y : Space => y 0 ^ 2 + y 1 ^ 2) :=
    hfjAdd (f := fun y : Space => y 0 ^ 2) (g := fun y : Space => y 1 ^ 2)
      (by fun_prop) (by fun_prop) (hfjPow c0 h0 2) (hfjPow c1 h1 2)
  have hP : HeatJetBdd W (fun y : Space => (y 0 ^ 2 + y 1 ^ 2) ^ j) :=
    hfjPow cw hw j
  have hG1 : HeatJetBdd W (fun y : Space => UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) (y 2)) :=
    hfjCompProj (W := W) (UnforcedLeray.Short.IIb.contDiff_profileDeriv ν (2 * j + 1))
      (fun k' => hfjProfileDeriv hν (2 * j + 1) k') 2
  have hG0 : HeatJetBdd W (fun y : Space => UnforcedLeray.B0191.profileDeriv ν (2 * j) (y 2)) :=
    hfjCompProj (W := W) (UnforcedLeray.Short.IIb.contDiff_profileDeriv ν (2 * j))
      (fun k' => hfjProfileDeriv hν (2 * j) k') 2
  have hA : HeatJetBdd W (hfjA ν R j) := by
    unfold hfjA
    exact hfjMul (f := fun _ : Space => -((R ^ (2 * j + 1))⁻¹))
      (g := fun y : Space => (y 0 ^ 2 + y 1 ^ 2) ^ j *
        UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) (y 2))
      contDiff_const ((cwj j).mul (cg (2 * j + 1))) (hfjConst _)
      (hfjMul (cwj j) (cg (2 * j + 1)) hP hG1)
  have hB : HeatJetBdd W (hfjB ν R j) := by
    unfold hfjB
    exact hfjMul (f := fun _ : Space => (2 * (j : ℝ) + 2) * (R ^ (2 * j + 1))⁻¹)
      (g := fun y : Space => (y 0 ^ 2 + y 1 ^ 2) ^ j *
        UnforcedLeray.B0191.profileDeriv ν (2 * j) (y 2))
      contDiff_const ((cwj j).mul (cg (2 * j))) (hfjConst _)
      (hfjMul (cwj j) (cg (2 * j)) hP hG0)
  have cA : ContDiff ℝ ∞ (hfjA ν R j) := by
    unfold hfjA
    exact contDiff_const.mul ((cwj j).mul (cg (2 * j + 1)))
  have cB : ContDiff ℝ ∞ (hfjB ν R j) := by
    unfold hfjB
    exact contDiff_const.mul ((cwj j).mul (cg (2 * j)))
  have hAy0 : HeatJetBdd W (fun y : Space => hfjA ν R j y * y 0) := hfjMul cA c0 hA h0
  have hAy1 : HeatJetBdd W (fun y : Space => hfjA ν R j y * y 1) := hfjMul cA c1 hA h1
  have hT0 : HeatJetBdd W (fun y : Space => (hfjA ν R j y * y 0) • coordinateVector 0) :=
    hfjSmulConst (cA.mul c0) (coordinateVector 0) hAy0
  have hT1 : HeatJetBdd W (fun y : Space => (hfjA ν R j y * y 1) • coordinateVector 1) :=
    hfjSmulConst (cA.mul c1) (coordinateVector 1) hAy1
  have hT2 : HeatJetBdd W (fun y : Space => hfjB ν R j y • Axi.e3) :=
    hfjSmulConst cB Axi.e3 hB
  have cT1 : ContDiff ℝ ∞ (fun y : Space => (hfjA ν R j y * y 1) • coordinateVector 1) :=
    (cA.mul c1).smul contDiff_const
  have cT2 : ContDiff ℝ ∞ (fun y : Space => hfjB ν R j y • Axi.e3) :=
    cB.smul contDiff_const
  have cT0 : ContDiff ℝ ∞ (fun y : Space => (hfjA ν R j y * y 0) • coordinateVector 0) :=
    (cA.mul c0).smul contDiff_const
  have hS : HeatJetBdd W (fun y : Space =>
      (hfjA ν R j y * y 1) • coordinateVector 1 + hfjB ν R j y • Axi.e3) :=
    hfjAdd cT1 cT2 hT1 hT2
  have cS : ContDiff ℝ ∞ (fun y : Space =>
      (hfjA ν R j y * y 1) • coordinateVector 1 + hfjB ν R j y • Axi.e3) :=
    cT1.add cT2
  have hall : HeatJetBdd W (fun y : Space => (hfjA ν R j y * y 0) • coordinateVector 0 +
      ((hfjA ν R j y * y 1) • coordinateVector 1 + hfjB ν R j y • Axi.e3)) :=
    hfjAdd cT0 cS hT0 hS
  have hfun : heatField ν R j = fun y : Space => (hfjA ν R j y * y 0) • coordinateVector 0 +
      ((hfjA ν R j y * y 1) • coordinateVector 1 + hfjB ν R j y • Axi.e3) :=
    funext (hfjField ν R j)
  obtain ⟨C, _, hC⟩ := hall k
  refine ⟨C, fun y hy => ?_⟩
  rw [hfun]
  exact hC y hy

end UnforcedLeray.Short.PartIIIb.Concrete
