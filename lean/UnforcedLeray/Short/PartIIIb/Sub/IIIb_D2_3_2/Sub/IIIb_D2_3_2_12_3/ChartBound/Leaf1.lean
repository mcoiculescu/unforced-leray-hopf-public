import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_12_3_1

/-!
# `PartIII-b:IIIb-D2/3/2/12/3/1/1` (leaf 1: `StrPhysAbsLe`)

Source of record: `the November 2 reference manuscript`,
line 2683.  `strPhys R c g x = cylFrame z * (s • nsSym (g (chartOf ..))) * (cylFrame z)ᵀ` with
`z = x.2`, `s = R²/ϱ² ≥ 0`, and every entry of `cylFrame z` has absolute value at most `1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell)

/-- `|w / ϱ| ≤ 1` whenever `|w| ≤ ϱ` (including `ϱ = 0`, where the quotient is `0`). -/
theorem leaf1_abs_div_hRad_le (z : Space) (w : ℝ) (hw : |w| ≤ NearInst.hRad z) :
    |w / NearInst.hRad z| ≤ 1 := by
  by_cases h0 : NearInst.hRad z = 0
  · rw [h0, div_zero, abs_zero]
    exact zero_le_one
  · have hnn : 0 ≤ NearInst.hRad z := Real.sqrt_nonneg _
    have hpos : 0 < NearInst.hRad z := lt_of_le_of_ne hnn (Ne.symm h0)
    rw [abs_div, abs_of_pos hpos, div_le_one hpos]
    exact hw

/-- Every entry of `NearInst.cylFrame z` has absolute value at most `1`. -/
theorem leaf1_cylFrame_entry_le (z : Space) (a b : Fin 3) :
    |NearInst.cylFrame z a b| ≤ 1 := by
  have h0 : |z 0| ≤ NearInst.hRad z := by
    unfold NearInst.hRad
    apply Real.abs_le_sqrt
    nlinarith [sq_nonneg (z 1)]
  have h1 : |z 1| ≤ NearInst.hRad z := by
    unfold NearInst.hRad
    apply Real.abs_le_sqrt
    nlinarith [sq_nonneg (z 0)]
  have k0 := leaf1_abs_div_hRad_le z (z 0) h0
  have k1 := leaf1_abs_div_hRad_le z (z 1) h1
  fin_cases a <;> fin_cases b <;> simp [NearInst.cylFrame, k0, k1]

/-- Entrywise bound for a sandwich `A (s • M) Aᵀ` with `|A i j| ≤ 1` and `s ≥ 0`. -/
theorem leaf1_sandwich_abs (A M : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) (hs : 0 ≤ s)
    (hA : ∀ a b, |A a b| ≤ 1) (i j : Fin 3) :
    |(A * (s • M) * Matrix.transpose A) i j| ≤ s * ∑ a : Fin 3, ∑ b : Fin 3, |M a b| := by
  have hexp : (A * (s • M) * Matrix.transpose A) i j = ∑ k : Fin 3, ∑ l : Fin 3, A i k * (s * M k l) * A j l := by
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply,
      Finset.sum_mul]
    exact Finset.sum_comm
  rw [hexp]
  have hterm : ∀ k l : Fin 3, |A i k * (s * M k l) * A j l| ≤ s * |M k l| := by
    intro k l
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hs]
    have h1 := hA i k
    have h2 := hA j l
    have h3 : 0 ≤ s * |M k l| := by positivity
    calc |A i k| * (s * |M k l|) * |A j l| ≤ 1 * (s * |M k l|) * 1 := by gcongr
      _ = s * |M k l| := by ring
  calc |∑ k : Fin 3, ∑ l : Fin 3, A i k * (s * M k l) * A j l|
      ≤ ∑ k : Fin 3, |∑ l : Fin 3, A i k * (s * M k l) * A j l| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin 3, ∑ l : Fin 3, |A i k * (s * M k l) * A j l| :=
        Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin 3, ∑ l : Fin 3, s * |M k l| :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hterm k l
    _ = s * ∑ a : Fin 3, ∑ b : Fin 3, |M a b| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]

/-- **Leaf 1** (source 2683): `|𝒩_T g| ≤ s Σ_{ab} |nsSym g_{ab}|` entrywise, `s = R²/ϱ²`. -/
theorem strPhysAbsLe_proved : UnforcedLeray.Short.PartIIIb.Concrete.StrPhysAbsLe := by
  intro R c g x i j
  have hs : 0 ≤ (NearInst.chartOf R c x.2 x.1).1 := by
    show 0 ≤ R ^ 2 / NearInst.hRad x.2 ^ 2
    positivity
  have hA : ∀ a b, |NearInst.cylFrame x.2 a b| ≤ 1 :=
    fun a b => leaf1_cylFrame_entry_le x.2 a b
  exact leaf1_sandwich_abs (NearInst.cylFrame x.2)
    (NearInst.nsSym (g (NearInst.chartOf R c x.2 x.1))) (NearInst.chartOf R c x.2 x.1).1 hs hA i j

end UnforcedLeray.Short.PartIIIb.Concrete
