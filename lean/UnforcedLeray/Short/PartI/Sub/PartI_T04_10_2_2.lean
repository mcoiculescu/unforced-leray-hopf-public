import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.SliceT1

/-!
# Part I, `PartI:T04/10/2/2`: `SliceT2Bound` from three source facts

Source of record: `the November 2 reference manuscript`, lines 285-288
(`t2 = |D²ω|² |Dv|`).  Route: Hölder `(3,3,3)`: `(∫ t2)³ ≤ ∫|Dv|³ (∫|D²ω|³)²`;
`∫|D²ω|³ ≤ C A ∫|D³ω|²` (`cylGN_proof`, `m = 3`, `l = 2`); `∫|Dv|³ ≤ sup|Dv| ∫|Dv|²` with
`sup|Dv| ≤ K (1 + ‖D²ω‖²)` (`CylSupInterp` on components of `Dv`, `apElliptic`) and
`∫|Dv|² ≤ K₀ A` (`apElliptic`, `j = 0`).  Final absorption: `T³ ≤ a b Y²` gives `T ≤ ν Y + a b/ν²`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- **Sub 1** (lines 285-288, `cylGN_proof` `m = 3`, `l = 2`, as in `sliceT1Bound`): on a slice with
`‖u‖²,‖ω‖²,‖Dω‖² ≤ A`, `|ω| ≤ A`, the jet `D²ω` lies in `L³(cell)` and
`∫ |D²ω|³ ≤ C ∫ |D³ω|²`, `C` depending only on `A`. -/
def SliceD2OmegaCube : Prop :=
  ∀ A : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (u : Plane → Vec), 1 ≤ c → SliceOK c u →
    (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 u z‖ ^ 2) ≤ A →
    (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 (Cyl.curl u) z‖ ^ 2) ≤ A →
    (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 1 (Cyl.curl u) z‖ ^ 2) ≤ A →
    (∀ z : Plane, |Cyl.curl u z| ≤ A) →
      MemLp (Train.jet 2 (Cyl.curl u)) (ENNReal.ofReal 3) (Cyl.cellμ c) ∧
      ∫ z, ‖Train.jet 2 (Cyl.curl u) z‖ ^ (3:ℝ) ∂(Cyl.cellμ c) ≤
        C * ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 3 (Cyl.curl u) z‖ ^ 2

/-- **Sub 2** (lines 285-288): sup bound `‖Du z‖ ≤ K (1 + ‖D²ω‖₂²)` on a slice with the hypotheses of
`SliceT2Bound`.  Route: `cylinder_interpolation_uniform` (`CylSupInterp`, `Sub/T07.lean:47`) on the
components `∂_k u_i` of `Du` (smooth, periodic, `L²` jets): `‖f‖_∞² ≲ ‖f‖₂‖D²f‖₂ + ‖f‖₂‖Df‖₂`;
`‖D^{j+1}u‖₂² ≤ K_j ‖D^jω‖₂²` (`apElliptic`, `j = 0,1,2`) with `‖ω‖₂²,‖Dω‖₂² ≤ A`; then
`‖Du z‖ ≤ C Σ |∂_k u_i z|` (matrix norm vs. components) and `s^{1/4}·const ≤ const (1 + s)`. -/
def SliceDuSup : Prop :=
  ∀ A : ℝ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (c : ℝ) (u : Plane → Vec), 1 ≤ c → SliceOK c u →
    (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 u z‖ ^ 2) ≤ A →
    (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 (Cyl.curl u) z‖ ^ 2) ≤ A →
    (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 1 (Cyl.curl u) z‖ ^ 2) ≤ A →
    (∀ z : Plane, |Cyl.curl u z| ≤ A) →
      ∀ z : Plane, ‖iteratedFDeriv ℝ 1 u z‖ ≤
        K * (1 + ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 2 (Cyl.curl u) z‖ ^ 2)

/-- **Sub 3** (Hölder `(3,3,3)`, lines 285-288): for nonnegative `F, G ∈ L³(μ)`, `F·(G·F)` is
integrable and `(∫ F (G F))³ ≤ ∫ G³ · (∫ F³)²`.  Route: `MemLp.mul` with `HolderTriple 3 3 (3/2)`
and then `integral_mul_le_Lp_mul_Lq_of_nonneg` with `(3, 3/2)`, as in `sl_holder_T`/`sl_holder_S`
(here `∫ (G F)^{3/2} ≤ (∫G³)^{1/2} (∫F³)^{1/2}` by Cauchy-Schwarz). -/
def Holder333 : Prop :=
  ∀ (μ : Measure Plane) (F G : Plane → ℝ), (∀ z, 0 ≤ F z) → (∀ z, 0 ≤ G z) →
    MemLp F (ENNReal.ofReal 3) μ → MemLp G (ENNReal.ofReal 3) μ →
      Integrable (fun z => F z * (G z * F z)) μ ∧
      (∫ z, F z * (G z * F z) ∂μ) ^ 3 ≤
        (∫ z, G z ^ (3:ℝ) ∂μ) * (∫ z, F z ^ (3:ℝ) ∂μ) ^ 2

/-- Absorption: `T³ ≤ a b Y²` with `a, b ≥ 0` gives `T ≤ ν Y + a b / ν²`. -/
theorem sl2_absorb {T Y a b ν : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hY : 0 ≤ Y) (hab : 0 ≤ a * b)
    (h : T ^ 3 ≤ a * b * Y ^ 2) : T ≤ ν * Y + a * b / ν ^ 2 := by
  by_contra hcon
  push_neg at hcon
  have h1 : ν * Y < T := by
    have : 0 ≤ a * b / ν ^ 2 := by positivity
    linarith
  have hTpos : 0 < T := lt_of_le_of_lt (mul_nonneg hν.le hY) h1
  have h2 : (ν * Y) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (mul_nonneg hν.le hY) h1.le 2
  have h3 : ν ^ 2 * T ^ 3 ≤ a * b * T ^ 2 := by
    calc ν ^ 2 * T ^ 3 ≤ ν ^ 2 * (a * b * Y ^ 2) := mul_le_mul_of_nonneg_left h (sq_nonneg ν)
      _ = a * b * (ν * Y) ^ 2 := by ring
      _ ≤ a * b * T ^ 2 := mul_le_mul_of_nonneg_left h2 hab
  have h4 : ν ^ 2 * T ≤ a * b := by
    have hT2 : 0 < T ^ 2 := by positivity
    nlinarith
  have h6 : T ≤ a * b / ν ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have h7 : 0 ≤ ν * Y := mul_nonneg hν.le hY
  linarith

/-- **`SliceT2Bound` from the three source facts.** -/
theorem sliceT2Bound_of (h1 : SliceD2OmegaCube) (h2 : SliceDuSup) (h3 : Holder333) :
    SliceT2Bound := by
  intro ν A hν
  obtain ⟨C, hC, H1⟩ := h1 A
  obtain ⟨K, hK, H2⟩ := h2 A
  obtain ⟨K0, hK0, hE0⟩ := apElliptic 0
  refine ⟨((K * (K0 * |A|)) * C ^ 2) / ν ^ 2, by positivity, ?_⟩
  intro c u hc hS hA0 hW0 hW1 hsup
  obtain ⟨hmF, hP⟩ := H1 c u hc hS hA0 hW0 hW1 hsup
  have hD := H2 c u hc hS hA0 hW0 hW1 hsup
  obtain ⟨hu, hper, hdiv, hbdd, hL⟩ := hS
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 2 (Cyl.curl u) z‖ ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 3 (Cyl.curl u) z‖ ^ 2 :=
    ⟨_, rfl⟩
  have hW0' : 0 ≤ W := by rw [hWdef]; exact integral_nonneg fun z => sq_nonneg _
  have hY0 : 0 ≤ Y := by rw [hYdef]; exact integral_nonneg fun z => sq_nonneg _
  rw [← hWdef] at hD
  rw [← hYdef] at hP
  have hS0 : 0 ≤ K * (1 + W) := mul_nonneg hK (by linarith)
  -- the function `G = |Du|`
  have hGc : Continuous (fun z => ‖Train.jet 1 u z‖) :=
    (hu.continuous_iteratedFDeriv (m := 1) (by exact_mod_cast le_top)).norm
  have hG2 : Integrable (fun z => ‖Train.jet 1 u z‖ ^ (2:ℝ)) (Cyl.cellμ c) := by
    have := hL 1
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Real.rpow_two]; rfl
  have hG3int : Integrable (fun z => ‖Train.jet 1 u z‖ ^ (3:ℝ)) (Cyl.cellμ c) := by
    refine Integrable.mono' (hG2.const_mul (K * (1 + W)))
      ((hGc.rpow_const fun _ => Or.inr (by norm_num)).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    have hz0 : 0 ≤ ‖Train.jet 1 u z‖ := norm_nonneg _
    have hz1 : ‖Train.jet 1 u z‖ ≤ K * (1 + W) := hD z
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hz0 _)]
    calc ‖Train.jet 1 u z‖ ^ (3:ℝ) = ‖Train.jet 1 u z‖ * ‖Train.jet 1 u z‖ ^ (2:ℝ) := by
          rw [show (3:ℝ) = 1 + 2 by norm_num, Real.rpow_add' hz0 (by norm_num), Real.rpow_one]
      _ ≤ (K * (1 + W)) * ‖Train.jet 1 u z‖ ^ (2:ℝ) :=
          mul_le_mul_of_nonneg_right hz1 (Real.rpow_nonneg hz0 _)
  have hmG : MemLp (fun z => ‖Train.jet 1 u z‖) (ENNReal.ofReal 3) (Cyl.cellμ c) := by
    rw [← integrable_norm_rpow_iff (p := ENNReal.ofReal 3) hGc.aestronglyMeasurable
      (ENNReal.ofReal_pos.2 (by norm_num)).ne' ENNReal.ofReal_ne_top]
    simp only [ENNReal.toReal_ofReal (show (0:ℝ) ≤ 3 by norm_num), norm_norm]
    exact hG3int
  have hmF' : MemLp (fun z => ‖Train.jet 2 (Cyl.curl u) z‖) (ENNReal.ofReal 3) (Cyl.cellμ c) :=
    hmF.norm
  -- `∫ |Du|² ≤ K0 A`
  have hEu : ∫ z, ‖Train.jet 1 u z‖ ^ (2:ℝ) ∂(Cyl.cellμ c) ≤ K0 * |A| := by
    have h := hE0 c hc u hu hper hdiv hbdd hL
    have e : ∫ z, ‖Train.jet 1 u z‖ ^ (2:ℝ) ∂(Cyl.cellμ c) =
        ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ (0 + 1) u z‖ ^ 2 := by
      simp only [Real.rpow_two]; rfl
    rw [e]
    calc _ ≤ K0 * ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 (Cyl.curl u) z‖ ^ 2 := h
      _ ≤ K0 * |A| := mul_le_mul_of_nonneg_left (hW0.trans (le_abs_self A)) hK0
  have hG3 : ∫ z, ‖Train.jet 1 u z‖ ^ (3:ℝ) ∂(Cyl.cellμ c) ≤ (K * (K0 * |A|)) * (1 + W) := by
    calc _ ≤ ∫ z, (K * (1 + W)) * ‖Train.jet 1 u z‖ ^ (2:ℝ) ∂(Cyl.cellμ c) := by
          refine integral_mono hG3int (hG2.const_mul _) fun z => ?_
          have hz0 : 0 ≤ ‖Train.jet 1 u z‖ := norm_nonneg _
          have hz1 : ‖Train.jet 1 u z‖ ≤ K * (1 + W) := hD z
          calc ‖Train.jet 1 u z‖ ^ (3:ℝ) = ‖Train.jet 1 u z‖ * ‖Train.jet 1 u z‖ ^ (2:ℝ) := by
                rw [show (3:ℝ) = 1 + 2 by norm_num, Real.rpow_add' hz0 (by norm_num),
                  Real.rpow_one]
            _ ≤ _ := mul_le_mul_of_nonneg_right hz1 (Real.rpow_nonneg hz0 _)
      _ = (K * (1 + W)) * ∫ z, ‖Train.jet 1 u z‖ ^ (2:ℝ) ∂(Cyl.cellμ c) := by
          rw [integral_const_mul]
      _ ≤ (K * (1 + W)) * (K0 * |A|) := mul_le_mul_of_nonneg_left hEu hS0
      _ = _ := by ring
  -- Hölder
  obtain ⟨hint, hHol⟩ := h3 (Cyl.cellμ c) _ _ (fun z => norm_nonneg _) (fun z => norm_nonneg _)
    hmF' hmG
  have hcT : (∫ z in Cyl.cell c, commT2 u z) =
      ∫ z, ‖Train.jet 2 (Cyl.curl u) z‖ * (‖Train.jet 1 u z‖ * ‖Train.jet 2 (Cyl.curl u) z‖)
        ∂(Cyl.cellμ c) := rfl
  have hTn : 0 ≤ ∫ z, ‖Train.jet 2 (Cyl.curl u) z‖ * (‖Train.jet 1 u z‖ *
      ‖Train.jet 2 (Cyl.curl u) z‖) ∂(Cyl.cellμ c) :=
    integral_nonneg fun z => mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hPn : 0 ≤ ∫ z, ‖Train.jet 2 (Cyl.curl u) z‖ ^ (3:ℝ) ∂(Cyl.cellμ c) :=
    integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  have hG3n : 0 ≤ ∫ z, ‖Train.jet 1 u z‖ ^ (3:ℝ) ∂(Cyl.cellμ c) :=
    integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  have hT3 : (∫ z in Cyl.cell c, commT2 u z) ^ 3 ≤
      ((K * (K0 * |A|)) * C ^ 2) * (1 + W) * Y ^ 2 := by
    rw [hcT]
    refine hHol.trans ?_
    have hP2 : (∫ z, ‖Train.jet 2 (Cyl.curl u) z‖ ^ (3:ℝ) ∂(Cyl.cellμ c)) ^ 2 ≤ (C * Y) ^ 2 :=
      pow_le_pow_left₀ hPn hP 2
    calc _ ≤ ((K * (K0 * |A|)) * (1 + W)) * (C * Y) ^ 2 :=
          mul_le_mul hG3 hP2 (sq_nonneg _) (mul_nonneg (mul_nonneg hK (mul_nonneg hK0
            (abs_nonneg A))) (by linarith))
      _ = _ := by ring
  have hab : 0 ≤ ((K * (K0 * |A|)) * C ^ 2) * (1 + W) :=
    mul_nonneg (mul_nonneg (mul_nonneg hK (mul_nonneg hK0 (abs_nonneg A))) (sq_nonneg C))
      (by linarith)
  have hT0 : 0 ≤ ∫ z in Cyl.cell c, commT2 u z := by rw [hcT]; exact hTn
  have habs := sl2_absorb hν hT0 hY0 (a := (K * (K0 * |A|)) * C ^ 2) (b := 1 + W) hab
    (by linarith [hT3])
  refine ⟨?_, ?_⟩
  · exact hint
  · rw [← hYdef, ← hWdef]
    have e : ((K * (K0 * |A|)) * C ^ 2) / ν ^ 2 * (1 + W) =
        ((K * (K0 * |A|)) * C ^ 2) * (1 + W) / ν ^ 2 := by ring
    rw [e]
    exact habs

end UnforcedLeray.Short.PartI
