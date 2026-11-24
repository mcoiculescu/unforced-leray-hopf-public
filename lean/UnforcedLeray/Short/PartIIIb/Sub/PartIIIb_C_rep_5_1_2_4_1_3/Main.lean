import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3`: `WardYMajBinCore` from the leaves

Source `the November 2 reference manuscript` 5585-5593.  The chain (see
`Kernel.lean` for the architecture): chart majorant (`ChartMajSq`), chart output to physical
output (`ChartToPhys`, with `PsiMajMeasurable`, `PsiMajRotInv`, `PsiMajPeriodic`), Minkowski over
the source atoms (`PsiAtomsMinkowski`), the atom bound (`AtomBound`), the folded source mass
(`SourceMass`) and the constants (`ConstAlgebra`); bins with `S ≤ 0` are null (`BinNull`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- The source age threshold `s₁/θ² = e^{δ-h}s₀` (`θ = e^{-δ/2}`, `h = δ/4`). -/
theorem binUpper_succ_div_theta (S δ : ℝ) (j : ℕ) :
    binUpper S (δ / 4) (j + 1) / Real.exp (-(δ / 2)) ^ 2 =
      Real.exp (δ - δ / 4) * binUpper S (δ / 4) j := by
  have hθ : Real.exp (-(δ / 2)) ^ 2 ≠ 0 := pow_ne_zero _ (Real.exp_pos _).ne'
  rw [div_eq_iff hθ]
  unfold binUpper
  rw [sq, show Real.exp (δ - δ / 4) * (S * Real.exp (-(δ / 4 * (j : ℝ)))) *
      (Real.exp (-(δ / 2)) * Real.exp (-(δ / 2))) =
      S * (Real.exp (δ - δ / 4) * Real.exp (-(δ / 4 * (j : ℝ))) * Real.exp (-(δ / 2)) *
        Real.exp (-(δ / 2))) by ring]
  simp only [← Real.exp_add]
  congr 2
  push_cast
  ring

/-- **`WardYMajBinCore` from the leaves.** -/
theorem wardYMajBinCore_of (hMaj : ChartMajSq) (hMeas : PsiMajMeasurable)
    (hRot : PsiMajRotInv) (hPer : PsiMajPeriodic) (hC2P : ChartToPhys)
    (hMink : PsiAtomsMinkowski) (hAtom : AtomBound) (hSrc : SourceMass)
    (hConst : ConstAlgebra) (hNull : BinNull) : WardYMajBinCore := by
  intro δ hδ _
  refine ⟨wyC0 (Real.exp (-(δ / 2))), ?_⟩
  intro R c S hR hc j g hg
  rcases le_or_gt S 0 with hS | hS
  · have h0 : ∫⁻ p in binSet S (δ / 4) j,
        wardYChartMaj R c (Real.exp (-(δ / 2))) g p ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) = 0 :=
      hNull c _ S _ j _ hS
    rw [h0, ENNReal.zero_rpow_of_pos (by norm_num)]
    exact zero_le
  -- constants
  have hθ0 : 0 < Real.exp (-(δ / 2)) := Real.exp_pos _
  have hθ1 : Real.exp (-(δ / 2)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hs1 : 0 < binUpper S (δ / 4) (j + 1) := by
    unfold binUpper; exact mul_pos hS (Real.exp_pos _)
  have hs10 : binUpper S (δ / 4) (j + 1) ≤ binUpper S (δ / 4) j := by
    unfold binUpper
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hS.le
    push_cast
    nlinarith
  have hs0 : 0 < binUpper S (δ / 4) j := lt_of_lt_of_le hs1 hs10
  have hP : 0 < 2 * c / R := by positivity
  have hG : Measurable (fun p : Chart => ‖g p‖ₑ) := hg.enorm
  -- step 1-2: chart majorant and chart output to physical output
  have step12 : ∫⁻ p in binSet S (δ / 4) j,
      wardYChartMaj R c (Real.exp (-(δ / 2))) g p ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) ≤
      ENNReal.ofReal ((2 * Real.pi * c * R)⁻¹) *
        ∫⁻ x in Ioc 0 (2 * c / R) ×ˢ ybin R (binUpper S (δ / 4) (j + 1)) (binUpper S (δ / 4) j),
          psiMaj R c (Real.exp (-(δ / 2))) (fun p => ‖g p‖ₑ) x.1 x.2 ^ (2 : ℝ) := by
    calc ∫⁻ p in binSet S (δ / 4) j,
          wardYChartMaj R c (Real.exp (-(δ / 2))) g p ^ (2 : ℝ) ∂(ageμ c (-3 / 2))
        ≤ ∫⁻ p in {p : Chart | p.1 ∈ Ioc (binUpper S (δ / 4) (j + 1)) (binUpper S (δ / 4) j)},
            ENNReal.ofReal (p.1⁻¹) *
              psiMaj R c (Real.exp (-(δ / 2))) (fun q => ‖g q‖ₑ) (NearInst.chartTau R p)
                (NearInst.chartY R p) ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) :=
          lintegral_mono (fun p => hMaj R c _ g p)
      _ ≤ _ := by
          refine hC2P R c hR hc
            (fun τ y => psiMaj R c (Real.exp (-(δ / 2))) (fun p => ‖g p‖ₑ) τ y ^ (2 : ℝ))
            ((hMeas R c _ _ hG).pow_const _) (fun α τ y => by beta_reduce; rw [hRot]) ?_
            (Ioc (binUpper S (δ / 4) (j + 1)) (binUpper S (δ / 4) j)) measurableSet_Ioc
            (fun x hx => lt_trans hs1 hx.1)
          intro y τ
          have h := hPer R c (Real.exp (-(δ / 2))) (fun p => ‖g p‖ₑ) hR hc y τ
          simp only at h ⊢
          rw [h]
  -- step 3: square root
  have step3 := ENNReal.rpow_le_rpow step12 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)] at step3
  -- step 4: Minkowski over the atoms
  have step4 := hMink R c (Real.exp (-(δ / 2))) _ hG
    (Ioc 0 (2 * c / R) ×ˢ ybin R (binUpper S (δ / 4) (j + 1)) (binUpper S (δ / 4) j))
  -- step 5: the atom bound
  have step5 : ∫⁻ a : ℝ × Space, srcW R c (fun p => ‖g p‖ₑ) a.1 a.2 *
        (∫⁻ x in Ioc 0 (2 * c / R) ×ˢ
            ybin R (binUpper S (δ / 4) (j + 1)) (binUpper S (δ / 4) j),
          phKer (Real.exp (-(δ / 2))) x.1 x.2 a.1 a.2 ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (gapA (Real.exp (-(δ / 2))) R (binUpper S (δ / 4) j))) *
        ∫⁻ a : ℝ × Space, Set.indicator
            {a : ℝ × Space | binUpper S (δ / 4) (j + 1) / Real.exp (-(δ / 2)) ^ 2 < age R a.2}
            (fun a => srcW R c (fun p => ‖g p‖ₑ) a.1 a.2) a *
            ENNReal.ofReal (Real.sqrt (omega2 (2 * c / R) a.1)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono (fun a => ?_)
    refine (hAtom R c _ _ _ _ _ hR hθ0 hθ1 hs1 hs10 hP a).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    ring
  -- step 6: the folded source mass
  have step6 := hSrc R c hR hc g hg (binUpper S (δ / 4) (j + 1) / Real.exp (-(δ / 2)) ^ 2)
  rw [binUpper_succ_div_theta] at step5 step6
  -- step 7: the constants
  have step7 := hConst (Real.exp (-(δ / 2))) R c (binUpper S (δ / 4) j) hθ0 hθ1 hR hc hs0
  calc (∫⁻ p in binSet S (δ / 4) j,
          wardYChartMaj R c (Real.exp (-(δ / 2))) g p ^ (2 : ℝ) ∂(ageμ c (-3 / 2))) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal ((2 * Real.pi * c * R)⁻¹) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal (Real.sqrt (gapA (Real.exp (-(δ / 2))) R (binUpper S (δ / 4) j))) *
            (ENNReal.ofReal (Real.sqrt (2 * c / R) + 1 / Real.sqrt (2 * c / R)) *
              ENNReal.ofReal (2 * c / R * (Real.pi * R ^ 2)) *
              ageMass c (Real.exp (δ - δ / 4) * binUpper S (δ / 4) j) g)) := by
        refine step3.trans ?_
        gcongr
        exact step4.trans (step5.trans (by gcongr))
    _ = (ENNReal.ofReal ((2 * Real.pi * c * R)⁻¹) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (Real.sqrt (gapA (Real.exp (-(δ / 2))) R (binUpper S (δ / 4) j))) *
          ENNReal.ofReal (Real.sqrt (2 * c / R) + 1 / Real.sqrt (2 * c / R)) *
          ENNReal.ofReal (2 * c / R * (Real.pi * R ^ 2))) *
          ageMass c (Real.exp (δ - δ / 4) * binUpper S (δ / 4) j) g := by ring
    _ ≤ _ := by gcongr

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
