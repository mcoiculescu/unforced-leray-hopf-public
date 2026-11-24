import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# `PartIII-b:C/rep/8/2/3/2/14`: joint derivative bounds `PcJointJet` for the Gaussian pressure

Source of record: `the November 2 reference manuscript` 4963-4968, 5484-5495.
On `U = Ioi 0 ×ˢ univ`, `PcTheta` writes the pressure as `E * T` with the envelope `E` (`PcEnvJet`)
and the theta factor `T` (`TtCompJet`). Both are smooth on `U`, so the Leibniz rule applies
pointwise at each `y ∈ U`, and the derivatives of the pressure agree with those of `E * T` there.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

theorem pcJointJet_of (h1 : PcTheta) (h2 : PcEnvJet) (h3 : TtCompJet) : PcJointJet := by
  unfold PcEnvJet at h2
  unfold TtCompJet at h3
  choose KE hKE using h2
  choose KT hKT using h3
  unfold PcJointJet
  intro n
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |KE i| * |KT (n - i)|, ?_⟩
  intro ν hν0 hν2 y hy0 hy1
  have hν1 : ν ≤ 1 := by linarith
  have hνpos : (0 : ℝ) < ν := hν0
  set U : Set (ℝ × Plane) := Ioi (0 : ℝ) ×ˢ (univ : Set Plane) with hUdef
  have hUo : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hU : UniqueDiffOn ℝ U := hUo.uniqueDiffOn
  have hy : y ∈ U := ⟨hy0, mem_univ _⟩
  have hc : (0 : ℝ) < cOf ν := by
    unfold cOf
    exact inv_pos.2 (pow_pos hνpos 2)
  -- positivity of `1 + ν s` on `U`
  have hpos : ∀ x : ℝ × Plane, x ∈ U → 0 < 1 + ν * x.1 := by
    intro x hx
    have := mul_pos hνpos hx.1
    linarith
  -- smoothness of the envelope and of the theta factor on `U`
  have hc1 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => 1 + ν * x.1) U := by
    fun_prop
  have hc3 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => ((1 + ν * x.1) ^ 3)⁻¹) U :=
    (hc1.pow 3).inv fun x hx => pow_ne_zero _ (hpos x hx).ne'
  have hexp : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) U := by
    refine ContDiffOn.exp ?_
    refine ContDiffOn.div ?_ ?_ fun x hx => ?_
    · fun_prop
    · exact contDiffOn_const.mul hc1
    · exact (mul_pos two_pos (hpos x hx)).ne'
  have hE : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => -((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1))))
      U :=
    hc3.neg.mul hexp
  have hm : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1)) U := by
    refine ContDiffOn.prodMk ?_ (by fun_prop)
    exact (contDiffOn_const.mul hc1).inv fun x hx => (mul_pos two_pos (hpos x hx)).ne'
  have hmaps : MapsTo (fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1))
      U {x : ℝ × ℝ | 0 < x.1} := by
    intro x hx
    show 0 < (2 * (1 + ν * x.1))⁻¹
    exact inv_pos.2 (mul_pos two_pos (hpos x hx))
  have hT : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => UnforcedLeray.Short.IIb.tt (cOf ν) 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1))
      U :=
    (UnforcedLeray.Short.IIb.contDiffOn_tt_infty hc.ne' 0).comp hm hmaps
  -- the pressure equals `E * T` on `U`
  have hEq : EqOn (fun x : ℝ × Plane => UnforcedLeray.Train.pc ν (cOf ν) x.1 x.2)
      (fun x : ℝ × Plane =>
        (-((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) *
          UnforcedLeray.Short.IIb.tt (cOf ν) 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1)) U :=
    fun x hx => h1 ν (cOf ν) x.1 hνpos hc hx.1.le x.2
  -- conversion between the within-derivatives on `U` and the global ones
  have hconv : ∀ (i : ℕ) (F : ℝ × Plane → ℝ),
      iteratedFDerivWithin ℝ i F U y = iteratedFDeriv ℝ i F y :=
    fun i F => iteratedFDerivWithin_of_isOpen i hUo hy
  have hcongr : iteratedFDerivWithin ℝ n (fun x : ℝ × Plane => UnforcedLeray.Train.pc ν (cOf ν) x.1 x.2) U y
      = iteratedFDerivWithin ℝ n (fun x : ℝ × Plane =>
            (-((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) *
              UnforcedLeray.Short.IIb.tt (cOf ν) 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1)) U y :=
    iteratedFDerivWithin_congr hEq hy n
  have hL := norm_iteratedFDerivWithin_mul_le hE hT hU hy
    (n := n) (by exact_mod_cast le_top)
  -- termwise bound
  have key : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i
          (fun x : ℝ × Plane => -((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) U y‖
        * ‖iteratedFDerivWithin ℝ (n - i)
          (fun x : ℝ × Plane => UnforcedLeray.Short.IIb.tt (cOf ν) 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1))
          U y‖
      ≤ (n.choose i : ℝ) * |KE i| * |KT (n - i)| := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have ha : ‖iteratedFDerivWithin ℝ i
          (fun x : ℝ × Plane => -((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) U y‖
        ≤ |KE i| := by
      rw [hconv]
      exact (hKE i ν hνpos hν1 y hy0 hy1).trans (le_abs_self _)
    have hb : ‖iteratedFDerivWithin ℝ (n - i)
          (fun x : ℝ × Plane => UnforcedLeray.Short.IIb.tt (cOf ν) 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1))
          U y‖ ≤ |KT (n - i)| := by
      rw [hconv]
      exact (hKT (n - i) ν hνpos hν2 y hy0 hy1).trans (le_abs_self _)
    have hc0 : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
    exact mul_le_mul (mul_le_mul_of_nonneg_left ha hc0) hb (norm_nonneg _)
      (mul_nonneg hc0 (abs_nonneg _))
  calc ‖iteratedFDeriv ℝ n (fun x : ℝ × Plane => UnforcedLeray.Train.pc ν (cOf ν) x.1 x.2) y‖
      = ‖iteratedFDerivWithin ℝ n (fun x : ℝ × Plane => UnforcedLeray.Train.pc ν (cOf ν) x.1 x.2) U y‖ := by
        rw [hconv]
    _ = ‖iteratedFDerivWithin ℝ n
          (fun x : ℝ × Plane =>
            (-((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) *
              UnforcedLeray.Short.IIb.tt (cOf ν) 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1)) U y‖ := by
        rw [hcongr]
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i
            (fun x : ℝ × Plane => -((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) U y‖
          * ‖iteratedFDerivWithin ℝ (n - i)
            (fun x : ℝ × Plane => UnforcedLeray.Short.IIb.tt (cOf ν) 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1))
            U y‖ := hL
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |KE i| * |KT (n - i)| :=
        Finset.sum_le_sum key

end UnforcedLeray.Short.PartIIIb.Concrete

end
