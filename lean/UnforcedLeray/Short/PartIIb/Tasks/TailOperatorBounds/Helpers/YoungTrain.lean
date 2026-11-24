import UnforcedLeray.Short.PartIIb.Tasks.FlatReconstruction.FreeInteraction
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_3
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_4

/-!
# Helpers for `PartII-b:G2/3/2`: pointwise young-end train bounds (SP 2443-2445)
-/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb
namespace YoungHelp

open UnforcedLeray.Cons.C03.Concrete

/-- Band bound for all `0 < s ≤ 1`, any `ageCut`. -/
theorem train_young_bound (dm dp : ℝ) (hdm : 0 < dm) :
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
        ∀ x : Coord, 0 < x.1 → x.1 ≤ 1 →
          ‖p.train.v x.1 x.2‖ ≤ C * (p.ν ^ k)⁻¹ ∧
          ‖Axi.dQ (fun m : Coord => p.train.v m.1 m.2) x‖ ≤ C * (p.ν ^ k)⁻¹ ∧
          ‖Axi.dEta (fun m : Coord => p.train.v m.1 m.2) x‖ ≤ C * (p.ν ^ k)⁻¹ := by
  obtain ⟨C, k, νb, hC, hνb, H⟩ := FreeInteractionAux.trainVel_band_bound 1 one_pos dm dp hdm
  refine ⟨C, k, min νb 1, hC, lt_min hνb one_pos, fun p d hreg hν x hx0 hx1 => ?_⟩
  let p' : Params := { p with ageCut := 1, ageCut_pos := one_pos }
  have hreg' : BgRegime p' d dm dp :=
    ⟨hreg.dm_pos, hreg.dm_le, hreg.le_dp, hreg.eps_eq, hreg.c_eq, hreg.train_buc,
      hreg.train_stream_smooth⟩
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hxH : x.1 ≤ p'.H := by
    show x.1 ≤ 1 / p.ν
    rw [le_div_iff₀ p.ν_pos]
    nlinarith [p.ν_pos]
  exact H p' d hreg' (hν.trans (min_le_left _ _)) rfl x hx0 hxH

/-- Component of the slice derivative is bounded by the chart derivative. -/
theorem fderiv_comp_le {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hv : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (z e : UnforcedLeray.Cyl.Plane) (i : Fin 2) :
    |fderiv ℝ (fun w : UnforcedLeray.Cyl.Plane => tr.v s w i) z e| ≤
      ‖fderiv ℝ (fun x : Coord => tr.v x.1 x.2) (s, z) (0, e)‖ := by
  have hdiff : DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Cyl.Plane => tr.v x.1 x.2) (s, z) :=
    (hv.differentiableOn (by simp)).differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds (show (s, z) ∈ Ioi 0 ×ˢ univ from ⟨hs, trivial⟩))
  have hG : HasFDerivAt (fun w : UnforcedLeray.Cyl.Plane => tr.v s w)
      ((fderiv ℝ (fun x : Coord => tr.v x.1 x.2) (s, z)).comp
        ((0 : UnforcedLeray.Cyl.Plane →L[ℝ] ℝ).prod
          (ContinuousLinearMap.id ℝ UnforcedLeray.Cyl.Plane))) z :=
    hdiff.hasFDerivAt.comp z ((hasFDerivAt_const s z).prodMk (hasFDerivAt_id z))
  have hP := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i).hasFDerivAt.comp z hG
  have hq : fderiv ℝ (fun w : UnforcedLeray.Cyl.Plane => tr.v s w i) z e =
      (fderiv ℝ (fun x : Coord => tr.v x.1 x.2) (s, z) (0, e)) i := by
    have : (fun w : UnforcedLeray.Cyl.Plane => tr.v s w i) =
        (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i) ∘ (fun w => tr.v s w) := rfl
    rw [this, hP.fderiv]
    simp
  rw [hq]
  have := PiLp.norm_apply_le (fderiv ℝ (fun x : Coord => tr.v x.1 x.2) (s, z) (0, e)) i
  rwa [Real.norm_eq_abs] at this

theorem flatK_norm_le {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hv : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ))
    (b gq gη : CProf) (x : Coord) (hx : 0 < x.1) (B : ℝ)
    (h1 : ‖tr.v x.1 x.2‖ ≤ B)
    (h2 : ‖Axi.dQ (fun m : Coord => tr.v m.1 m.2) x‖ ≤ B)
    (h3 : ‖Axi.dEta (fun m : Coord => tr.v m.1 m.2) x‖ ≤ B) :
    ‖flatK tr b gq gη x‖ ≤ 2 * (x.1 * B * (‖gq x‖ + ‖gη x‖ + 2 * ‖b x‖)) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans h1
  have hcomp : ∀ i : Fin 2, ‖(flatK tr b gq gη x) i‖ ≤
      x.1 * B * (‖gq x‖ + ‖gη x‖ + 2 * ‖b x‖) := by
    intro i
    have a0 : |tr.v x.1 x.2 0| ≤ B := by
      have := PiLp.norm_apply_le (tr.v x.1 x.2) 0
      rw [Real.norm_eq_abs] at this; linarith
    have a1 : |tr.v x.1 x.2 1| ≤ B := by
      have := PiLp.norm_apply_le (tr.v x.1 x.2) 1
      rw [Real.norm_eq_abs] at this; linarith
    have d1 := fderiv_comp_le tr hv hx x.2 (1, 0) i
    have d2 := fderiv_comp_le tr hv hx x.2 (0, 1) i
    have d1' : |fderiv ℝ (fun z => tr.v x.1 z i) x.2 ((1 : ℝ), (0 : ℝ))| ≤ B :=
      d1.trans h2
    have d2' : |fderiv ℝ (fun z => tr.v x.1 z i) x.2 ((0 : ℝ), (1 : ℝ))| ≤ B :=
      d2.trans h3
    have g1 : ‖gq x i‖ ≤ ‖gq x‖ := PiLp.norm_apply_le _ i
    have g2 : ‖gη x i‖ ≤ ‖gη x‖ := PiLp.norm_apply_le _ i
    have b0 : ‖b x 0‖ ≤ ‖b x‖ := PiLp.norm_apply_le _ 0
    have b1 : ‖b x 1‖ ≤ ‖b x‖ := PiLp.norm_apply_le _ 1
    show ‖(x.1 : ℂ) * (((tr.v x.1 x.2 0 : ℝ) : ℂ) * gq x i + ((tr.v x.1 x.2 1 : ℝ) : ℂ) * gη x i +
      b x 0 * ((fderiv ℝ (fun z => tr.v x.1 z i) x.2 ((1 : ℝ), (0 : ℝ)) : ℝ) : ℂ) +
      b x 1 * ((fderiv ℝ (fun z => tr.v x.1 z i) x.2 ((0 : ℝ), (1 : ℝ)) : ℝ) : ℂ))‖ ≤ _
    set D1 := fderiv ℝ (fun z => tr.v x.1 z i) x.2 ((1 : ℝ), (0 : ℝ))
    set D2 := fderiv ℝ (fun z => tr.v x.1 z i) x.2 ((0 : ℝ), (1 : ℝ))
    rw [norm_mul]
    have hxn : ‖(x.1 : ℂ)‖ = x.1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    rw [hxn, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hx.le
    have e1 : ‖((tr.v x.1 x.2 0 : ℝ) : ℂ) * gq x i‖ ≤ B * ‖gq x‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul a0 g1 (norm_nonneg _) hB
    have e2 : ‖((tr.v x.1 x.2 1 : ℝ) : ℂ) * gη x i‖ ≤ B * ‖gη x‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul a1 g2 (norm_nonneg _) hB
    have e3 : ‖b x 0 * (D1 : ℂ)‖ ≤ B * ‖b x‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul d1' b0 (norm_nonneg _) hB
    have e4 : ‖b x 1 * (D2 : ℂ)‖ ≤ B * ‖b x‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul d2' b1 (norm_nonneg _) hB
    have t1 := norm_add_le (((tr.v x.1 x.2 0 : ℝ) : ℂ) * gq x i + ((tr.v x.1 x.2 1 : ℝ) : ℂ) * gη x i +
      b x 0 * (D1 : ℂ)) (b x 1 * (D2 : ℂ))
    have t2 := norm_add_le (((tr.v x.1 x.2 0 : ℝ) : ℂ) * gq x i + ((tr.v x.1 x.2 1 : ℝ) : ℂ) * gη x i)
      (b x 0 * (D1 : ℂ))
    have t3 := norm_add_le (((tr.v x.1 x.2 0 : ℝ) : ℂ) * gq x i) (((tr.v x.1 x.2 1 : ℝ) : ℂ) * gη x i)
    linarith
  have hs : ‖flatK tr b gq gη x‖ ≤ ‖(flatK tr b gq gη x) 0‖ + ‖(flatK tr b gq gη x) 1‖ := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [norm_nonneg ((flatK tr b gq gη x) 0), norm_nonneg ((flatK tr b gq gη x) 1)]
  have := hcomp 0
  have := hcomp 1
  linarith

end YoungHelp
end UnforcedLeray.Short.IIb
