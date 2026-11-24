import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1_1_3_2.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1_1_3_2.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L4
import Mathlib.MeasureTheory.Group.Measure

/-!
# Cylinder kernel bound `farKernelL2` (`PartIII-b:IIIb-D2/3/1/3/1/1/1/3/2`, target `farKernelL2`)

Source `the November 2 reference manuscript`
4155-4186, 3631-3646.  On the cylinder `ϱ z ≤ rOut` with `2 rOut ≤ ϱ y` and `l ∈ (0,1)`:
`ϱ(y - l z) ≥ ϱ y / 2 =: a`, so `‖y - l z‖² ≥ a² + (y₂ - l z₂)²`.  Hence the squared kernel is
dominated by `1_{cyl} G(z₂)` with `G t = (a² + (y₂ - l t)²)^{-(4+n)}`; the slice bound `farSlice`
gives `4 rOut²` times `∫ G`, the affine change of variables gives `l⁻¹ ∫ (a² + u²)^{-(4+n)} du`,
and `farVert` evaluates the vertical integral as `c a^{-(7+2n)}`.  Finally
`a^{-(7+2n)} ≤ 64 ϱ(y)^{-6} rOut^{-(1+2n)}` because `a ≥ rOut`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Rewriting `(x^(-k))^2` as `(x^2)^(-k)` for real powers, `x ≥ 0`. -/
lemma farK_pow2 (x k : ℝ) (hx : 0 ≤ x) : (x ^ (-k)) ^ (2 : ℝ) = (x ^ (2 : ℝ)) ^ (-k) := by
  rw [← Real.rpow_mul hx, ← Real.rpow_mul hx]
  congr 1
  ring

/-- Squared norm split into the distance to the axis and the third coordinate. -/
lemma farNorm_sq (w : Space) : ‖w‖ ^ 2 = ϱ w ^ 2 + w 2 ^ 2 := by
  have h0 : 0 ≤ w 0 ^ 2 + w 1 ^ 2 := by positivity
  have hs : 0 ≤ ∑ i : Fin 3, ‖w i‖ ^ 2 := Finset.sum_nonneg (fun i _ => by positivity)
  unfold ϱ
  rw [Real.sq_sqrt h0, EuclideanSpace.norm_eq, Real.sq_sqrt hs, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  try ring

/-- Exponent arithmetic: `(p/2)^{-(7+2n)} ≤ 64 p^{-6} r^{-(1+2n)}` when `r ≤ p/2`. -/
lemma farPowBound (p r : ℝ) (hp : 0 < p) (hr : 0 < r) (h : r ≤ p / 2) (n : ℕ) :
    (p / 2) ^ (-(7 + 2 * (n : ℝ))) ≤ 64 * p ^ (-6 : ℝ) * r ^ (-(1 + 2 * (n : ℝ))) := by
  have ha : 0 < p / 2 := by positivity
  have hsix : ∀ x : ℝ, 0 < x → x ^ (-6 : ℝ) = (x ^ 6)⁻¹ := by
    intro x hx
    rw [show (-6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx.le, Real.rpow_natCast]
  have e1 : (p / 2) ^ (-(7 + 2 * (n : ℝ))) =
      (p / 2) ^ (-6 : ℝ) * (p / 2) ^ (-(1 + 2 * (n : ℝ))) := by
    rw [← Real.rpow_add ha]
    congr 1
    ring
  have e2 : (p / 2) ^ (-6 : ℝ) = 64 * p ^ (-6 : ℝ) := by
    rw [hsix _ ha, hsix _ hp, div_pow, inv_div, div_eq_mul_inv]
    norm_num
  have e3 : (p / 2) ^ (-(1 + 2 * (n : ℝ))) ≤ r ^ (-(1 + 2 * (n : ℝ))) := by
    apply Real.rpow_le_rpow_of_nonpos hr h
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left e3 (by positivity)

/-- **Cylinder kernel bound** (`FarKernelL2`, 3631-3646 with `p = 2`, 4155-4186). -/
theorem farKernelL2 : FarKernelL2 := by
  unfold FarKernelL2
  intro n hn rOut hr
  obtain ⟨c, hc, hV⟩ := farVert n hn
  refine ⟨4 * rOut ^ 2 * c * 64 * rOut ^ (-(1 + 2 * (n : ℝ))), by positivity, ?_⟩
  intro y hy l hl
  have hl0 : 0 < l := hl.1
  have hl1 : l < 1 := hl.2
  have hϱy : 0 ≤ ϱ y := ϱ_nonneg y
  have ha : 0 < ϱ y / 2 := by linarith
  have hr2 : rOut ≤ ϱ y / 2 := by linarith
  -- pointwise domination of the squared kernel by the slice majorant
  have hpt : ∀ z : Space,
      (Set.indicator {z : Space | ϱ z ≤ rOut}
        (fun z => ENNReal.ofReal (‖y - l • z‖ ^ (-(4 + (n : ℝ))))) z) ^ (2 : ℝ) ≤
      Set.indicator {z : Space | ϱ z ≤ rOut}
        (fun z => (fun t : ℝ => ENNReal.ofReal
          (((ϱ y / 2) ^ 2 + (y 2 - l * t) ^ 2) ^ (-(4 + (n : ℝ))))) (z 2)) z := by
    intro z
    by_cases hz : ϱ z ≤ rOut
    · rw [Set.indicator_of_mem (show z ∈ {z : Space | ϱ z ≤ rOut} from hz),
        Set.indicator_of_mem (show z ∈ {z : Space | ϱ z ≤ rOut} from hz)]
      dsimp only
      have hzn : 0 ≤ ϱ z := ϱ_nonneg z
      have h1 := L4_varrho_tri y (l • z)
      have h2 := L4_varrho_smul l hl0.le z
      have h3 : l * ϱ z ≤ rOut := by nlinarith [mul_nonneg (sub_nonneg.2 hl1.le) hzn]
      have hw : ϱ y / 2 ≤ ϱ (y - l • z) := by linarith
      have hw2 : (ϱ y / 2) ^ 2 ≤ ϱ (y - l • z) ^ 2 := by
        nlinarith [mul_le_mul hw hw ha.le (ha.le.trans hw)]
      have hc2 : (y - l • z) 2 = y 2 - l * z 2 := by simp
      have hsq : (ϱ y / 2) ^ 2 + (y 2 - l * z 2) ^ 2 ≤ ‖y - l • z‖ ^ 2 := by
        rw [farNorm_sq, hc2]
        linarith
      have hA2 : 0 < (ϱ y / 2) ^ 2 := pow_pos ha 2
      have hnn : 0 ≤ ‖y - l • z‖ ^ (-(4 + (n : ℝ))) := Real.rpow_nonneg (norm_nonneg _) _
      rw [ENNReal.ofReal_rpow_of_nonneg hnn (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      rw [farK_pow2 (‖y - l • z‖) (4 + (n : ℝ)) (norm_nonneg _), Real.rpow_two]
      apply Real.rpow_le_rpow_of_nonpos (add_pos_of_pos_of_nonneg hA2 (sq_nonneg _)) hsq
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · rw [Set.indicator_of_notMem (show z ∉ {z : Space | ϱ z ≤ rOut} from hz),
        Set.indicator_of_notMem (show z ∉ {z : Space | ϱ z ≤ rOut} from hz)]
      rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
  -- measurability of the slice function and of the vertical kernel
  have hG : Measurable (fun t : ℝ => ENNReal.ofReal
      (((ϱ y / 2) ^ 2 + (y 2 - l * t) ^ 2) ^ (-(4 + (n : ℝ))))) := by
    apply Measurable.ennreal_ofReal
    fun_prop
  have hS := farSlice rOut hr _ hG
  have hH : Measurable (fun u : ℝ => ENNReal.ofReal
      (((ϱ y / 2) ^ 2 + (y 2 - u) ^ 2) ^ (-(4 + (n : ℝ))))) := by
    apply Measurable.ennreal_ofReal
    fun_prop
  have hF : Measurable (fun u : ℝ => ENNReal.ofReal
      (((ϱ y / 2) ^ 2 + u ^ 2) ^ (-(4 + (n : ℝ))))) := by
    apply Measurable.ennreal_ofReal
    fun_prop
  -- affine change of variables `t ↦ l t` and `u ↦ y₂ - u`
  have hint1 : ∫⁻ t : ℝ, ENNReal.ofReal
      (((ϱ y / 2) ^ 2 + (y 2 - l * t) ^ 2) ^ (-(4 + (n : ℝ)))) ≤
      ENNReal.ofReal l⁻¹ * ENNReal.ofReal (c * (ϱ y / 2) ^ (-(7 + 2 * (n : ℝ)))) := by
    have hscale : ∫⁻ t : ℝ, ENNReal.ofReal
        (((ϱ y / 2) ^ 2 + (y 2 - l * t) ^ 2) ^ (-(4 + (n : ℝ)))) =
        ENNReal.ofReal l⁻¹ * ∫⁻ u : ℝ, ENNReal.ofReal
          (((ϱ y / 2) ^ 2 + (y 2 - u) ^ 2) ^ (-(4 + (n : ℝ)))) :=
      farVert_scale _ hH l hl0
    have hmp : ∫⁻ u : ℝ, ENNReal.ofReal
        (((ϱ y / 2) ^ 2 + (y 2 - u) ^ 2) ^ (-(4 + (n : ℝ)))) =
        ∫⁻ u : ℝ, ENNReal.ofReal (((ϱ y / 2) ^ 2 + u ^ 2) ^ (-(4 + (n : ℝ)))) :=
      (Measure.measurePreserving_sub_left (volume : Measure ℝ) (y 2)).lintegral_comp hF
    have hv := hV (ϱ y / 2) ha
    rw [hscale, hmp]
    exact mul_le_mul_of_nonneg_left hv zero_le
  -- assemble: Cauchy-type domination, slice bound, change of variables
  have hfinal : ∫⁻ z : Space,
      (Set.indicator {z : Space | ϱ z ≤ rOut}
        (fun z => ENNReal.ofReal (‖y - l • z‖ ^ (-(4 + (n : ℝ))))) z) ^ (2 : ℝ) ≤
      ENNReal.ofReal (4 * rOut ^ 2 * (l⁻¹ * (c * (ϱ y / 2) ^ (-(7 + 2 * (n : ℝ)))))) := by
    have hfin : ENNReal.ofReal (4 * rOut ^ 2) *
        (ENNReal.ofReal l⁻¹ * ENNReal.ofReal (c * (ϱ y / 2) ^ (-(7 + 2 * (n : ℝ))))) =
        ENNReal.ofReal (4 * rOut ^ 2 * (l⁻¹ * (c * (ϱ y / 2) ^ (-(7 + 2 * (n : ℝ)))))) := by
      rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 * rOut ^ 2 by positivity),
        ENNReal.ofReal_mul (show (0 : ℝ) ≤ l⁻¹ by positivity)]
    exact le_trans (lintegral_mono hpt)
      (le_trans hS (le_trans (mul_le_mul_of_nonneg_left hint1 zero_le) (le_of_eq hfin)))
  -- exponent bound on the cylinder side
  have hA := farPowBound (ϱ y) rOut (by linarith) hr hr2 n
  have hL : 0 ≤ 4 * rOut ^ 2 * l⁻¹ * c := by positivity
  have harith : 4 * rOut ^ 2 * (l⁻¹ * (c * (ϱ y / 2) ^ (-(7 + 2 * (n : ℝ))))) ≤
      4 * rOut ^ 2 * c * 64 * rOut ^ (-(1 + 2 * (n : ℝ))) * l⁻¹ * ϱ y ^ (-6 : ℝ) := by
    calc 4 * rOut ^ 2 * (l⁻¹ * (c * (ϱ y / 2) ^ (-(7 + 2 * (n : ℝ)))))
        = (4 * rOut ^ 2 * l⁻¹ * c) * (ϱ y / 2) ^ (-(7 + 2 * (n : ℝ))) := by ring
      _ ≤ (4 * rOut ^ 2 * l⁻¹ * c) * (64 * ϱ y ^ (-6 : ℝ) * rOut ^ (-(1 + 2 * (n : ℝ)))) :=
          mul_le_mul_of_nonneg_left hA hL
      _ = 4 * rOut ^ 2 * c * 64 * rOut ^ (-(1 + 2 * (n : ℝ))) * l⁻¹ * ϱ y ^ (-6 : ℝ) := by ring
  rw [Real.rpow_neg_one]
  exact le_trans hfinal (ENNReal.ofReal_le_ofReal harith)

end UnforcedLeray.Short.PartIIIb.Concrete
