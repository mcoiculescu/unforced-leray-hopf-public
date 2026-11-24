import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub3

/-!
# Decomposition of `FullOutLip` (source 1688-1689, 3996-4011 without the mask, 3604-3621, 2683)

Source: `the November 2 reference manuscript`.

`FullOutLip` follows from (a) linearity of `fullOut` in the box tensor (`FullOutSubLin`, the
dilation integrals converge absolutely for a bounded band tensor), (b) the one-tensor `L²` bound
`FullOutOneBound` applied to the box tensor `f - g` (`tv4 (f - g) = tv4 f - tv4 g`).
The one-tensor bound is the unmasked version of `FarKernelL2` (3996-4011): pointwise positive
majorant `FullOutMajorant` (triangle inequality) and the `L²` bound `FullMajL2` of the positive
operator `fullMaj` (Young with `‖∇K_t‖_{L¹} ≤ C t^{-1/2}`, `GradKL1`, dilation integral
`∫_0^1 λ^{2μ+1/2}(1-λ²)^{-1/2}dλ < ∞` for `μ > -1/4`, normalized-phase Minkowski, lifts multiply
both norms by `√π R`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- `Σ_{i,j,k} |∂_k (K_t)_{ij}(w)|` as an extended real (the gradient of the heat-Leray kernel). -/
def gradKNorm (t : ℝ) (w : Space) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    |fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK t i j x) w (coordinateVector k)|)

/-- The positive majorant of the unmasked dilation integral (source 3611-3621, 3996-4011): with
`y = chartY R x`, `τ = chartTau R x`,
`∫_0^1 λ^{2μ+2} ∫ |∇K_{ν(1-λ²)}|(y - λz) |𝒩_T f(z, τ + 2 log λ)| dz dλ`. -/
def fullMaj (R c ν μ : ℝ) (f : Chart → Ten3) (x : Chart) : ℝ≥0∞ :=
  ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) *
    ∫⁻ z : Space, gradKNorm (ν * (1 - l ^ 2)) (chartY R x - l • z) *
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
        (cartLift R c f (chartTau R x + 2 * Real.log l) z))

/-- **Linearity** (source 3611-3621): on box tensors `fullOut` is additive (`sepW` is linear in a
bounded band tensor: the kernel `∇K_t` is locally integrable for `t > 0`, `‖∇K_t‖_{L¹} ≲ t^{-1/2}`,
and `(1-λ²)^{-1/2}` is integrable in `λ`). -/
def FullOutSubLin : Prop :=
  ∀ (R c ν μ : ℝ), 0 < R → 0 < c → 0 < ν → -(1 / 4) < μ → ∀ f g : Chart → Ten3,
    IsBoxTensor f → IsBoxTensor g → ∀ x : Chart,
      fullOut R c ν μ (fun y => f y - g y) x = fullOut R c ν μ f x - fullOut R c ν μ g x

/-- **Pointwise positive majorant** (source 3611-3621): `|fullOut f x| ≤ 4 s^{-1/2} fullMaj f x`
(`‖(a,b)‖ ≤ |a|+|b|`, `|Re w| ≤ |w|`, norm of the integral at most the integral of the norm,
`|T_jk| ≤ ‖T‖`, `|λ^{2μ+2}| = λ^{2μ+2}` for real `μ`). -/
def FullOutMajorant : Prop :=
  ∀ (R c ν μ : ℝ), 0 < R → 0 < c → 0 < ν → ∀ f : Chart → Ten3, IsBoxTensor f → ∀ x : Chart,
    ENNReal.ofReal ‖fullOut R c ν μ f x‖ ≤
      ENNReal.ofReal 4 * (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * fullMaj R c ν μ f x)

/-- **`L¹` norm of the heat-Leray gradient** (source 3604-3610, heat scaling
`K_t(x) = t^{-3/2}K_1(x/√t)`): `∫ Σ|∂_k (K_t)_{ij}| ≤ C t^{-1/2}`. -/
def GradKL1 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∫⁻ w : Space, gradKNorm t w ≤
    ENNReal.ofReal C * ENNReal.ofReal (t ^ (-(1 / 2 : ℝ)))

/-- **`L²` bound of the positive operator** (source 3996-4011, 2683): Young with `GradKL1`, the
dilation integral margin for `μ > -1/4`, normalized-phase Minkowski; the bound reads the tensor only
through `tv4` (`‖nsSym T‖` is controlled by `‖tv4 T‖`). -/
def FullMajL2 : Prop :=
  ∀ (R c ν μ : ℝ), 0 < R → 0 < c → 0 < ν → -(1 / 4) < μ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Chart → Ten3, IsBoxTensor f →
      ∫⁻ x, (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * fullMaj R c ν μ f x) ^ (2 : ℝ)
          ∂(ageμ c (-3 / 2)) ≤
        ENNReal.ofReal C ^ (2 : ℝ) * ∫⁻ x, ‖tv4 (f x)‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2))

/-- **One-tensor `L²` bound** (source 1688-1689, 3996-4011 without the mask). -/
def FullOutOneBound : Prop :=
  ∀ (R c ν μ : ℝ), 0 < R → 0 < c → 0 < ν → -(1 / 4) < μ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Chart → Ten3, IsBoxTensor f →
      eLpNorm (fun x => fullOut R c ν μ f x) 2 (ageμ c (-3 / 2)) ≤
        ENNReal.ofReal C * eLpNorm (fun x => tv4 (f x)) 2 (ageμ c (-1 / 2))

theorem fullOutOneBound_of (h1 : FullOutMajorant) (h2 : FullMajL2) : FullOutOneBound := by
  intro R c ν μ hR hc hν hμ
  obtain ⟨C2, hC2, hl⟩ := h2 R c ν μ hR hc hν hμ
  have hp : (0 : ℝ) < 2 := by norm_num
  refine ⟨4 * C2, mul_nonneg (by norm_num) hC2, fun f hf => ?_⟩
  have key : ∫⁻ x, ‖fullOut R c ν μ f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) ≤
      (ENNReal.ofReal 4 * ENNReal.ofReal C2) ^ (2 : ℝ) *
        ∫⁻ x, ‖tv4 (f x)‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) := by
    calc ∫⁻ x, ‖fullOut R c ν μ f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2))
        ≤ ∫⁻ x, (ENNReal.ofReal 4) ^ (2 : ℝ) *
            (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * fullMaj R c ν μ f x) ^ (2 : ℝ)
            ∂(ageμ c (-3 / 2)) := by
          refine lintegral_mono fun x => ?_
          rw [← ofReal_norm, ← ENNReal.mul_rpow_of_nonneg _ _ hp.le]
          exact ENNReal.rpow_le_rpow (h1 R c ν μ hR hc hν f hf x) hp.le
      _ = (ENNReal.ofReal 4) ^ (2 : ℝ) *
            ∫⁻ x, (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * fullMaj R c ν μ f x) ^ (2 : ℝ)
              ∂(ageμ c (-3 / 2)) :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
      _ ≤ (ENNReal.ofReal 4) ^ (2 : ℝ) *
            (ENNReal.ofReal C2 ^ (2 : ℝ) * ∫⁻ x, ‖tv4 (f x)‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2))) := by
          gcongr; exact hl f hf
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, mul_assoc]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  calc (∫⁻ x, ‖fullOut R c ν μ f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2))) ^ (1 / (2 : ℝ))
      ≤ ((ENNReal.ofReal 4 * ENNReal.ofReal C2) ^ (2 : ℝ) *
        ∫⁻ x, ‖tv4 (f x)‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2))) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow key (by norm_num)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num

theorem isBoxTensor_sub {f g : Chart → Ten3} (hf : IsBoxTensor f) (hg : IsBoxTensor g) :
    IsBoxTensor (fun x => f x - g x) := by
  obtain ⟨Bf, hBf⟩ := hf.bounded
  obtain ⟨Bg, hBg⟩ := hg.bounded
  obtain ⟨a₁, a₂, La, ha, hfa⟩ := hf.band
  obtain ⟨b₁, b₂, Lb, hb, hgb⟩ := hg.band
  refine ⟨hf.measurable.sub hg.measurable, ⟨Bf + Bg, fun p => ?_⟩,
    ⟨min a₁ b₁, max a₂ b₂, max La Lb, lt_min ha hb, fun p hp => ?_⟩⟩
  · exact (norm_sub_le _ _).trans (add_le_add (hBf p) (hBg p))
  · by_cases hfp : f p = 0
    · have hgp : g p ≠ 0 := by
        intro h; apply hp; rw [hfp, h, sub_zero]
      obtain ⟨h1, h2, h3⟩ := hgb p hgp
      exact ⟨min_le_of_right_le h1, le_max_of_le_right h2, le_max_of_le_right h3⟩
    · obtain ⟨h1, h2, h3⟩ := hfa p hfp
      exact ⟨min_le_of_left_le h1, le_max_of_le_left h2, le_max_of_le_left h3⟩

theorem tv4_sub (a b : Ten3) : tv4 (a - b) = tv4 a - tv4 b := by
  unfold tv4 symRZ
  ext i
  fin_cases i <;> simp <;> ring

theorem fullOutLip_of (h1 : FullOutSubLin) (h2 : FullOutOneBound) : FullOutLip := by
  intro R c ν μ hR hc hν hμ
  obtain ⟨C, hC, hb⟩ := h2 R c ν μ hR hc hν hμ
  refine ⟨C, hC, fun f g hf hg => ?_⟩
  have e1 : (fun x => fullOut R c ν μ f x - fullOut R c ν μ g x) =
      fun x => fullOut R c ν μ (fun y => f y - g y) x :=
    funext fun x => (h1 R c ν μ hR hc hν hμ f g hf hg x).symm
  have e2 : (fun x => tv4 (f x) - tv4 (g x)) = fun x => tv4 ((fun y => f y - g y) x) :=
    funext fun x => (tv4_sub _ _).symm
  rw [e1, e2]
  exact hb _ (isBoxTensor_sub hf hg)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
