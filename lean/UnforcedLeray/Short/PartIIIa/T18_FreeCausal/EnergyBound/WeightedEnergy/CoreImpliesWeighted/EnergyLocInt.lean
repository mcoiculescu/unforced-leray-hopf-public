import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_3_1_4
import UnforcedLeray.Short.PartIIIa.Sub.Audit0.AuditT18_3_1_4_GainFactsCorrected

/-!
# Part III-a, `PartIII-a:T18/3/1/4/1`: `EnergyLocIntegrable` (Lemma 1)

Source of record: `the November 2 reference manuscript`, lines 3541-3552 and
3427-3440. For standing data `(F, b, G)` and `[s₁, s₂] ⊂ (0,∞)`, the functions `E(s) = energyE`,
`N(s) = energyN`, `R(s) = energyR` and `J(s) = ∫_cell |F||G|` are integrable on `Icc s₁ s₂`.

Route: `energyLoc` (for `|b|² + |G|²`) and `L2locTensor` (for `|F|²`) give finiteness of the
lower integrals over `Icc s₁ s₂ × cell` of majorants `g`. The `s`-integrability of the cell integral
of `f` with `|f| ≤ g` follows from `Integrable.integral_prod_left` on the product of restricted
measures (`Measure.prod_restrict`). The product term `R` and `J` are bounded by
`|F̃||G̃| ≤ |F|² + |G|²` (`abs_sum_re_le_tnorm2_mul`, Cauchy-Schwarz).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace EnergyLocInt

theorem measurable_vnorm2_pt {α : Type*} [MeasurableSpace α] {f : α → Fin 2 → ℂ}
    (hf : ∀ i, Measurable fun a => f a i) : Measurable fun a => vnorm2 (f a) := by
  unfold vnorm2
  apply Measurable.sqrt
  apply Finset.measurable_sum
  intro i _
  exact ((hf i).norm).pow_const 2

theorem measurable_tnorm2_pt {α : Type*} [MeasurableSpace α] {f : α → Fin 2 → Fin 2 → ℂ}
    (hf : ∀ i j, Measurable fun a => f a i j) : Measurable fun a => tnorm2 (f a) := by
  unfold tnorm2
  apply Measurable.sqrt
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact ((hf i j).norm).pow_const 2

/-- `|x y| ≤ x² + y²`. -/
theorem abs_mul_le_sq_add' (x y : ℝ) : |x * y| ≤ x ^ 2 + y ^ 2 := by
  rw [abs_mul]
  nlinarith [abs_nonneg x, abs_nonneg y, sq_abs x, sq_abs y, sq_nonneg (|x| - |y|)]

/-- The `s`-integrability of the cell integral of `f`, from a majorant `g` with finite lower
integral over `Icc s₁ s₂ × cell`. -/
theorem integrableOn_cell_integral {c s₁ s₂ : ℝ} (f g : ℝ × (ℝ × ℝ) → ℝ)
    (hf : Measurable f) (hbd : ∀ p, |f p| ≤ g p)
    (hfin : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (g p) < ⊤) :
    IntegrableOn (fun s => ∫ x in B0579.cell c, f (s, x)) (Icc s₁ s₂) := by
  have hI : Integrable f ((volume.restrict (Icc s₁ s₂)).prod (volume.restrict (B0579.cell c))) := by
    rw [Measure.prod_restrict]
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (lintegral_mono fun p => ?_) hfin
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hbd p)
  exact hI.integral_prod_left

/-- Sum of two functions with finite lower integrals of `ofReal` has finite lower integral. -/
theorem lintegral_ofReal_add_lt_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b : α → ℝ} (ha : Measurable a)
    (ha' : ∫⁻ x, ENNReal.ofReal (a x) ∂μ < ⊤) (hb' : ∫⁻ x, ENNReal.ofReal (b x) ∂μ < ⊤) :
    ∫⁻ x, ENNReal.ofReal (a x + b x) ∂μ < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono fun x => ENNReal.ofReal_add_le) ?_
  rw [lintegral_add_left ha.ennreal_ofReal]
  exact ENNReal.add_lt_top.2 ⟨ha', hb'⟩

end EnergyLocInt

open EnergyLocInt

/-- **Lemma 1** (`PartIII-a:T18/3/1/4/1`; SP 3541-3552): `EnergyLocIntegrable`. -/
theorem energyLocIntegrable : UnforcedLeray.Short.IIIa.EnergyLocIntegrable := by
  unfold EnergyLocIntegrable
  intro c ν μ F b G hD s₁ s₂ h₁ h₂
  have hbm : ∀ i, Measurable fun p => b p i := hD.sol.measurable
  have hGm : ∀ i j, Measurable fun p => G p i j := hD.sol.gradMeasurable
  have hFm : ∀ i j, Measurable fun p => F p i j := hD.meas
  have hLoc := hD.sol.energyLoc s₁ s₂ h₁ h₂
  have hF2 := hD.l2loc s₁ s₂ h₁ h₂
  have hV2 : Measurable fun p => vnorm2 (b p) ^ 2 := (measurable_vnorm2_pt hbm).pow_const 2
  have hG2 : Measurable fun p => tnorm2 (G p) ^ 2 := (measurable_tnorm2_pt hGm).pow_const 2
  have hF2m : Measurable fun p => tnorm2 (F p) ^ 2 := (measurable_tnorm2_pt hFm).pow_const 2
  have hTG : Measurable fun p => tnorm2 (G p) := measurable_tnorm2_pt hGm
  have hTF : Measurable fun p => tnorm2 (F p) := measurable_tnorm2_pt hFm
  -- finiteness of the majorants
  have hB : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
      ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) < ⊤ := hLoc
  have hA : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
      ENNReal.ofReal (tnorm2 (F p) ^ 2 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2)) < ⊤ :=
    lintegral_ofReal_add_lt_top hF2m hF2 hB
  have hVb : ∀ p, |vnorm2 (b p) ^ 2| ≤ vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2 := fun p => by
    rw [abs_of_nonneg (sq_nonneg _)]
    linarith [sq_nonneg (tnorm2 (G p))]
  have hGb : ∀ p, |tnorm2 (G p) ^ 2| ≤ vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2 := fun p => by
    rw [abs_of_nonneg (sq_nonneg _)]
    linarith [sq_nonneg (vnorm2 (b p))]
  have hRm : Measurable fun p => ∑ i : Fin 2, ∑ j : Fin 2,
      ((F p i j).re * (G p i j).re + (F p i j).im * (G p i j).im) := by
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    exact ((Complex.measurable_re.comp (hFm i j)).mul (Complex.measurable_re.comp (hGm i j))).add
      ((Complex.measurable_im.comp (hFm i j)).mul (Complex.measurable_im.comp (hGm i j)))
  have hRb : ∀ p, |∑ i : Fin 2, ∑ j : Fin 2,
      ((F p i j).re * (G p i j).re + (F p i j).im * (G p i j).im)|
      ≤ tnorm2 (F p) ^ 2 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) := fun p => by
    have h1 := abs_sum_re_le_tnorm2_mul (F p) (G p)
    have h2 := abs_mul_le_sq_add' (tnorm2 (F p)) (tnorm2 (G p))
    have h3 : 0 ≤ vnorm2 (b p) ^ 2 := sq_nonneg _
    linarith [le_abs_self (tnorm2 (F p) * tnorm2 (G p))]
  have hJm : Measurable fun p => tnorm2 (F p) * tnorm2 (G p) := hTF.mul hTG
  have hJb : ∀ p, |tnorm2 (F p) * tnorm2 (G p)|
      ≤ tnorm2 (F p) ^ 2 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) := fun p => by
    have h2 := abs_mul_le_sq_add' (tnorm2 (F p)) (tnorm2 (G p))
    have h3 : 0 ≤ vnorm2 (b p) ^ 2 := sq_nonneg _
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact integrableOn_cell_integral (fun p => vnorm2 (b p) ^ 2)
      (fun p => vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) hV2 hVb hB
  · exact integrableOn_cell_integral (fun p => tnorm2 (G p) ^ 2)
      (fun p => vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) hG2 hGb hB
  · exact integrableOn_cell_integral
      (fun p => ∑ i : Fin 2, ∑ j : Fin 2,
        ((F p i j).re * (G p i j).re + (F p i j).im * (G p i j).im))
      (fun p => tnorm2 (F p) ^ 2 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2)) hRm hRb hA
  · exact integrableOn_cell_integral (fun p => tnorm2 (F p) * tnorm2 (G p))
      (fun p => tnorm2 (F p) ^ 2 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2)) hJm hJb hA

end UnforcedLeray.Short.IIIa
