import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L3_SepX0PhaseBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L4_OutPrimPhaseBound

/-!
# `PartIII-b:C/rep/2/5`: the stream-cutoff gradient bound `WardGradXPhase` from its leaves

Source `the November 2 reference manuscript` 4161-4192 (`X = 𝒞_y X₀`,
`DX = χ_y DX₀ + X₀ ⊗ ∇χ_y + D((χ_y'/r) Ψ e_z)`, `∂_rΨ = r X₀_z`, `∂_zΨ = -r X₀_r`), 5212-5217.

Leaves: `WGXPointwise` (the calculus: pointwise derivative of the cutoff field, off the axis),
`WGXMeas` (measurability of the three slice densities), `WGXAxisNull` (the axis is null).
The assembly (Minkowski, S2 for `j = 0, 1`, S3a, exponent bookkeeping) is proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The slice density `1_{rIn ≤ |y'|} ‖D^j X₀(τ)‖` of `SepX0PhaseBound`. -/
def wgxJet (j : ℕ) (ν μ rIn : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (y : Space) : ℝ≥0∞ :=
  if rIn ≤ ϱ y then ‖iteratedFDeriv ℝ j (sepX0 ν μ T τ) y‖ₑ else 0

/-- The slice density `1_{annulus} |Ψ_{X₀}(τ, |y'|, y₃)|` of `OutPrimPhaseBound`. -/
def wgxPsi (ν μ R : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space) :
    ℝ≥0∞ :=
  (streamAnn ν R).indicator
    (fun y => ENNReal.ofReal |outPrim (sepX0 ν μ T) τ (ϱ y) (y 2)|) y

/-- **Leaf 1 (calculus, source 4181-4192).**  Off the axis,
`‖D(𝒞_y X₀)(y)‖ ≤ 1_{|y'|≥L}‖DX₀‖ + C L⁻¹ 1_{|y'|≥L}‖X₀‖ + C L⁻³ 1_{ann}|Ψ_{X₀}|`, `L = R√ν`.
Here `X = 0` for `|y'| < L` (`χ_y = 0`, `χ_y' = 0` on `[1,∞)`), `X = X₀` for `|y'| > R√(5ν/4)`
(`χ_y = 1`, `χ_y' = 0` on `[0,4/5]`), and on the annulus
`DX = χ_y DX₀ + X₀ ⊗ ∇χ_y + D(f(ϱ) Ψ e_z)`, `f(r) = χ_y'(νR²/r²)(-2νR²/r⁴)`,
`|∇χ_y| ≤ C/L`, `|f| ≤ C L⁻²`, `|f'| ≤ C L⁻³`, `DΨ[v] = ϱ'[v] ϱ X₀_z - ϱ X₀_r v₂`
(`outPrimDerivR`, `outPrimDerivZ`), `ϱ ≤ 2L`, and `|X₀(ϱ,0,z)| = |X₀(y)|` (axisymmetry). -/
def WGXPointwise : Prop :=
  ∀ σ₁ σ₂ : ℝ, -(1 / 4) < σ₁ → ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ν μ R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P → P ≤ 1 → μ ∈ Icc σ₁ σ₂ →
      ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
        ∀ (τ : ℝ) (y : Space), 0 < ϱ y →
          ENNReal.ofReal ‖fderiv ℝ (sepWX ν μ R χy T τ) y‖ ≤
            wgxJet 1 ν μ (R * Real.sqrt ν) T τ y +
              ENNReal.ofReal (C * (R * Real.sqrt ν) ^ (-1 : ℝ)) *
                wgxJet 0 ν μ (R * Real.sqrt ν) T τ y +
              ENNReal.ofReal (C * (R * Real.sqrt ν) ^ (-3 : ℝ)) * wgxPsi ν μ R T τ y

/-- **Leaf 2 (measurability).**  The three slice densities are a.e.-measurable in `y`. -/
def WGXMeas : Prop :=
  ∀ (ν μ R P : ℝ), 0 < ν → 0 < R → 0 < P →
    ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → ∀ τ : ℝ,
      AEMeasurable (wgxJet 1 ν μ (R * Real.sqrt ν) T τ) volume ∧
      AEMeasurable (wgxJet 0 ν μ (R * Real.sqrt ν) T τ) volume ∧
      AEMeasurable (wgxPsi ν μ R T τ) volume

/-- **Leaf 3.**  The axis `{ϱ = 0}` is a null set of `ℝ³`. -/
def WGXAxisNull : Prop := volume {y : Space | ϱ y = 0} = 0

theorem lqNorm_add_le {q : ℝ} (hq : 1 ≤ q) {f g : Space → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) :
    lqNorm q (fun y => f y + g y) ≤ lqNorm q f + lqNorm q g :=
  ENNReal.lintegral_Lp_add_le hf hg hq

theorem lqNorm_mono_ae {q : ℝ} (hq : 0 < q) {f g : Space → ℝ≥0∞} (h : ∀ᵐ y, f y ≤ g y) :
    lqNorm q f ≤ lqNorm q g := by
  unfold lqNorm
  exact ENNReal.rpow_le_rpow (lintegral_mono_ae (by
    filter_upwards [h] with y hy
    exact ENNReal.rpow_le_rpow hy hq.le)) (by positivity)

/-- **`WardGradXPhase` from its leaves** (source 4181-4192, 5212-5217). -/
theorem wardGradXPhase_of (hP : WGXPointwise) (hM : WGXMeas) (hA : WGXAxisNull)
    (h3 : SepX0PhaseBound) (h4 : OutPrimPhaseBound) : WardGradXPhase := by
  intro σ₁ σ₂ hσ χy hχ
  obtain ⟨Cp, hCp, hPt⟩ := hP σ₁ σ₂ hσ χy hχ
  obtain ⟨C0, hC0, H0⟩ := h3 σ₁ σ₂ hσ 0 (by norm_num)
  obtain ⟨C1, hC1, H1⟩ := h3 σ₁ σ₂ hσ 1 (by norm_num)
  obtain ⟨Co, hCo, Ho⟩ := h4 σ₁ σ₂ hσ
  set c0 : ℝ := 1 - Real.sqrt (5 / 6) with hc0
  have hs56 : Real.sqrt (5 / 6) < 1 := by
    rw [Real.sqrt_lt' one_pos]; norm_num
  have hc0pos : 0 < c0 := by rw [hc0]; linarith
  refine ⟨C1 * c0 ^ (-(46 / 11 : ℝ)) + Cp * C0 * c0 ^ (-(35 / 11 : ℝ)) + Cp * Co,
    0, by positivity, ?_⟩
  intro ν μ R P hν hν1 hR1 hP0 hP1 hμ T hT hSM hAx
  have hR : 0 < R := by linarith
  set L : ℝ := R * Real.sqrt ν with hL
  have hLpos : 0 < L := by rw [hL]; positivity
  set F : ℝ≥0∞ := IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) with hF
  have hrO : R * Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6) * L := by
    rw [hL, show 5 * ν / 6 = 5 / 6 * ν by ring, Real.sqrt_mul (by norm_num)]; ring
  have hD : L - R * Real.sqrt (5 * ν / 6) = c0 * L := by rw [hrO, hc0]; ring
  have hrOnn : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hlt : R * Real.sqrt (5 * ν / 6) < L := by
    have : 0 < c0 * L := mul_pos hc0pos hLpos
    linarith
  refine Filter.Eventually.of_forall (fun τ => ?_)
  obtain ⟨m1, m0, mP⟩ := hM ν μ R P hν hR hP0 T hT hSM τ
  have hq : (1 : ℝ) ≤ 22 / 3 := by norm_num
  have hq0 : (0 : ℝ) < 22 / 3 := by norm_num
  have haxis : ∀ᵐ y : Space, 0 < ϱ y := by
    have : ∀ᵐ y : Space, y ∉ {y : Space | ϱ y = 0} := measure_eq_zero_iff_ae_notMem.1 hA
    filter_upwards [this] with y hy
    exact lt_of_le_of_ne (Real.sqrt_nonneg _) (fun h => hy h.symm)
  have e1 := H1 ν μ (R * Real.sqrt (5 * ν / 6)) L P hν hμ hrOnn hlt hP0 hP1 T hT hSM τ
  have e0 := H0 ν μ (R * Real.sqrt (5 * ν / 6)) L P hν hμ hrOnn hlt hP0 hP1 T hT hSM τ
  have eo := (Ho ν μ R P hν hR hP0 hP1 hμ T hT hSM τ).2
  rw [hD] at e1 e0
  have hmc : ∀ (a : ℝ), 0 ≤ a → ∀ (g : Space → ℝ≥0∞), AEMeasurable g volume →
      AEMeasurable (fun y => ENNReal.ofReal a * g y) volume :=
    fun a _ g hg => hg.const_mul _
  unfold sliceLq
  calc lqNorm (22 / 3) (fun y => ENNReal.ofReal |‖fderiv ℝ (sepWX ν μ R χy T τ) y‖|)
      ≤ lqNorm (22 / 3) (fun y => (wgxJet 1 ν μ L T τ y +
            ENNReal.ofReal (Cp * L ^ (-1 : ℝ)) * wgxJet 0 ν μ L T τ y) +
            ENNReal.ofReal (Cp * L ^ (-3 : ℝ)) * wgxPsi ν μ R T τ y) := by
        refine lqNorm_mono_ae hq0 ?_
        filter_upwards [haxis] with y hy
        have := hPt ν μ R P hν hν1 hR1 hP0 hP1 hμ T hT hSM hAx τ y hy
        rw [abs_of_nonneg (norm_nonneg _)]
        exact this
    _ ≤ lqNorm (22 / 3) (fun y => wgxJet 1 ν μ L T τ y +
            ENNReal.ofReal (Cp * L ^ (-1 : ℝ)) * wgxJet 0 ν μ L T τ y) +
          lqNorm (22 / 3) (fun y => ENNReal.ofReal (Cp * L ^ (-3 : ℝ)) * wgxPsi ν μ R T τ y) :=
        lqNorm_add_le hq (m1.add (hmc _ (by positivity) _ m0)) (hmc _ (by positivity) _ mP)
    _ ≤ (lqNorm (22 / 3) (wgxJet 1 ν μ L T τ) +
          lqNorm (22 / 3) (fun y => ENNReal.ofReal (Cp * L ^ (-1 : ℝ)) * wgxJet 0 ν μ L T τ y)) +
          lqNorm (22 / 3) (fun y => ENNReal.ofReal (Cp * L ^ (-3 : ℝ)) * wgxPsi ν μ R T τ y) := by
        gcongr
        exact lqNorm_add_le hq m1 (hmc _ (by positivity) _ m0)
    _ = (lqNorm (22 / 3) (wgxJet 1 ν μ L T τ) +
          ENNReal.ofReal (Cp * L ^ (-1 : ℝ)) * lqNorm (22 / 3) (wgxJet 0 ν μ L T τ)) +
          ENNReal.ofReal (Cp * L ^ (-3 : ℝ)) * lqNorm (22 / 3) (wgxPsi ν μ R T τ) := by
        rw [lqNorm_const_mul hq0 _ ENNReal.ofReal_ne_top, lqNorm_const_mul hq0 _ ENNReal.ofReal_ne_top]
    _ ≤ (ENNReal.ofReal (C1 * (c0 * L) ^ (-4 - ((1 : ℕ) : ℝ) + 9 / 11)) * F +
          ENNReal.ofReal (Cp * L ^ (-1 : ℝ)) *
            (ENNReal.ofReal (C0 * (c0 * L) ^ (-4 - ((0 : ℕ) : ℝ) + 9 / 11)) * F)) +
          ENNReal.ofReal (Cp * L ^ (-3 : ℝ)) *
            (ENNReal.ofReal (Co * L ^ (-(13 / 11 : ℝ))) * F) := by
        gcongr
        · exact e1
        · exact e0
        · exact eo
    _ = ENNReal.ofReal ((C1 * c0 ^ (-(46 / 11 : ℝ)) + Cp * C0 * c0 ^ (-(35 / 11 : ℝ)) + Cp * Co) *
          L ^ (-(46 / 11 : ℝ))) * F := by
        have a1 : (c0 * L) ^ (-4 - ((1 : ℕ) : ℝ) + 9 / 11) =
            c0 ^ (-(46 / 11 : ℝ)) * L ^ (-(46 / 11 : ℝ)) := by
          rw [Real.mul_rpow hc0pos.le hLpos.le]; congr 2 <;> norm_num
        have a0 : L ^ (-1 : ℝ) * (c0 * L) ^ (-4 - ((0 : ℕ) : ℝ) + 9 / 11) =
            c0 ^ (-(35 / 11 : ℝ)) * L ^ (-(46 / 11 : ℝ)) := by
          rw [Real.mul_rpow hc0pos.le hLpos.le]
          have : L ^ (-(46 / 11 : ℝ)) = L ^ (-1 : ℝ) * L ^ (-(35 / 11 : ℝ)) := by
            rw [← Real.rpow_add hLpos]; norm_num
          rw [this]
          have h2 : (-4 - ((0 : ℕ) : ℝ) + 9 / 11 : ℝ) = -(35 / 11 : ℝ) := by norm_num
          rw [h2]; ring
        have ao : L ^ (-3 : ℝ) * L ^ (-(13 / 11 : ℝ)) = L ^ (-(46 / 11 : ℝ)) := by
          rw [← Real.rpow_add hLpos]; norm_num
        have hL1 : 0 ≤ L ^ (-(46 / 11 : ℝ)) := by positivity
        rw [← mul_assoc (ENNReal.ofReal _), ← mul_assoc (ENNReal.ofReal _),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        have : Cp * L ^ (-1 : ℝ) * (C0 * (c0 * L) ^ (-4 - ((0 : ℕ) : ℝ) + 9 / 11)) =
            Cp * C0 * (L ^ (-1 : ℝ) * (c0 * L) ^ (-4 - ((0 : ℕ) : ℝ) + 9 / 11)) := by ring
        rw [this, a0, a1, show Cp * L ^ (-3 : ℝ) * (Co * L ^ (-(13 / 11 : ℝ))) =
          Cp * Co * (L ^ (-3 : ℝ) * L ^ (-(13 / 11 : ℝ))) by ring, ao]
        ring
    _ = ENNReal.ofReal ((C1 * c0 ^ (-(46 / 11 : ℝ)) + Cp * C0 * c0 ^ (-(35 / 11 : ℝ)) + Cp * Co) *
          (ν⁻¹ ^ 0) * L ^ (-(46 / 11 : ℝ))) * F := by
        simp

end UnforcedLeray.Short.PartIIIb.Concrete

end
