import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Core
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.Defs

/-!
# `PartIII-b:C/rep/5/1/2/4/1/4`: the stream bin bound from five leaves

Source `the November 2 reference manuscript` 5585-5593, 5592 ("The outward stream
primitive obeys the same bound"), 4178-4186.  The architecture is that of
`Sub/PartIII-b_C_rep_5_1_2_4_1_3/Kernel.lean` for the stream kernel
`k(y, w) = (ϱ(y)² (ϱ(y)² + (y₃ - w₃)²))⁻¹`.

Re-derived powers: for an output `y` with `ϱ(y) = r ≥ r₀ = R/√s₀`,
`∫ k(y, w)² dy = 2π ∫_{r ≥ r₀} r⁻³ (∫ (r² + h²)⁻² dh) dr = 2π ∫ r⁻³ (π/(2r³)) dr = (π²/5) r₀⁻⁵`,
i.e. `gapS R s₀ = (π²/5)(R/√s₀)⁻⁵`: the same `r₀⁻⁵` (hence `R^{-3/2} s₀^{5/4}` after the chart
normalization) as the order-four kernel off the gap; no radial gap (hence no `(1-θ)`) is needed.
The final constant is `2π^{3/2}/√5` (θ-free).

The proved assembly is `wardYStreamMajBinCore_of`, from the Props `StreamChartMajSq`,
`StreamChartMeasurable`, `PsiSMeasurable`, `PsiSRotInv`, `PsiSPeriodic`, `PsiSAtomsMinkowski`,
`StreamAtomBound`, `StreamConstAlgebra`; the generic leaves `ChartToPhys`, `SourceMass`, `BinNull`
are already proved (`WYCore.chartToPhys`, `WYCore.sourceMass`, `WYCore.binNull`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYStream

open UnforcedLeray.Short.PartIIIb.Concrete.WYCore (srcW omega2 ybin)

/-- The azimuth-free stream majorant
`Ψ_s(τ, y) = ∫₀¹ ∫_{ϱ(z) < θϱ(y)} ϱ(y)⁻² (ϱ(y)² + (y₃ - λz₃)²)⁻¹ W(τ + 2 log λ, z) dz dλ`
(source 4178-4186, 5592; `W = srcW`). -/
def psiMajS (R c θ : ℝ) (G : Chart → ℝ≥0∞) (τ : ℝ) (y : Space) : ℝ≥0∞ :=
  ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z in {z : Space | ϱ z < θ * ϱ y},
    ENNReal.ofReal ((ϱ y ^ 2 * (ϱ y ^ 2 + (y 2 - l * z 2) ^ 2))⁻¹) *
      srcW R c G (τ + 2 * Real.log l) z

/-- The phase kernel of the stream majorant between output `(τ, y)` and atom `(σ, z)`:
`1_{σ<τ} 1_{ϱ(z)<θϱ(y)} (λ/2) ϱ(y)⁻² (ϱ(y)² + (y₃ - λz₃)²)⁻¹`, `λ = e^{(σ-τ)/2}`. -/
def phKerS (θ τ : ℝ) (y : Space) (σ : ℝ) (z : Space) : ℝ≥0∞ :=
  if σ < τ ∧ ϱ z < θ * ϱ y then
    ENNReal.ofReal (Real.exp ((σ - τ) / 2) / 2) *
      ENNReal.ofReal ((ϱ y ^ 2 * (ϱ y ^ 2 + (y 2 - Real.exp ((σ - τ) / 2) * z 2) ^ 2))⁻¹)
  else 0

/-- The spatial `L²` constant of the stream kernel on `{ϱ ≥ R/√s₀}`: `(π²/5)(R/√s₀)⁻⁵`. -/
def gapS (R s0 : ℝ) : ℝ := Real.pi ^ 2 / 5 * (((R / Real.sqrt s0)⁻¹) ^ 5)

/-- The final constant `2π^{3/2}/√5`. -/
def wyC0S : ℝ := 2 * Real.pi * Real.sqrt Real.pi / Real.sqrt 5

/-- **Chart majorant** (source 2683, 4178-4186): `wardYStreamChartMaj² ≤ s⁻¹ Ψ_s(τ_p, y_p)²`
(`srcNorm(𝒩_T g) ≤ age·‖g(chartOf)‖`, `cartLiftFrobBound`). -/
def StreamChartMajSq : Prop :=
  ∀ (R c θ : ℝ) (g : Chart → Ten3) (p : Chart),
    wardYStreamChartMaj R c θ g p ^ (2 : ℝ) ≤
      ENNReal.ofReal (p.1⁻¹) *
        psiMajS R c θ (fun q => ‖g q‖ₑ) (NearInst.chartTau R p) (NearInst.chartY R p) ^ (2 : ℝ)

/-- Measurability of the chart stream majorant (part (a) of the core; the lintegral of a jointly
measurable function, `Measurable.lintegral_prod_right'`). -/
def StreamChartMeasurable : Prop :=
  ∀ (R c θ : ℝ) (g : Chart → Ten3), Measurable g → Measurable (wardYStreamChartMaj R c θ g)

/-- Joint measurability of `Ψ_s` in `(τ, y)`. -/
def PsiSMeasurable : Prop :=
  ∀ (R c θ : ℝ) (G : Chart → ℝ≥0∞), Measurable G →
    Measurable (fun x : ℝ × Space => psiMajS R c θ G x.1 x.2)

/-- Rotation invariance of `Ψ_s` about the vertical axis (it depends on `y` only through
`ϱ(y), y₃`). -/
def PsiSRotInv : Prop :=
  ∀ (R c θ : ℝ) (G : Chart → ℝ≥0∞) (α τ : ℝ) (y : Space),
    psiMajS R c θ G τ (Axi.rotZ α y) = psiMajS R c θ G τ y

/-- `2c/R`-periodicity of `Ψ_s` in the phase. -/
def PsiSPeriodic : Prop :=
  ∀ (R c θ : ℝ) (G : Chart → ℝ≥0∞), 0 < R → 0 < c → ∀ y : Space,
    Function.Periodic (fun τ => psiMajS R c θ G τ y) (2 * c / R)

/-- **Minkowski over the atoms** for `Ψ_s` (source 5590 "Minkowski"): the log substitution
`λ = e^{(σ-τ)/2}` plus Minkowski's integral inequality. -/
def PsiSAtomsMinkowski : Prop :=
  ∀ (R c θ : ℝ) (G : Chart → ℝ≥0∞), Measurable G → ∀ X : Set (ℝ × Space),
    (∫⁻ x in X, psiMajS R c θ G x.1 x.2 ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      ∫⁻ a : ℝ × Space, srcW R c G a.1 a.2 *
        (∫⁻ x in X, phKerS θ x.1 x.2 a.1 a.2 ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- **Atom bound** for the stream kernel (source 5588-5592): spatial `L²` of the kernel over
`{ϱ ≥ R/√s₀}` is `gapS`, translation invariance in `y₃`; phase factor `omega2`; atoms of age
`≤ s₁/θ²` (with `ϱ z > 0`) have zero kernel on the bin, and `ϱ z = 0` atoms have `srcW = 0`. -/
def StreamAtomBound : Prop :=
  ∀ (R c θ s1 s0 P : ℝ) (G : Chart → ℝ≥0∞), 0 < R → 0 < θ → θ < 1 → 0 < s1 → s1 ≤ s0 →
    0 < P → ∀ a : ℝ × Space,
      srcW R c G a.1 a.2 * (∫⁻ x in Ioc 0 P ×ˢ ybin R s1 s0,
          phKerS θ x.1 x.2 a.1 a.2 ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        Set.indicator {a : ℝ × Space | s1 / θ ^ 2 < age R a.2}
            (fun a => srcW R c G a.1 a.2) a *
          ENNReal.ofReal (Real.sqrt (gapS R s0) * Real.sqrt (omega2 P a.1))

/-- **The constants** (θ-free): `(2πcR)^{-1/2} √gapS (√P + 1/√P) PπR² ≤ C₀ (1 + c/R) R^{-3/2}
s₀^{5/4}`, `P = 2c/R`. -/
def StreamConstAlgebra : Prop :=
  ∀ (R c s0 : ℝ), 0 < R → 0 < c → 0 < s0 →
    ENNReal.ofReal ((2 * Real.pi * c * R)⁻¹) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (Real.sqrt (gapS R s0)) *
        ENNReal.ofReal (Real.sqrt (2 * c / R) + 1 / Real.sqrt (2 * c / R)) *
        ENNReal.ofReal (2 * c / R * (Real.pi * R ^ 2)) ≤
      ENNReal.ofReal (wyC0S * (1 + c / R) * R ^ (-(3 / 2 : ℝ)) * s0 ^ (5 / 4 : ℝ))

/-- **`WardYStreamMajBinCore` from the leaves** (the statement of
`Concrete.WardYStreamMajBinCore`, spelled out because that definition lives in the target file). -/
theorem wardYStreamMajBinCore_of (hMaj : StreamChartMajSq) (hMeasC : StreamChartMeasurable)
    (hMeas : PsiSMeasurable) (hRot : PsiSRotInv) (hPer : PsiSPeriodic)
    (hMink : PsiSAtomsMinkowski) (hAtom : StreamAtomBound) (hConst : StreamConstAlgebra) :
    ∀ δ : ℝ, 0 < δ → δ < Real.log (12 / 11) → ∃ C0 : ℝ, ∀ (R c S : ℝ), 0 < R → 0 < c →
      ∀ (j : ℕ) (g : Chart → Ten3), Measurable g →
        AEMeasurable (wardYStreamChartMaj R c (Real.exp (-(δ / 2))) g)
            ((ageμ c (-3 / 2)).restrict (binSet S (δ / 4) j)) ∧
        (∫⁻ p in binSet S (δ / 4) j,
            wardYStreamChartMaj R c (Real.exp (-(δ / 2))) g p ^ (2 : ℝ) ∂(ageμ c (-3 / 2))) ^
              (1 / 2 : ℝ) ≤
          ENNReal.ofReal (C0 * (1 + c / R) * R ^ (-(3 / 2 : ℝ)) *
              binUpper S (δ / 4) j ^ (5 / 4 : ℝ)) *
            ageMass c (Real.exp (δ - δ / 4) * binUpper S (δ / 4) j) g := by
  intro δ hδ _
  refine ⟨wyC0S, ?_⟩
  intro R c S hR hc j g hg
  refine ⟨(hMeasC R c _ g hg).aemeasurable, ?_⟩
  rcases le_or_gt S 0 with hS | hS
  · have h0 : ∫⁻ p in binSet S (δ / 4) j,
        wardYStreamChartMaj R c (Real.exp (-(δ / 2))) g p ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) = 0 :=
      WYCore.binNull c _ S _ j _ hS
    rw [h0, ENNReal.zero_rpow_of_pos (by norm_num)]
    exact zero_le
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
  have step12 : ∫⁻ p in binSet S (δ / 4) j,
      wardYStreamChartMaj R c (Real.exp (-(δ / 2))) g p ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) ≤
      ENNReal.ofReal ((2 * Real.pi * c * R)⁻¹) *
        ∫⁻ x in Ioc 0 (2 * c / R) ×ˢ ybin R (binUpper S (δ / 4) (j + 1)) (binUpper S (δ / 4) j),
          psiMajS R c (Real.exp (-(δ / 2))) (fun p => ‖g p‖ₑ) x.1 x.2 ^ (2 : ℝ) := by
    calc ∫⁻ p in binSet S (δ / 4) j,
          wardYStreamChartMaj R c (Real.exp (-(δ / 2))) g p ^ (2 : ℝ) ∂(ageμ c (-3 / 2))
        ≤ ∫⁻ p in {p : Chart | p.1 ∈ Ioc (binUpper S (δ / 4) (j + 1)) (binUpper S (δ / 4) j)},
            ENNReal.ofReal (p.1⁻¹) *
              psiMajS R c (Real.exp (-(δ / 2))) (fun q => ‖g q‖ₑ) (NearInst.chartTau R p)
                (NearInst.chartY R p) ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) :=
          lintegral_mono (fun p => hMaj R c _ g p)
      _ ≤ _ := by
          refine WYCore.chartToPhys R c hR hc
            (fun τ y => psiMajS R c (Real.exp (-(δ / 2))) (fun p => ‖g p‖ₑ) τ y ^ (2 : ℝ))
            ((hMeas R c _ _ hG).pow_const _) (fun α τ y => by beta_reduce; rw [hRot]) ?_
            (Ioc (binUpper S (δ / 4) (j + 1)) (binUpper S (δ / 4) j)) measurableSet_Ioc
            (fun x hx => lt_trans hs1 hx.1)
          intro y τ
          have h := hPer R c (Real.exp (-(δ / 2))) (fun p => ‖g p‖ₑ) hR hc y τ
          simp only at h ⊢
          rw [h]
  have step3 := ENNReal.rpow_le_rpow step12 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)] at step3
  have step4 := hMink R c (Real.exp (-(δ / 2))) _ hG
    (Ioc 0 (2 * c / R) ×ˢ ybin R (binUpper S (δ / 4) (j + 1)) (binUpper S (δ / 4) j))
  have step5 : ∫⁻ a : ℝ × Space, srcW R c (fun p => ‖g p‖ₑ) a.1 a.2 *
        (∫⁻ x in Ioc 0 (2 * c / R) ×ˢ
            ybin R (binUpper S (δ / 4) (j + 1)) (binUpper S (δ / 4) j),
          phKerS (Real.exp (-(δ / 2))) x.1 x.2 a.1 a.2 ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (gapS R (binUpper S (δ / 4) j))) *
        ∫⁻ a : ℝ × Space, Set.indicator
            {a : ℝ × Space | binUpper S (δ / 4) (j + 1) / Real.exp (-(δ / 2)) ^ 2 < age R a.2}
            (fun a => srcW R c (fun p => ‖g p‖ₑ) a.1 a.2) a *
            ENNReal.ofReal (Real.sqrt (omega2 (2 * c / R) a.1)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono (fun a => ?_)
    refine (hAtom R c _ _ _ _ _ hR hθ0 hθ1 hs1 hs10 hP a).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    ring
  have step6 := WYCore.sourceMass R c hR hc g hg
    (binUpper S (δ / 4) (j + 1) / Real.exp (-(δ / 2)) ^ 2)
  rw [WYCore.binUpper_succ_div_theta] at step5 step6
  have step7 := hConst R c (binUpper S (δ / 4) j) hR hc hs0
  calc (∫⁻ p in binSet S (δ / 4) j,
          wardYStreamChartMaj R c (Real.exp (-(δ / 2))) g p ^ (2 : ℝ) ∂(ageμ c (-3 / 2))) ^
            (1 / 2 : ℝ)
      ≤ ENNReal.ofReal ((2 * Real.pi * c * R)⁻¹) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal (Real.sqrt (gapS R (binUpper S (δ / 4) j))) *
            (ENNReal.ofReal (Real.sqrt (2 * c / R) + 1 / Real.sqrt (2 * c / R)) *
              ENNReal.ofReal (2 * c / R * (Real.pi * R ^ 2)) *
              ageMass c (Real.exp (δ - δ / 4) * binUpper S (δ / 4) j) g)) := by
        refine step3.trans ?_
        gcongr
        exact step4.trans (step5.trans (by gcongr))
    _ = (ENNReal.ofReal ((2 * Real.pi * c * R)⁻¹) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (Real.sqrt (gapS R (binUpper S (δ / 4) j))) *
          ENNReal.ofReal (Real.sqrt (2 * c / R) + 1 / Real.sqrt (2 * c / R)) *
          ENNReal.ofReal (2 * c / R * (Real.pi * R ^ 2))) *
          ageMass c (Real.exp (δ - δ / 4) * binUpper S (δ / 4) j) g := by ring
    _ ≤ _ := by gcongr

end UnforcedLeray.Short.PartIIIb.Concrete.WYStream

end
