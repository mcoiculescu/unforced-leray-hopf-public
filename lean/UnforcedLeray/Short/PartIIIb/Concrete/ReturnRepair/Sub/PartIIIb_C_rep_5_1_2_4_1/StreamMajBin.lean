import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_4.ChartSide
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_4.PsiSProps
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_4.AtomsMinkowski
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_4.AtomBoundConst

/-!
# `PartIII-b:C/rep/5/1/2/4/1/4`: the chart bin bound of the Ward `Y` stream majorant

Source `the November 2 reference manuscript` 5585-5593, 4178-4186.

`WardYStreamMajBinCore` is the analytic content (measurability of the chart stream majorant on the
bin, and its `L²` bin bound with explicit constants), the analogue of `WardYMajBinCore`
(`PartIII-b:C/rep/5/1/2/4/1/3`).  `wardYStreamMajBin_of_core` and `wardYStreamMajBinSeq_of` derive the
sequence statement from the core.  The core is proved here from the five stream leaves
(`WYStream.wardYStreamMajBinCore_of` applied to `streamChartSide`, `psiSProps`,
`psiSAtomsMinkowski`, `streamAtomBoundConst`), and the target `wardYStreamMajBinSeq` is closed by
`wardYStreamMajBinSeq_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Core of the stream bin bound** (source 5592, 5585-5593).  For `0 < δ < log(12/11)`, `h = δ/4`,
there is `C₀` such that for all `R, c, S > 0`, every output bin `j` and every measurable chart source
`g`: the chart stream majorant is AE-measurable on the bin and its `L²(bin, ageμ c (-3/2))` norm is
`≤ C₀ (1 + c/R) R^{-3/2} s_j^{5/4} · N₀(e^{δ-h}s_j)`.  (Exponents copied from `WardYMajBinCore`;
their re-derivation for the stream kernel `ϱ^{-2}(ϱ²+h²)^{-1}` is open.) -/
def WardYStreamMajBinCore : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < Real.log (12 / 11) → ∃ C0 : ℝ, ∀ (R c S : ℝ), 0 < R → 0 < c →
    ∀ (j : ℕ) (g : Chart → Ten3), Measurable g →
      AEMeasurable (wardYStreamChartMaj R c (Real.exp (-(δ / 2))) g)
          ((ageμ c (-3 / 2)).restrict (binSet S (δ / 4) j)) ∧
      (∫⁻ p in binSet S (δ / 4) j,
          wardYStreamChartMaj R c (Real.exp (-(δ / 2))) g p ^ (2 : ℝ) ∂(ageμ c (-3 / 2))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C0 * (1 + c / R) * R ^ (-(3 / 2 : ℝ)) * binUpper S (δ / 4) j ^ (5 / 4 : ℝ)) *
          ageMass c (Real.exp (δ - δ / 4) * binUpper S (δ / 4) j) g

/-- `WardYStreamMajBin` for `0 < ν ≤ 1`, `0 < ε ≤ 1`, `c = ν⁻²` from the core. -/
theorem wardYStreamMajBin_of_core (hcore : WardYStreamMajBinCore) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ < Real.log (12 / 11)) :
    ∃ (C : ℝ) (k : ℕ), ∀ ν ε S : ℝ, 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 → 0 ≤ S →
      WardYStreamMajBin ν ε (cOf ν) δ (δ / 4) S C k := by
  obtain ⟨C0, hC0⟩ := hcore δ hδ hδ'
  refine ⟨2 * |C0|, 2, fun ν ε S hν hν1 hε hε1 hS => ?_⟩
  intro _ _ hc _ _ hh j g hg _
  have hc0 : 0 < cOf ν := by unfold cOf; positivity
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  obtain ⟨hm, h⟩ := hC0 ε⁻¹ (cOf ν) S hR hc0 j g hg
  rw [hh]
  refine ⟨hm, h.trans ?_⟩
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have e1 : ε⁻¹ ^ (-(3 / 2 : ℝ)) = ε ^ (3 / 2 : ℝ) := by
    rw [Real.inv_rpow hε.le, ← Real.rpow_neg hε.le, neg_neg]
  rw [e1]
  have hcR : cOf ν / ε⁻¹ ≤ ν⁻¹ ^ 2 := by
    unfold cOf
    rw [div_inv_eq_mul, ← inv_pow]
    have : (ν ^ 2)⁻¹ * ε ≤ (ν ^ 2)⁻¹ * 1 := mul_le_mul_of_nonneg_left hε1 (by positivity)
    simpa using this
  have h1 : (1 : ℝ) ≤ ν⁻¹ ^ 2 := one_le_pow₀ (one_le_inv₀ hν |>.2 hν1)
  have hfac : 1 + cOf ν / ε⁻¹ ≤ 2 * ν⁻¹ ^ 2 := by linarith
  have hB : 0 ≤ binUpper S (δ / 4) j ^ (5 / 4 : ℝ) := by
    unfold binUpper; exact Real.rpow_nonneg (mul_nonneg hS (Real.exp_pos _).le) _
  have hE : 0 ≤ ε ^ (3 / 2 : ℝ) := Real.rpow_nonneg hε.le _
  have hP : 0 ≤ ε ^ (3 / 2 : ℝ) * binUpper S (δ / 4) j ^ (5 / 4 : ℝ) := mul_nonneg hE hB
  have hk : C0 * (1 + cOf ν / ε⁻¹) ≤ 2 * |C0| * ν⁻¹ ^ 2 := by
    calc C0 * (1 + cOf ν / ε⁻¹) ≤ |C0| * (1 + cOf ν / ε⁻¹) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C0| * (2 * ν⁻¹ ^ 2) := mul_le_mul_of_nonneg_left hfac (abs_nonneg _)
      _ = 2 * |C0| * ν⁻¹ ^ 2 := by ring
  calc C0 * (1 + cOf ν / ε⁻¹) * ε ^ (3 / 2 : ℝ) * binUpper S (δ / 4) j ^ (5 / 4 : ℝ)
      = (C0 * (1 + cOf ν / ε⁻¹)) * (ε ^ (3 / 2 : ℝ) * binUpper S (δ / 4) j ^ (5 / 4 : ℝ)) := by ring
    _ ≤ (2 * |C0| * ν⁻¹ ^ 2) * (ε ^ (3 / 2 : ℝ) * binUpper S (δ / 4) j ^ (5 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right hk hP
    _ = _ := by ring

/-- **Sequence statement from the core**: `WardYStreamMajBinSeq` follows from `WardYStreamMajBinCore`.
The target `wardYStreamMajBinSeq` is this applied to the proved core `wardYStreamMajBinCore_proved`. -/
theorem wardYStreamMajBinSeq_of (D : SeqData) {dm dp : ℝ} (hcore : WardYStreamMajBinCore) :
    D.WardYStreamMajBinSeq dm dp := by
  intro hst
  obtain ⟨C, k, hCk⟩ := wardYStreamMajBin_of_core hcore hst.δ_pos hst.δ_lt
  refine ⟨C, k, ?_⟩
  have hle : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 ∧ retEps D.Pl D.σ₀ n ≤ 1 :=
    retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  filter_upwards [hle] with n hn
  have hS : 0 ≤ (D.level n).Scut D.K := by
    unfold ReturnLevel.Scut
    exact Real.rpow_nonneg (D.level n).ε_pos.le _
  exact hCk (D.level n).ν (D.level n).ε _ (D.level n).ν_pos hn.1 (D.level n).ε_pos hn.2 hS

/-- **The stream core, proved** (source 5592, 5585-5593, 4178-4186): `WardYStreamMajBinCore` from
the five stream leaves: chart side, `Ψ_s` measurability/rotation/periodicity, Minkowski over the
atoms, and the atom bound with the θ-free constants. -/
theorem wardYStreamMajBinCore_proved : WardYStreamMajBinCore :=
  WYStream.wardYStreamMajBinCore_of WYStream.streamChartSide.1 WYStream.streamChartSide.2
    WYStream.psiSProps.1 WYStream.psiSProps.2.1 WYStream.psiSProps.2.2 WYStream.psiSAtomsMinkowski
    WYStream.streamAtomBoundConst.1 WYStream.streamAtomBoundConst.2

/-- **`wardYStreamMajBinSeq`** (source 5585-5593, 4178-4186): the stream bin bound of the Ward `Y`
majorant for every sequence datum. -/
theorem wardYStreamMajBinSeq (D : SeqData) {dm dp : ℝ} : D.WardYStreamMajBinSeq dm dp :=
  wardYStreamMajBinSeq_of D wardYStreamMajBinCore_proved

end UnforcedLeray.Short.PartIIIb.Concrete

end
