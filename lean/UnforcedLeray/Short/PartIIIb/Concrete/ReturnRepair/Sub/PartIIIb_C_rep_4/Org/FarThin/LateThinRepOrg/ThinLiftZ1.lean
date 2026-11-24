import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinRepOrg.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.Transfer
import UnforcedLeray.Short.PartIIIb.Concrete.Spaces
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartL2Source
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AgeShift
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.PolarReduction
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChange
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChangeSE
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChangeTQ
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.GAxFacts
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.NsSymNormLe
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.CartLiftNormOffAxis
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AxisNull

/-!
# `PartIII-b:C/rep/4/1/org/3/2`: the thin source lift `‖𝒩_TT₁‖_{L²_τL²} ≤ √π ε⁻¹ ‖T₁‖_{Z₁}`

Source `the November 2 reference manuscript` 2683-2689 (`𝒩_TT = sT`,
`‖𝒩_TT‖²_{Y₂} = πR²‖T‖²_{H_T}`), 2697 (`Z₁ = L²(W²s^{-1/2}dς)`, `W ≥ 1`).

Proof: with `R = ε⁻¹`, `P = 2εc = 2c/R`, the phase norm is `(P⁻¹ ∫_0^P ∫|strPhys|²)^{1/2}`;
off the null axis `|strPhys(τ,y)| = gAx(τ,y)` (`cartLiftNormOffAxis_holds`), `Ioc 0 P` and
`Ico 0 P` agree up to a null set, `ChartL2Source` gives `∫_0^P∫ gAx² = 2πRc ∫|nsSym f|² dageμ`,
and `P⁻¹·2πRc = πR²`. Finally `|nsSym f| ≤ |f| ≤ W|f|` (`NsSymNormLe`, `W ≥ 1`) and
`dageμ W²|f|² = dz1Measure |f|²`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Square root bound: `(a·J)^{1/2} ≤ √a · I^{1/2}` for `J ≤ I`, `a ≥ 0`. -/
theorem tl_sqrt_bound (a : ℝ) (ha : 0 ≤ a) (J I : ℝ≥0∞) (h : J ≤ I) :
    (ENNReal.ofReal a * J) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt a) * I ^ (1 / 2 : ℝ) := by
  calc (ENNReal.ofReal a * J) ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal a * I) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (by gcongr) (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt a) * I ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg ha (by norm_num), Real.sqrt_eq_rpow]

/-- **The thin source lift** (source 2683-2689, 2697): for `ε, c > 0`, `m_Z ≥ 0` and measurable
`f`, `‖𝒩_Tf‖_{L²_τL²} ≤ √π ε⁻¹ ‖f‖_{Z₁}` over the period `P = 2εc`. -/
theorem thinLiftZ1 : ThinLiftZ1 := by
  intro ε c mZ hε hc hmZ f hf
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hPos : (0 : ℝ) < 2 * ε * c := by positivity
  have e2 : 2 * c / ε⁻¹ = 2 * ε * c := by
    rw [div_inv_eq_mul]
    ring
  -- Off the null axis the physical norm is the source profile `gAx`.
  have hN : volume {z : UnforcedLeray.Space | NearInst.hRad z = 0} = 0 :=
    NearInst.Masked.axisNull_holds
  have hax : ∀ᵐ z : UnforcedLeray.Space ∂volume, NearInst.hRad z ≠ 0 := by
    rw [ae_iff]
    simpa using hN
  have hCL : NearInst.Masked.CartLiftNormOffAxis := NearInst.Masked.cartLiftNormOffAxis_holds
  have hpt : ∀ τ : ℝ, ∀ᵐ y : UnforcedLeray.Space ∂volume,
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (strPhys ε⁻¹ c f (τ, y))) ^ (2 : ℝ) =
        NearInst.Masked.gAx ε⁻¹ c f τ y ^ (2 : ℝ) := by
    intro τ
    filter_upwards [hax] with y hy
    have h1 := NearInst.Masked.cartLiftNormOffAxis_holds ε⁻¹ c f τ y hy
    rw [← h1]
    rfl
  have hinner : ∀ τ : ℝ,
      (∫⁻ y : UnforcedLeray.Space,
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (strPhys ε⁻¹ c f (τ, y))) ^ (2 : ℝ)) =
      ∫⁻ y : UnforcedLeray.Space, NearInst.Masked.gAx ε⁻¹ c f τ y ^ (2 : ℝ) :=
    fun τ => lintegral_congr_ae (hpt τ)
  -- The chart L² identity (source 2683), with `Ico 0 P`.
  have hCS : NearInst.Masked.ChartL2Source :=
    NearInst.Masked.chartL2Source_of NearInst.Masked.ageShift_holds
      NearInst.Masked.polarReduction_holds
      (NearInst.Masked.chartChange_of NearInst.Masked.chartChangeSE_holds
        NearInst.Masked.chartChangeTQ_holds)
      NearInst.Masked.gAxFacts_holds
  have hL := hCS ε⁻¹ c hR hc f hf
  rw [e2] at hL
  have hsq : ∀ τ : ℝ, (∫⁻ z : UnforcedLeray.Space, NearInst.Masked.gAx ε⁻¹ c f τ z ^ (2 : ℝ)) ^
      (2 / (2 : ℝ)) = ∫⁻ z : UnforcedLeray.Space, NearInst.Masked.gAx ε⁻¹ c f τ z ^ (2 : ℝ) :=
    fun τ => by
      rw [show (2 : ℝ) / 2 = 1 by norm_num, ENNReal.rpow_one]
  have hIoc : ∀ g : ℝ → ℝ≥0∞, (∫⁻ t in Set.Ioc (0 : ℝ) (2 * ε * c), g t) =
      ∫⁻ t in Set.Ico (0 : ℝ) (2 * ε * c), g t :=
    fun g => setLIntegral_congr Ico_ae_eq_Ioc.symm
  have hK : (2 * ε * c)⁻¹ * (2 * Real.pi * ε⁻¹ * c) = Real.pi * (ε⁻¹) ^ 2 := by
    have h1 := hε.ne'
    have h2 := hc.ne'
    field_simp
  -- The phase norm as `(π R² · J)^{1/2}`.
  have hmain : phaseL2Lr (2 * ε * c) 2 (strPhys ε⁻¹ c f) =
      (ENNReal.ofReal (Real.pi * (ε⁻¹) ^ 2) *
        ∫⁻ x, ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
            (UnforcedLeray.Short.PartIIIb.NearInst.nsSym (f x))) ^ (2 : ℝ)
          ∂(ageμ c (-1 / 2))) ^ (1 / 2 : ℝ) := by
    unfold phaseL2Lr
    simp only [hinner, hsq]
    rw [hIoc, hL, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hPos.le), hK]
  -- The weight `W ≥ 1` and the density identity for `z1Measure`.
  have hWm : Measurable (fun p : Chart =>
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2)) := by
    unfold UnforcedLeray.Short.IIIa.transWeight
    fun_prop
  have hgm : Measurable (fun p : Chart => ‖f p‖ₑ ^ (2 : ℝ)) :=
    (hf.enorm).pow_const (2 : ℝ)
  have hI : (∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ)) =
      ∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) * ‖f p‖ₑ ^ (2 : ℝ)
        ∂(ageμ c (-1 / 2)) :=
    lintegral_withDensity_eq_lintegral_mul _ hWm hgm
  have hJI : (∫⁻ x, ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
            (UnforcedLeray.Short.PartIIIb.NearInst.nsSym (f x))) ^ (2 : ℝ)
          ∂(ageμ c (-1 / 2))) ≤ ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ) := by
    rw [hI]
    refine lintegral_mono fun x => ?_
    have hn : ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
        (UnforcedLeray.Short.PartIIIb.NearInst.nsSym (f x))) ≤ ‖f x‖ₑ := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (NearInst.Masked.nsSymNormLe_holds (f x))
    have hb : (1 : ℝ) ≤ UnforcedLeray.Short.IIIa.transWeight mZ x := by
      unfold UnforcedLeray.Short.IIIa.transWeight
      exact Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg _)) (by linarith)
    have hW1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ x ^ 2) := by
      rw [ENNReal.one_le_ofReal]
      nlinarith
    calc ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
            (UnforcedLeray.Short.PartIIIb.NearInst.nsSym (f x))) ^ (2 : ℝ)
        ≤ ‖f x‖ₑ ^ (2 : ℝ) := ENNReal.rpow_le_rpow hn (by norm_num)
      _ = 1 * ‖f x‖ₑ ^ (2 : ℝ) := (one_mul _).symm
      _ ≤ ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ x ^ 2) * ‖f x‖ₑ ^ (2 : ℝ) := by
        gcongr
  have hsq' : Real.sqrt (Real.pi * (ε⁻¹) ^ 2) = Real.sqrt Real.pi * ε⁻¹ := by
    rw [Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hR.le]
  rw [hmain]
  refine (tl_sqrt_bound (Real.pi * (ε⁻¹) ^ 2) (by positivity) _ _ hJI).trans (le_of_eq ?_)
  unfold z1Ung
  rw [hsq']

end UnforcedLeray.Short.PartIIIb.Concrete
