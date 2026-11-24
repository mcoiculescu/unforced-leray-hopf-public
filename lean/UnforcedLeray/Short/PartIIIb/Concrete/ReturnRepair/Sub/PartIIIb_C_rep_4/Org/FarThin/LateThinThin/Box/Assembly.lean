import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinThin.Kernel
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinThin.Box.Pointwise
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinThin.Box.AgeIntegral
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.FarKernel.Recv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.FarOutChartQ
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3.KerDeriv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps

/-!
# `PartIII-b:C/rep/4/1/org/2/1` (e): the box leaf of the thin-source/thin-receiver far column

Source `the November 2 reference manuscript` 5342-5355 (separated pointwise
velocity `≤ P_νε²s²N₀(e^δ s)`; after the normalized velocity lift and thin multiplication the
square root of the output stress age density is `≤ P_νε²(s^{1/2}+s^{3/4})V_m(s)‖T‖_{Z₁}`; its
square is integrable at zero and the integral up to `S` is polynomial in `S`), 5573-5594 (mass
estimate), 2713-2721 (`V_m(s) = ‖Wv(s)‖_{L²_ηL^∞_q}`).

`farThinThinBox_of`: `FarThinThinBox` (`k₀ = 2`) from the coefficient bound `EtaQSupSeq` of
`stress-short:coefficients` (the shared leaf of `PartIII-b:C/rep/4/4/1/org/7/1/8`).  The route is
that of `farThinRecvUng_of` (`LateRepThinOrg/FarKernel/Recv.lean`): the thin multiplier
(`frk_thinMultUng_level`), the `L^∞_q × L²_q` Tonelli step `farOutChartQ`, and, in place of the
`p = 22/19` pointwise kernel, `farPt_le` (`≤ P_ν ε² s² N₀(e^δ s)`) with the mass estimate
`thinMassBoundSlice` (`N₀(a) ≤ C(a^{-3/4}+a^{-1/2})‖T‖_{Z₁}`) and `age_integral`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `(((1-θ)·(R/√s))⁴)⁻¹·πR²·|C_m|·B = K₀·(R²)⁻¹·s²·B` with `K₀ = 18|C|π|C_m|((1-θ)⁴)⁻¹`. -/
theorem ftt_const_eq {R s θ Cker Cm B : ℝ} (hR : 0 < R) (hs : 0 < s) (hθ : θ < 1) :
    18 * |Cker| * ((((1 - θ) * (R / Real.sqrt s)) ^ 4)⁻¹) * (Real.pi * R ^ 2) * (|Cm| * B) =
      (18 * |Cker| * Real.pi * |Cm| * (((1 - θ) ^ 4)⁻¹) * (R ^ 2)⁻¹) * s ^ 2 * B := by
  have h4 : Real.sqrt s ^ 4 = s ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hs.le]
  have h1 : (1 - θ) ≠ 0 := (sub_pos.2 hθ).ne'
  have hsq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  rw [mul_pow, div_pow, h4]
  field_simp

theorem ftt_sqrt_eq {E K T : ℝ} (hE : 0 ≤ E) (hK : 0 ≤ K) (hT : 0 ≤ T) :
    Real.sqrt (8 * (4 * E ^ 2 * K ^ 2 * T ^ 2)) = Real.sqrt 32 * E * K * T := by
  have h0 : 0 ≤ Real.sqrt 32 * E * K * T := by positivity
  rw [← Real.sqrt_sq h0]
  congr 1
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  ring

/-- **`FarThinThinBox` from the coefficient bound `EtaQSupSeq`** (source 5342-5355, 5573-5594,
2713-2721), `k₀ = 2`. -/
theorem farThinThinBox_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) (hE : EtaQSupSeq dm dp) :
    FarThinThinBox Pl σ₀ mZ dm dp := by
  refine ⟨2, fun D _ _ _ hst => ?_⟩
  obtain ⟨CE, kE, hCE0, hEev⟩ := hE D hst
  obtain ⟨Cker, hCker0, hCker⟩ := farKerDeriv
  obtain ⟨Cm, hCm⟩ := thinMassBoundSlice D.K.mZ hst.mZ_gt
  have hκ0 : 0 < 1 - Real.exp (-(D.K.δ / 2)) := by
    rw [sub_pos]; exact Real.exp_lt_one_iff.mpr (by linarith [hst.δ_pos])
  have hθ1 : Real.exp (-(D.K.δ / 2)) < 1 := by linarith
  set K0 : ℝ := 18 * |Cker| * Real.pi * |Cm| * (((1 - Real.exp (-(D.K.δ / 2))) ^ 4)⁻¹) with hK0
  have hK00 : 0 ≤ K0 := by positivity
  refine ⟨Real.sqrt 32 * CE * K0, kE, by positivity, ?_⟩
  filter_upwards [hEev, hst.near, hst.pins,
    retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne] with
    n hEn hnear hpins hle z hz hμ v g hg hv
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε1 : (D.level n).ε ≤ 1 := hle.2
  have hc : 0 < cOf (D.level n).ν := cOf_pos hν
  have hR : 0 < (D.level n).ε⁻¹ := inv_pos.2 hε
  have hS : 0 < (D.level n).Scut D.K := Real.rpow_pos_of_pos hε _
  have hS1 : 1 ≤ (D.level n).Scut D.K :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith [hst.b_pos])
  have hνi : 0 ≤ (D.level n).ν⁻¹ := inv_nonneg.2 hν.le
  obtain ⟨hz1, hz2⟩ := frk_thinMultUng_level D.Pl D.K (D.level n) (D.mu n z) (hnear z hz)
    (hpins z hz).split v
  set E : ℝ := CE * (D.level n).ν⁻¹ ^ kE with hEdef
  have hE0 : 0 ≤ E := by positivity
  set K1 : ℝ := K0 * ((D.level n).ε⁻¹ ^ 2)⁻¹ with hK1
  have hK10 : 0 ≤ K1 := by positivity
  set Z : ℝ≥0∞ := z1Ung (cOf (D.level n).ν) D.K.mZ g with hZ
  set Φ : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (K1 * s ^ 2 *
    ((Real.exp D.K.δ * s) ^ (-3 / 4 : ℝ) + (Real.exp D.K.δ * s) ^ (-1 / 2 : ℝ))) * Z with hΦ
  -- the separated pointwise velocity
  have hpt : ∀ p : Chart, 0 < p.1 → p.1 < (D.level n).Scut D.K →
      farPt (D.level n).ε⁻¹ (cOf (D.level n).ν) (D.level n).ν (D.mu n z) D.K.δ g p ≤ Φ p.1 := by
    intro p hp _
    have h1 := FTT.farPt_le hCker hν hR hc hμ hst.δ_pos g hg.measurable p hp
    have h2 := hCm (cOf (D.level n).ν) hc (Real.exp D.K.δ * p.1)
      (mul_pos (Real.exp_pos _) hp) g hg.measurable
    have hsq : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp
    set B : ℝ := (Real.exp D.K.δ * p.1) ^ (-3 / 4 : ℝ) + (Real.exp D.K.δ * p.1) ^ (-1 / 2 : ℝ)
      with hB
    have hB0 : 0 ≤ B := by
      have : 0 < Real.exp D.K.δ * p.1 := mul_pos (Real.exp_pos _) hp
      positivity
    have h3 : ENNReal.ofReal (Cm * B) ≤ ENNReal.ofReal (|Cm| * B) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self Cm) hB0)
    refine h1.trans ?_
    calc _ ≤ ENNReal.ofReal (18 * |Cker| * ((((1 - Real.exp (-(D.K.δ / 2))) *
            ((D.level n).ε⁻¹ / Real.sqrt p.1)) ^ 4)⁻¹) * (Real.pi * (D.level n).ε⁻¹ ^ 2)) *
          (ENNReal.ofReal (|Cm| * B) * Z) :=
          mul_le_mul' le_rfl (h2.trans (mul_le_mul' h3 le_rfl))
      _ = Φ p.1 := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ftt_const_eq hR hp hθ1]
  -- the thin multiplier and the Tonelli step
  have hHm : Measurable fun p : Chart =>
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight D.K.mZ p ^ 2) *
        ‖((multOp D.Pl D.K (D.level n) v).fst : Chart → Ten3) p‖ₑ ^ (2 : ℝ) :=
    (((frk_measurable_transWeight D.K.mZ).pow_const 2).ennreal_ofReal).mul
      ((Lp.stronglyMeasurable _).measurable.enorm.pow_const _)
  have hQ' := farOutChartQ (D.level n).ε⁻¹ (cOf (D.level n).ν) (D.level n).ν (D.mu n z) D.K.δ
    ((D.level n).Scut D.K) D.K.mZ hR hc hS
    (UnforcedLeray.Short.IIIa.chartCoeff (D.level n).ε⁻¹ (D.level n).V) (v : Chart → Merid) g
    _ 4 ENNReal.ofNat_ne_top Φ hHm (Lp.stronglyMeasurable v).measurable hz2 hv hpt
  -- the coefficient bound and the age integral
  have hmono : ∫⁻ s in Ioo 0 ((D.level n).Scut D.K), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        UnforcedLeray.Short.IIIa.etaL2QSup (cOf (D.level n).ν) D.K.mZ
          (UnforcedLeray.Short.IIIa.chartCoeff (D.level n).ε⁻¹ (D.level n).V) s ^ (2 : ℝ) *
        Φ s ^ (2 : ℝ) ≤
      ∫⁻ s in Ioo 0 ((D.level n).Scut D.K), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        ENNReal.ofReal E ^ (2 : ℝ) * Φ s ^ (2 : ℝ) := by
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2
      (Eventually.of_forall fun s hs => ?_))
    gcongr
    exact hEn s hs.1
  have hI := FTT.age_integral hS1 hst.δ_pos.le hE0 hK10 Z
  have htot : ∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight D.K.mZ p ^ 2) *
        ‖((multOp D.Pl D.K (D.level n) v).fst : Chart → Ten3) p‖ₑ ^ (2 : ℝ)
          ∂(ageμ (cOf (D.level n).ν) (-1 / 2)) ≤
      2 * 4 * (ENNReal.ofReal (4 * E ^ 2 * K1 ^ 2 * ((D.level n).Scut D.K) ^ (5 / 2 : ℝ)) *
        Z ^ (2 : ℝ)) :=
    hQ'.trans (mul_le_mul_of_nonneg_left (hmono.trans hI) zero_le)
  have hX0 : 0 ≤ 4 * E ^ 2 * K1 ^ 2 * ((D.level n).Scut D.K) ^ (5 / 2 : ℝ) := by positivity
  have hfin := frk_sqrt_bound hX0 htot
  rw [← hz1] at hfin
  refine hfin.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
  -- the constants
  set S := (D.level n).Scut D.K with hSdef
  have hSe : S = (D.level n).ε ^ (-D.K.b) := rfl
  have hS54 : S ^ (5 / 2 : ℝ) = (S ^ (5 / 4 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS.le]; norm_num
  have hS54' : S ^ (5 / 4 : ℝ) ≤ (D.level n).ε ^ (-(((2 : ℕ) : ℝ) * D.K.b)) := by
    rw [hSe, ← Real.rpow_mul hε.le]
    refine Real.rpow_le_rpow_of_exponent_ge hε hε1 ?_
    push_cast
    nlinarith [hst.b_pos]
  have hS540 : 0 ≤ S ^ (5 / 4 : ℝ) := Real.rpow_nonneg hS.le _
  have hsq : Real.sqrt (8 * (4 * E ^ 2 * K1 ^ 2 * S ^ (5 / 2 : ℝ))) =
      Real.sqrt 32 * E * K1 * S ^ (5 / 4 : ℝ) := by
    rw [hS54]
    exact ftt_sqrt_eq hE0 hK10 hS540
  rw [hsq]
  have hK1e : K1 = K0 * (D.level n).ε ^ (2 : ℝ) := by
    rw [hK1, inv_pow, inv_inv, Real.rpow_two]
  calc Real.sqrt 32 * E * K1 * S ^ (5 / 4 : ℝ)
      = Real.sqrt 32 * CE * K0 * (D.level n).ν⁻¹ ^ kE * (D.level n).ε ^ (2 : ℝ) *
          S ^ (5 / 4 : ℝ) := by rw [hEdef, hK1e]; ring
    _ ≤ Real.sqrt 32 * CE * K0 * (D.level n).ν⁻¹ ^ kE * (D.level n).ε ^ (2 : ℝ) *
          (D.level n).ε ^ (-(((2 : ℕ) : ℝ) * D.K.b)) := by
        gcongr
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
