import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinRepOrg.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.FarVelPointwise
import UnforcedLeray.Short.PartIIIa.Tasks16.DomYoung
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.GAxFacts
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.CartLiftNormOffAxis
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AxisNull
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.FarKernelL2.farOutMeasurable
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WeakDmuAdd
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates

/-!
# `PartIII-b:C/rep/4/1/org/3/1`: the order-four kernel `L² → L^{22/3}` on the far mask

Source `the November 2 reference manuscript` 5336-5338 (the thin-to-repair entry
uses the order-four kernel from `L²` to `L^{22/3}`, off-diagonal norm `D^{-23/11}`), 3624-3646
(`sep:young`), 5303-5306 (far mask). Proves `farVelYoungBoxL2 : FarVelYoungBoxL2` from
`farVelPointwise` and `sepDomYoung` at `j = 0`, `p = 2`, `q = 22/3`, `b = 11/7`, `δ = 1`, `a = 2μ+2`.
This is the `p = 2` twin of `FarVelYoungBox` (`p = 22/19`, `b = 11/3`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Almost everywhere on a phase cell, first in the phase, then in the receiver. -/
theorem fvl2_ae_cell {P : ℝ} {Q : ℝ × UnforcedLeray.Space → Prop}
    (h : ∀ᵐ p ∂(volume.restrict (UnforcedLeray.Cons.C03.Concrete.phaseCell P)), Q p) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioc (0 : ℝ) P)), ∀ᵐ y : UnforcedLeray.Space, Q (τ, y) := by
  have h' : ∀ᵐ p ∂((volume.restrict (Set.Ioc (0 : ℝ) P)).prod
      (volume.restrict (Set.univ : Set UnforcedLeray.Space))), Q p := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact h
  have h2 := Measure.ae_ae_of_ae_prod h'
  simpa only [Measure.restrict_univ] using h2

/-- The axisymmetric source profile has the mixed norm of the physical tensor `strPhys` (`p = 2`). -/
theorem fvl2_ltauLq_gAx (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c) (f : Chart → Ten3) :
    UnforcedLeray.Short.IIIa.ltauLq (2 * ε * c) 2
        (NearInst.Masked.gAx ε⁻¹ c f) =
      phaseL2Lr (2 * ε * c) 2 (strPhys ε⁻¹ c f) := by
  have hPos : (0 : ℝ) < 2 * ε * c := by positivity
  have hN : volume {z : UnforcedLeray.Space | NearInst.hRad z = 0} = 0 :=
    NearInst.Masked.axisNull_holds
  have hax : ∀ᵐ z : UnforcedLeray.Space ∂volume, NearInst.hRad z ≠ 0 := by
    rw [ae_iff]
    simpa using hN
  have hCL : NearInst.Masked.CartLiftNormOffAxis := NearInst.Masked.cartLiftNormOffAxis_holds
  have hpt : ∀ τ : ℝ, ∀ᵐ y : UnforcedLeray.Space ∂volume,
      NearInst.Masked.gAx ε⁻¹ c f τ y ^ (2 : ℝ) =
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (strPhys ε⁻¹ c f (τ, y))) ^
          (2 : ℝ) := by
    intro τ
    filter_upwards [hax] with y hy
    have h1 := hCL ε⁻¹ c f τ y hy
    rw [← h1]
    rfl
  have hcongr : (∫⁻ τ in Set.Ioc (0 : ℝ) (2 * ε * c),
      (∫⁻ y : UnforcedLeray.Space, NearInst.Masked.gAx ε⁻¹ c f τ y ^ (2 : ℝ)) ^
        (2 / (2 : ℝ))) =
      ∫⁻ τ in Set.Ioc (0 : ℝ) (2 * ε * c),
        (∫⁻ y : UnforcedLeray.Space,
          ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (strPhys ε⁻¹ c f (τ, y))) ^
            (2 : ℝ)) ^ (2 / (2 : ℝ)) :=
    lintegral_congr fun τ => by
      rw [lintegral_congr_ae (hpt τ)]
  unfold UnforcedLeray.Short.IIIa.ltauLq phaseL2Lr
  rw [ENNReal.ofReal_inv_of_pos hPos, hcongr]

/-- The dilated kernel is the separated dilation integral with `a = 2μ+2`, `j = 0`. -/
theorem fvl2_dilMaj_eq (μ d : ℝ) (g : ℝ → UnforcedLeray.Space → ℝ≥0∞) :
    NearInst.Masked.dilMaj μ d g = UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0 d g := by
  funext τ y
  unfold NearInst.Masked.dilMaj UnforcedLeray.Short.IIIa.sepDom
  refine lintegral_congr fun l => ?_
  congr 1
  refine lintegral_congr fun z => ?_
  simp [NearInst.Masked.farKern, UnforcedLeray.Short.IIIa.sepKd]

/-- The power of the truncation radius, in the form of the target constant (exponent `23/11`). -/
theorem fvl2_const (ε S δ : ℝ) (hε : 0 < ε) (hS : 0 < S) (hA : 0 < 1 - Real.exp (-δ / 2)) :
    ((1 - Real.exp (-δ / 2)) * ε⁻¹ / Real.sqrt S) ^ (-(23 / 11 : ℝ)) =
      (1 - Real.exp (-δ / 2)) ^ (-(23 / 11 : ℝ)) * ε ^ (23 / 11 : ℝ) * S ^ (23 / 22 : ℝ) := by
  have e1 : (1 / (2 : ℝ)) * -(23 / 11 : ℝ) = -(23 / 22 : ℝ) := by norm_num
  rw [Real.div_rpow (mul_nonneg hA.le (inv_nonneg.2 hε.le)) (Real.sqrt_nonneg _),
    Real.mul_rpow hA.le (inv_nonneg.2 hε.le), Real.inv_rpow hε.le, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hS.le, e1, Real.rpow_neg hε.le, Real.rpow_neg hS.le, inv_inv,
    div_inv_eq_mul]

/-- **The order-four separated kernel `L² → L^{22/3}` on the far mask** (source 5336-5338,
3624-3646, 5303-5306): from the pointwise majorant `farVelPointwise` and `sepDomYoung` at
`j = 0`, `p = 2`, `q = 22/3`, `b = 11/7` (`1 + 3/22 = 1/2 + 7/11`, `-4 + 3/b = -23/11`), with
`δ = 1 ≤ 2μ + 3/2` for `μ > -1/4`. -/
theorem farVelYoungBoxL2 : FarVelYoungBoxL2 := by
  have hV0 : FarVelPointwise := farVelPointwise
  unfold FarVelPointwise at hV0
  obtain ⟨C1, hC1, hV⟩ := hV0
  have hY0 : UnforcedLeray.Short.IIIa.SepDomYoung := sepDomYoung
  unfold UnforcedLeray.Short.IIIa.SepDomYoung at hY0
  have hY := hY0 0 2 (22 / 3) (11 / 7) 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨C2, hC2, hY2⟩ := hY
  refine ⟨C1 * C2, mul_nonneg hC1 hC2, ?_⟩
  intro ε c ν δ S μ hε hc hν hδ hS hμ f hf b hb hbae
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hPos : (0 : ℝ) < 2 * ε * c := by positivity
  have hA : (0 : ℝ) < 1 - Real.exp (-δ / 2) := by
    have h := Real.exp_lt_exp.2 (show -δ / 2 < 0 by linarith)
    rw [Real.exp_zero] at h
    linarith
  have hD : (0 : ℝ) < (1 - Real.exp (-δ / 2)) * ε⁻¹ / Real.sqrt S :=
    div_pos (mul_pos hA hR) (Real.sqrt_pos.2 hS)
  have hGA : NearInst.Masked.GAxFacts := NearInst.Masked.gAxFacts_holds
  obtain ⟨-, hPer, hMeas⟩ := hGA ε⁻¹ c f hR hc hf.measurable
  have e2 : 2 * c / ε⁻¹ = 2 * ε * c := by
    rw [div_inv_eq_mul]
    ring
  have hPer' : ∀ τ z, NearInst.Masked.gAx ε⁻¹ c f (τ + 2 * ε * c) z =
      NearInst.Masked.gAx ε⁻¹ c f τ z := by
    intro τ z
    rw [← e2]
    exact hPer τ z
  have hb' : Measurable (NearInst.Masked.farOut ε⁻¹ c ν μ δ S f) :=
    NearInst.Masked.measurable_farOut_fn ε⁻¹ c ν μ δ S f hf.measurable
  have hvel := wda_velPhys_congr hc hε hb hb' hbae
  have hcell := fvl2_ae_cell (P := 2 * ε * c)
    (Q := fun p => velPhys ε⁻¹ c b p =
      velPhys ε⁻¹ c (NearInst.Masked.farOut ε⁻¹ c ν μ δ S f) p) hvel
  have hpt : ∀ᵐ τ ∂(volume.restrict (Set.Ioc (0 : ℝ) (2 * ε * c))), ∀ᵐ y : UnforcedLeray.Space,
      ‖velPhys ε⁻¹ c b (τ, y)‖ₑ ≤ ENNReal.ofReal C1 *
        NearInst.Masked.dilMaj μ ((1 - Real.exp (-δ / 2)) * ε⁻¹ / Real.sqrt S)
          (NearInst.Masked.gAx ε⁻¹ c f) τ y := by
    filter_upwards [hcell] with τ hτ
    filter_upwards [hτ, hV ε c ν δ S μ hε hc hν hδ hS f hf τ] with y hy1 hy2
    have hy1' : velPhys ε⁻¹ c b (τ, y) =
        velPhys ε⁻¹ c (NearInst.Masked.farOut ε⁻¹ c ν μ δ S f) (τ, y) := hy1
    rw [hy1']
    exact hy2
  have h1 : UnforcedLeray.Short.IIIa.ltauLq (2 * ε * c) (22 / 3)
        (fun τ y => ‖velPhys ε⁻¹ c b (τ, y)‖ₑ) ≤
      UnforcedLeray.Short.IIIa.ltauLq (2 * ε * c) (22 / 3)
        (fun τ y => ENNReal.ofReal C1 *
          NearInst.Masked.dilMaj μ ((1 - Real.exp (-δ / 2)) * ε⁻¹ / Real.sqrt S)
            (NearInst.Masked.gAx ε⁻¹ c f) τ y) :=
    UnforcedLeray.Short.IIIa.sepAE_ltauLq_mono (2 * ε * c) (22 / 3) (by norm_num) hpt
  rw [UnforcedLeray.Short.IIIa.ltauLq_const_mul (2 * ε * c) (22 / 3) (by norm_num)
    (ENNReal.ofReal C1) ENNReal.ofReal_ne_top
    (NearInst.Masked.dilMaj μ ((1 - Real.exp (-δ / 2)) * ε⁻¹ / Real.sqrt S)
      (NearInst.Masked.gAx ε⁻¹ c f)), fvl2_dilMaj_eq] at h1
  have ha0 : (0 : ℝ) ≤ 2 * μ + 2 := by linarith
  have hδ' : (1 : ℝ) ≤ (2 * μ + 2) - 2 + 3 / (2 : ℝ) := by
    norm_num
    linarith
  have hYa := hY2 (2 * μ + 2) ha0 hδ' _ _ hD hPos (NearInst.Masked.gAx ε⁻¹ c f) hMeas hPer'
  have he : (-4 - ((0 : ℕ) : ℝ) + 3 / (11 / 7 : ℝ)) = -(23 / 11 : ℝ) := by norm_num
  rw [he, fvl2_ltauLq_gAx ε c hε hc f] at hYa
  have hconst := fvl2_const ε S δ hε hS hA
  have hfin : ENNReal.ofReal (C1 * C2 * (1 - Real.exp (-δ / 2)) ^ (-(23 / 11 : ℝ)) *
        ε ^ (23 / 11 : ℝ) * S ^ (23 / 22 : ℝ)) =
      ENNReal.ofReal C1 * ENNReal.ofReal (C2 *
        ((1 - Real.exp (-δ / 2)) * ε⁻¹ / Real.sqrt S) ^ (-(23 / 11 : ℝ))) := by
    rw [← ENNReal.ofReal_mul hC1]
    congr 1
    rw [hconst]
    ring
  rw [hfin, mul_assoc (ENNReal.ofReal C1)]
  refine h1.trans ?_
  gcongr

end UnforcedLeray.Short.PartIIIb.Concrete
