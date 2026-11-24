import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Defs
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Pointwise.PhaseSum
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Pointwise.SpaceSplit
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Pointwise.CS

/-!
# The thin source: separated-source structure and the finite order-0 majorant

Helper for `OscFarPt` (source 5400-5427, 3768-3790): `thinSource ε F` is a `2εc`-periodic
separated source, and `thinMoment c F ≠ ⊤` makes the order-0 majorant finite at every `τ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

open UnforcedLeray UnforcedLeray.Short.IIIa

structure ThinHyp (c ρo : ℝ) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) : Prop where
  meas : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j
  per : ∀ x' Y q, F x' Y (q + c) = F x' Y q
  supp : ∀ x' Y q, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → F x' Y q = 0

/-- the phase of the point `z` -/
def q0 (ε τ : ℝ) (z : Space) : ℝ :=
  ε⁻¹ * Real.log (ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2)) + τ / (2 * ε)

theorem thin_isSep {ε c ρo : ℝ} {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hε : 0 < ε)
    (h : ThinHyp c ρo F) : IsSepSource (2 * ε * c) (ρo / ε) (thinSource ε F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have h1 : Measurable fun p : ℝ × Space => ((ε * p.2 0, ε * p.2 1), (p.2 2,
        ε⁻¹ * Real.log (ε * Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2)) + p.1 / (2 * ε))) := by
      fun_prop
    exact (h.meas i j).comp h1
  · intro τ z
    unfold thinSource
    have : ε⁻¹ * Real.log (ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2)) + (τ + 2 * ε * c) / (2 * ε) =
        (ε⁻¹ * Real.log (ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2)) + τ / (2 * ε)) + c := by
      field_simp
      ring
    rw [this, h.per]
  · intro τ z hz
    unfold thinSource
    apply h.supp
    have : Real.sqrt ((ε * z 0) ^ 2 + (ε * z 1) ^ 2) = ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := by
      rw [show (ε * z 0) ^ 2 + (ε * z 1) ^ 2 = ε ^ 2 * (z 0 ^ 2 + z 1 ^ 2) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hε.le]
    show ρo < Real.sqrt ((ε * z 0) ^ 2 + (ε * z 1) ^ 2)
    rw [this]
    rwa [div_lt_iff₀ hε, mul_comm] at hz

theorem srcNorm_thin (ε : ℝ) (hε : 0 < ε) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (τ l : ℝ) (z : Space) :
    srcNorm (thinSource ε F) (τ + 2 * Real.log l) z =
      ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) (q0 ε τ z + ε⁻¹ * Real.log l))) := by
  unfold srcNorm thinSource q0
  congr 3
  field_simp
  ring

theorem tn_meas_phase {c ρo : ℝ} {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (h : ThinHyp c ρo F) (x' : ℝ × ℝ) (Y : ℝ) :
    Measurable fun q => tensorNorm (F x' Y q) := by
  unfold tensorNorm
  refine Measurable.sqrt ?_
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  have : Measurable fun q : ℝ => F x' Y q i j :=
    (h.meas i j).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  exact this.pow_const 2

theorem tn_meas_joint {c ρo : ℝ} {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (h : ThinHyp c ρo F) :
    Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => tensorNorm (F w.1 w.2.1 w.2.2) := by
  unfold tensorNorm
  refine Measurable.sqrt ?_
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact (h.meas i j).pow_const 2

theorem sepKd_zero_le (D : ℝ) (hD : 0 < D) (x : Space) :
    sepKd 0 D x ≤ ENNReal.ofReal (D ^ (-4 : ℝ)) := by
  unfold sepKd
  split_ifs with h
  · refine ENNReal.ofReal_le_ofReal ?_
    simp only [Nat.cast_zero, sub_zero]
    exact Real.rpow_le_rpow_of_nonpos hD h (by norm_num)
  · exact zero_le

theorem thin_phase_bound {ε c ρo : ℝ} {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hε : 0 < ε) (hc : 0 < c) (h : ThinHyp c ρo F) (a : ℝ) (ha : -1 < a) (τ : ℝ) (z : Space) :
    ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) * srcNorm (thinSource ε F) (τ + 2 * Real.log l) z ≤
      ENNReal.ofReal (ε / (1 - Real.exp (-(ε * (a + 1) * c)))) *
        ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q)) := by
  have := phaseSum_le ε c (q0 ε τ z) a hε hc ha
    (fun q => ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q)))
    (fun q => by rw [h.per])
  simpa only [srcNorm_thin ε hε] using this

theorem thin_total {ε c ρo : ℝ} {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hε : 0 < ε) (hc : 0 < c) (h : ThinHyp c ρo F) (a : ℝ) (ha : -1 < a) (τ : ℝ) :
    ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) *
        ∫⁻ z : Space, srcNorm (thinSource ε F) (τ + 2 * Real.log l) z ≤
      ENNReal.ofReal (ε / (1 - Real.exp (-(ε * (a + 1) * c)))) * ENNReal.ofReal (ε⁻¹) ^ 2 *
        (ENNReal.ofReal c * thinMoment c F) := by
  have hS := thin_isSep (c := c) (ρo := ρo) hε h
  have hφ : Measurable fun q : ℝ × Space => (τ + 2 * Real.log q.1, q.2) :=
    (measurable_const.add (measurable_const.mul
      (Real.measurable_log.comp measurable_fst))).prodMk measurable_snd
  have hTn : Measurable fun q : ℝ × Space =>
      ENNReal.ofReal (tensorNorm (thinSource ε F (τ + 2 * Real.log q.1) q.2)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    unfold tensorNorm
    refine Measurable.sqrt ?_
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact ((hS.measurable i j).comp hφ).pow_const 2
  have hm : Measurable fun q : ℝ × Space => ENNReal.ofReal (q.1 ^ a) *
      srcNorm (thinSource ε F) (τ + 2 * Real.log q.1) q.2 := by
    unfold srcNorm
    exact (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul hTn
  have hsw : ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) *
        ∫⁻ z : Space, srcNorm (thinSource ε F) (τ + 2 * Real.log l) z =
      ∫⁻ z : Space, ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) *
        srcNorm (thinSource ε F) (τ + 2 * Real.log l) z := by
    rw [← lintegral_lintegral_swap hm.aemeasurable]
    refine lintegral_congr (fun l => ?_)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hsw]
  calc _ ≤ ∫⁻ z : Space, ENNReal.ofReal (ε / (1 - Real.exp (-(ε * (a + 1) * c)))) *
        ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q)) :=
        lintegral_mono (fun z => thin_phase_bound hε hc h a ha τ z)
    _ = ENNReal.ofReal (ε / (1 - Real.exp (-(ε * (a + 1) * c)))) *
        ∫⁻ z : Space, (fun w : (ℝ × ℝ) × ℝ =>
          ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F w.1 w.2 q))) ((ε * z 0, ε * z 1), z 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (ε / (1 - Real.exp (-(ε * (a + 1) * c)))) *
        (ENNReal.ofReal (ε⁻¹) ^ 2 * ∫⁻ w : (ℝ × ℝ) × ℝ,
          ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F w.1 w.2 q))) := by
        rw [lintegral_space_scale hε (fun w : (ℝ × ℝ) × ℝ =>
          ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F w.1 w.2 q)))]
    _ ≤ ENNReal.ofReal (ε / (1 - Real.exp (-(ε * (a + 1) * c)))) *
        (ENNReal.ofReal (ε⁻¹) ^ 2 * (ENNReal.ofReal c * thinMoment c F)) := by
        gcongr
        unfold thinMoment
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono (fun w => ?_)
        refine (cs_phase c hc _ (tn_meas_phase h w.1 w.2) (fun q => Real.sqrt_nonneg _)).trans ?_
        refine mul_le_mul' le_rfl (le_mul_of_one_le_left (zero_le) ?_)
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by linarith [abs_nonneg w.2])
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg
