import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.Leaves
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel.FarPointwise
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.FarMajorantPointwise
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.DilMajAxisym
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.RotExists
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.GAxFacts
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AxisNull
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.CartLiftNormOffAxis
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel.FarSeparation
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_A2
import UnforcedLeray.Lib.AxisymmetricB.Lift
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.FarUpperZero

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Integer shifts of a periodic profile leave `dilMaj` unchanged. -/
theorem fvp_dilMaj_int_shift (μ d : ℝ) (g : ℝ → UnforcedLeray.Space → ℝ≥0∞) (P : ℝ)
    (hg : ∀ τ z, g (τ + P) z = g τ z) (k : ℤ) (τ : ℝ) (y : UnforcedLeray.Space) :
    NearInst.Masked.dilMaj μ d g (τ + (k : ℝ) * P) y = NearInst.Masked.dilMaj μ d g τ y := by
  unfold NearInst.Masked.dilMaj
  refine lintegral_congr fun l => ?_
  congr 1
  refine lintegral_congr fun z => ?_
  have hper : Function.Periodic (fun t => g t z) P := fun t => hg t z
  have h := hper.int_mul k (τ + 2 * Real.log l)
  have e : τ + (k : ℝ) * P + 2 * Real.log l = τ + 2 * Real.log l + (k : ℝ) * P := by ring
  rw [e]
  rw [h]

/-- The chart point of the phase cell: `chartTau` of `(s, (cellRep ξ, η))` with `ξ` the phase. -/
theorem fvp_chartTau_cell (R c τ s η : ℝ) (hR : R ≠ 0) (hc : c ≠ 0) :
    ∃ k : ℤ, NearInst.chartTau R (s, (cellRep c (R * τ / 2 - (R / 2) * Real.log s), η)) =
      τ + (k : ℝ) * (2 * c / R) := by
  refine ⟨-⌊(R * τ / 2 - (R / 2) * Real.log s + c / 2) / c⌋, ?_⟩
  unfold NearInst.chartTau cellRep
  push_cast
  field_simp
  ring

/-- The chart `y ↦ chartY` of a cell point has the same radius and height as `y`. -/
theorem fvp_chartY_facts {R : ℝ} (hR : 0 < R) {y : UnforcedLeray.Space}
    (hy : y ∉ UnforcedLeray.Axi.axis) (q : ℝ) :
    NearInst.hRad (NearInst.chartY R (UnforcedLeray.Axi.age R y, (q, UnforcedLeray.Axi.trans R y)))
        = NearInst.hRad y ∧
      NearInst.chartY R (UnforcedLeray.Axi.age R y, (q, UnforcedLeray.Axi.trans R y)) 2 = y 2 := by
  have hρ : 0 < UnforcedLeray.Axi.ϱ y := UnforcedLeray.Axi.ϱ_pos hy
  have hs : Real.sqrt (UnforcedLeray.Axi.age R y) = R / UnforcedLeray.Axi.ϱ y :=
    UnforcedLeray.Axi.sqrt_age hR hy
  have h0 : R / Real.sqrt (UnforcedLeray.Axi.age R y) = UnforcedLeray.Axi.ϱ y := by
    rw [hs]
    field_simp
  have hrad : NearInst.hRad y = UnforcedLeray.Axi.ϱ y := rfl
  have e0 : NearInst.chartY R (UnforcedLeray.Axi.age R y, (q, UnforcedLeray.Axi.trans R y)) 0
      = UnforcedLeray.Axi.ϱ y := by
    simp only [NearInst.chartY, PiLp.toLp_apply]
    simpa using h0
  have e2 : NearInst.chartY R (UnforcedLeray.Axi.age R y, (q, UnforcedLeray.Axi.trans R y)) 2
      = y 2 := by
    simp only [NearInst.chartY, PiLp.toLp_apply]
    rw [hs]
    simp only [UnforcedLeray.Axi.trans]
    field_simp
    simp
  have hsq : UnforcedLeray.Axi.ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
  have e1 : NearInst.chartY R (UnforcedLeray.Axi.age R y, (q, UnforcedLeray.Axi.trans R y)) 1 = 0 := by
    simp only [NearInst.chartY, PiLp.toLp_apply]
    simp
  constructor
  · unfold NearInst.hRad
    rw [e0, e1, hsq]
    simp
  · exact e2

/-- The pointwise bound for the far velocity, at a point of age `s < S` away from the axis. -/
theorem farVelPointwise : FarVelPointwise := by
  unfold FarVelPointwise
  obtain ⟨C, hC0, hC⟩ := NearInst.Masked.farPointwiseMajorant_of
    UnforcedLeray.Short.IIIa.sepKernelBounds
  refine ⟨C, hC0, ?_⟩
  intro ε c ν δ S μ hε hc hν hδ hS f hf τ
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hMaj : NearInst.Masked.FarMajorantPointwise :=
    NearInst.Masked.farMajorantPointwise_of NearInst.Masked.farSeparation_holds
      NearInst.Masked.cartLiftNormOffAxis_holds NearInst.Masked.axisNull_holds
  have hDA : NearInst.Masked.DilMajAxisym := NearInst.Masked.dilMajAxisym_of
    NearInst.Masked.rotExists_holds
  obtain ⟨hAx, hPer, -⟩ := NearInst.Masked.gAxFacts_holds ε⁻¹ c f hR hc hf.measurable
  have hae : ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space), NearInst.hRad y ≠ 0 := by
    rw [ae_iff]
    have hN' : volume {z : UnforcedLeray.Space | NearInst.hRad z = 0} = 0 :=
      NearInst.Masked.axisNull_holds
    simpa using hN'
  filter_upwards [hae] with y hy
  have hyax : y ∉ UnforcedLeray.Axi.axis := by
    intro h
    have h' : y 0 = 0 ∧ y 1 = 0 := h
    apply hy
    simp [NearInst.hRad, h'.1, h'.2]
  have hsp : 0 < UnforcedLeray.Axi.age ε⁻¹ y :=
    UnforcedLeray.Axi.age_pos (inv_ne_zero hε.ne') hyax
  obtain ⟨x', hx'⟩ : ∃ x' : ℝ × (ℝ × ℝ), x' = (UnforcedLeray.Axi.age ε⁻¹ y,
      (cellRep c (UnforcedLeray.Axi.phase ε⁻¹ τ y), UnforcedLeray.Axi.trans ε⁻¹ y)) := ⟨_, rfl⟩
  have hnorm : ‖velPhys ε⁻¹ c (NearInst.Masked.farOut ε⁻¹ c ν μ δ S f) (τ, y)‖ₑ =
      ENNReal.ofReal (Real.sqrt (UnforcedLeray.Axi.age ε⁻¹ y) *
        ‖NearInst.Masked.farOut ε⁻¹ c ν μ δ S f x'‖) := by
    rw [← ofReal_norm]
    have hn : ‖velPhys ε⁻¹ c (NearInst.Masked.farOut ε⁻¹ c ν μ δ S f) (τ, y)‖ =
        ‖UnforcedLeray.Axi.Nv ε⁻¹ (UnforcedLeray.Axi.perExt c
          (NearInst.Masked.farOut ε⁻¹ c ν μ δ S f)) τ y‖ := by
      unfold velPhys
      exact fwuB_realC_norm _
    rw [hn, UnforcedLeray.Axi.norm_Nv ε⁻¹ _ τ hyax, hx']
    rfl
  rw [hnorm]
  by_cases hsS : UnforcedLeray.Axi.age ε⁻¹ y < S
  · have hx1 : (0 : ℝ) < x'.1 := by rw [hx']; exact hsp
    have hx2 : x'.1 < S := by rw [hx']; exact hsS
    have hmaj := hMaj ε⁻¹ c δ μ S hR hδ hS f x' hx1 hx2
    have hfar := hC ε⁻¹ c ν δ S μ hν f x'
    have hcy := fvp_chartY_facts hR hyax (cellRep c (UnforcedLeray.Axi.phase ε⁻¹ τ y))
    have hcy' : NearInst.hRad (NearInst.chartY ε⁻¹ x') = NearInst.hRad y ∧
        NearInst.chartY ε⁻¹ x' 2 = y 2 := by
      rw [hx']; exact hcy
    obtain ⟨k, hk⟩ : ∃ k : ℤ, NearInst.chartTau ε⁻¹ x' = τ + (k : ℝ) * (2 * c / ε⁻¹) := by
      rw [hx']
      unfold UnforcedLeray.Axi.phase
      exact fvp_chartTau_cell ε⁻¹ c τ _ _ hR.ne' hc.ne'
    have hd1 : NearInst.Masked.dilMaj μ ((1 - Real.exp (-δ / 2)) * ε⁻¹ / Real.sqrt S)
        (NearInst.Masked.gAx ε⁻¹ c f) (NearInst.chartTau ε⁻¹ x') (NearInst.chartY ε⁻¹ x') =
        NearInst.Masked.dilMaj μ ((1 - Real.exp (-δ / 2)) * ε⁻¹ / Real.sqrt S)
          (NearInst.Masked.gAx ε⁻¹ c f) τ (NearInst.chartY ε⁻¹ x') := by
      rw [hk]
      exact fvp_dilMaj_int_shift _ _ _ (2 * c / ε⁻¹) hPer k τ _
    have hd2 : NearInst.Masked.dilMaj μ ((1 - Real.exp (-δ / 2)) * ε⁻¹ / Real.sqrt S)
        (NearInst.Masked.gAx ε⁻¹ c f) τ (NearInst.chartY ε⁻¹ x') =
        NearInst.Masked.dilMaj μ ((1 - Real.exp (-δ / 2)) * ε⁻¹ / Real.sqrt S)
          (NearInst.Masked.gAx ε⁻¹ c f) τ y :=
      hDA _ _ _ hAx τ _ y hcy'.1 hcy'.2
    have hsqrt : 0 < Real.sqrt (UnforcedLeray.Axi.age ε⁻¹ y) := Real.sqrt_pos.2 hsp
    have hne0 : ENNReal.ofReal (Real.sqrt (UnforcedLeray.Axi.age ε⁻¹ y)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 hsqrt).ne'
    have hnetop : ENNReal.ofReal (Real.sqrt (UnforcedLeray.Axi.age ε⁻¹ y)) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), ofReal_norm]
    calc ENNReal.ofReal (Real.sqrt (UnforcedLeray.Axi.age ε⁻¹ y)) *
          ‖NearInst.Masked.farOut ε⁻¹ c ν μ δ S f x'‖ₑ
        ≤ ENNReal.ofReal (Real.sqrt (UnforcedLeray.Axi.age ε⁻¹ y)) *
          (ENNReal.ofReal C * (ENNReal.ofReal (Real.sqrt x'.1)⁻¹ *
            NearInst.Masked.farMajE ε⁻¹ c δ μ f x')) := by gcongr
      _ = ENNReal.ofReal C * (ENNReal.ofReal (Real.sqrt (UnforcedLeray.Axi.age ε⁻¹ y)) *
            (ENNReal.ofReal (Real.sqrt (UnforcedLeray.Axi.age ε⁻¹ y)))⁻¹) *
            NearInst.Masked.farMajE ε⁻¹ c δ μ f x' := by
          rw [hx', ENNReal.ofReal_inv_of_pos hsqrt]
          ac_rfl
      _ = ENNReal.ofReal C * NearInst.Masked.farMajE ε⁻¹ c δ μ f x' := by
          rw [ENNReal.mul_inv_cancel hne0 hnetop, mul_one]
      _ ≤ ENNReal.ofReal C * NearInst.Masked.dilMaj μ ((1 - Real.exp (-δ / 2)) * ε⁻¹ / Real.sqrt S)
          (NearInst.Masked.gAx ε⁻¹ c f) (NearInst.chartTau ε⁻¹ x') (NearInst.chartY ε⁻¹ x') :=
          by gcongr
      _ = ENNReal.ofReal C * NearInst.Masked.dilMaj μ ((1 - Real.exp (-δ / 2)) * ε⁻¹ / Real.sqrt S)
          (NearInst.Masked.gAx ε⁻¹ c f) τ y := by rw [hd1, hd2]
  · have h0 : NearInst.Masked.farOut ε⁻¹ c ν μ δ S f x' = 0 :=
      NearInst.Masked.farOut_eq_zero_of_le f x' (by rw [hx']; exact not_lt.1 hsS)
    rw [h0, norm_zero, mul_zero, ENNReal.ofReal_zero]
    exact zero_le

end UnforcedLeray.Short.PartIIIb.Concrete
