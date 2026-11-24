import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.PartIIIb_IIIb_D2_3_1_3

/-!
# `WardX0Decay` from a power-decay leaf (`PartIII-b:IIIb-D2/3/1/3/1`)

Source of record: `the November 2 reference manuscript` 4175-4186 (decay 4177-4179).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **Leaf (power decay of `X₀` far from the old disk)** (source 4177-4179).  `Z = wardX0` is the
difference of two `IIIa.sepW` integrals against the old source `oldPhys`, supported in
`r ≤ R√(ν/1.2) = R√(5ν/6)` (4161-4166, 3611-3621) with finite `Y₂ = L²_τL²` moment (4155-4156;
`OldSourceReg`, which needs `c, ρ_b > 0`, `m_Z ≥ 0`: `Defs.lean`, *Parameters*); by
`IIIa.SepKernelBounds` (`|D^j∇K| ≤ C|x|^{-4-j}`) and differentiation under the integral, for
`ϱ = ρ > r > R√(5ν/6)` and `z'` in the unit ball about `z`:
`|ρ Z_z|, |ρ ∂_zZ_z|, |ρ Z_r| ≤ C ρ^{-a}` for some `a > 1`. -/
def WardX0FarBound (c mZ ρb γ ν : ℝ) (ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) : Prop :=
  0 < c → 0 < ρb → 0 ≤ mZ → 0 < ν → 0 < ε → -(1 / 4) < μ →
  ∀ (T : StrG c mZ ρb γ ν) (g₁ g₂ : Chart → Ten3),
    ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] g₁ →
    ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] g₂ →
      ∀ (τ r z : ℝ), ε⁻¹ * Real.sqrt (5 * ν / 6) < r →
        ∃ a C : ℝ, 1 < a ∧ ∀ ρ ∈ Ioi r, ∀ z' ∈ Metric.ball z 1,
          ‖ρ * wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ !₂[ρ, 0, z'] 2‖ ≤ C * ρ ^ (-a) ∧
          ‖ρ * fderiv ℝ (wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ) !₂[ρ, 0, z'] (coordinateVector 2) 2‖
            ≤ C * ρ ^ (-a) ∧
          ‖ρ * wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ !₂[ρ, 0, z'] 0‖ ≤ C * ρ ^ (-a)

theorem wardX0Decay_of (c mZ ρb γ ν ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (hA : WardX0FarBound c mZ ρb γ ν ε μ hχo) : WardX0Decay c mZ ρb γ ν ε μ hχo := by
  intro hc hρ hm hν hε hμ T g₁ g₂ e₁ e₂ τ r z hr
  obtain ⟨a, C, ha, h⟩ := hA hc hρ hm hν hε hμ T g₁ g₂ e₁ e₂ τ r z hr
  refine ⟨⟨fun ρ => C * ρ ^ (-a), ?_, fun ρ hρ z' hz' =>
    ⟨(h ρ hρ z' hz').1, (h ρ hρ z' hz').2.1⟩⟩, ?_⟩
  · have hr0 : 0 < ε⁻¹ * Real.sqrt (5 * ν / 6) := by positivity
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) (hr0.trans hr)).const_mul C
  · have hz : Tendsto (fun ρ : ℝ => C * ρ ^ (-a)) atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < a)).const_mul C
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_gt_atTop r] with ρ hρ
    exact (h ρ hρ z (Metric.mem_ball_self one_pos)).2.2

end UnforcedLeray.Short.PartIIIb.Concrete
