import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YKerBound.Norm2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YKerBound.Scale

/-!
# `PDYKerBound`: the kernel bound for `Y`

Source `the November 2 reference manuscript` 4198-4205 (`ward:shifted-resolvent`,
`ward:cutoff-source`), 3700-3713 (cutoff commutators), 4178-4186 (outward primitive, stream
cutoff), 5592 (the outward stream primitive obeys the same bound).

The kernel of `X = 𝒞_y X₀` is parabolically homogeneous of degree `-4`, and `D_{μ+1}` commutes with
the dilation `y ↦ y/ϱ(y)` up to `ν ↦ ν ϱ(y)^{-2}` (`ykb_fullKer_scale`, `ykb_physDmu_scale`).  So
the bound reduces to the receiver radius `ϱ y = 1`, where `ν ϱ^{-2} ≤ νR²ϱ^{-2} = ν·age ≤ 1`.
There the kernel is the `χ_y X₀` part (`ykb_part1`: `D_{μ+1}` of it is `χ_y wKer` plus the cutoff
commutators, `≤ C λ^{2μ+3}|y - λz|^{-4}|M|`) plus the stream part (`ykb_part2`:
`≤ C λ^{2μ+3}(1 + (y₃ - λz₃)²)^{-1}|M|`, via the dilation identity of the outward primitive).
Scaling back turns these into `|y - λz|^{-4}` and `ϱ^{-2}(ϱ² + (y₃ - λz₃)²)^{-1}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `D_μ` is additive for kernels differentiable in time and `C²` in space at the point. -/
private theorem ykbF_physDmu_add {ν μ' : ℝ} {X Y : ℝ → Space → Space} {h : ℝ} {y : Space}
    (hXt : DifferentiableAt ℝ (fun t => X t y) h) (hYt : DifferentiableAt ℝ (fun t => Y t y) h)
    (hXy : ContDiffAt ℝ 2 (X h) y) (hYy : ContDiffAt ℝ 2 (Y h) y) :
    physDmu ν μ' (fun t y' => X t y' + Y t y') h y = physDmu ν μ' X h y + physDmu ν μ' Y h y := by
  have h1 : deriv (fun t => X t y + Y t y) h =
      deriv (fun t => X t y) h + deriv (fun t => Y t y) h :=
    deriv_fun_add hXt hYt
  have h2 : fderiv ℝ (fun y' => X h y' + Y h y') y = fderiv ℝ (X h) y + fderiv ℝ (Y h) y :=
    fderiv_fun_add (hXy.differentiableAt (by norm_num)) (hYy.differentiableAt (by norm_num))
  have h3 : physLap (fun y' => X h y' + Y h y') y = physLap (X h) y + physLap (Y h) y :=
    tcle_physLap_add hXy hYy
  simp only [physDmu, h1, h2, h3, ContinuousLinearMap.add_apply]
  module

/-- The scaled distance: `c^4 |c y - λ c z|^{-4} = |y - λz|^{-4}`. -/
private theorem ykbF_scale_x {c : ℝ} (hc : 0 < c) (l : ℝ) (y z : Space) :
    c ^ 4 * (‖c • y - l • c • z‖ ^ 4)⁻¹ = (‖y - l • z‖ ^ 4)⁻¹ := by
  have e : c • y - l • c • z = c • (y - l • z) := by
    rw [smul_sub, smul_comm c l z]
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_pow, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero 4 hc.ne'), one_mul]

/-- The scaled stream weight: `c^4 (1 + (c b)²)^{-1} = (r²(r² + b²))^{-1}` for `c = r^{-1}`. -/
private theorem ykbF_scale_s {r : ℝ} (hr : 0 < r) (b : ℝ) :
    r⁻¹ ^ 4 * (1 + (r⁻¹ * b) ^ 2)⁻¹ = (r ^ 2 * (r ^ 2 + b ^ 2))⁻¹ := by
  have hr0 : r ≠ 0 := hr.ne'
  have hD : 0 < 1 + (r⁻¹ * b) ^ 2 := by positivity
  have hE : 0 < r ^ 2 * (r ^ 2 + b ^ 2) := by positivity
  rw [inv_pow, ← mul_inv]
  congr 1
  field_simp

/-- **The kernel bound for `Y`** (source 4198-4205, 3700-3713, 4178-4186, 5592). -/
theorem pdYKerBound : PDYKerBound := by
  intro χy hχ
  obtain ⟨C, hC⟩ := ykb_exists
  obtain ⟨A, hA0, hcut⟩ := ykb_cut hχ
  obtain ⟨CF, hCF0, hpsi⟩ := ykb_psi_bounds hC
  have hκ := ykKap_pos
  have hK1 : 0 ≤ 3 + 4 * (ykKap ^ 2)⁻¹ + 2 * A + 2 * A * ykKap⁻¹ := by positivity
  have hK2 : 0 ≤ A * (9 * CF + (3 / 2 + (ykKap ^ 2)⁻¹) * ykKap⁻¹ * (ykKap ^ 2)⁻¹) := by
    positivity
  refine ⟨((3 + 4 * (ykKap ^ 2)⁻¹ + 2 * A + 2 * A * ykKap⁻¹) +
      A * (9 * CF + (3 / 2 + (ykKap ^ 2)⁻¹) * ykKap⁻¹ * (ykKap ^ 2)⁻¹)) * C,
    mul_nonneg (add_nonneg hK1 hK2) hC.1, ?_⟩
  intro ν μ R hν hR hμ0 hμ1 h hh y z M hy hage hz
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (ϱ y)⁻¹ := ⟨_, rfl⟩
  have hc : 0 < c := hcdef ▸ inv_pos.2 hy
  have hcr : c * ϱ y = 1 := by rw [hcdef]; exact inv_mul_cancel₀ hy.ne'
  have hν1 : 0 < ν * c ^ 2 := by positivity
  have hνR : ν * c ^ 2 * R ^ 2 ≤ 1 := by
    have e : ν * c ^ 2 * R ^ 2 = ν * age R y := by
      rw [age, hcdef]
      ring
    rw [e]
    exact hage
  have hν1le : ν * c ^ 2 ≤ 1 := by
    have hR2 : 1 ≤ R ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left hR2 hν1.le
    linarith
  have hy1 : ϱ (c • y) = 1 := by rw [ykb_ϱ_smul hc.le, hcr]
  have hz1 : ϱ (c • z) ≤ ykR0 := by
    rw [ykb_ϱ_smul hc.le]
    calc c * ϱ z ≤ c * (Real.sqrt (5 / 6) * ϱ y) := mul_le_mul_of_nonneg_left hz hc.le
      _ = Real.sqrt (5 / 6) * (c * ϱ y) := by ring
      _ = ykR0 := by unfold ykR0; rw [hcr, mul_one]
  have hev : ∀ᶠ t in 𝓝 h, ∀ y' : Space,
      fullKer ν μ R χy t y' z M = c ^ 4 • fullKer (ν * c ^ 2) μ R χy t (c • y') (c • z) M := by
    filter_upwards [lt_mem_nhds hh] with t ht y'
    exact ykb_fullKer_scale ν μ R χy t hν ht hc y' z M
  rw [ykb_physDmu_scale ν (μ + 1) (c ^ 4) hc.ne' (fun h' y' => fullKer ν μ R χy h' y' z M)
    (fun h' y' => fullKer (ν * c ^ 2) μ R χy h' y' (c • z) M) h y hev]
  obtain ⟨hc2, hf2, hc0, hc1, hcc, hf0, hf1, hff⟩ := hcut (ν * c ^ 2) R hν1 hνR
  obtain ⟨hP2, hPb⟩ := hpsi (ν * c ^ 2) μ hν1 hμ0 hμ1 M h hh (c • y) (c • z) hy1 hz1
  obtain ⟨d1, e1, b1⟩ := ykb_part1 hC (ν * c ^ 2) μ R χy hν1 hν1le hμ0 hμ1 M hh (c • y) (c • z)
    hy1 hz1 hA0 hc2 hc0 hc1 hcc
  obtain ⟨d2, e2, b2⟩ := ykb_part2 hC (ν * c ^ 2) μ R χy hν1 hν1le hμ0 hμ1 M hh (c • y) (c • z)
    hy1 hz1 hA0 hCF0 hP2 hPb hf2 hf0 hf1 hff
  have hsum : physDmu (ν * c ^ 2) (μ + 1)
      (fun h' y' => fullKer (ν * c ^ 2) μ R χy h' y' (c • z) M) h (c • y) =
      physDmu (ν * c ^ 2) (μ + 1) (ykX1 (ν * c ^ 2) μ R χy (c • z) M) h (c • y) +
        physDmu (ν * c ^ 2) (μ + 1) (ykX2 (ν * c ^ 2) μ R χy (c • z) M) h (c • y) :=
    ykbF_physDmu_add d1 d2 e1 e2
  rw [hsum, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < c ^ 4)]
  have i1 := ykbF_scale_x hc (pdLam h) y z
  have i2 : c ^ 4 * (1 + ((c • y) 2 - pdLam h * (c • z) 2) ^ 2)⁻¹ =
      (ϱ y ^ 2 * (ϱ y ^ 2 + (y 2 - pdLam h * z 2) ^ 2))⁻¹ := by
    have e : (c • y) 2 - pdLam h * (c • z) 2 = c * (y 2 - pdLam h * z 2) := by
      simp only [PiLp.smul_apply, smul_eq_mul]
      ring
    rw [e, hcdef]
    exact ykbF_scale_s hy _
  have hK0 : 0 ≤ C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M :=
    mul_nonneg (mul_nonneg hC.1 (ykb_rpow_nonneg μ h)) (kb_tensor_nonneg M)
  have hX0 : 0 ≤ (‖y - pdLam h • z‖ ^ 4)⁻¹ := by positivity
  have hY0 : 0 ≤ (ϱ y ^ 2 * (ϱ y ^ 2 + (y 2 - pdLam h * z 2) ^ 2))⁻¹ := by positivity
  have hc4 : 0 ≤ c ^ 4 := by positivity
  set P1 := physDmu (ν * c ^ 2) (μ + 1) (ykX1 (ν * c ^ 2) μ R χy (c • z) M) h (c • y)
  set P2 := physDmu (ν * c ^ 2) (μ + 1) (ykX2 (ν * c ^ 2) μ R χy (c • z) M) h (c • y)
  set K := C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M with hKdef
  set K1 := 3 + 4 * (ykKap ^ 2)⁻¹ + 2 * A + 2 * A * ykKap⁻¹
  set K2 := A * (9 * CF + (3 / 2 + (ykKap ^ 2)⁻¹) * ykKap⁻¹ * (ykKap ^ 2)⁻¹)
  set X1 := (‖c • y - pdLam h • c • z‖ ^ 4)⁻¹
  set Y1 := (1 + ((c • y) 2 - pdLam h * (c • z) 2) ^ 2)⁻¹
  set X := (‖y - pdLam h • z‖ ^ 4)⁻¹
  set Y := (ϱ y ^ 2 * (ϱ y ^ 2 + (y 2 - pdLam h * z 2) ^ 2))⁻¹
  have s1 : c ^ 4 * ‖P1 + P2‖ ≤ c ^ 4 * (K1 * K * X1 + K2 * K * Y1) :=
    mul_le_mul_of_nonneg_left ((norm_add_le P1 P2).trans (add_le_add b1 b2)) hc4
  have s2 : c ^ 4 * (K1 * K * X1 + K2 * K * Y1) = K1 * K * X + K2 * K * Y := by
    rw [← i1, ← i2]
    ring
  have s3 : K1 * K * X + K2 * K * Y ≤ (K1 + K2) * K * (X + Y) := by
    have := mul_nonneg (mul_nonneg hK1 hK0) hY0
    have := mul_nonneg (mul_nonneg hK2 hK0) hX0
    nlinarith
  calc c ^ 4 * ‖P1 + P2‖ ≤ (K1 + K2) * K * (X + Y) := s1.trans (s2.le.trans s3)
    _ = (K1 + K2) * C * pdLam h ^ (2 * μ + 3) * (X + Y) * IIIa.tensorNorm M := by
      rw [hKdef]
      ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
