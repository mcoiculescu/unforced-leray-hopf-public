import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelHeatEq.ApproxId

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/3/3` (decomposition): `φ'(r) = νB(r) - A(r)`

Source of record: `the November 2 reference manuscript`,
lines 3427-3440. With `φ(r) = ∫ G_{νr}(z) h(s - r, x - z) dz` split
`φ(r') - φ(r) = ∫ G_{νr'}(z) (h(s - r', x - z) - h(s - r, x - z)) dz
  + (∫ G_{νr'}(z) h(s - r, x - z) dz - ∫ G_{νr}(z) h(s - r, x - z) dz)`:
the second bracket is the heat-age derivative (`∂_θ G_θ = ΔG_θ`, two integrations by parts), the
first is the time derivative (`-A`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Space part** (SP 3427-3440): with the source frozen at time `s - r`, the heat-age
derivative of the convolution is `ν B(r)`:
`d/dr' ∫ G_{νr'}(z) h(s - r, x - z) dz = ν ∫ G_{νr}(z) Δh(s - r, ·)(x - z) dz` at `r' = r > 0`.
Proof: `deqhd_theta_hasDerivAt` (PartII-b DuhamelEquation/HeatDeriv.lean:398, bounded continuous
real slices), `TrainB.integral_heatKernel2AgeDerivative_mul_comp_sub`
(Lib/TrainB/P0GaussianSecondOrderIBP.lean:170) on real and imaginary parts, chain rule `θ = νr`. -/
def DuhEqSpacePart : Prop :=
  ∀ (c ν : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ), 0 < c → 0 < ν → NiceScalar c h → ∀ (s : ℝ) (x : ℝ × ℝ)
    (r : ℝ), 0 < r →
    HasDerivAt (fun r' : ℝ => ∫ z : ℝ × ℝ,
      ((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
        h (s - r, (x.1 - z.1, x.2 - z.2))) ((ν : ℂ) * duhLap ν h s x r) r

/-- **Time part** (SP 3427-3440): the difference quotient in the source time with the kernel at
`νr'` tends to `-A(r)`:
`(r' - r)⁻¹ ∫ G_{νr'}(z) (h(s - r', x - z) - h(s - r, x - z)) dz → -∫ G_{νr}(z) ∂_t h(s - r, x - z) dz`
as `r' → r`, `r > 0`. Proof: Taylor in `t` with a uniform second-derivative bound
(`duhSm_bound`), unit mass of `G_{νr'}`, and continuity of `θ ↦ ∫ G_θ(z) ∂_t h(s - r, x - z) dz`
(`deqhd_theta_hasDerivAt` gives differentiability, hence continuity, on re/im parts). -/
def DuhEqTimePart : Prop :=
  ∀ (c ν : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ), 0 < c → 0 < ν → NiceScalar c h → ∀ (s : ℝ) (x : ℝ × ℝ)
    (r : ℝ), 0 < r →
    Tendsto (fun r' : ℝ => (((r' - r)⁻¹ : ℝ) : ℂ) * ∫ z : ℝ × ℝ,
      ((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
        (h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2))))
      (𝓝[≠] r) (𝓝 (-duhDt ν h s x r))

/-- `DuhEqPhiDeriv` from the space part and the time part. -/
theorem duhEqPhiDeriv_of (hS : DuhEqSpacePart) (hT : DuhEqTimePart) : DuhEqPhiDeriv := by
  intro c ν h hc hν hn s x r hr
  have hS' := (hasDerivAt_iff_tendsto_slope.mp (hS c ν h hc hν hn s x r hr))
  have hT' := hT c ν h hc hν hn s x r hr
  have hsum := hT'.add hS'
  rw [hasDerivAt_iff_tendsto_slope]
  have hlim : -duhDt ν h s x r + (ν : ℂ) * duhLap ν h s x r =
      (ν : ℂ) * duhLap ν h s x r - duhDt ν h s x r := by ring
  rw [hlim] at hsum
  refine hsum.congr' ?_
  have hpos : ∀ᶠ r' in 𝓝[≠] r, 0 < r' :=
    (nhdsWithin_le_nhds (Ioi_mem_nhds hr))
  filter_upwards [hpos] with r' hr'
  obtain ⟨K0, hK0⟩ := duhSm_bound hc hn 0
  have hM0 : ∀ q, ‖h q‖ ≤ K0 := fun q => by simpa only [norm_iteratedFDeriv_zero] using hK0 q
  have hcont : Continuous h := hn.1.continuous
  have hθ : 0 < ν * r' := mul_pos hν hr'
  have hG := UnforcedLeray.B0284.integrable_heatKernel2 hθ
  have hc1 : Continuous fun z : ℝ × ℝ => h (s - r', (x.1 - z.1, x.2 - z.2)) :=
    hcont.comp (by fun_prop)
  have hc2 : Continuous fun z : ℝ × ℝ => h (s - r, (x.1 - z.1, x.2 - z.2)) :=
    hcont.comp (by fun_prop)
  have i1 : Integrable (fun z : ℝ × ℝ => ((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
      (h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2)))) :=
    duhAI_intC hG (hc1.sub hc2) (M := K0 + K0) (fun z => by
      have h1 := norm_sub_le (h (s - r', (x.1 - z.1, x.2 - z.2))) (h (s - r, (x.1 - z.1, x.2 - z.2)))
      have h2 := hM0 (s - r', (x.1 - z.1, x.2 - z.2))
      have h3 := hM0 (s - r, (x.1 - z.1, x.2 - z.2))
      show ‖h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2))‖ ≤ K0 + K0
      linarith)
  have i2 : Integrable (fun z : ℝ × ℝ => ((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
      h (s - r, (x.1 - z.1, x.2 - z.2))) :=
    duhAI_intC hG hc2 (M := K0) (fun z => hM0 _)
  have hsplit : duhPhi ν h s x r' =
      (∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
        (h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2)))) +
      ∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
        h (s - r, (x.1 - z.1, x.2 - z.2)) := by
    unfold duhPhi
    rw [← integral_add i1 i2]
    congr 1; funext z; ring
  have hr0 : duhPhi ν h s x r = ∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
        h (s - r, (x.1 - z.1, x.2 - z.2)) := rfl
  simp only [slope, vsub_eq_sub, Complex.real_smul]
  rw [hsplit, hr0]
  ring

end UnforcedLeray.Short.IIIa
