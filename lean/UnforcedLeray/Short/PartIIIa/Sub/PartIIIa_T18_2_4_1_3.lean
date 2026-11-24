import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_1

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/3` (decomposition): `w_s - νΔw = h` for the Duhamel solution

Target (`Sub/T18_2_4_1.lean`): `DuhamelHeatEq`. Source of record:
`the November 2 reference manuscript`,
lines 3427-3440 (the Duhamel formula for the heat equation, "start from zero at `s = δ`, let
`δ ↓ 0`").

For fixed `(s, x)` put `φ(r) = (G_{νr} * h(s - r))(x)` (`duhPhi`), `A(r) = (G_{νr} * ∂_t h(s - r))(x)`
(`duhDt`) and `B(r) = (G_{νr} * Δh(s - r))(x)` (`duhLap`). The proof is:
`w_s = ∫_{r>0} A` and `Δw = ∫_{r>0} B` (differentiation under the integral sign, leaves `A`, `B`),
`φ' = νB - A` on `r > 0` (`∂_θ G_θ = ΔG_θ` and integration by parts, leaf `C`),
`φ(r) = 0` for `r > s - a` and `φ(r) → h(s,x)` as `r → 0⁺` (leaf `D`),
so `w_s - νΔw = -∫_0^∞ φ' = h(s,x)` (the abstract fundamental theorem, leaf `E`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `φ(r) = (G_{νr} * h(s - r))(x)`, the inner integral of `duhamelHeat`. -/
def duhPhi (ν : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ) (s : ℝ) (x : ℝ × ℝ) (r : ℝ) : ℂ :=
  ∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
    h (s - r, (x.1 - z.1, x.2 - z.2))

/-- `A(r) = (G_{νr} * ∂_t h(s - r))(x)`. -/
def duhDt (ν : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ) (s : ℝ) (x : ℝ × ℝ) (r : ℝ) : ℂ :=
  ∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
    deriv (fun t : ℝ => h (t, (x.1 - z.1, x.2 - z.2))) (s - r)

/-- `B(r) = (G_{νr} * Δ_x h(s - r))(x)`. -/
def duhLap (ν : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ) (s : ℝ) (x : ℝ × ℝ) (r : ℝ) : ℂ :=
  ∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
    lapC (fun y => h (s - r, y)) (x.1 - z.1, x.2 - z.2)

/-- **Leaf A** (SP 3427-3440): `s ↦ w(s, x)` is differentiable with derivative `∫_{r>0} A(r) dr`
(`A` integrable on `(0,∞)`). Differentiation under the integral sign: bounded derivatives of `h`,
unit mass of `G`, integrand vanishing for `r > S - a` when `s ≤ S`. -/
def DuhEqDt : Prop :=
  ∀ (c ν : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ), 0 < c → 0 < ν → NiceScalar c h → ∀ (s : ℝ) (x : ℝ × ℝ),
    IntegrableOn (fun r => duhDt ν h s x r) (Ioi 0) ∧
      HasDerivAt (fun s' => duhamelHeat ν h s' x) (∫ r in Ioi (0 : ℝ), duhDt ν h s x r) s

/-- **Leaf B** (SP 3427-3440): `Δ_x w(s, ·)(x) = ∫_{r>0} B(r) dr` (`B` integrable on `(0,∞)`).
Differentiation under the integral sign in `x` (use `duhamelSmooth` for the existence of the
derivatives; the derivatives fall on `h` after `z ↦ x - z`). -/
def DuhEqLap : Prop :=
  ∀ (c ν : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ), 0 < c → 0 < ν → NiceScalar c h → ∀ (s : ℝ) (x : ℝ × ℝ),
    IntegrableOn (fun r => duhLap ν h s x r) (Ioi 0) ∧
      lapC (fun y => duhamelHeat ν h s y) x = ∫ r in Ioi (0 : ℝ), duhLap ν h s x r

/-- **Leaf C** (SP 3427-3440): for `r > 0`, `φ'(r) = νB(r) - A(r)`; from
`UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative_eq_spatialLaplacian`
(`Lib/HeatCylinder/HeatKernelAgeLaplacian.lean:145`) and integration by parts
(`Lib/TrainB/P0GaussianSecondOrderIBP.lean:169`). -/
def DuhEqPhiDeriv : Prop :=
  ∀ (c ν : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ), 0 < c → 0 < ν → NiceScalar c h → ∀ (s : ℝ) (x : ℝ × ℝ)
    (r : ℝ), 0 < r →
    HasDerivAt (fun r' => duhPhi ν h s x r') ((ν : ℂ) * duhLap ν h s x r - duhDt ν h s x r) r

/-- **Leaf D** (SP 3427-3440): approximate identity, `φ(r) → h(s, x)` as `r → 0⁺` (unit mass of
`G_{νr}`, `h` continuous and bounded; `Units/B0418/HeatGen.lean:132`, `Units/B0284/Contraction.lean`). -/
def DuhEqApproxId : Prop :=
  ∀ (c ν : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ), 0 < c → 0 < ν → NiceScalar c h → ∀ (s : ℝ) (x : ℝ × ℝ),
    Tendsto (fun r => duhPhi ν h s x r) (𝓝[>] 0) (𝓝 (h (s, x)))

/-- **Leaf E** (abstract fundamental theorem of calculus on `(0, ∞)`): if `φ` has derivative `φ'`
on `r > 0` with `φ'` integrable, `φ = 0` beyond `T` and `φ(r) → v` as `r → 0⁺`, then
`∫_{r>0} φ' = -v`. (Mathlib: `integral_Ioi_of_hasDerivAt_of_tendsto`, after extending `φ` by `v`
at `0`, or cut at `ε` and let `ε → 0`.) -/
def DuhEqFTC : Prop :=
  ∀ (φ φ' : ℝ → ℂ) (T : ℝ) (v : ℂ), (∀ r, 0 < r → HasDerivAt φ (φ' r) r) →
    IntegrableOn φ' (Ioi 0) → (∀ r, T < r → φ r = 0) → Tendsto φ (𝓝[>] 0) (𝓝 v) →
    ∫ r in Ioi (0 : ℝ), φ' r = -v

/-- `φ(r) = 0` once `r > s - a`, because then `s - r < a` and the source vanishes. -/
theorem duhPhi_eq_zero {c : ℝ} {h : ℝ × (ℝ × ℝ) → ℂ} (hn : NiceScalar c h) (ν : ℝ) (s : ℝ)
    (x : ℝ × ℝ) : ∃ T : ℝ, ∀ r, T < r → duhPhi ν h s x r = 0 := by
  obtain ⟨-, -, a, B, R, ha, hz⟩ := hn
  refine ⟨s - a, fun r hr => ?_⟩
  unfold duhPhi
  have : ∀ z : ℝ × ℝ, h (s - r, (x.1 - z.1, x.2 - z.2)) = 0 := fun z =>
    hz _ _ (Or.inl (by linarith))
  simp [this]

/-- `DuhamelHeatEq` from the five leaves. -/
theorem duhamelHeatEq_of (hA : DuhEqDt) (hB : DuhEqLap) (hC : DuhEqPhiDeriv)
    (hD : DuhEqApproxId) (hE : DuhEqFTC) : DuhamelHeatEq := by
  intro c ν h hc hν hn s x
  obtain ⟨hAi, hAd⟩ := hA c ν h hc hν hn s x
  obtain ⟨hBi, hBl⟩ := hB c ν h hc hν hn s x
  obtain ⟨T, hT⟩ := duhPhi_eq_zero hn ν s x
  have hint : IntegrableOn (fun r => (ν : ℂ) * duhLap ν h s x r - duhDt ν h s x r) (Ioi 0) :=
    (hBi.const_mul (ν : ℂ)).sub hAi
  have hftc := hE (fun r => duhPhi ν h s x r)
    (fun r => (ν : ℂ) * duhLap ν h s x r - duhDt ν h s x r) T (h (s, x))
    (fun r hr => hC c ν h hc hν hn s x r hr) hint hT (hD c ν h hc hν hn s x)
  rw [integral_sub (hBi.const_mul (ν : ℂ)) hAi, integral_const_mul] at hftc
  show deriv (fun s' => duhamelHeat ν h s' x) s - (ν : ℂ) * lapC (fun y => duhamelHeat ν h s y) x
    = h (s, x)
  rw [hAd.deriv, hBl]
  linear_combination -hftc

end UnforcedLeray.Short.IIIa
