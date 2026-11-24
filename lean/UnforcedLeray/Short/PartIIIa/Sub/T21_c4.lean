import UnforcedLeray.Short.PartIIIa.Clock.Moving

/-!
# Part III-a, task `PartIII-a:T21/c4`: the scalar budget `AmplitudeGronwall` from two integrals

Source: `the November 2 reference manuscript` lines 2998-3016.

`a` is the normalised amplitude, `ρ` the normalised complement, `A_* = ⨆_{[t,s]} a` the running
maximum (SP 3002-3004, finite by hypothesis). With `θ = clockTheta ν r = (ν A)⁻¹`,
`A = clockA ν r = 1 + νr` and `dz = A⁻² dr` (SP 2855):

* `AmplKernelBudget` (leaf `T21/c4/2`): the closed amplitude kernel
  `A⁻²(δ + c·Cη)`, `δ = Cν³/θ`, `c = C(θ⁻¹ + δ)`, `η = C(1+ν³)/θ` (SP 2998-3001), has total
  integral `≤ K₀/b` on `[t,s]` (the displayed budget of SP 3011-3015; it equals
  `Cν⁴/A + C³ν²(1+Cν³)(1+ν³) ≤ K₀ν²`, and `ν²s ≤ 1/b` from `b ≤ θ(s)`).
* `AmplCouplingBudget` (leaf `T21/c4/3`): the initial-complement coupling
  `∫ A⁻² c C e^{-h₀(z-z_t)} dr ≤ K₁` (SP 3005-3008: "integrable with bound `C‖r(t)‖/b`").
* `MovingExpIntegral` (leaf `T21/c4/1`): `∫_t^s A⁻² e^{-h₀(z(r)-z(t))} dr ≤ 1/h₀`, since
  `dz/dr = A⁻²` (input of `T21/c4/3`).

`amplitudeGronwall_of`: substituting the complement bound into the amplitude inequality gives
`A_* ≤ a(t) + (K₀/b) A_* + K₁ ρ(t)`; for `b ≥ 2K₀` this absorbs (`A_* < ⊤`), so
`A_* ≤ 2(a(t) + K₁ρ(t))` (the scalar Gronwall of SP 3011 with a small budget), and then
`ρ(s) ≤ Cρ(t) + Cη(s)A_*` with `Cη(s) ≤ 2C²/b ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- `∫_t^s a(r)⁻² e^{-h₀(z(r)-z(t))} dr ≤ 1/h₀` for `z = movingZ ν`, `dz/dr = clockA⁻²`
(SP 2855; used for the initial-complement coupling, SP 3005-3008). -/
def MovingExpIntegral : Prop :=
  ∀ ν h₀ t s : ℝ, 0 < ν → 0 < h₀ → 0 ≤ t → t ≤ s →
    ∫⁻ r in Ioc t s, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) *
        Real.exp (-h₀ * (movingZ ν r - movingZ ν t))) ≤ ENNReal.ofReal (1 / h₀)

/-- **Closed amplitude kernel budget** (SP 2998-3001, 3011-3015): with `δ = Cν³/θ`,
`c = C(θ⁻¹ + δ)`, `η = C(1+ν³)/θ`, `∫_t^s a⁻²(δ + c·Cη) dr ≤ K₀/b` when `b ≤ θ(s)`, `ν ≤ 1`. -/
def AmplKernelBudget : Prop :=
  ∀ C : ℝ, 0 < C → ∃ K₀ : ℝ, ∀ b : ℝ, 1 ≤ b → ∀ ν ∈ Ioc (0 : ℝ) 1, ∀ t s : ℝ, 0 ≤ t → t ≤ s →
    b ≤ clockTheta ν s →
      ∫⁻ r in Ioc t s, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
        (ENNReal.ofReal (C * ν ^ 3 / clockTheta ν r) +
          ENNReal.ofReal (C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r)) *
            ENNReal.ofReal (C * (C * (1 + ν ^ 3) / clockTheta ν r))) ≤ ENNReal.ofReal (K₀ / b)

/-- **Initial-complement coupling budget** (SP 3005-3008): `∫_t^s a⁻² c · C e^{-h₀(z-z_t)} dr ≤ K₁`
with `c = C(θ⁻¹ + Cν³/θ)`, when `1 ≤ b ≤ θ(s)`, `ν ≤ 1`. -/
def AmplCouplingBudget : Prop :=
  ∀ C h₀ : ℝ, 0 < C → 0 < h₀ → ∃ K₁ : ℝ, ∀ b : ℝ, 1 ≤ b → ∀ ν ∈ Ioc (0 : ℝ) 1, ∀ t s : ℝ,
    0 ≤ t → t ≤ s → b ≤ clockTheta ν s →
      ∫⁻ r in Ioc t s, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
        (ENNReal.ofReal (C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r)) *
          ENNReal.ofReal (C * Real.exp (-h₀ * (movingZ ν r - movingZ ν t)))) ≤ ENNReal.ofReal K₁

/-- `z = s/a(s)` is nondecreasing on the ages `s ≥ 0`. -/
theorem movingZ_le_movingZ {ν t s : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hts : t ≤ s) :
    movingZ ν t ≤ movingZ ν s := by
  unfold movingZ clockA
  have hs : 0 ≤ s := ht.trans hts
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hν.le ht, mul_le_mul_of_nonneg_left hts (mul_nonneg hν.le ht)]

/-- The scalar budget from the two integral bounds. -/
theorem amplitudeGronwall_of (hK : AmplKernelBudget) (hP : AmplCouplingBudget) :
    AmplitudeGronwall := by
  intro C h₀ hh hC
  obtain ⟨K₀, hK₀⟩ := hK C hC
  obtain ⟨K₁, hK₁⟩ := hP C h₀ hC hh
  refine ⟨4 + 4 * max K₁ 0 + C, max 1 (max (2 * K₀) (2 * C ^ 2)), fun b hb => ⟨1, one_pos, ?_⟩⟩
  intro ν hν t s ht hts hθ a ρ hfin_pt _ _ hfin hamp hcomp
  have hb1 : 1 ≤ b := le_trans (le_max_left _ _) hb
  have hbK : 2 * K₀ ≤ b := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hb
  have hbC : 2 * C ^ 2 ≤ b := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hb
  have hbpos : 0 < b := by linarith
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := hν.2
  have hρt : ρ t ≠ ⊤ := (hfin_pt t ⟨le_rfl, hts⟩).2
  set Astar : ℝ≥0∞ := ⨆ r ∈ Icc t s, a r with hAstar
  -- the two kernels
  let k : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
    (ENNReal.ofReal (C * ν ^ 3 / clockTheta ν r) +
      ENNReal.ofReal (C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r)) *
        ENNReal.ofReal (C * (C * (1 + ν ^ 3) / clockTheta ν r)))
  let p : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
    (ENNReal.ofReal (C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r)) *
      ENNReal.ofReal (C * Real.exp (-h₀ * (movingZ ν r - movingZ ν t))))
  have hkint : ∫⁻ r in Ioc t s, k r ≤ ENNReal.ofReal (K₀ / b) := hK₀ b hb1 ν hν t s ht hts hθ
  have hpint : ∫⁻ r in Ioc t s, p r ≤ ENNReal.ofReal K₁ := hK₁ b hb1 ν hν t s ht hts hθ
  have hkhalf : ENNReal.ofReal (K₀ / b) ≤ 2⁻¹ := by
    calc ENNReal.ofReal (K₀ / b) ≤ ENNReal.ofReal (2⁻¹) := by
          apply ENNReal.ofReal_le_ofReal
          rw [div_le_iff₀ hbpos]
          linarith
      _ = 2⁻¹ := by rw [ENNReal.ofReal_inv_of_pos two_pos]; simp
  have hkm : Measurable k := by
    simp only [k, clockTheta, clockA]
    fun_prop
  -- pointwise bound of the amplitude integrand
  have hpt : ∀ r ∈ Ioc t s,
      ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
          (ENNReal.ofReal (C * ν ^ 3 / clockTheta ν r) * a r +
            ENNReal.ofReal (C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r)) * ρ r) ≤
        k r * Astar + p r * ρ t := by
    intro r hr
    have hrI : r ∈ Icc t s := ⟨hr.1.le, hr.2⟩
    have har : a r ≤ Astar := le_biSup a hrI
    have hsup : (⨆ r' ∈ Icc t r, a r') ≤ Astar :=
      biSup_mono fun x hx => ⟨hx.1, hx.2.trans hr.2⟩
    have hρr := hcomp r hrI
    calc ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
          (ENNReal.ofReal (C * ν ^ 3 / clockTheta ν r) * a r +
            ENNReal.ofReal (C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r)) * ρ r)
        ≤ ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
          (ENNReal.ofReal (C * ν ^ 3 / clockTheta ν r) * Astar +
            ENNReal.ofReal (C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r)) *
              (ENNReal.ofReal (C * Real.exp (-h₀ * (movingZ ν r - movingZ ν t))) * ρ t +
                ENNReal.ofReal (C * (C * (1 + ν ^ 3) / clockTheta ν r)) * Astar)) := by
          gcongr
          exact hρr.trans (by gcongr)
      _ = k r * Astar + p r * ρ t := by simp only [k, p]; ring
  -- the integral bound
  have hint : ∫⁻ r in Ioc t s, (k r * Astar + p r * ρ t) =
      (∫⁻ r in Ioc t s, k r) * Astar + (∫⁻ r in Ioc t s, p r) * ρ t := by
    rw [lintegral_add_left (hkm.mul_const _), lintegral_mul_const' _ _ hfin,
      lintegral_mul_const' _ _ hρt]
  have hX : Astar ≤ Astar / 2 + (a t + ENNReal.ofReal K₁ * ρ t) := by
    refine iSup₂_le fun s'' hs'' => ?_
    calc a s'' ≤ a t + ∫⁻ r in Ioc t s'', ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
          (ENNReal.ofReal (C * ν ^ 3 / clockTheta ν r) * a r +
            ENNReal.ofReal (C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r)) * ρ r) :=
          hamp s'' hs''
      _ ≤ a t + ∫⁻ r in Ioc t s, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
          (ENNReal.ofReal (C * ν ^ 3 / clockTheta ν r) * a r +
            ENNReal.ofReal (C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r)) * ρ r) := by
          exact add_le_add le_rfl (lintegral_mono_set (Ioc_subset_Ioc_right hs''.2))
      _ ≤ a t + ∫⁻ r in Ioc t s, (k r * Astar + p r * ρ t) := by
          exact add_le_add le_rfl (setLIntegral_mono' measurableSet_Ioc hpt)
      _ = a t + ((∫⁻ r in Ioc t s, k r) * Astar + (∫⁻ r in Ioc t s, p r) * ρ t) := by
          rw [hint]
      _ ≤ a t + (2⁻¹ * Astar + ENNReal.ofReal K₁ * ρ t) := by
          gcongr
          exact hkint.trans hkhalf
      _ = Astar / 2 + (a t + ENNReal.ofReal K₁ * ρ t) := by
          rw [ENNReal.div_eq_inv_mul]; ring
  have hA2 : Astar ≤ 2 * (a t + ENNReal.ofReal K₁ * ρ t) := by
    have h1 : Astar / 2 ≤ a t + ENNReal.ofReal K₁ * ρ t := by
      rw [← ENNReal.sub_half hfin]
      exact tsub_le_iff_left.mpr hX
    rw [ENNReal.div_le_iff (by norm_num) (by norm_num)] at h1
    rw [mul_comm]; exact h1
  -- the endpoint
  have has : a s ≤ Astar := le_biSup a (⟨hts, le_rfl⟩ : s ∈ Icc t s)
  have hexp : ENNReal.ofReal (C * Real.exp (-h₀ * (movingZ ν s - movingZ ν t))) ≤
      ENNReal.ofReal C := by
    apply ENNReal.ofReal_le_ofReal
    have hz := movingZ_le_movingZ hν0 ht hts
    have : Real.exp (-h₀ * (movingZ ν s - movingZ ν t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    nlinarith
  have heta : ENNReal.ofReal (C * (C * (1 + ν ^ 3) / clockTheta ν s)) ≤ 1 := by
    rw [ENNReal.ofReal_le_one]
    have hθpos : 0 < clockTheta ν s := hbpos.trans_le hθ
    have hν3 : ν ^ 3 ≤ 1 := pow_le_one₀ hν0.le hν1
    rw [← mul_div_assoc, div_le_one hθpos]
    nlinarith [sq_nonneg C]
  have hρs : ρ s ≤ ENNReal.ofReal C * ρ t + Astar := by
    calc ρ s ≤ ENNReal.ofReal (C * Real.exp (-h₀ * (movingZ ν s - movingZ ν t))) * ρ t +
          ENNReal.ofReal (C * (C * (1 + ν ^ 3) / clockTheta ν s)) * ⨆ r ∈ Icc t s, a r :=
          hcomp s ⟨hts, le_rfl⟩
      _ ≤ ENNReal.ofReal C * ρ t + 1 * Astar := by gcongr
      _ = ENNReal.ofReal C * ρ t + Astar := by rw [one_mul]
  have hK1 : ENNReal.ofReal K₁ ≤ ENNReal.ofReal (max K₁ 0) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  calc a s + ρ s ≤ Astar + (ENNReal.ofReal C * ρ t + Astar) := add_le_add has hρs
    _ = 2 * Astar + ENNReal.ofReal C * ρ t := by ring
    _ ≤ 2 * (2 * (a t + ENNReal.ofReal (max K₁ 0) * ρ t)) + ENNReal.ofReal C * ρ t := by
        gcongr
        exact hA2.trans (by gcongr)
    _ ≤ (4 * a t + 4 * ENNReal.ofReal (max K₁ 0) * ρ t + ENNReal.ofReal C * ρ t) +
        (4 * ρ t + 4 * ENNReal.ofReal (max K₁ 0) * a t + ENNReal.ofReal C * a t) := by
        rw [show (2 : ℝ≥0∞) * (2 * (a t + ENNReal.ofReal (max K₁ 0) * ρ t)) =
          4 * a t + 4 * ENNReal.ofReal (max K₁ 0) * ρ t by ring]
        exact le_self_add
    _ = (4 + 4 * ENNReal.ofReal (max K₁ 0) + ENNReal.ofReal C) * (a t + ρ t) := by ring
    _ = ENNReal.ofReal (4 + 4 * max K₁ 0 + C) * (a t + ρ t) := by
        rw [ENNReal.ofReal_add (by positivity) hC.le, ENNReal.ofReal_add (by norm_num)
          (by positivity), ENNReal.ofReal_mul (by norm_num)]
        simp

end UnforcedLeray.Short.IIIa
