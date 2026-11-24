import UnforcedLeray.Short.PartI.Sub.T08_3
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrBasic.QcSmooth.Schwartz

/-!
# Part I, task `PartI:T08/3/1` (`pcSmoothDecay_proof`): the summed radial pressures

Source: `the November 2 reference manuscript` lines 326-329. `Train.pc ν c s` is
the periodization of the Gaussian `isoPressure = -a⁻³ e^{-|x|²/(2a)}`.

Smoothness: `isoPressure` is a Schwartz function (`QcSmoothAux.SchFn`), so
`Gaussian.contDiff_periodize` (with `s = 2`) applies. Decay: a lattice-sum bound for the Gaussian
at an arbitrary width `a` (the library's version needs `a ≤ c²`):
`∑ₙ e^{-(y-nc)²/(4a)} ≤ 2(1 + 4a/c²)`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Gaussian (tsum_int_le_of_le_two_sides summable_exp_neg_mul_nat
  tsum_exp_neg_mul_nat inv_one_sub_exp_neg_le)

namespace PcAux

/-- Gaussian lattice sum at an arbitrary width: summable and bounded, uniformly in `y`. -/
theorem gauss_shift_gen {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (y : ℝ) :
    Summable (fun n : ℤ => Real.exp (-(y - n * c) ^ 2 / (4 * a))) ∧
      ∑' n : ℤ, Real.exp (-(y - n * c) ^ 2 / (4 * a)) ≤ 2 * (1 + (c ^ 2 / (4 * a))⁻¹) := by
  set β : ℝ := c ^ 2 / (4 * a) with hβ
  have hβ0 : 0 < β := by positivity
  set N : ℤ := ⌈y / c⌉ with hN
  set f : ℤ → ℝ := fun n => Real.exp (-(y - n * c) ^ 2 / (4 * a)) with hf
  have hNy : y ≤ N * c := by
    have := Int.le_ceil (y / c); rwa [div_le_iff₀ hc] at this
  have hNy' : ((N : ℝ) - 1) * c < y := by
    have := Int.ceil_lt_add_one (y / c)
    rw [← sub_lt_iff_lt_add, lt_div_iff₀ hc] at this; exact this
  have hkey : ∀ (x : ℝ) (m : ℕ), (m : ℝ) * c ≤ |y - x| →
      Real.exp (-(y - x) ^ 2 / (4 * a)) ≤ Real.exp (-β * m) := by
    intro x m hm
    refine Real.exp_le_exp.2 ?_
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hsq : ((m : ℝ) * c) ^ 2 ≤ (y - x) ^ 2 := by
      rw [← sq_abs (y - x)]; exact pow_le_pow_left₀ (by positivity) hm 2
    have hmm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos m with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ m := by exact_mod_cast h
        nlinarith
    have h1 : (m : ℝ) * c ^ 2 ≤ (y - x) ^ 2 := by
      calc (m : ℝ) * c ^ 2 ≤ (m : ℝ) ^ 2 * c ^ 2 :=
            mul_le_mul_of_nonneg_right hmm (by positivity)
        _ = ((m : ℝ) * c) ^ 2 := by ring
        _ ≤ (y - x) ^ 2 := hsq
    have : -β * m = -((m : ℝ) * c ^ 2) / (4 * a) := by rw [hβ]; field_simp
    rw [this]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hshift : Summable (fun n : ℤ => f (N + n)) ∧ ∑' n : ℤ, f (N + n) ≤
      2 * ∑' m : ℕ, Real.exp (-β * m) := by
    refine tsum_int_le_of_le_two_sides (fun n => (Real.exp_pos _).le)
      (summable_exp_neg_mul_nat hβ0) (fun m => ?_) (fun m => ?_)
    · refine hkey _ m ?_
      push_cast
      have : (m : ℝ) * c ≤ (N + m) * c - y := by nlinarith
      rw [abs_sub_comm, abs_of_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) m])]
      linarith
    · refine hkey _ m ?_
      push_cast
      have hmc : (0 : ℝ) ≤ m * c := by positivity
      have : (m : ℝ) * c ≤ y - (N + -((m : ℝ) + 1)) * c := by nlinarith
      rw [abs_of_nonneg (by linarith)]
      exact this
  have hsum : Summable f := by
    have := hshift.1.comp_injective (add_right_injective (-N))
    refine this.congr fun n => ?_
    simp
  refine ⟨hsum, ?_⟩
  have heq : ∑' n : ℤ, f n = ∑' n : ℤ, f (N + n) :=
    ((Equiv.addLeft N).tsum_eq f).symm
  rw [heq]
  refine hshift.2.trans ?_
  rw [tsum_exp_neg_mul_nat hβ0]
  exact mul_le_mul_of_nonneg_left (inv_one_sub_exp_neg_le hβ0) (by norm_num)

/-- The isolated pressure is a Schwartz function. -/
theorem schFn_pExp {a : ℝ} (ha : 0 < a) : QcSmoothAux.SchFn (B0113.pExp a) := by
  have hg := QcSmoothAux.SchFn.gauss (b := a⁻¹ / 4) (by positivity)
  have e : ∀ z : Plane, B0113.gw a z = Real.exp (-(a⁻¹ / 4 * (z.1 ^ 2 + z.2 ^ 2))) := fun z => by
    unfold B0113.gw GaussianVortex.radiusSq
    congr 1; ring
  obtain ⟨s, hs⟩ := (hg.mul hg).const_mul (-(a⁻¹ ^ 3))
  refine ⟨s, ?_⟩
  rw [hs]; funext z
  simp only [B0113.pExp, e]

/-- Pointwise Gaussian bound for the isolated pressure. -/
theorem norm_pExp_le {a : ℝ} (ha : 0 < a) (z : Plane) :
    ‖B0113.pExp a z‖ ≤ a⁻¹ ^ 3 * (Real.exp (-z.2 ^ 2 / (4 * a)) *
      Real.exp (-z.1 ^ 2 / (4 * a))) := by
  have e : B0113.gw a z = Real.exp (-(a⁻¹ * (z.1 ^ 2 + z.2 ^ 2) / 4)) := by
    unfold B0113.gw GaussianVortex.radiusSq; rfl
  have hnn : 0 ≤ a⁻¹ ^ 3 := by positivity
  have h1 : ‖B0113.pExp a z‖ = a⁻¹ ^ 3 * (B0113.gw a z * B0113.gw a z) := by
    unfold B0113.pExp
    have hgw : 0 ≤ B0113.gw a z := by unfold B0113.gw; positivity
    rw [neg_mul, norm_neg, Real.norm_of_nonneg (mul_nonneg hnn (mul_nonneg hgw hgw))]
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ hnn
  rw [e, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hq : 0 ≤ z.1 ^ 2 := sq_nonneg _
  have hy : 0 ≤ z.2 ^ 2 := sq_nonneg _
  have : (a⁻¹ * (z.1 ^ 2 + z.2 ^ 2) / 4) = (z.1 ^ 2 + z.2 ^ 2) / (4 * a) := by
    field_simp
  have h2 : -(a⁻¹ * (z.1 ^ 2 + z.2 ^ 2) / 4) + -(a⁻¹ * (z.1 ^ 2 + z.2 ^ 2) / 4) =
      -(z.1 ^ 2 + z.2 ^ 2) / (2 * a) := by
    rw [this]; field_simp; ring
  rw [h2]
  have h3 : -z.2 ^ 2 / (4 * a) + -z.1 ^ 2 / (4 * a) = -(z.1 ^ 2 + z.2 ^ 2) / (4 * a) := by ring
  rw [h3]
  have : -(z.1 ^ 2 + z.2 ^ 2) / (2 * a) ≤ -(z.1 ^ 2 + z.2 ^ 2) / (4 * a) := by
    have hs : 0 ≤ z.1 ^ 2 + z.2 ^ 2 := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  exact this

end PcAux

theorem pcSmoothDecay_proof : UnforcedLeray.Short.PartI.PcSmoothDecay := by
  intro ν c s hν hc hs
  have hc0 : 0 < c := by linarith
  have ha : 0 < B0113.heatWidth ν s := B0113.heatWidth_pos hν hs
  set a := B0113.heatWidth ν s with hadef
  have hiso : Train.isoP ν s = B0113.pExp a := rfl
  have hsch := PcAux.schFn_pExp ha
  refine ⟨?_, ?_⟩
  · show ContDiff ℝ ∞ (Gaussian.periodize c (Train.isoP ν s))
    rw [hiso]
    exact Gaussian.contDiff_periodize (N := ⊤) (s := 2) (by norm_num) hc0.ne' hsch.contDiff
      (fun n _ => hsch.decay n)
  · -- decay
    set K : ℝ := 2 * (1 + (c ^ 2 / (4 * a))⁻¹) with hK
    have hbound : ∀ z : Plane, ‖Train.pc ν c s z‖ ≤
        a⁻¹ ^ 3 * K * Real.exp (-z.2 ^ 2 / (4 * a)) := by
      intro z
      have hmaj : ∀ n : ℤ, ‖Train.isoP ν s (z.1 - n * c, z.2)‖ ≤
          a⁻¹ ^ 3 * Real.exp (-z.2 ^ 2 / (4 * a)) *
            Real.exp (-(z.1 - n * c) ^ 2 / (4 * a)) := by
        intro n
        have h := PcAux.norm_pExp_le ha (z.1 - n * c, z.2)
        dsimp only at h
        rw [hiso]
        calc _ ≤ _ := h
          _ = _ := by ring
      obtain ⟨hsm, hle⟩ := PcAux.gauss_shift_gen ha hc0 z.1
      have hsmaj : Summable fun n : ℤ => a⁻¹ ^ 3 * Real.exp (-z.2 ^ 2 / (4 * a)) *
          Real.exp (-(z.1 - n * c) ^ 2 / (4 * a)) := hsm.mul_left _
      have hnorm : Summable fun n : ℤ => ‖Train.isoP ν s (z.1 - n * c, z.2)‖ :=
        Summable.of_nonneg_of_le (fun n => norm_nonneg _) hmaj hsmaj
      have hpos : 0 ≤ a⁻¹ ^ 3 * Real.exp (-z.2 ^ 2 / (4 * a)) := by positivity
      show ‖∑' n : ℤ, Train.isoP ν s (z.1 - n * c, z.2)‖ ≤ _
      refine (norm_tsum_le_tsum_norm hnorm).trans ?_
      refine (hnorm.tsum_le_tsum hmaj hsmaj).trans ?_
      rw [tsum_mul_left]
      calc a⁻¹ ^ 3 * Real.exp (-z.2 ^ 2 / (4 * a)) *
            ∑' n : ℤ, Real.exp (-(z.1 - n * c) ^ 2 / (4 * a))
          ≤ a⁻¹ ^ 3 * Real.exp (-z.2 ^ 2 / (4 * a)) * K :=
            mul_le_mul_of_nonneg_left hle hpos
        _ = _ := by ring
    have hg : Tendsto (fun t : ℝ => a⁻¹ ^ 3 * K * Real.exp (-t ^ 2 / (4 * a))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => -t ^ 2 / (4 * a)) atTop atBot := by
        have : Tendsto (fun t : ℝ => t ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
        have h2 := tendsto_neg_atTop_atBot.comp
          (this.atTop_mul_const (r := (4 * a)⁻¹) (by positivity))
        refine h2.congr fun t => ?_
        simp only [Function.comp]; field_simp
      have := (Real.tendsto_exp_atBot.comp h1).const_mul (a⁻¹ ^ 3 * K)
      simpa using this
    have habs : Tendsto (fun z : Plane => |z.2|) (comap (fun z : Plane => |z.2|) atTop) atTop :=
      tendsto_comap
    have hg' : Tendsto (fun z : Plane => a⁻¹ ^ 3 * K * Real.exp (-z.2 ^ 2 / (4 * a)))
        (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
      refine (hg.comp habs).congr fun z => ?_
      simp only [Function.comp, sq_abs]
    refine squeeze_zero_norm hbound hg'

end UnforcedLeray.Short.PartI
