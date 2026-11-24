import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_10
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_10.Translate
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_10.WeightShift

/-!
# `PDShiftBound`: the period shift for the weighted source integral

Source `the November 2 reference manuscript` 2667 (period `P = 2c/R`), 3631-3646.
The part `σ ∈ [τ₀, τ₀+ε)` is moved down by `m` whole periods `s = m·2c/R > ε` (`oldPhysPeriodic`
gives `srcNorm`-invariance), which lands in `σ < τ₀`; the weight changes by at most
`e^{(2μ+3)s/2}` (`srcWeight_shift`), and the time translation is `lintegral_shift_time`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem pdShiftBound : PDShiftBound := by
  unfold PDShiftBound
  intro μ R c g hR hc hμ hg τ₀ ε hε
  have hP : 0 < 2 * c / R := div_pos (by linarith) hR
  -- whole periods `m` with `ε < m · 2c/R`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ε < (m : ℝ) * (2 * c / R) := by
    obtain ⟨m, hm⟩ := exists_nat_gt (ε / (2 * c / R))
    exact ⟨m, by rwa [div_lt_iff₀ hP] at hm⟩
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = (m : ℝ) * (2 * c / R) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs_def]; exact mul_nonneg (Nat.cast_nonneg m) hP.le
  have hεs : ε < s := by rw [hs_def]; exact hm
  -- periodicity of `oldPhys` under whole periods
  have hpp : ∀ (R c : ℝ) (g : Chart → Ten3) (τ : ℝ) (z : Space),
      oldPhys R c g (τ + 2 * c / R) z = oldPhys R c g τ z := oldPhysPeriodic
  have hperiod : ∀ k : ℕ, ∀ (τ : ℝ) (z : Space),
      oldPhys R c g (τ + (k : ℝ) * (2 * c / R)) z = oldPhys R c g τ z := by
    intro k
    induction k with
    | zero => intro τ z; simp
    | succ k ih =>
      intro τ z
      rw [show τ + ((k + 1 : ℕ) : ℝ) * (2 * c / R) = (τ + (k : ℝ) * (2 * c / R)) + 2 * c / R by
        push_cast; ring]
      rw [hpp, ih]
  have hper_s : ∀ (σ : ℝ) (z : Space), oldPhys R c g (σ + s) z = oldPhys R c g σ z := by
    intro σ z
    rw [hs_def]
    exact hperiod m σ z
  have hN : ∀ (σ : ℝ) (z : Space),
      IIIa.srcNorm (oldPhys R c g) (σ + s) z = IIIa.srcNorm (oldPhys R c g) σ z := by
    intro σ z
    unfold IIIa.srcNorm
    rw [hper_s]
  have hsm := measurable_srcNorm' R c g hg
  have hWm : Measurable (fun e : ℝ × Space => ENNReal.ofReal (srcWeight μ (τ₀ - e.1) e.2)) := by
    refine Measurable.ennreal_ofReal ?_
    unfold srcWeight pdLam
    fun_prop
  -- the two pieces: `Fi` (the part `σ < τ₀`) and `Fr` (the part `σ ∈ [τ₀, τ₀+ε)`)
  set Fi : ℝ × Space → ℝ≥0∞ := fun e =>
    (if e.1 < τ₀ then ENNReal.ofReal (srcWeight μ (τ₀ - e.1) e.2) else 0) *
      IIIa.srcNorm (oldPhys R c g) e.1 e.2 with hFi
  set Fr : ℝ × Space → ℝ≥0∞ := fun e =>
    (if τ₀ ≤ e.1 ∧ e.1 < τ₀ + ε then ENNReal.ofReal (srcWeight μ (τ₀ - e.1) e.2) else 0) *
      IIIa.srcNorm (oldPhys R c g) e.1 e.2 with hFr
  have hFiM : Measurable Fi := by
    rw [hFi]
    refine Measurable.mul ?_ hsm
    exact Measurable.ite (measurableSet_lt measurable_fst measurable_const) hWm measurable_const
  -- pointwise split of the integrand
  have hA : ∀ e : ℝ × Space,
      (if e.1 < τ₀ + ε then ENNReal.ofReal (srcWeight μ (τ₀ - e.1) e.2) else 0) *
        IIIa.srcNorm (oldPhys R c g) e.1 e.2 ≤ Fi e + Fr e := by
    intro e
    rw [hFi, hFr]
    dsimp only
    by_cases h1 : e.1 < τ₀
    · have h2 : e.1 < τ₀ + ε := by linarith
      simp [h1, h2, not_le.mpr h1]
    · by_cases h2 : e.1 < τ₀ + ε
      · have h3 : τ₀ ≤ e.1 := not_lt.mp h1
        rw [if_neg h1, if_pos h2, if_pos ⟨h3, h2⟩]
        simp
      · rw [if_neg h1, if_neg h2]
        simp
  -- the shifted piece is bounded by the piece `σ < τ₀` with the weight factor
  have hC : ∫⁻ e : ℝ × Space, Fr e ≤
      ENNReal.ofReal (Real.exp ((2 * μ + 3) * (s / 2))) * ∫⁻ e : ℝ × Space, Fi e := by
    calc ∫⁻ e : ℝ × Space, Fr e = ∫⁻ e : ℝ × Space, Fr (e.1 + s, e.2) :=
          (lintegral_shift_time Fr s).symm
      _ ≤ ∫⁻ e : ℝ × Space, ENNReal.ofReal (Real.exp ((2 * μ + 3) * (s / 2))) * Fi e :=
          lintegral_mono (fun e => ?_)
      _ = ENNReal.ofReal (Real.exp ((2 * μ + 3) * (s / 2))) * ∫⁻ e : ℝ × Space, Fi e :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [hFr, hFi]
    dsimp only
    by_cases hcnd : τ₀ ≤ e.1 + s ∧ e.1 + s < τ₀ + ε
    · have h1 : e.1 < τ₀ := by linarith [hcnd.2]
      rw [if_pos hcnd, if_pos h1, hN]
      have hw : srcWeight μ (τ₀ - (e.1 + s)) e.2 ≤
          Real.exp ((2 * μ + 3) * (s / 2)) * srcWeight μ (τ₀ - e.1) e.2 := by
        have := srcWeight_shift μ hμ (τ₀ - e.1) s hs0 e.2
        rw [show τ₀ - (e.1 + s) = τ₀ - e.1 - s by ring]
        exact this
      have hw' : ENNReal.ofReal (srcWeight μ (τ₀ - (e.1 + s)) e.2) ≤
          ENNReal.ofReal (Real.exp ((2 * μ + 3) * (s / 2))) *
            ENNReal.ofReal (srcWeight μ (τ₀ - e.1) e.2) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        exact ENNReal.ofReal_le_ofReal hw
      calc ENNReal.ofReal (srcWeight μ (τ₀ - (e.1 + s)) e.2) *
            IIIa.srcNorm (oldPhys R c g) e.1 e.2
          ≤ (ENNReal.ofReal (Real.exp ((2 * μ + 3) * (s / 2))) *
              ENNReal.ofReal (srcWeight μ (τ₀ - e.1) e.2)) *
                IIIa.srcNorm (oldPhys R c g) e.1 e.2 := by gcongr
        _ = ENNReal.ofReal (Real.exp ((2 * μ + 3) * (s / 2))) *
              (ENNReal.ofReal (srcWeight μ (τ₀ - e.1) e.2) *
                IIIa.srcNorm (oldPhys R c g) e.1 e.2) := by ring
    · rw [if_neg hcnd]
      simp
  -- conclusion
  refine ⟨1 + ENNReal.ofReal (Real.exp ((2 * μ + 3) * (s / 2))),
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩, ?_⟩
  calc ∫⁻ e : ℝ × Space, (if e.1 < τ₀ + ε then ENNReal.ofReal (srcWeight μ (τ₀ - e.1) e.2)
        else 0) * IIIa.srcNorm (oldPhys R c g) e.1 e.2
      ≤ ∫⁻ e : ℝ × Space, (Fi e + Fr e) := lintegral_mono hA
    _ = (∫⁻ e : ℝ × Space, Fi e) + (∫⁻ e : ℝ × Space, Fr e) := lintegral_add_left hFiM _
    _ ≤ (∫⁻ e : ℝ × Space, Fi e) +
          (ENNReal.ofReal (Real.exp ((2 * μ + 3) * (s / 2))) * ∫⁻ e : ℝ × Space, Fi e) :=
          add_le_add (le_refl _) hC
    _ = (1 + ENNReal.ofReal (Real.exp ((2 * μ + 3) * (s / 2)))) *
          ∫⁻ e : ℝ × Space, Fi e := by ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
