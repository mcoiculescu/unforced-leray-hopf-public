import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_2
import UnforcedLeray.Short.PartIIb.Sub.T22.CylDecayBridge
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.Common

/-!
# Part II-b, task `PartII-b:T22/2/2/7`: the tested right-hand side is bounded (`rtdRhsBound`)

Source of record: `the November 2 reference manuscript`, lines 2074-2105.
On the cell the integrand `ω r x * (∂_r φ + ν Δφ + v·∇φ)` is bounded pointwise by
`K * jb^(-4)`, with `K = |C₁| (|C_d| + |ν| |C₂| + |M| |C₂|)`: the decay of `ω` with exponent `4`
on the strip `|q| ≤ c/2`, the uniform bound on `∂_r φ` (`N = 0`), the decay of `φ` (`N = 0`) and
the velocity bound. `jb^(-4)` is integrable on the plane, so the cell integral is bounded by its
integral.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

theorem rtdRhsBound : UnforcedLeray.Short.IIb.RtdRhsBound := by
  intro ν c tr s T t₁ ω φ hc hst htT hω hφ hφr hMv
  obtain ⟨M, hM⟩ := hMv
  obtain ⟨C1, hC1⟩ := hω.cell_decay 4
  obtain ⟨C2, hC2⟩ := hφ.decay 0
  obtain ⟨Cd, hCd⟩ := hφr 0
  have hsub : Icc s t₁ ⊆ Icc s T := fun r hr => ⟨hr.1, hr.2.trans htT⟩
  -- pointwise bound on ω, on the strip |q| ≤ c/2
  have hωb : ∀ r ∈ Icc s t₁, ∀ x : B0579.Plane, |x.1| ≤ c / 2 →
      |ω r x| ≤ |C1| * B0579.jb x ^ (-4 : ℝ) := by
    intro r hr x hx
    have h := hC1 r (hsub hr) x hx
    have hpos : 0 < B0579.jb x ^ (4 : ℝ) := Real.rpow_pos_of_pos (B0579.jb_pos x) _
    have hneg : B0579.jb x ^ (-4 : ℝ) = (B0579.jb x ^ (4 : ℝ))⁻¹ :=
      Real.rpow_neg (B0579.jb_pos x).le 4
    have h0 : |ω r x| ≤ |ω r x| + |B0579.pd 0 (ω r) x| + |B0579.pd 1 (ω r) x|
        + |lapP (ω r) x| := by
      linarith [abs_nonneg (B0579.pd 0 (ω r) x), abs_nonneg (B0579.pd 1 (ω r) x),
        abs_nonneg (lapP (ω r) x)]
    have h1 : |ω r x| * B0579.jb x ^ (4 : ℝ) ≤ C1 :=
      le_trans (mul_le_mul_of_nonneg_right h0 hpos.le) h
    rw [hneg, ← div_eq_mul_inv, le_div_iff₀ hpos]
    linarith [le_abs_self C1]
  -- pointwise bounds on φ, its derivatives and its Laplacian
  have hφb : ∀ r ∈ Icc s t₁, ∀ x : B0579.Plane,
      |φ r x| ≤ |C2| ∧ |B0579.pd 0 (φ r) x| ≤ |C2| ∧ |B0579.pd 1 (φ r) x| ≤ |C2| ∧
        |lapP (φ r) x| ≤ |C2| := by
    intro r hr x
    have h := hC2 r hr x
    rw [Real.rpow_zero, mul_one] at h
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      linarith [le_abs_self C2, abs_nonneg (B0579.pd 0 (φ r) x), abs_nonneg (B0579.pd 1 (φ r) x),
        abs_nonneg (lapP (φ r) x), abs_nonneg (φ r x)]
  refine ⟨∫ x in B0579.cell c, |C1| * (|Cd| + |ν| * |C2| + |M| * |C2|) *
      B0579.jb x ^ (-4 : ℝ), fun r hr => ?_⟩
  have hrs : r ∈ Icc s t₁ := ⟨hr.1.le, hr.2.le⟩
  have hrT : r ∈ Icc s T := hsub hrs
  have hbound : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      ‖ω r x * (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
          (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x))‖ ≤
        |C1| * (|Cd| + |ν| * |C2| + |M| * |C2|) * B0579.jb x ^ (-4 : ℝ) := by
    refine ae_restrict_of_forall_mem (B0579.measurableSet_cell c) fun x hx => ?_
    have hx' := abs_fst_le_of_mem_cell hx
    have hw := hωb r hrs x hx'
    obtain ⟨hf0, hf1, hf2, hf3⟩ := hφb r hrs x
    -- the derivative in the age
    have hD : |deriv (fun r' => φ r' x) r| ≤ |Cd| := by
      have h := hCd r hr x
      rw [Real.rpow_zero, mul_one] at h
      linarith [le_abs_self Cd]
    -- the velocity
    have hv : |tr.v r x 0| + |tr.v r x 1| ≤ |M| := by
      linarith [le_abs_self M, hM r hrT x]
    have hv0 : 0 ≤ |C2| := abs_nonneg _
    have hL : |ν * lapP (φ r) x| ≤ |ν| * |C2| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hf3 (abs_nonneg _)
    have hT0 : |tr.v r x 0 * B0579.pd 0 (φ r) x| ≤ |tr.v r x 0| * |C2| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hf1 (abs_nonneg _)
    have hT1 : |tr.v r x 1 * B0579.pd 1 (φ r) x| ≤ |tr.v r x 1| * |C2| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hf2 (abs_nonneg _)
    have hVsum : |tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x| ≤
        |M| * |C2| := by
      have h1 := abs_add_le (tr.v r x 0 * B0579.pd 0 (φ r) x) (tr.v r x 1 * B0579.pd 1 (φ r) x)
      have h2 : (|tr.v r x 0| + |tr.v r x 1|) * |C2| ≤ |M| * |C2| :=
        mul_le_mul_of_nonneg_right hv hv0
      linarith
    have hS : |deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
        (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x)| ≤
        |Cd| + |ν| * |C2| + |M| * |C2| := by
      have h1 := abs_add_le (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x)
        (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x)
      have h2 := abs_add_le (deriv (fun r' => φ r' x) r) (ν * lapP (φ r) x)
      linarith
    rw [Real.norm_eq_abs, abs_mul]
    have hJ : 0 ≤ B0579.jb x ^ (-4 : ℝ) := Real.rpow_nonneg (B0579.jb_pos x).le _
    calc |ω r x| * |deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
          (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x)|
        ≤ (|C1| * B0579.jb x ^ (-4 : ℝ)) * (|Cd| + |ν| * |C2| + |M| * |C2|) :=
          mul_le_mul hw hS (abs_nonneg _) (mul_nonneg (abs_nonneg _) hJ)
      _ = |C1| * (|Cd| + |ν| * |C2| + |M| * |C2|) * B0579.jb x ^ (-4 : ℝ) := by ring
  have hint : Integrable (fun x : B0579.Plane =>
      |C1| * (|Cd| + |ν| * |C2| + |M| * |C2|) * B0579.jb x ^ (-4 : ℝ))
      (volume.restrict (B0579.cell c)) :=
    (DbCommon.integrable_jb_neg4.const_mul (|C1| * (|Cd| + |ν| * |C2| + |M| * |C2|))).integrableOn
  have := norm_integral_le_of_norm_le hint hbound
  rw [Real.norm_eq_abs] at this
  exact this

end UnforcedLeray.Short.IIb
