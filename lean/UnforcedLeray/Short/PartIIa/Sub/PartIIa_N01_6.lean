import UnforcedLeray.Short.PartIIa.Sub.N01.Defs
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1
import UnforcedLeray.Short.PartIIa.Sub.F13

/-!
# `PartII-a:N01/6` (`CartLiftNorm`) reduced to the slab-Frobenius identity

Source `the November 2 reference manuscript`
lines 1644-1648 (`T ↦ sT` multiplies norms by `√π R`), 1639-1643 (chart).

`cartLiftNorm_of (h : SlabFrobIdentity) : CartLiftNorm`; the identity `SlabFrobIdentity` (the change
of variables `x = εz` to the chart over one period, with the exact constant `2π/(Pε)`) is the leaf.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart Ten3)
open UnforcedLeray.Short.PartIIIb.NearInst (tv4 cartLift nsSym symRZ)

/-- Squared Frobenius norm of the symmetric axisymmetric part `nsSym T` of a chart tensor. -/
def frob2 (T : Ten3) : ℝ := ∑ a : Fin 3, ∑ b : Fin 3, (nsSym T a b) ^ 2

/-- **Slab-Frobenius identity** (lines 1644-1648; `R = ε⁻¹`, `P = 2εc`; cylindrical coordinates
`ds dq dη = s² dτ dρ dz₃`, `ρ = R s^{-1/2}`, `dz = 2π ρ dρ dφ dz₃`, `q` covers one cell of length
`RP/2 = c` as `τ` runs over one period): `‖𝒩_T m‖²_{Y₂(Sym₃)} = (2π/(Pε)) ∫ |nsSym m|_F² s^{-1/2}
ds dq dη` (`measureHT c` is `s^{-1/2} ds dq dη` on the cell, unnormalised). -/
def SlabFrobIdentity : Prop :=
  ∀ (ε c P : ℝ) [Fact (0 < P)], 0 < ε → 0 < c → P = 2 * ε * c → ∀ m : Chart → Ten3,
    IsTensorTest c (fun p => tv4 (m p)) →
      ‖smoothTensor P (cartRowsC (cartLift ε⁻¹ c m))‖ ^ 2 =
        2 * Real.pi / (P * ε) * ∫ p, frob2 (m p) ∂(measureHT c)

/-- Pointwise: `|nsSym T|_F² = ‖tv4 T‖² + |symRZ T|²  ≤  2 ‖tv4 T‖²`. -/
theorem frob2_le (T : Ten3) : frob2 T ≤ 2 * ‖tv4 T‖ ^ 2 := by
  have hn : ‖tv4 T‖ ^ 2 = T (0, 0) ^ 2 + symRZ T ^ 2 + T (2, 2) ^ 2 + T (1, 1) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [tv4, Fin.sum_univ_four]
  have hf : frob2 T = T (0, 0) ^ 2 + T (1, 1) ^ 2 + T (2, 2) ^ 2 + 2 * symRZ T ^ 2 := by
    simp [frob2, nsSym, Fin.sum_univ_three]
    ring
  rw [hf, hn]
  nlinarith [sq_nonneg (symRZ T), sq_nonneg (T (0, 0)), sq_nonneg (T (1, 1)),
    sq_nonneg (T (2, 2))]

/-- `‖F‖² = ∫ ‖F‖² d measureHT`, for the representative `tv4 ∘ m`. -/
theorem normSq_HT (c : ℝ) (m : Chart → Ten3) (F : HTSpace c)
    (hF : (F : Profile → TensorVal) =ᵐ[measureHT c] (fun p => tv4 (m p))) :
    ‖F‖ ^ 2 = ∫ p, ‖tv4 (m p)‖ ^ 2 ∂(measureHT c) := by
  have h1 : ((‖F‖ ^ 2 : ℝ) : ℂ) = ∫ a, (((‖F a‖ ^ 2 : ℝ)) : ℂ) ∂(measureHT c) := by
    have := MeasureTheory.L2.inner_def (𝕜 := ℂ) F F
    rw [inner_self_eq_norm_sq_to_K] at this
    simpa [inner_self_eq_norm_sq_to_K] using this
  have h2 : ((‖F‖ ^ 2 : ℝ) : ℂ) = ((∫ a, ‖F a‖ ^ 2 ∂(measureHT c) : ℝ) : ℂ) := by
    rw [h1]; exact integral_complex_ofReal
  have h3 := Complex.ofReal_injective h2
  rw [h3]
  refine integral_congr_ae ?_
  filter_upwards [hF] with p hp
  rw [hp]

/-! ## Leaves of `SlabFrobIdentity` (tasks `PartII-a:N01/6/1` … `/4`; `/5` assembles) -/

open UnforcedLeray.Short.PartIIIb.NearInst (chartOf)

/-- **`/1` pointwise Frobenius identity of the lift** (source 1644-1648, 2683; `cylFrame z` is an
orthogonal matrix off the axis, and on the axis `s = R²/0 = 0` and the frame is `0`, so both sides
vanish): `Σ_{ij} (cartLift R c m τ z)_{ij}² = s² |nsSym (m (chartOf R c z τ))|_F²`,
`s = (chartOf R c z τ).1`. -/
def SlabFrobPointwise : Prop :=
  ∀ (R c : ℝ) (m : Chart → Ten3) (τ : ℝ) (z : UnforcedLeray.Space),
    ∑ i : Fin 3, ∑ j : Fin 3, (cartLift R c m τ z i j) ^ 2 =
      (chartOf R c z τ).1 ^ 2 * frob2 (m (chartOf R c z τ))

/-- **`/2` change of variables over one period with the age weight** (source 2666-2668, 2684-2687;
`ChartPhaseLIntegral` for `F p = ofReal (p.1 ^ 2) * G p`, then `AgeWeightShift`). -/
def ChartPhaseFrob : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c → ∀ G : Chart → ℝ≥0∞, Measurable G →
    ∫⁻ τ in Ioc 0 (2 * c / R), ∫⁻ z : UnforcedLeray.Space,
        ENNReal.ofReal ((chartOf R c z τ).1 ^ 2) * G (chartOf R c z τ) =
      ENNReal.ofReal (2 * c / R) * ENNReal.ofReal (Real.pi * R ^ 2) *
        ∫⁻ p, G p ∂(UnforcedLeray.Axi.ageμ c (-1 / 2))

/-- **`/3` the age cell measure versus `measureHT`** (`ageμ c (-1/2) = s^{-1/2} ds ⊗ c⁻¹ dq dη` on
the centred cell `[-c/2, c/2)`, `measureHT c = s^{-1/2} ds dq dη` on `(0, c]`; a measurable
`q`-`c`-periodic integrand has the same integral over both cells). -/
def AgeCellTransfer : Prop :=
  ∀ c : ℝ, 0 < c → ∀ G : Chart → ℝ≥0∞, Measurable G →
    (∀ p : Chart, G (p.1, p.2.1 + c, p.2.2) = G p) →
      ∫⁻ p, G p ∂(UnforcedLeray.Axi.ageμ c (-1 / 2)) =
        ENNReal.ofReal c⁻¹ * ∫⁻ p, G p ∂(measureHT c)

/-- **`/4` slab inner product as an iterated lintegral** (Tonelli; a phase test is continuous with
bounded support): `Σ_i Re slabInner P (rows i) (rows i) = ∫_0^P ∫ Σ_{ij} T_{ij}²`. -/
def SlabToLintegral : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (T : ℝ → UnforcedLeray.Space → Matrix (Fin 3) (Fin 3) ℝ),
    (∀ i, IsPhaseTest P (cartRowsC T i)) →
      ENNReal.ofReal (∑ i : Fin 3, (slabInner P (cartRowsC T i) (cartRowsC T i)).re) =
        ∫⁻ τ in Ioc 0 P, ∫⁻ z : UnforcedLeray.Space,
          ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3, (T τ z i j) ^ 2)

theorem cartLiftNorm_of (h : SlabFrobIdentity) : CartLiftNorm := by
  intro ε c P _ hε hc hP m hm F hF
  have hPpos : 0 < P := by rw [hP]; positivity
  have hPe : 0 < P * ε := by positivity
  have hid := h ε c P hε hc hP m hm
  have hle : ∫ p, frob2 (m p) ∂(measureHT c) ≤ 2 * ‖F‖ ^ 2 := by
    have hFi : Integrable (fun p => ‖tv4 (m p)‖ ^ 2) (measureHT c) := by
      have hL : MemLp (F : Profile → TensorVal) 2 (measureHT c) := Lp.memLp F
      have h2 : Integrable (fun p => ‖(F : Profile → TensorVal) p‖ ^ 2) (measureHT c) := by
        simpa using hL.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
      refine h2.congr ?_
      filter_upwards [hF] with p hp
      rw [hp]
    rw [normSq_HT c m F hF, ← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hFi.const_mul 2) ?_
    · exact Eventually.of_forall fun p => Finset.sum_nonneg fun a _ =>
        Finset.sum_nonneg fun b _ => sq_nonneg _
    · exact Eventually.of_forall fun p => frob2_le (m p)
  have hsq : ‖smoothTensor P (cartRowsC (cartLift ε⁻¹ c m))‖ ^ 2 ≤
      2 * Real.pi / (P * ε) * (2 * ‖F‖ ^ 2) := by
    rw [hid]
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  set S := ‖smoothTensor P (cartRowsC (cartLift ε⁻¹ c m))‖
  have hS : 0 ≤ S := norm_nonneg _
  have key : (Real.sqrt (P * ε) * S) ^ 2 ≤
      (Real.sqrt (2 * Real.pi) * Real.sqrt 2 * ‖F‖) ^ 2 := by
    have e1 : (Real.sqrt (P * ε) * S) ^ 2 = P * ε * S ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hPe.le]
    have e2 : (Real.sqrt (2 * Real.pi) * Real.sqrt 2 * ‖F‖) ^ 2 = 2 * Real.pi * 2 * ‖F‖ ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    rw [e1, e2]
    calc P * ε * S ^ 2 ≤ P * ε * (2 * Real.pi / (P * ε) * (2 * ‖F‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq hPe.le
      _ = 2 * Real.pi * 2 * ‖F‖ ^ 2 := by field_simp
  exact abs_le_of_sq_le_sq' key (by positivity) |>.2

end UnforcedLeray.Short.PartIIa.N01
