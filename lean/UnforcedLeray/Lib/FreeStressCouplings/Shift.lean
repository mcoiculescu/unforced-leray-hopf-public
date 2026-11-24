import UnforcedLeray.Lib.FreeStressCouplings.MulRep

/-!
# `D₀ = 1 + A` and `C₀ = 1 + |B|` in concrete representations (INF10 F1)


§4 bypass **B9** and §5 Level F, target **F1** (Wave 1, block 1J); blueprint units **B0459**
(tex 7698-7722) and **B0474** (tex 7789-7793).

The manuscript puts `C₀ = 1 + |B|` and `D₀ = 1 + A` (tex 7789), with `A = -νΔ ≥ 0` selfadjoint
and `B = T₀ - 3/4` skew-adjoint (tex 7704-7715, B0459(i)).  In bypass B9 each is given by a
concrete diagonalisation: `A` by a `MulRep` with symbol `≥ 0`, `B` by a unitary and a real
symbol `b` with `B = U⁻¹ (i b ·) U` (`SkewRep`).  This file builds `D₀` and `C₀` from these
and proves the two facts of tex 7790-7793 that feed the interpolation:

* `SkewRep.inner_hasGen`: `B` is skew-symmetric, `⟪u, B x⟫ = -⟪B u, x⟫` (B0459(i) in the
  representation);
* `SkewRep.exists_onePlusAbs_hasPow_one`: `x ∈ dom B` gives `x ∈ dom C₀` with
  `‖C₀ x‖ ≤ ‖x‖ + ‖B x‖`, so the graph bound for `B 𝓡_μ` gives the bounded `C₀ 𝓡_μ`
  (`SkewRep.onePlusAbs_comp_bound`, tex 7791);
* `MulRep.onePlus_hasPow_one_iff`: `(1 + A) x = z` iff `A x = z - x`, and the bound for
  `D₀ 𝓡_μ*` from bounds for `𝓡_μ` and `A 𝓡_μ*` (`MulRep.onePlus_comp_bound`, tex 7792).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology InnerProductSpace ComplexConjugate

namespace UnforcedLeray.FreeStress

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

namespace MulRep

/-- `1 + T` for a concrete nonnegative selfadjoint `T` (the manuscript's `D₀ = 1 + A`,
tex 7789). -/
def onePlus (T : MulRep H μ E) : MulRep H μ E where
  U := T.U
  sym := fun a => 1 + T.sym a
  measurable_sym := measurable_const.add T.measurable_sym
  sym_nonneg := fun a => add_nonneg zero_le_one (T.sym_nonneg a)

variable (T : MulRep H μ E)

@[simp] theorem onePlus_U : T.onePlus.U = T.U := rfl

@[simp] theorem onePlus_sym (a : α) : T.onePlus.sym a = 1 + T.sym a := rfl

/-- `(1 + T) x = z` iff `T x = z - x`. -/
theorem onePlus_hasPow_one_iff {x z : H} : T.onePlus.HasPow 1 x z ↔ T.HasPow 1 x (z - x) := by
  constructor
  · intro h
    filter_upwards [h, Lp.coeFn_sub (T.U z) (T.U x)] with a h1 h2
    rw [map_sub, h2, Pi.sub_apply]
    rw [onePlus_U] at h1
    rw [h1, onePlus_sym, Real.rpow_one, Real.rpow_one, Complex.ofReal_add, Complex.ofReal_one,
      add_smul, one_smul, add_sub_cancel_left]
  · intro h
    filter_upwards [h, Lp.coeFn_sub (T.U z) (T.U x)] with a h1 h2
    rw [map_sub, h2, Pi.sub_apply, Real.rpow_one] at h1
    rw [onePlus_U, onePlus_sym, Real.rpow_one, Complex.ofReal_add, Complex.ofReal_one, add_smul,
      one_smul, ← h1, add_sub_cancel]

/-- Bound for `(1 + T) S` from bounds for `S` and `T S` (tex 7792: `D₀ 𝓡_μ*` from the graph
bound for `A 𝓡_μ*`). -/
theorem onePlus_comp_bound (S : H →L[ℂ] H) {M : ℝ}
    (h : ∀ v, ∃ w, T.HasPow 1 (S v) w ∧ ‖w‖ ≤ M * ‖v‖) :
    ∀ v, ∃ w, T.onePlus.HasPow 1 (S v) w ∧ ‖w‖ ≤ (‖S‖ + M) * ‖v‖ := by
  intro v
  obtain ⟨w, hw, hwn⟩ := h v
  refine ⟨S v + w, (T.onePlus_hasPow_one_iff).2 (by rwa [add_sub_cancel_left]), ?_⟩
  calc ‖S v + w‖ ≤ ‖S v‖ + ‖w‖ := norm_add_le _ _
    _ ≤ ‖S‖ * ‖v‖ + M * ‖v‖ := add_le_add (S.le_opNorm v) hwn
    _ = (‖S‖ + M) * ‖v‖ := by ring

end MulRep

/-- **Concrete diagonalisation of a skew-adjoint operator** (bypass B9 for `B`, tex 7704-7715):
a unitary `U : H ≃ₗᵢ[ℂ] L²(α, μ; E)` and a measurable real symbol `b`, encoding
`B = U⁻¹ (i b ·) U` on its maximal domain. -/
structure SkewRep (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  /-- The diagonalising unitary. -/
  U : H ≃ₗᵢ[ℂ] Lp E 2 μ
  /-- The real symbol: `B` acts as multiplication by `i · sym`. -/
  sym : α → ℝ
  measurable_sym : Measurable sym

namespace SkewRep

variable (B : SkewRep H μ E)

/-- `B.HasGen x y`: `x ∈ dom B` and `B x = y`, i.e. `U y = i b · U x` a.e. -/
def HasGen (x y : H) : Prop :=
  ∀ᵐ a ∂μ, B.U y a = (Complex.I * (B.sym a : ℂ)) • B.U x a

/-- `C₀ = 1 + |B|` (tex 7789), the nonnegative selfadjoint operator with symbol `1 + |b|`. -/
def onePlusAbs : MulRep H μ E where
  U := B.U
  sym := fun a => 1 + |B.sym a|
  measurable_sym := measurable_const.add (continuous_abs.measurable.comp B.measurable_sym)
  sym_nonneg := fun _ => add_nonneg zero_le_one (abs_nonneg _)

/-- **`B` is skew-symmetric** (B0459(i), tex 7715-7717, in the representation):
`⟪u, B x⟫ = -⟪B u, x⟫`. -/
theorem inner_hasGen {x y u w : H} (hxy : B.HasGen x y) (huw : B.HasGen u w) :
    ⟪u, y⟫_ℂ = -⟪w, x⟫_ℂ := by
  rw [← B.U.inner_map_map, ← B.U.inner_map_map w, L2.inner_def, L2.inner_def, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hxy, huw] with a h1 h2
  rw [h1, h2, inner_smul_right, inner_smul_left, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- **`dom B ⊂ dom C₀`** with `‖C₀ x‖ ≤ ‖x‖ + ‖B x‖` (tex 7790-7791). -/
theorem exists_onePlusAbs_hasPow_one {x y : H} (h : B.HasGen x y) :
    ∃ z, B.onePlusAbs.HasPow 1 x z ∧ ‖z‖ ≤ ‖x‖ + ‖y‖ := by
  set g : α → E := fun a => ((|B.sym a| : ℝ) : ℂ) • B.U x a with hg
  have hgle : ∀ᵐ a ∂μ, ‖g a‖ ≤ ‖B.U y a‖ := by
    filter_upwards [h] with a ha
    rw [ha, hg]
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_abs, norm_mul,
      Complex.norm_I, one_mul]
    exact le_rfl
  have hgmeas : AEStronglyMeasurable g μ :=
    ((Complex.measurable_ofReal.comp (continuous_abs.measurable.comp B.measurable_sym)).aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable _)
  have hgmem : MemLp g 2 μ := (Lp.memLp (B.U y)).of_le hgmeas hgle
  refine ⟨x + B.U.symm (hgmem.toLp g), ?_, ?_⟩
  · change ∀ᵐ a ∂μ, B.U (x + B.U.symm (hgmem.toLp g)) a =
      (((1 + |B.sym a|) ^ (1 : ℝ) : ℝ) : ℂ) • B.U x a
    rw [map_add, LinearIsometryEquiv.apply_symm_apply]
    filter_upwards [Lp.coeFn_add (B.U x) (hgmem.toLp g), hgmem.coeFn_toLp] with a h1 h2
    rw [h1, Pi.add_apply, h2, hg, Real.rpow_one, Complex.ofReal_add, Complex.ofReal_one, add_smul,
      one_smul]
  · refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [LinearIsometryEquiv.norm_map, ← B.U.norm_map y]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hgmem.coeFn_toLp, hgle] with a h1 h2
    rw [h1]
    exact h2

/-- **Graph bound to `C₀ 𝓡_μ`** (tex 7791): if `B R` is bounded by `M`, then `C₀ R` is bounded
by `‖R‖ + M`. -/
theorem onePlusAbs_comp_bound (R : H →L[ℂ] H) {M : ℝ}
    (h : ∀ v, ∃ w, B.HasGen (R v) w ∧ ‖w‖ ≤ M * ‖v‖) :
    ∀ v, ∃ w, B.onePlusAbs.HasPow 1 (R v) w ∧ ‖w‖ ≤ (‖R‖ + M) * ‖v‖ := by
  intro v
  obtain ⟨w, hw, hwn⟩ := h v
  obtain ⟨z, hz, hzn⟩ := B.exists_onePlusAbs_hasPow_one hw
  refine ⟨z, hz, ?_⟩
  calc ‖z‖ ≤ ‖R v‖ + ‖w‖ := hzn
    _ ≤ ‖R‖ * ‖v‖ + M * ‖v‖ := add_le_add (R.le_opNorm v) hwn
    _ = (‖R‖ + M) * ‖v‖ := by ring

end SkewRep

end UnforcedLeray.FreeStress
