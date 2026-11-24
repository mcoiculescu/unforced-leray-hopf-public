import UnforcedLeray.Lib.Semigroups.Multiplication
import UnforcedLeray.Lib.FreeStressCouplings.Heinz
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Concrete spectral representations (INF10 F1, generic layer)


§4 bypass **B9** and §5 Level F, target **F1** (Wave 1, block 1J); blueprint units **B0459**
(tex 7698-7722), **B0473** (tex 7774-7788) and **B0474** (tex 7790-7812).

Bypass B9 replaces the unbounded spectral theorem of tex 7790-7802 by concrete
diagonalisations: each of `D₀ = 1 + A` and `C₀ = 1 + |B|` is unitarily equivalent to
multiplication by a real function, so its Borel calculus is the multiplication calculus
(scoping note §4 B9, "Soundness").  This file is the representation-independent layer.

* `MulRep H μ E`: a unitary `U : H ≃ₗᵢ[ℂ] L²(α, μ; E)` and a measurable symbol `sym ≥ 0`.  It
  encodes the nonnegative selfadjoint operator `T = U⁻¹ (sym ·) U` on its maximal domain.
* `MulRep.HasPow T s x y`: `x ∈ dom T^s` and `T^s x = y`, i.e. `U y = sym^s · U x` a.e.  For
  `sym ≥ 0` the real power `sym ^ s` has no junk values (`0 ^ s = 0` for `s > 0`,
  `0 ^ 0 = 1`).
* `MulRep.cutOp T s N`: the spectral cutoff `T^s 1_{T ≤ N}` (bounded, selfadjoint), the
  "spectral cutoffs" of tex 7799.

Main results: selfadjointness and composition of cutoffs (`isSelfAdjoint_cutOp`,
`cutOp_mul_cutOp`), the cutoff bounds (`norm_cutOp_le`, `norm_cutOp_apply_le_of_hasPow`),
strong convergence of cutoffs on the domain (`tendsto_cutOp`), the Fatou closure of the domain
(`exists_hasPow_of_norm_cutOp_le`), symmetry of `T^s` (`inner_eq_of_hasPow`) and the duality
step of tex 7792-7793 (`norm_apply_le_of_adjoint`: `𝓡 D₀` is bounded when `D₀ 𝓡*` is).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology InnerProductSpace ComplexConjugate

namespace UnforcedLeray.FreeStress

open UnforcedLeray.Infra

section MulOp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A multiplication operator on `L²` by an a.e. real multiplier is symmetric. -/
theorem inner_mulOp_of_real {m : α → ℂ} (hm : AEStronglyMeasurable m μ) {C : ℝ}
    (hC : ∀ᵐ a ∂μ, ‖m a‖ ≤ C) (hreal : ∀ᵐ a ∂μ, conj (m a) = m a) (f g : Lp E 2 μ) :
    ⟪Mult.mulOp m hm hC f, g⟫_ℂ = ⟪f, Mult.mulOp m hm hC g⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Mult.coeFn_mulOp hm hC f, Mult.coeFn_mulOp hm hC g, hreal] with a h1 h2 h3
  rw [h1, h2, inner_smul_left, inner_smul_right, h3]

end MulOp

/-- **Concrete spectral representation** of a nonnegative selfadjoint operator on `H`
(bypass B9, scoping note §4): a unitary `U : H ≃ₗᵢ[ℂ] L²(α, μ; E)` and a measurable symbol
`sym ≥ 0`; the operator is `U⁻¹ (sym ·) U` on its maximal domain. -/
structure MulRep (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  /-- The diagonalising unitary. -/
  U : H ≃ₗᵢ[ℂ] Lp E 2 μ
  /-- The (real, nonnegative) symbol. -/
  sym : α → ℝ
  measurable_sym : Measurable sym
  sym_nonneg : ∀ a, 0 ≤ sym a

namespace MulRep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (T : MulRep H μ E)

/-- `T.HasPow s x y`: `x` lies in the domain of `T^s` and `T^s x = y`, i.e. `U y = sym^s · U x`
almost everywhere. -/
def HasPow (s : ℝ) (x y : H) : Prop :=
  ∀ᵐ a ∂μ, T.U y a = ((T.sym a ^ s : ℝ) : ℂ) • T.U x a

/-- `T^s` is single valued. -/
theorem HasPow.unique {T : MulRep H μ E} {s : ℝ} {x y y' : H} (h : T.HasPow s x y)
    (h' : T.HasPow s x y') : y = y' := by
  apply T.U.injective
  apply Lp.ext
  filter_upwards [h, h'] with a h1 h2
  rw [h1, h2]

/-- The real cutoff symbol `sym^s 1_{sym ≤ N}`. -/
def cutR (s N : ℝ) (a : α) : ℝ := if T.sym a ≤ N then T.sym a ^ s else 0

/-- The complex cutoff multiplier `sym^s 1_{sym ≤ N}`. -/
def cut (s N : ℝ) (a : α) : ℂ := (T.cutR s N a : ℂ)

theorem measurable_cutR (s N : ℝ) : Measurable (T.cutR s N) :=
  Measurable.ite (measurableSet_le T.measurable_sym measurable_const)
    (T.measurable_sym.pow_const s) measurable_const

theorem aestronglyMeasurable_cut (s N : ℝ) : AEStronglyMeasurable (T.cut s N) μ :=
  (Complex.measurable_ofReal.comp (T.measurable_cutR s N)).aestronglyMeasurable

theorem cutR_nonneg (s N : ℝ) (a : α) : 0 ≤ T.cutR s N a := by
  unfold cutR
  split_ifs
  · exact Real.rpow_nonneg (T.sym_nonneg a) s
  · exact le_rfl

theorem cutR_le_max {s : ℝ} (hs : 0 ≤ s) (N : ℝ) (a : α) : T.cutR s N a ≤ max N 0 ^ s := by
  unfold cutR
  split_ifs with h
  · exact Real.rpow_le_rpow (T.sym_nonneg a) (h.trans (le_max_left _ _)) hs
  · exact Real.rpow_nonneg (le_max_right _ _) s

theorem cut_bound {s : ℝ} (hs : 0 ≤ s) (N : ℝ) :
    ∀ᵐ a ∂μ, ‖T.cut s N a‖ ≤ max N 0 ^ s :=
  Eventually.of_forall fun a => by
    rw [cut, Complex.norm_real, Real.norm_of_nonneg (T.cutR_nonneg s N a)]
    exact T.cutR_le_max hs N a

/-- The cutoff multiplication operator on `L²`. -/
def cutMul (s : ℝ) (hs : 0 ≤ s) (N : ℝ) : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  Mult.mulOp (T.cut s N) (T.aestronglyMeasurable_cut s N) (T.cut_bound hs N)

/-- **Spectral cutoff** `T^s 1_{T ≤ N} = U⁻¹ (sym^s 1_{sym ≤ N} ·) U` (tex 7799), for `s ≥ 0`. -/
def cutOp (s : ℝ) (hs : 0 ≤ s) (N : ℝ) : H →L[ℂ] H :=
  (T.U.symm.toContinuousLinearEquiv : Lp E 2 μ →L[ℂ] H) ∘L T.cutMul s hs N ∘L
    (T.U.toContinuousLinearEquiv : H →L[ℂ] Lp E 2 μ)

theorem U_cutOp {s : ℝ} (hs : 0 ≤ s) (N : ℝ) (x : H) :
    T.U (T.cutOp s hs N x) = T.cutMul s hs N (T.U x) := by
  simp [cutOp]

theorem coeFn_cutOp {s : ℝ} (hs : 0 ≤ s) (N : ℝ) (x : H) :
    (T.U (T.cutOp s hs N x) : α → E) =ᵐ[μ] fun a => T.cut s N a • T.U x a := by
  rw [U_cutOp]
  exact Mult.coeFn_mulOp _ _ _

/-- Spectral cutoffs are selfadjoint. -/
theorem isSelfAdjoint_cutOp [CompleteSpace H] {s : ℝ} (hs : 0 ≤ s) (N : ℝ) :
    IsSelfAdjoint (T.cutOp s hs N) := by
  refine LinearMap.IsSymmetric.isSelfAdjoint fun x y => ?_
  change ⟪T.cutOp s hs N x, y⟫_ℂ = ⟪x, T.cutOp s hs N y⟫_ℂ
  rw [← T.U.inner_map_map, ← T.U.inner_map_map x, U_cutOp, U_cutOp]
  exact inner_mulOp_of_real _ _ (Eventually.of_forall fun a => Complex.conj_ofReal _) _ _

theorem cutR_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (N : ℝ) (a : α) :
    T.cutR (s + t) N a = T.cutR s N a * T.cutR t N a := by
  unfold cutR
  split_ifs
  · exact Real.rpow_add_of_nonneg (T.sym_nonneg a) hs ht
  · simp

/-- Spectral cutoffs compose: `T^s 1_{T≤N} T^t 1_{T≤N} = T^{s+t} 1_{T≤N}`. -/
theorem cutOp_mul_cutOp {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (N : ℝ) :
    T.cutOp s hs N * T.cutOp t ht N = T.cutOp (s + t) (add_nonneg hs ht) N := by
  ext1 x
  apply T.U.injective
  change T.U (T.cutOp s hs N (T.cutOp t ht N x)) = T.U (T.cutOp (s + t) _ N x)
  rw [U_cutOp, U_cutOp, U_cutOp, cutMul, cutMul, cutMul,
    Mult.mulOp_eq_comp (T.aestronglyMeasurable_cut (s + t) N) (T.aestronglyMeasurable_cut s N)
      (T.aestronglyMeasurable_cut t N) (T.cut_bound (add_nonneg hs ht) N) (T.cut_bound hs N)
      (T.cut_bound ht N) (Eventually.of_forall fun a => by
        simp only [cut, T.cutR_add hs ht, Complex.ofReal_mul])]
  rfl

/-- Norm of a spectral cutoff: `‖T^s 1_{T ≤ N}‖ ≤ (max N 0)^s`. -/
theorem norm_cutOp_le {s : ℝ} (hs : 0 ≤ s) (N : ℝ) : ‖T.cutOp s hs N‖ ≤ max N 0 ^ s := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg (le_max_right _ _) s)
    fun x => ?_
  rw [← T.U.norm_map, U_cutOp, ← T.U.norm_map x]
  refine ((T.cutMul s hs N).le_opNorm _).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine (Mult.norm_mulOp_le _ _).trans ?_
  exact max_le le_rfl (Real.rpow_nonneg (le_max_right _ _) s)

/-- The projection `1_{T ≤ N}` is a contraction. -/
theorem norm_cutOp_zero_le (N : ℝ) : ‖T.cutOp 0 le_rfl N‖ ≤ 1 := by
  simpa using T.norm_cutOp_le (s := 0) le_rfl N

/-- On the domain of `T^s`, `‖T^s 1_{T≤N} x‖ ≤ ‖T^s x‖`. -/
theorem norm_cutOp_apply_le_of_hasPow {s : ℝ} (hs : 0 ≤ s) (N : ℝ) {x y : H}
    (h : T.HasPow s x y) : ‖T.cutOp s hs N x‖ ≤ ‖y‖ := by
  rw [← T.U.norm_map, ← T.U.norm_map y]
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [T.coeFn_cutOp hs N x, h] with a h1 h2
  rw [h1, h2, norm_smul, norm_smul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [cut, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (T.cutR_nonneg s N a),
    Real.norm_of_nonneg (Real.rpow_nonneg (T.sym_nonneg a) s)]
  unfold cutR
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (T.sym_nonneg a) s

/-- `1_{T ≤ N} x` lies in the domain of every `T^s`, and `T^s (1_{T≤N} x) = (T^s 1_{T≤N}) x`. -/
theorem hasPow_cutOp_zero {s : ℝ} (hs : 0 ≤ s) (N : ℝ) (x : H) :
    T.HasPow s (T.cutOp 0 le_rfl N x) (T.cutOp s hs N x) := by
  filter_upwards [T.coeFn_cutOp hs N x, T.coeFn_cutOp le_rfl N x] with a h1 h2
  rw [h1, h2, smul_smul]
  congr 1
  simp only [cut, cutR, ← Complex.ofReal_mul]
  congr 1
  split_ifs
  · rw [Real.rpow_zero, mul_one]
  · rw [mul_zero]

/-- Spectral cutoffs converge strongly on the domain: `T^s 1_{T ≤ n} x → T^s x`. -/
theorem tendsto_cutOp {s : ℝ} (hs : 0 ≤ s) {x y : H} (h : T.HasPow s x y) :
    Tendsto (fun n : ℕ => T.cutOp s hs n x) atTop (𝓝 y) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set g : ℕ → α → ℂ := fun n a => if T.sym a ≤ n then 0 else -1 with hg
  have hmeas : ∀ n, AEStronglyMeasurable (g n) μ := fun n =>
    (Measurable.ite (measurableSet_le T.measurable_sym measurable_const) measurable_const
      measurable_const).aestronglyMeasurable
  have hlim := Mult.tendsto_eLpNorm_smul_of_dominated (p := 2) (μ := μ) (l := atTop)
    ENNReal.ofNat_ne_top (g := g) (Eventually.of_forall hmeas) (B := 1)
    (Eventually.of_forall fun n => Eventually.of_forall fun a => by
      simp only [hg]; split_ifs <;> simp)
    (Eventually.of_forall fun a => by
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨n₀, hn₀⟩ := exists_nat_ge (T.sym a)
      filter_upwards [eventually_ge_atTop n₀] with n hn
      simp only [hg]
      rw [ite_eq_left_iff.mpr fun h => absurd (hn₀.trans (by exact_mod_cast hn)) h])
    (Lp.memLp (T.U y))
  have heq : ∀ n : ℕ, ‖T.cutOp s hs n x - y‖ =
      (eLpNorm (fun a => g n a • T.U y a) 2 μ).toReal := by
    intro n
    rw [← T.U.norm_map, map_sub, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub (T.U (T.cutOp s hs n x)) (T.U y), T.coeFn_cutOp hs n x, h]
      with a h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    simp only [hg, cut, cutR]
    split_ifs <;> simp
  simp_rw [heq]
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim

/-- **Fatou closure of the domain.** If the cutoffs `T^s 1_{T ≤ n} z` stay bounded by `M`, then
`z ∈ dom T^s` and `‖T^s z‖ ≤ M`. -/
theorem exists_hasPow_of_norm_cutOp_le {s : ℝ} (hs : 0 ≤ s) {z : H} {M : ℝ}
    (hM : ∀ n : ℕ, ‖T.cutOp s hs n z‖ ≤ M) : ∃ w, T.HasPow s z w ∧ ‖w‖ ≤ M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set flim : α → E := fun a => ((T.sym a ^ s : ℝ) : ℂ) • T.U z a with hflim
  have hmeas : AEStronglyMeasurable flim μ :=
    ((Complex.measurable_ofReal.comp (T.measurable_sym.pow_const s)).aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable _)
  have hae : ∀ᵐ a ∂μ, ∀ n : ℕ,
      (T.U (T.cutOp s hs n z) : α → E) a = T.cut s n a • T.U z a :=
    ae_all_iff.2 fun n => T.coeFn_cutOp hs n z
  have hlim : ∀ᵐ a ∂μ, Tendsto (fun n : ℕ => (T.U (T.cutOp s hs n z) : α → E) a) atTop
      (𝓝 (flim a)) := by
    filter_upwards [hae] with a ha
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨n₀, hn₀⟩ := exists_nat_ge (T.sym a)
    filter_upwards [eventually_ge_atTop n₀] with n hn
    rw [ha n, hflim]
    simp only [cut, cutR]
    rw [ite_eq_left_iff.mpr fun h => absurd (hn₀.trans (by exact_mod_cast hn)) h]
  have hle := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2)
    (fun n => Lp.aestronglyMeasurable (T.U (T.cutOp s hs n z))) flim hlim
  have hbd : atTop.liminf (fun n : ℕ => eLpNorm (T.U (T.cutOp s hs n z) : α → E) 2 μ) ≤
      ENNReal.ofReal M := by
    refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
    rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (T.U (T.cutOp s hs n z))), ← Lp.norm_def,
      T.U.norm_map]
    exact ENNReal.ofReal_le_ofReal (hM n)
  have hfin : eLpNorm flim 2 μ ≤ ENNReal.ofReal M := hle.trans hbd
  have hmem : MemLp flim 2 μ := ⟨hmeas, hfin.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨T.U.symm (hmem.toLp flim), ?_, ?_⟩
  · rw [HasPow, LinearIsometryEquiv.apply_symm_apply]
    exact hmem.coeFn_toLp
  · rw [LinearIsometryEquiv.norm_map, Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal hM0 hfin

/-- `T^s` is symmetric on its domain: `⟪u, T^s x⟫ = ⟪T^s u, x⟫`. -/
theorem inner_eq_of_hasPow {s : ℝ} {x y u w : H} (hxy : T.HasPow s x y) (huw : T.HasPow s u w) :
    ⟪u, y⟫_ℂ = ⟪w, x⟫_ℂ := by
  rw [← T.U.inner_map_map, ← T.U.inner_map_map w, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hxy, huw] with a h1 h2
  rw [h1, h2, inner_smul_right, inner_smul_left, Complex.conj_ofReal]

/-- **Duality step** (tex 7792-7793): if `T R*` is bounded by `M` on all of `H`, then `R T` is
bounded by `M` on the domain of `T`: `‖R (T x)‖ ≤ M ‖x‖`.  Here `T x = y` means
`T.HasPow 1 x y`. -/
theorem norm_apply_le_of_adjoint [CompleteSpace H] (R : H →L[ℂ] H) {M : ℝ} (hM : 0 ≤ M)
    (hadj : ∀ v, ∃ w, T.HasPow 1 (ContinuousLinearMap.adjoint R v) w ∧ ‖w‖ ≤ M * ‖v‖)
    {x y : H} (hxy : T.HasPow 1 x y) : ‖R y‖ ≤ M * ‖x‖ := by
  obtain ⟨w, hw, hwn⟩ := hadj (R y)
  have h1 : ⟪R y, R y⟫_ℂ = ⟪w, x⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact T.inner_eq_of_hasPow hxy hw
  have h2 : ‖R y‖ ^ 2 ≤ M * ‖R y‖ * ‖x‖ := by
    have : ‖R y‖ ^ 2 = ‖⟪R y, R y⟫_ℂ‖ := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [this, h1]
    exact (norm_inner_le_norm w x).trans (mul_le_mul_of_nonneg_right hwn (norm_nonneg _))
  rcases (norm_nonneg (R y)).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg hM (norm_nonneg _)
  · rw [sq, mul_assoc, mul_comm M, mul_assoc] at h2
    have := le_of_mul_le_mul_left h2 hpos
    linarith

/-! ### Linearity and closedness of `T^s` -/

variable {T} in
theorem HasPow.add {s : ℝ} {x y x' y' : H} (h : T.HasPow s x y) (h' : T.HasPow s x' y') :
    T.HasPow s (x + x') (y + y') := by
  filter_upwards [h, h', Lp.coeFn_add (T.U x) (T.U x'), Lp.coeFn_add (T.U y) (T.U y')]
    with a h1 h2 h3 h4
  rw [map_add, map_add, h4, h3, Pi.add_apply, Pi.add_apply, h1, h2, smul_add]

variable {T} in
theorem HasPow.smul {s : ℝ} {x y : H} (c : ℂ) (h : T.HasPow s x y) :
    T.HasPow s (c • x) (c • y) := by
  filter_upwards [h, Lp.coeFn_smul c (T.U x), Lp.coeFn_smul c (T.U y)] with a h1 h2 h3
  rw [map_smul, map_smul, h3, h2, Pi.smul_apply, Pi.smul_apply, h1, smul_comm]

variable {T} in
theorem HasPow.sub {s : ℝ} {x y x' y' : H} (h : T.HasPow s x y) (h' : T.HasPow s x' y') :
    T.HasPow s (x - x') (y - y') := by
  filter_upwards [h, h', Lp.coeFn_sub (T.U x) (T.U x'), Lp.coeFn_sub (T.U y) (T.U y')]
    with a h1 h2 h3 h4
  rw [map_sub, map_sub, h4, h3, Pi.sub_apply, Pi.sub_apply, h1, h2, smul_sub]

/-- `T^0 = 1` on all of `H`. -/
theorem hasPow_zero (x : H) : T.HasPow 0 x x :=
  Eventually.of_forall fun a => by rw [Real.rpow_zero, Complex.ofReal_one, one_smul]

/-- `T^s` is closed: graph limits stay in the graph. -/
theorem HasPow.of_tendsto {s : ℝ} (hs : 0 ≤ s) {xn yn : ℕ → H} {x y : H}
    (hx : Tendsto xn atTop (𝓝 x)) (hy : Tendsto yn atTop (𝓝 y))
    (h : ∀ n, T.HasPow s (xn n) (yn n)) : T.HasPow s x y := by
  have key : ∀ (N : ℝ) n, T.cutOp s hs N (xn n) = T.cutOp 0 le_rfl N (yn n) := by
    intro N n
    apply T.U.injective
    apply Lp.ext
    filter_upwards [T.coeFn_cutOp hs N (xn n), T.coeFn_cutOp le_rfl N (yn n), h n]
      with a h1 h2 h3
    rw [h1, h2, h3, smul_smul]
    congr 1
    simp only [cut, cutR, ← Complex.ofReal_mul]
    congr 1
    split_ifs
    · rw [Real.rpow_zero, one_mul]
    · rw [zero_mul]
  have key' : ∀ N : ℕ, T.cutOp s hs N x = T.cutOp 0 le_rfl N y := by
    intro N
    have h1 := ((T.cutOp s hs N).continuous.tendsto x).comp hx
    have h2 := ((T.cutOp 0 le_rfl N).continuous.tendsto y).comp hy
    refine tendsto_nhds_unique h1 ?_
    convert h2 using 1
    funext n
    exact key N n
  have hae : ∀ᵐ a ∂μ, ∀ N : ℕ, T.cut s N a • T.U x a = T.cut 0 N a • T.U y a := by
    refine ae_all_iff.2 fun N => ?_
    filter_upwards [T.coeFn_cutOp hs N x, T.coeFn_cutOp le_rfl N y] with a h1 h2
    rw [← h1, ← h2, key' N]
  filter_upwards [hae] with a ha
  obtain ⟨N, hN⟩ := exists_nat_ge (T.sym a)
  have := ha N
  simp only [cut, cutR, hN, ↓reduceIte, Real.rpow_zero, Complex.ofReal_one, one_smul] at this
  exact this.symm

end MulRep

end UnforcedLeray.FreeStress
