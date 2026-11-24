import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# The frozen pair exists: the reduction to the leaves of `Pair/Defs.lean`
(source 2894-2912, 4352-4356, 3030-3035, 593-610, 4349-4350)

Source of record: `the November 2 reference manuscript` (73 pages).

The construction of `FrozenPair κ ν c m` on the band `a = bandA ν s ∈ [1, 3]`, `d = c/√a`:

* `q_{k,s}` is the class of `qFun κ ν c k s = J_aP_de_k` (`Qv`); it lies in `X_{m,c}` by zero
  circulation (`QFunCirc`, `∫ q = 0`, 597) and central evenness (the seed is an angular-two mode);
* the dual rows are represented by Riesz vectors: `Lv k s` is the class of
  `dualVec m (lam0Ker κ ν c k s)`, so that `⟪Lv k s, f⟫ = ∫_{cell c} aΛ⁰_{d,k}(x/√a) f(x) dx`
  (`inner_eq_integral_cell`), and `Ev i s = Σ_k conj(G⁻¹_{ik}) • Lv k s` (`G = IIIa.perGram κ d`), so
  `ℓ_{i,s} = ⟪Ev i s, ·⟫` is `frozenEll` (2896-2902, the change of variables `x = √a y`);
* `ℓ_{i,s}q_{j,s} = δ_{ij}` is the first field of `IIIa.PerFrameFacts` at the band age
  (`θ ≥ 1/(3ν) ≥ b` for small `ν`; 2894-2896 "normalize their dual rows `Λ(z)` by `ΛE = I₂`",
  4354-4355), and it gives `G⁻¹G = I`, hence `det G ≠ 0` along the band; `G_{kl} = ⟪Lv k s, Qv l s⟫`
  is continuous in the age, so is `G⁻¹`, and so are `Ev` and `ℓ` (2896-2899: "The finite Gram
  inverse exists uniformly");
* `q_- = q̄_+`, `ℓ_- = ℓ̄_+` from `e₁ = ē₀`, `λ₁ = λ̄₀` (`IIIa.IsSeedKernels`, `SeedDualConj`,
  `PerLamConj`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair

/-! ## The band -/

section Band

variable {ν : ℝ}

theorem bandAge_nonneg (s : ℝ) : 0 ≤ bandAge ν s := le_max_left _ _

theorem bandAge_le (hν : 0 < ν) (s : ℝ) : bandAge ν s ≤ 2 / ν := by
  unfold bandAge flatSigma
  exact max_le (by positivity) (min_le_right _ _)

theorem one_le_bandA (hν : 0 < ν) (s : ℝ) : 1 ≤ bandA ν s := by
  unfold bandA IIIa.clockA
  have := bandAge_nonneg (ν := ν) s
  nlinarith

theorem bandA_pos (hν : 0 < ν) (s : ℝ) : 0 < bandA ν s :=
  lt_of_lt_of_le one_pos (one_le_bandA hν s)

theorem bandA_le_three (hν : 0 < ν) (s : ℝ) : bandA ν s ≤ 3 := by
  unfold bandA IIIa.clockA
  have h := bandAge_le hν s
  have : ν * bandAge ν s ≤ 2 := by
    calc ν * bandAge ν s ≤ ν * (2 / ν) := mul_le_mul_of_nonneg_left h hν.le
      _ = 2 := by field_simp
  linarith

theorem bandD_pos (hν : 0 < ν) {c : ℝ} (hc : 0 < c) (s : ℝ) : 0 < bandD ν c s := by
  unfold bandD IIIa.cellLen
  exact div_pos hc (Real.sqrt_pos.2 (bandA_pos hν s))

/-- On the band the heat clock stays above `1/(3ν)`. -/
theorem le_clockTheta_bandAge (hν : 0 < ν) {b : ℝ} (hb : 0 < b) (hνb : ν ≤ 1 / (3 * b))
    (s : ℝ) : b ≤ IIIa.clockTheta ν (bandAge ν s) := by
  unfold IIIa.clockTheta IIIa.clockA
  have h1 := bandAge_nonneg (ν := ν) s
  have h2 := bandAge_le hν s
  have h3 : ν * bandAge ν s ≤ 2 := by
    calc ν * bandAge ν s ≤ ν * (2 / ν) := mul_le_mul_of_nonneg_left h2 hν.le
      _ = 2 := by field_simp
  have hpos : 0 < ν * (1 + ν * bandAge ν s) := by positivity
  rw [le_inv_comm₀ hb hpos]
  have h4 : 3 * b * ν ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hνb (by positivity : (0 : ℝ) ≤ 3 * b)
    rwa [mul_one_div_cancel (by positivity : (3 * b) ≠ 0)] at this
  have h5 : ν * (1 + ν * bandAge ν s) ≤ 3 * ν := by nlinarith
  calc ν * (1 + ν * bandAge ν s) ≤ 3 * ν := h5
    _ ≤ b⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hb]
      rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
      linarith

end Band

/-! ## The change of variables, in the forms used -/

section CV

/-- `frozenEll`-type integrals over `cell d` as integrals over `cell c` (`d = c/√a`). -/
theorem cv_ker (h6 : IntegralCellDilate) {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (P f : ℝ × ℝ → ℂ) :
    ∫ y in B0579.cell (IIIa.cellLen c a), P y * IIIa.JscaleInv a f y =
      ∫ x in B0579.cell c, ((a : ℂ) * P (x.1 / Real.sqrt a, x.2 / Real.sqrt a)) * f x := by
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h := h6 (fun x => ((a : ℂ) * P (x.1 / Real.sqrt a, x.2 / Real.sqrt a)) * f x) a c ha hc
  have e : ∀ y : ℝ × ℝ,
      ((a : ℂ) * P ((Real.sqrt a * y.1) / Real.sqrt a, (Real.sqrt a * y.2) / Real.sqrt a)) *
          f (Real.sqrt a * y.1, Real.sqrt a * y.2) =
        (a : ℂ)⁻¹ * (P y * IIIa.JscaleInv a f y) := by
    intro y
    rw [mul_div_cancel_left₀ _ hs, mul_div_cancel_left₀ _ hs]
    simp only [IIIa.JscaleInv]
    push_cast
    field_simp
  simp only [e] at h
  rw [integral_const_mul] at h
  exact mul_left_cancel₀ (inv_ne_zero ha') h

/-- `J_a⁻¹(J_aW) = W`. -/
theorem jscaleInv_jscale {a : ℝ} (ha : 0 < a) (W : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    IIIa.JscaleInv a (IIIa.Jscale a W) y = W y := by
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  simp only [IIIa.JscaleInv, IIIa.Jscale]
  rw [mul_div_cancel_left₀ _ hs, mul_div_cancel_left₀ _ hs, ← mul_assoc, ← Complex.ofReal_mul]
  have : a ^ 2 * a ^ (-2 : ℝ) = 1 := by
    rw [Real.rpow_neg ha.le, Real.rpow_two, mul_inv_cancel₀ (by positivity)]
  rw [this, Complex.ofReal_one, one_mul]

end CV

/-! ## Riesz vectors and elements of `X_{m,c}` -/

section Riesz

variable {c m : ℝ}

/-- Integrals for the weighted cell measure. -/
theorem integral_cellMeasure (F : ℝ × ℝ → ℂ) :
    ∫ x, F x ∂(B0579.cellMeasure c m) =
      ∫ x in B0579.cell c, ((B0579.jb x ^ m : ℝ) : ℂ) * F x := by
  rw [B0579.cellMeasure, integral_withDensity_eq_integral_smul (B0579.measurable_density m)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show (B0579.density m x) • F x = _
  rw [NNReal.smul_def, B0579.coe_density, Complex.real_smul]

/-- **The Riesz pairing**: if `u` is the class of `ḡ⟨x⟩^{-2m}`, then `⟪u, f⟫ = ∫_cell g f`. -/
theorem inner_eq_integral_cell {g : ℝ × ℝ → ℂ} {u : XAmb c m}
    (hu : (u : ℝ × ℝ → ℂ) =ᵐ[B0579.cellMeasure c m] dualVec m g) (f : XAmb c m) :
    inner ℂ u f = ∫ x in B0579.cell c, g x * f x := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : (fun a => inner ℂ (u a) (f a)) =ᵐ[B0579.cellMeasure c m]
      fun x => ((B0579.jb x ^ (-m) : ℝ) : ℂ) * (g x * f x) := by
    filter_upwards [hu] with x hx
    rw [RCLike.inner_apply', hx, dualVec, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  rw [integral_congr_ae h1, integral_cellMeasure]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show ((B0579.jb x ^ m : ℝ) : ℂ) * (((B0579.jb x ^ (-m) : ℝ) : ℂ) * (g x * f x)) = g x * f x
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (B0579.jb_pos x), add_neg_cancel,
    Real.rpow_zero, Complex.ofReal_one, one_mul]

/-- `⟨x⟩^{-2m} ∈ X_{m,c}` for `m > 1`. -/
theorem memLp_jb_neg (hm : 1 < m) :
    MemLp (fun x : ℝ × ℝ => B0579.jb x ^ (-m)) 2 (B0579.cellMeasure c m) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ × ℝ => B0579.jb x ^ (-m))
      (B0579.cellMeasure c m) :=
    (B0579.continuous_jb_rpow (-m)).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  rw [B0579.cellMeasure, integrable_withDensity_iff_integrable_smul (B0579.measurable_density m)]
  have hI : Integrable (fun y : ℝ × ℝ => B0579.jb y ^ (-m)) := B0592.integrable_jb_rpow_neg hm
  refine (hI.restrict (s := B0579.cell c)).congr (Eventually.of_forall fun x => ?_)
  show B0579.jb x ^ (-m) = (B0579.density m x) • (B0579.jb x ^ (-m)) ^ 2
  rw [NNReal.smul_def, smul_eq_mul, B0579.coe_density, ← Real.rpow_natCast,
    ← Real.rpow_mul (B0579.jb_pos x).le, ← Real.rpow_add (B0579.jb_pos x)]
  congr 1
  push_cast
  ring

/-- A kernel continuous and bounded on the cell has its Riesz vector in `X_{m,c}`, `m > 1`. -/
theorem memLp_dualVec (hm : 1 < m) {g : ℝ × ℝ → ℂ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ x, x ∈ B0579.cell c → ‖g x‖ ≤ M) :
    MemLp (dualVec m g) 2 (B0579.cellMeasure c m) := by
  have hJ := (memLp_jb_neg (c := c) hm).const_mul M
  refine hJ.of_le ?_ ?_
  · exact ((Complex.continuous_conj.comp hg).mul
      (Complex.continuous_ofReal.comp (B0579.continuous_jb_rpow (-m)))).aestronglyMeasurable
  · have hcell : ∀ᵐ x ∂(B0579.cellMeasure c m), x ∈ B0579.cell c :=
      (B0579.cellMeasure_ac c m).ae_le (ae_restrict_mem (B0579.measurableSet_cell c))
    filter_upwards [hcell] with x hx
    have h0 : 0 ≤ B0579.jb x ^ (-m) := Real.rpow_nonneg (B0579.jb_pos x).le _
    rw [dualVec, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg h0]
    exact (mul_le_mul_of_nonneg_right (hM x hx) h0).trans (Real.le_norm_self _)

/-- The bound of `memLp_dualVec`, almost everywhere for the weighted cell measure. -/
theorem norm_dualVec_le {g : ℝ × ℝ → ℂ} {M : ℝ} (hM : ∀ x, x ∈ B0579.cell c → ‖g x‖ ≤ M) :
    ∀ᵐ x ∂(B0579.cellMeasure c m), ‖dualVec m g x‖ ≤ M * B0579.jb x ^ (-m) := by
  have hcell : ∀ᵐ x ∂(B0579.cellMeasure c m), x ∈ B0579.cell c :=
    (B0579.cellMeasure_ac c m).ae_le (ae_restrict_mem (B0579.measurableSet_cell c))
  filter_upwards [hcell] with x hx
  have h0 : 0 ≤ B0579.jb x ^ (-m) := Real.rpow_nonneg (B0579.jb_pos x).le _
  rw [dualVec, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg h0]
  exact mul_le_mul_of_nonneg_right (hM x hx) h0

variable [Fact (1 < m)]

/-- A square-integrable, zero-circulation, centrally even planar function is (the planar function
of) an element of `X_{m,c}` (source 4349-4350). -/
theorem toLp_mem_xmcSub {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 (B0579.cellMeasure c m))
    (hcirc : ∫ x in B0579.cell c, f x = 0) (heven : ∀ x, f (-x) = f x) :
    hf.toLp f ∈ xmcSub c m := by
  refine mem_xmcSub.2 ⟨?_, ?_⟩
  · rw [← hcirc]
    exact integral_congr_ae (ae_cell_of_ae_cellMeasure hf.coeFn_toLp)
  · refine Lp.ext ?_
    have e1 := coeFn_reflX (hf.toLp f)
    have e2 := (mp_neg_cellMeasure c m).quasiMeasurePreserving.ae hf.coeFn_toLp
    filter_upwards [e1, e2, hf.coeFn_toLp] with x h1 h2 h3
    rw [h1, h2, h3, heven]

end Riesz

/-! ## Pointwise identities of the explicit functions -/

section Pointwise

variable {κ : IIIa.PlanarFrameKernels} {ν c : ℝ}

/-- The Gram matrix `G_{kl} = ∫_{cell d} Λ⁰_kE_l` at the age `s` (source 2896-2899). -/
def gramAt (κ : IIIa.PlanarFrameKernels) (ν c s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  IIIa.perGram κ (bandD ν c s)

/-- `aΛ_{d,i}(x/√a) = Σ_k G⁻¹_{ik} aΛ⁰_{d,k}(x/√a)`. -/
theorem ellKer_eq (s : ℝ) (i : Fin 2) (x : ℝ × ℝ) :
    ellKer κ ν c i s x = (gramAt κ ν c s)⁻¹ i 0 * lam0Ker κ ν c 0 s x +
      (gramAt κ ν c s)⁻¹ i 1 * lam0Ker κ ν c 1 s x := by
  simp only [ellKer, lam0Ker, IIIa.perLam, Fin.sum_univ_two, gramAt]
  ring

/-- `J_a⁻¹q_{k,s} = E_k`. -/
theorem jscaleInv_qFun (hν : 0 < ν) (k : Fin 2) (s : ℝ) (y : ℝ × ℝ) :
    IIIa.JscaleInv (bandA ν s) (qFun κ ν c k s) y = IIIa.perE κ (bandD ν c s) k y :=
  jscaleInv_jscale (bandA_pos hν s) _ y

/-- `q_{k,s}` is centrally even when `e_k` is. -/
theorem qFun_even {k : Fin 2} (he : ∀ y, κ.e k (-y) = κ.e k y) (s : ℝ) (x : ℝ × ℝ) :
    qFun κ ν c k s (-x) = qFun κ ν c k s x := by
  simp only [qFun, IIIa.Jscale, IIIa.perE, IIIa.perSum, Prod.fst_neg, Prod.snd_neg]
  congr 1
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  rw [← he (x.1 / Real.sqrt (bandA ν s) + (n : ℝ) * bandD ν c s, x.2 / Real.sqrt (bandA ν s))]
  congr 1
  refine Prod.ext ?_ ?_
  · simp only [Equiv.neg_apply, Int.cast_neg, Prod.fst_neg]
    ring
  · simp only [Prod.snd_neg]
    ring

/-- `q_{1,s} = q̄_{0,s}` when `e₁ = ē₀`. -/
theorem qFun_conj (he : ∀ y, κ.e 1 y = conj (κ.e 0 y)) (s : ℝ) (x : ℝ × ℝ) :
    qFun κ ν c 1 s x = conj (qFun κ ν c 0 s x) := by
  simp only [qFun, IIIa.Jscale, IIIa.perE, IIIa.perSum, map_mul, Complex.conj_ofReal,
    Complex.conj_tsum, he]

/-- The normalized dual kernels are conjugate when the dual rows are. -/
theorem ellKer_conj (hP : ∀ d y, IIIa.perLam κ d 1 y = conj (IIIa.perLam κ d 0 y)) (s : ℝ)
    (x : ℝ × ℝ) : ellKer κ ν c 1 s x = conj (ellKer κ ν c 0 s x) := by
  simp only [ellKer, map_mul, Complex.conj_ofReal, hP]

end Pointwise

/-! ## The construction at one regime -/

section Construction

variable {κ : IIIa.PlanarFrameKernels} {ν c m : ℝ}

/-- `q_{k,s}` as an element of `L²(cell, ⟨x⟩^{2m}dx)`. -/
def Qv (hQ : ∀ k s, MemLp (qFun κ ν c k s) 2 (B0579.cellMeasure c m)) (k : Fin 2) (s : ℝ) :
    XAmb c m :=
  (hQ k s).toLp _

/-- The Riesz vector of `f ↦ ∫_{cell c} aΛ⁰_{d,k}(x/√a)f(x)dx`. -/
def Lv (hL : ∀ k s, MemLp (dualVec m (lam0Ker κ ν c k s)) 2 (B0579.cellMeasure c m)) (k : Fin 2)
    (s : ℝ) : XAmb c m :=
  (hL k s).toLp _

/-- The Riesz vector of the Gram-normalized row `ℓ_{i,s}`: `Σ_k conj(G⁻¹_{ik}) • Lv k s`. -/
def Ev (hL : ∀ k s, MemLp (dualVec m (lam0Ker κ ν c k s)) 2 (B0579.cellMeasure c m)) (i : Fin 2)
    (s : ℝ) : XAmb c m :=
  conj ((gramAt κ ν c s)⁻¹ i 0) • Lv hL 0 s + conj ((gramAt κ ν c s)⁻¹ i 1) • Lv hL 1 s

variable (hL : ∀ k s, MemLp (dualVec m (lam0Ker κ ν c k s)) 2 (B0579.cellMeasure c m))
  (hQ : ∀ k s, MemLp (qFun κ ν c k s) 2 (B0579.cellMeasure c m))

theorem Ev_ae (i : Fin 2) (s : ℝ) :
    (Ev hL i s : ℝ × ℝ → ℂ) =ᵐ[B0579.cellMeasure c m] dualVec m (ellKer κ ν c i s) := by
  set a := conj ((gramAt κ ν c s)⁻¹ i 0)
  set b := conj ((gramAt κ ν c s)⁻¹ i 1)
  have e : Ev hL i s = a • Lv hL 0 s + b • Lv hL 1 s := rfl
  rw [e]
  filter_upwards [Lp.coeFn_add (a • Lv hL 0 s) (b • Lv hL 1 s), Lp.coeFn_smul a (Lv hL 0 s),
    Lp.coeFn_smul b (Lv hL 1 s), (hL 0 s).coeFn_toLp, (hL 1 s).coeFn_toLp] with x h1 h2 h3 h4 h5
  have e4 : (Lv hL 0 s : ℝ × ℝ → ℂ) x = dualVec m (lam0Ker κ ν c 0 s) x := h4
  have e5 : (Lv hL 1 s : ℝ × ℝ → ℂ) x = dualVec m (lam0Ker κ ν c 1 s) x := h5
  rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, e4, e5]
  simp only [dualVec, ellKer_eq, map_add, map_mul, a, b]
  ring

theorem inner_Lv (k : Fin 2) (s : ℝ) (f : XAmb c m) :
    inner ℂ (Lv hL k s) f = ∫ x in B0579.cell c, lam0Ker κ ν c k s x * f x :=
  inner_eq_integral_cell (hL k s).coeFn_toLp f

theorem inner_Ev (i : Fin 2) (s : ℝ) (f : XAmb c m) :
    inner ℂ (Ev hL i s) f = ∫ x in B0579.cell c, ellKer κ ν c i s x * f x :=
  inner_eq_integral_cell (Ev_ae hL i s) f

theorem inner_Ev_eq (i : Fin 2) (s : ℝ) (f : XAmb c m) :
    inner ℂ (Ev hL i s) f = (gramAt κ ν c s)⁻¹ i 0 * inner ℂ (Lv hL 0 s) f +
      (gramAt κ ν c s)⁻¹ i 1 * inner ℂ (Lv hL 1 s) f := by
  rw [Ev, inner_add_left, inner_smul_left, inner_smul_left, Complex.conj_conj, Complex.conj_conj]

variable (h6 : IntegralCellDilate) (hν : 0 < ν) (hc : 0 < c)
include h6 hν hc

/-- `ℓ_{j,s} = ⟪Ev, ·⟫` is `frozenEll` (the change of variables `x = √a y`). -/
theorem inner_Ev_frozenEll (j : Bool) (s : ℝ) (f : XAmb c m) :
    inner ℂ (Ev hL (pmIdx j) s) f = frozenEll κ ν c j s f := by
  rw [inner_Ev]
  exact (cv_ker h6 (bandA_pos hν s) hc (IIIa.perLam κ (bandD ν c s) (pmIdx j)) f).symm

theorem inner_Ev_Qv (i j : Fin 2) (s : ℝ) :
    inner ℂ (Ev hL i s) (Qv hQ j s) = ∫ y in B0579.cell (bandD ν c s),
      IIIa.perLam κ (bandD ν c s) i y * IIIa.perE κ (bandD ν c s) j y := by
  rw [inner_Ev]
  have h1 : ∫ x in B0579.cell c, ellKer κ ν c i s x * (Qv hQ j s : ℝ × ℝ → ℂ) x =
      ∫ x in B0579.cell c, ellKer κ ν c i s x * qFun κ ν c j s x := by
    refine integral_congr_ae ?_
    filter_upwards [ae_cell_of_ae_cellMeasure (hQ j s).coeFn_toLp] with x hx
    have e : (Qv hQ j s : ℝ × ℝ → ℂ) x = qFun κ ν c j s x := hx
    rw [e]
  rw [h1]
  have h2 := cv_ker h6 (bandA_pos hν s) hc (IIIa.perLam κ (bandD ν c s) i) (qFun κ ν c j s)
  show _ = ∫ y in B0579.cell (IIIa.cellLen c (bandA ν s)),
      IIIa.perLam κ (bandD ν c s) i y * IIIa.perE κ (bandD ν c s) j y
  rw [show (∫ x in B0579.cell c, ellKer κ ν c i s x * qFun κ ν c j s x) =
      ∫ y in B0579.cell (IIIa.cellLen c (bandA ν s)),
        IIIa.perLam κ (bandD ν c s) i y * IIIa.JscaleInv (bandA ν s) (qFun κ ν c j s) y from h2.symm]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show IIIa.perLam κ (bandD ν c s) i y * IIIa.JscaleInv (bandA ν s) (qFun κ ν c j s) y = _
  rw [jscaleInv_qFun hν]

theorem inner_Lv_Qv (k l : Fin 2) (s : ℝ) :
    inner ℂ (Lv hL k s) (Qv hQ l s) = gramAt κ ν c s k l := by
  rw [inner_Lv]
  have h1 : ∫ x in B0579.cell c, lam0Ker κ ν c k s x * (Qv hQ l s : ℝ × ℝ → ℂ) x =
      ∫ x in B0579.cell c, lam0Ker κ ν c k s x * qFun κ ν c l s x := by
    refine integral_congr_ae ?_
    filter_upwards [ae_cell_of_ae_cellMeasure (hQ l s).coeFn_toLp] with x hx
    have e : (Qv hQ l s : ℝ × ℝ → ℂ) x = qFun κ ν c l s x := hx
    rw [e]
  rw [h1]
  have h2 := cv_ker h6 (bandA_pos hν s) hc (IIIa.perLam0 κ (bandD ν c s) k) (qFun κ ν c l s)
  show _ = ∫ y in B0579.cell (IIIa.cellLen c (bandA ν s)),
      IIIa.perLam0 κ (bandD ν c s) k y * IIIa.perE κ (bandD ν c s) l y
  rw [show (∫ x in B0579.cell c, lam0Ker κ ν c k s x * qFun κ ν c l s x) =
      ∫ y in B0579.cell (IIIa.cellLen c (bandA ν s)),
        IIIa.perLam0 κ (bandD ν c s) k y * IIIa.JscaleInv (bandA ν s) (qFun κ ν c l s) y
      from h2.symm]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show IIIa.perLam0 κ (bandD ν c s) k y * IIIa.JscaleInv (bandA ν s) (qFun κ ν c l s) y = _
  rw [jscaleInv_qFun hν]

variable (hgram : ∀ s (i j : Fin 2), ∫ y in B0579.cell (bandD ν c s),
  IIIa.perLam κ (bandD ν c s) i y * IIIa.perE κ (bandD ν c s) j y = if i = j then 1 else 0)
include hgram hL hQ

/-- `ΛE = I₂` gives `G⁻¹G = I` (source 2894-2899). -/
theorem gram_inv_mul (s : ℝ) : (gramAt κ ν c s)⁻¹ * gramAt κ ν c s = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, ← inner_Lv_Qv hL hQ h6 hν hc 0 j s,
    ← inner_Lv_Qv hL hQ h6 hν hc 1 j s, ← inner_Ev_eq, inner_Ev_Qv hL hQ h6 hν hc, hgram,
    Matrix.one_apply]

/-- The finite Gram inverse exists along the band (source 2898-2899). -/
theorem det_gramAt_ne_zero (s : ℝ) : (gramAt κ ν c s).det ≠ 0 :=
  (Matrix.isUnit_det_of_left_inverse (gram_inv_mul hL hQ h6 hν hc hgram s)).ne_zero

end Construction

/-! ## Continuity in the age and the pair -/

section Pair

variable {κ : IIIa.PlanarFrameKernels} {ν c m : ℝ}
  {hL : ∀ k s, MemLp (dualVec m (lam0Ker κ ν c k s)) 2 (B0579.cellMeasure c m)}
  {hQ : ∀ k s, MemLp (qFun κ ν c k s) 2 (B0579.cellMeasure c m)}

theorem continuous_gramAt (h6 : IntegralCellDilate) (hν : 0 < ν) (hc : 0 < c)
    (hLc : ∀ k, Continuous (Lv hL k)) (hQc : ∀ k, Continuous (Qv hQ k)) :
    Continuous (gramAt κ ν c) := by
  have e : gramAt κ ν c = fun s => Matrix.of fun k l => inner ℂ (Lv hL k s) (Qv hQ l s) := by
    funext s
    ext k l
    rw [Matrix.of_apply, inner_Lv_Qv hL hQ h6 hν hc]
  rw [e]
  exact continuous_matrix fun k l => (hLc k).inner (hQc l)

theorem continuous_gramAt_inv (hG : Continuous (gramAt κ ν c))
    (hdet : ∀ s, (gramAt κ ν c s).det ≠ 0) : Continuous fun s => (gramAt κ ν c s)⁻¹ := by
  refine continuous_iff_continuousAt.2 fun s => ?_
  have h : ContinuousAt Ring.inverse (gramAt κ ν c s).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hdet s)
  exact (continuousAt_matrix_inv _ h).comp hG.continuousAt

theorem continuous_Ev (hinv : Continuous fun s => (gramAt κ ν c s)⁻¹)
    (hLc : ∀ k, Continuous (Lv hL k)) (i : Fin 2) : Continuous (Ev hL i) := by
  have h0 : Continuous fun s => conj ((gramAt κ ν c s)⁻¹ i 0) :=
    Complex.continuous_conj.comp (hinv.matrix_elem i 0)
  have h1 : Continuous fun s => conj ((gramAt κ ν c s)⁻¹ i 1) :=
    Complex.continuous_conj.comp (hinv.matrix_elem i 1)
  exact (h0.smul (hLc 0)).add (h1.smul (hLc 1))

/-- **The frozen pair at one regime**, from the facts on the explicit functions. -/
theorem frozenPair_nonempty [Fact (1 < m)] (h6 : IntegralCellDilate) (hν : 0 < ν) (hc : 0 < c)
    (hLc : ∀ k, Continuous (Lv hL k)) (hQc : ∀ k, Continuous (Qv hQ k))
    (hcirc : ∀ k s, ∫ x in B0579.cell c, qFun κ ν c k s x = 0)
    (heven : ∀ k s x, qFun κ ν c k s (-x) = qFun κ ν c k s x)
    (hconjQ : ∀ s x, qFun κ ν c 1 s x = conj (qFun κ ν c 0 s x))
    (hconjL : ∀ s x, ellKer κ ν c 1 s x = conj (ellKer κ ν c 0 s x))
    (hgram : ∀ s (i j : Fin 2), ∫ y in B0579.cell (bandD ν c s),
      IIIa.perLam κ (bandD ν c s) i y * IIIa.perE κ (bandD ν c s) j y = if i = j then 1 else 0) :
    Nonempty (FrozenPair κ ν c m) := by
  have hmem : ∀ k s, Qv hQ k s ∈ xmcSub c m := fun k s =>
    toLp_mem_xmcSub (hQ k s) (hcirc k s) (heven k s)
  have hdet := det_gramAt_ne_zero hL hQ h6 hν hc hgram
  have hEc : ∀ i, Continuous (Ev hL i) :=
    continuous_Ev (continuous_gramAt_inv (continuous_gramAt h6 hν hc hLc hQc) hdet) hLc
  let q : Bool → ℝ → Xmc c m := fun j s => ⟨Qv hQ (pmIdx j) s, hmem _ _⟩
  let ell : Bool → ℝ → Xmc c m →L[ℂ] ℂ := fun j s =>
    (innerSL ℂ (Ev hL (pmIdx j) s)).comp (xmcSub c m).subtypeL
  refine ⟨⟨q, ell, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro j s
    exact ae_cell_of_ae_cellMeasure (hQ (pmIdx j) s).coeFn_toLp
  · intro j s x
    exact inner_Ev_frozenEll hL h6 hν hc j s (x : XAmb c m)
  · intro s i j
    show inner ℂ (Ev hL (pmIdx i) s) (Qv hQ (pmIdx j) s) = _
    rw [inner_Ev_Qv hL hQ h6 hν hc, hgram]
    cases i <;> cases j <;> simp [pmIdx]
  · intro s
    refine xmc_ext ?_
    filter_upwards [ae_cell_of_ae_cellMeasure (hQ 1 s).coeFn_toLp, xFn_conjX (q true s),
      ae_cell_of_ae_cellMeasure (hQ 0 s).coeFn_toLp] with x h1 h2 h3
    have e1 : xFn (q false s) x = qFun κ ν c 1 s x := h1
    have e3 : xFn (q true s) x = qFun κ ν c 0 s x := h3
    rw [e1, h2, e3, hconjQ]
  · intro s x
    show inner ℂ (Ev hL 1 s) (x : XAmb c m) =
      conj (inner ℂ (Ev hL 0 s) ((conjX x : Xmc c m) : XAmb c m))
    rw [inner_Ev, inner_Ev, ← integral_conj]
    refine integral_congr_ae ?_
    filter_upwards [xFn_conjX x] with y hy
    have e : ((conjX x : Xmc c m) : XAmb c m) y = conj (xFn x y) := hy
    rw [e, map_mul, Complex.conj_conj, hconjL]
    rfl
  · intro j
    exact (hQc (pmIdx j)).subtype_mk _
  · intro j
    exact ((innerSL ℂ).continuous.comp (hEc (pmIdx j))).clm_comp continuous_const

end Pair

/-! ## The reduction -/

/-- **`FrozenPairExists` from the leaves** (source 2894-2912, 4352-4356, 3030-3035, 593-610). -/
theorem frozenPairExists_of (l1 : PerEContinuous) (l2 : PerLam0Continuous) (l3 : QFunPtCont)
    (l4 : Lam0KerPtCont) (l5 : QFunGaussBound) (l6 : GaussStripMemLp) (l7 : Lam0KerBdd)
    (l8 : QFunCirc) (l9 : IntegralCellDilate) (l10 : ContinuousToLpOfDominated)
    (l11 : SeedKernelEven) (l12 : SeedKernelMeanZero) (l13 : SeedDualConj) (l14 : PerLamConj) :
    FrozenPairExists := by
  intro κ hκ hF m hm
  obtain ⟨K, b₀, hb₀⟩ := hF m hm
  have hb : (0 : ℝ) < max b₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨ν₁, hν₁, hPF⟩ := hb₀ (max b₀ 1) (le_max_left _ _)
  refine ⟨min ν₁ (min (1 / (3 * max b₀ 1)) (1 / 4)),
    lt_min hν₁ (lt_min (by positivity) (by norm_num)), ?_⟩
  intro ν hν c hc hfact
  have hν0 : 0 < ν := hν.1
  have hνle : ν ≤ ν₁ := hν.2.trans (min_le_left _ _)
  have hνb : ν ≤ 1 / (3 * max b₀ 1) :=
    hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν4 : ν ≤ 1 / 4 := hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcR : c = ν ^ (-2 : ℝ) := by
    rw [hc, cOf, Real.rpow_neg hν0.le, Real.rpow_two]
  have hc16 : 16 ≤ c := by
    rw [hc, cOf]
    have h1 : ν ^ 2 ≤ 1 / 16 := by nlinarith
    have h2 : 0 < ν ^ 2 := by positivity
    rw [le_inv_comm₀ (by norm_num) h2]
    linarith
  have hc0 : 0 < c := by linarith
  have hm1 : 1 < m := by linarith
  have hEc : ∀ y, κ.e 1 y = conj (κ.e 0 y) := by
    obtain ⟨_, h, _, _, _, he0, he1, _⟩ := hκ
    intro y
    rw [he1, he0]
  -- continuity on the plane
  have hQx : ∀ k s, Continuous (qFun κ ν c k s) := fun k s => by
    show Continuous fun x : ℝ × ℝ => ((bandA ν s ^ (-2 : ℝ) : ℝ) : ℂ) *
      IIIa.perE κ (bandD ν c s) k (x.1 / Real.sqrt (bandA ν s), x.2 / Real.sqrt (bandA ν s))
    exact continuous_const.mul ((l1 κ _ k (bandD_pos hν0 hc0 s)).comp
      ((continuous_fst.div_const _).prodMk (continuous_snd.div_const _)))
  have hLx : ∀ k s, Continuous (lam0Ker κ ν c k s) := fun k s => by
    show Continuous fun x : ℝ × ℝ => (bandA ν s : ℂ) *
      IIIa.perLam0 κ (bandD ν c s) k (x.1 / Real.sqrt (bandA ν s), x.2 / Real.sqrt (bandA ν s))
    exact continuous_const.mul ((l2 κ _ k (bandD_pos hν0 hc0 s)).comp
      ((continuous_fst.div_const _).prodMk (continuous_snd.div_const _)))
  -- the classes in `L²(cell, ⟨x⟩^{2m}dx)`
  choose A hA using fun k => l5 κ ν c k hν0 hc16
  have hgQ : ∀ k, MemLp (fun x : ℝ × ℝ => A k * Real.exp (-(x.2 ^ 2) / 24)) 2
      (B0579.cellMeasure c m) := fun k => l6 c m (A k)
  have hQ : ∀ k s, MemLp (qFun κ ν c k s) 2 (B0579.cellMeasure c m) := fun k s =>
    (hgQ k).of_le (hQx k s).aestronglyMeasurable
      (Eventually.of_forall fun x => (hA k s x).trans (Real.le_norm_self _))
  choose M hM using fun k => l7 κ ν c k hν0 hc16
  have hL : ∀ k s, MemLp (dualVec m (lam0Ker κ ν c k s)) 2 (B0579.cellMeasure c m) :=
    fun k s => memLp_dualVec hm1 (hLx k s) (hM k s)
  -- continuity in the age
  have hQc : ∀ k, Continuous (Qv hQ k) := fun k =>
    l10 (B0579.cellMeasure c m) (qFun κ ν c k) (hQ k)
      (fun x => A k * Real.exp (-(x.2 ^ 2) / 24)) (hgQ k)
      (fun s => Eventually.of_forall (hA k s))
      (Eventually.of_forall fun x => l3 κ ν c k x hν0 hc16)
  have hLc : ∀ k, Continuous (Lv hL k) := fun k =>
    l10 (B0579.cellMeasure c m) (fun s => dualVec m (lam0Ker κ ν c k s)) (hL k)
      (fun x => M k * B0579.jb x ^ (-m)) ((memLp_jb_neg hm1).const_mul (M k))
      (fun s => norm_dualVec_le (hM k s))
      (Eventually.of_forall fun x =>
        (Complex.continuous_conj.comp (l4 κ ν c k x hν0 hc16)).mul continuous_const)
  -- the Gram identity at the band age
  have hgram : ∀ s (i j : Fin 2), ∫ y in B0579.cell (bandD ν c s),
      IIIa.perLam κ (bandD ν c s) i y * IIIa.perE κ (bandD ν c s) j y =
        if i = j then 1 else 0 := by
    intro s i j
    have h := (hPF ν ⟨hν0, hνle⟩).1 (bandAge ν s) (bandAge_nonneg s)
      (le_clockTheta_bandAge hν0 hb hνb s) i j
    subst hcR
    exact h
  exact frozenPair_nonempty l9 hν0 hc0 hLc hQc
    (fun k s => l8 κ ν c k s hν0 hc16 (l12 κ hκ k))
    (fun k s x => qFun_even (l11 κ hκ k) s x)
    (fun s x => qFun_conj hEc s x)
    (fun s x => ellKer_conj (fun d y => l14 κ d hEc (l13 κ hκ) y) s x)
    hgram

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair
