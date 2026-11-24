import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import UnforcedLeray.Units.B0579

/-!
# B0581 helper: horizontal Fourier modes on the cylinder cell

Blueprint unit **B0581** (`paper/main.tex` lines 9407–9412), infrastructure for the
decomposition "into horizontal mean and nonzero modes" (line 9409) of a field on the
centered meridional cell `cell c = [-c/2, c/2) × ℝ` of the cylinder `(ℝ/cℤ) × ℝ`
(`B0579.cell`, `paper/main.tex:9370`).

* `eMode c k q = exp(2π i k q / c)`: the `k`-th horizontal mode, horizontal frequency
  `2πk/c ∈ (2π/c)ℤ`.
* `tensorLI c k : L²(ℝ; F) →ₗᵢ L²(cell; F)`, `g ↦ (√c)⁻¹ e_k(q) g(η)`; these form an orthogonal
  family (`orthogonalFamily_tensor`).
* `synth c : ℓ²(ℤ; L²(ℝ; F)) →ₗᵢ L²(cell; F)`, `(g_k) ↦ ∑ₖ (√c)⁻¹ e_k(q) g_k(η)` (the mode
  series; `hasSum_synth`), and its adjoint `modes c` (the horizontal Fourier coefficients,
  normalized so that `synth` is an isometry; `modes_synth`).

All measures are unnormalized Lebesgue measures on one cell, as in the manuscript
(`paper/main.tex:2110-2111`). Fields are `F`-valued for a complex Hilbert space `F`
(`F = ℂ` for the vorticity, `F = ℂ²` for the velocity).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Complex
open scoped ENNReal NNReal InnerProductSpace Real ComplexConjugate

namespace UnforcedLeray.B0581

/-- The centered horizontal period `[-c/2, c/2)`. -/
def qInt (c : ℝ) : Set ℝ := Ico (-(c / 2)) (c / 2)

theorem measurableSet_qInt (c : ℝ) : MeasurableSet (qInt c) := measurableSet_Ico

/-- Lebesgue measure on the horizontal period. -/
abbrev μq (c : ℝ) : Measure ℝ := volume.restrict (qInt c)

instance (c : ℝ) : IsFiniteMeasure (μq c) := by
  unfold μq qInt; infer_instance

/-- Unweighted Lebesgue measure on the centered cell `[-c/2, c/2) × ℝ`. -/
abbrev cellVol (c : ℝ) : Measure B0579.Plane := volume.restrict (B0579.cell c)

theorem cellVol_eq (c : ℝ) : cellVol c = (μq c).prod (volume : Measure ℝ) := by
  rw [cellVol, B0579.cell, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ]
  rfl

/-! ### The horizontal modes `e_k` -/

/-- The horizontal mode `e_k(q) = exp(2π i k q / c)`. -/
def eMode (c : ℝ) (k : ℤ) (q : ℝ) : ℂ := Complex.exp (((2 * π * k * q / c : ℝ) : ℂ) * I)

theorem norm_eMode (c : ℝ) (k : ℤ) (q : ℝ) : ‖eMode c k q‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem continuous_eMode (c : ℝ) (k : ℤ) : Continuous (eMode c k) := by
  unfold eMode; fun_prop

theorem eMode_zero (c q : ℝ) : eMode c 0 q = 1 := by
  simp [eMode]

theorem conj_eMode_mul (c : ℝ) (k j : ℤ) (q : ℝ) :
    conj (eMode c k q) * eMode c j q = eMode c (j - k) q := by
  unfold eMode
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Orthogonality of the horizontal modes over one period. -/
theorem integral_eMode {c : ℝ} (hc : 0 < c) (n : ℤ) :
    ∫ q in qInt c, eMode c n q = if n = 0 then (c : ℂ) else 0 := by
  split_ifs with hn
  · subst hn
    simp only [eMode_zero, integral_const]
    rw [Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter, qInt,
      Real.volume_Ico, ENNReal.toReal_ofReal (by linarith), Complex.real_smul, mul_one]
    push_cast
    ring
  · rw [qInt, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hfun : (fun q : ℝ => eMode c n q) =
        fun q : ℝ => Complex.exp ((2 * π * n / c * I : ℂ) * q) := by
      funext q
      unfold eMode
      congr 1
      push_cast
      ring
    have ha : (2 * π * n / c * I : ℂ) ≠ 0 := by
      have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hn', hpi, hc', I_ne_zero]
    rw [hfun, integral_exp_mul_complex ha]
    have key : (2 * π * n / c * I : ℂ) * ((c / 2 : ℝ) : ℂ) =
        (2 * π * n / c * I : ℂ) * ((-(c / 2) : ℝ) : ℂ) + n * (2 * π * I) := by
      push_cast
      field_simp
      ring
    rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, sub_self, zero_div]

/-! ### The tensor fields `(√c)⁻¹ e_k(q) g(η)` -/

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- `(√c)⁻¹ e_k(q) g(η)`. -/
def tensorFun (c : ℝ) (k : ℤ) (g : ℝ → F) (x : B0579.Plane) : F :=
  (((Real.sqrt c)⁻¹ : ℝ) * eMode c k x.1 : ℂ) • g x.2

theorem norm_tensorFun (c : ℝ) (k : ℤ) (g : ℝ → F) (x : B0579.Plane) :
    ‖tensorFun c k g x‖ = (Real.sqrt c)⁻¹ * ‖g x.2‖ := by
  rw [tensorFun, norm_smul, norm_mul, norm_eMode, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg c))]

theorem memLp_tensorFun (c : ℝ) (k : ℤ) {g : ℝ → F} (hg : MemLp g 2 volume) :
    MemLp (tensorFun c k g) 2 (cellVol c) := by
  rw [cellVol_eq]
  have h1 : MemLp (fun x : ℝ × ℝ => g x.2) 2 ((μq c).prod volume) := hg.comp_snd _
  refine (h1.const_smul (((Real.sqrt c)⁻¹ : ℝ) : ℂ)).of_le ?_ (Eventually.of_forall fun x => ?_)
  · exact (((continuous_const.mul (continuous_eMode c k)).comp
      continuous_fst).aestronglyMeasurable).smul h1.1
  · rw [norm_tensorFun, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg c))]

theorem tensorFun_ae_congr (c : ℝ) (k : ℤ) {g h : ℝ → F} (hgh : g =ᵐ[volume] h) :
    tensorFun c k g =ᵐ[cellVol c] tensorFun c k h := by
  rw [cellVol_eq]
  have := Measure.quasiMeasurePreserving_snd (μ := μq c) (ν := (volume : Measure ℝ))
  filter_upwards [this.ae_eq_comp hgh] with x hx
  simp only [Function.comp_apply] at hx
  simp only [tensorFun, hx]

variable [CompleteSpace F]

/-- The linear map `g ↦ (√c)⁻¹ e_k(q) g(η)`, `L²(ℝ; F) → L²(cell; F)`. -/
def tensorLM (c : ℝ) (k : ℤ) : Lp F 2 (volume : Measure ℝ) →ₗ[ℂ] Lp F 2 (cellVol c) where
  toFun g := (memLp_tensorFun c k (Lp.memLp g)).toLp _
  map_add' g h := by
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    filter_upwards [tensorFun_ae_congr c k (Lp.coeFn_add g h)] with x hx
    rw [hx]
    simp only [tensorFun, Pi.add_apply, smul_add]
  map_smul' a g := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    filter_upwards [tensorFun_ae_congr c k (Lp.coeFn_smul a g)] with x hx
    rw [hx]
    simp only [tensorFun, Pi.smul_apply, smul_comm _ a]

theorem coeFn_tensorLM (c : ℝ) (k : ℤ) (g : Lp F 2 (volume : Measure ℝ)) :
    tensorLM c k g =ᵐ[cellVol c] tensorFun c k g :=
  MemLp.coeFn_toLp (memLp_tensorFun c k (Lp.memLp g))

theorem inner_tensorFun (c : ℝ) (hc : 0 < c) (k j : ℤ) (g h : ℝ → F) (x : B0579.Plane) :
    ⟪tensorFun c k g x, tensorFun c j h x⟫_ℂ =
      ((c⁻¹ : ℝ) * eMode c (j - k) x.1 : ℂ) * ⟪g x.2, h x.2⟫_ℂ := by
  simp only [tensorFun, inner_smul_left, inner_smul_right, ← conj_eMode_mul]
  have hs : ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ : ℝ) = c⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hc.le]
  rw [← hs]
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- Orthogonality relations: `⟪V_k g, V_j h⟫ = δ_{kj} ⟪g, h⟫`. -/
theorem inner_tensorLM {c : ℝ} (hc : 0 < c) (k j : ℤ) (g h : Lp F 2 (volume : Measure ℝ)) :
    ⟪tensorLM c k g, tensorLM c j h⟫_ℂ = if k = j then ⟪g, h⟫_ℂ else 0 := by
  rw [L2.inner_def, L2.inner_def]
  have e1 : ∀ᵐ x ∂cellVol c, ⟪(tensorLM c k g : B0579.Plane → F) x, (tensorLM c j h) x⟫_ℂ =
      ((c⁻¹ : ℝ) * eMode c (j - k) x.1 : ℂ) * ⟪(g : ℝ → F) x.2, (h : ℝ → F) x.2⟫_ℂ := by
    filter_upwards [coeFn_tensorLM c k g, coeFn_tensorLM c j h] with x h1 h2
    rw [h1, h2, inner_tensorFun c hc]
  rw [integral_congr_ae e1, cellVol_eq,
    integral_prod_mul (fun q => ((c⁻¹ : ℝ) * eMode c (j - k) q : ℂ))
      (fun η => ⟪(g : ℝ → F) η, (h : ℝ → F) η⟫_ℂ),
    integral_const_mul, integral_eMode hc]
  by_cases hkj : k = j
  · subst hkj
    simp only [sub_self, if_true]
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    push_cast
    field_simp
  · have : j - k ≠ 0 := sub_ne_zero.mpr (Ne.symm hkj)
    simp [this, hkj]

/-- The isometry `g ↦ (√c)⁻¹ e_k(q) g(η)`. -/
def tensorLI (c : ℝ) [hc : Fact (0 < c)] (k : ℤ) :
    Lp F 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp F 2 (cellVol c) :=
  { tensorLM c k with
    norm_map' := fun g => by
      have h := inner_tensorLM hc.out k k g g
      rw [if_pos rfl] at h
      have h2 : ‖tensorLM c k g‖ ^ 2 = ‖g‖ ^ 2 := by
        rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ]
        exact congrArg RCLike.re h
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2 }

theorem tensorLI_apply (c : ℝ) [Fact (0 < c)] (k : ℤ) (g : Lp F 2 (volume : Measure ℝ)) :
    tensorLI c k g = tensorLM c k g := rfl

theorem orthogonalFamily_tensor (c : ℝ) [hc : Fact (0 < c)] :
    OrthogonalFamily ℂ (fun _ : ℤ => Lp F 2 (volume : Measure ℝ))
      (fun k => (tensorLI c k : Lp F 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp F 2 (cellVol c))) := by
  intro k j hkj g h
  simp only [tensorLI_apply]
  rw [inner_tensorLM hc.out, if_neg hkj]

/-- Mode sequences `(g_k)_{k ∈ ℤ}` with `∑ ‖g_k‖² < ∞`: `ℓ²(ℤ; L²(ℝ; F))`. -/
abbrev ModeSeq (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℂ F] : Type :=
  lp (fun _ : ℤ => Lp F 2 (volume : Measure ℝ)) 2

/-- **Mode synthesis** `(g_k) ↦ ∑ₖ (√c)⁻¹ e_k(q) g_k(η)`, an isometry `ℓ²(ℤ; L²(ℝ)) → L²(cell)`. -/
def synth (c : ℝ) [Fact (0 < c)] : ModeSeq F →ₗᵢ[ℂ] Lp F 2 (cellVol c) :=
  (orthogonalFamily_tensor (F := F) c).linearIsometry

theorem hasSum_synth (c : ℝ) [Fact (0 < c)] (g : ModeSeq F) :
    HasSum (fun k => tensorLI c k (g k)) (synth c g) :=
  (orthogonalFamily_tensor (F := F) c).hasSum_linearIsometry g

theorem synth_single (c : ℝ) [Fact (0 < c)] (k : ℤ) (g : Lp F 2 (volume : Measure ℝ)) :
    synth c (lp.single 2 k g : ModeSeq F) = tensorLI c k g :=
  (orthogonalFamily_tensor (F := F) c).linearIsometry_apply_single g

/-- **Horizontal Fourier coefficients** `ω ↦ (ω_k)_k`, the adjoint of `synth`. Its explicit form
is `modes_apply_ae` in `B0581/Coeff.lean` (`(modes ω)_k(η) = √c · c⁻¹ ∫ e^{-2πikq/c} ω(q, η) dq`
for a.e. `η`). -/
def modes (c : ℝ) [Fact (0 < c)] : Lp F 2 (cellVol c) →L[ℂ] ModeSeq F :=
  ContinuousLinearMap.adjoint (synth (F := F) c).toContinuousLinearMap

theorem inner_modes (c : ℝ) [Fact (0 < c)] (g : ModeSeq F) (ω : Lp F 2 (cellVol c)) :
    ⟪g, modes c ω⟫_ℂ = ⟪synth c g, ω⟫_ℂ := by
  rw [modes, ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem inner_modes_apply (c : ℝ) [Fact (0 < c)] (k : ℤ) (g : Lp F 2 (volume : Measure ℝ))
    (ω : Lp F 2 (cellVol c)) :
    ⟪g, (modes c ω : ModeSeq F) k⟫_ℂ = ⟪tensorLI c k g, ω⟫_ℂ := by
  have h := lp.inner_single_left (𝕜 := ℂ) (G := fun _ : ℤ => Lp F 2 (volume : Measure ℝ))
    k g (modes c ω)
  rw [inner_modes, synth_single] at h
  exact h.symm

theorem modes_synth (c : ℝ) [Fact (0 < c)] (g : ModeSeq F) : modes c (synth c g) = g := by
  refine ext_inner_left ℂ fun h => ?_
  rw [inner_modes, LinearIsometry.inner_map_map]

theorem norm_modes_le (c : ℝ) [Fact (0 < c)] (ω : Lp F 2 (cellVol c)) :
    ‖modes c ω‖ ≤ ‖ω‖ := by
  have h1 : ‖modes c ω‖ ^ 2 = RCLike.re ⟪synth c (modes c ω), ω⟫_ℂ := by
    rw [← inner_modes, @norm_sq_eq_re_inner ℂ]
  have h2 : RCLike.re ⟪synth c (modes c ω), ω⟫_ℂ ≤ ‖modes c ω‖ * ‖ω‖ := by
    calc RCLike.re ⟪synth c (modes c ω), ω⟫_ℂ ≤ ‖⟪synth c (modes c ω), ω⟫_ℂ‖ :=
          RCLike.re_le_norm _
      _ ≤ ‖synth c (modes c ω)‖ * ‖ω‖ := norm_inner_le_norm _ _
      _ = ‖modes c ω‖ * ‖ω‖ := by rw [LinearIsometry.norm_map]
  rcases (norm_nonneg (modes c ω)).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

end UnforcedLeray.B0581
