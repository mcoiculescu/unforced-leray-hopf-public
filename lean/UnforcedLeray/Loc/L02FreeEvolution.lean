import UnforcedLeray.Loc.L02FreeEvolution.Operators
import UnforcedLeray.Blueprint.Localization.Linear

/-!
# Step L2 `FreeEvolutionStep`: the free evolution `S₀(s)` and its three bounds

`paper/main.tex` lines 292–298 (`loc:eq:free-evolution`), blueprint unit B0712; the step
proposition is `Blueprint.FreeEvolutionStep`


> The free evolution is `S₀(s)f(y) = e^{s/2}[e^{h(e^s-1)Δ}f](e^{s/2}y)`. Its `X → X` norm is
> at most `C_h e^{-s/4}`, and its `L² → X` and `X → Z` norms are at most `C_h s^{-1/2}` for
> `0 < s ≤ 1`.  (lines 292–298)

Here `X = H¹_div`, `Z = H²_div` (line 268, `Blueprint/Localization/Spaces.lean`).

## Construction

With `t = h(e^s - 1)` and `D(s)` the similarity dilation `F ↦ e^{s/2} F(e^{s/2}·)` on `L²`
(see `L02FreeEvolution/Operators.lean`):
* `S0X h s = D(s) ∘ e^{tΔ}` on `X`, acting on `H¹` by `∂ᵢ ↦ e^{s/2} D(s) e^{tΔ} ∂ᵢ`;
* `S0L h s = D(s) ∘ e^{tΔ} : L²_div → X` for `t > 0`, with the Gaussian derivative kernels;
* `S0Z h s = D(s) ∘ e^{tΔ} : X → Z` for `t > 0`, with `∂ⱼ∂ᵢ ↦ e^{s} D(s) ∂ⱼ e^{tΔ} ∂ᵢ`.
For `t ≤ 0` (that is `s ≤ 0`) `S0L` and `S0Z` are `0`; the step speaks of them only at `s > 0`.
Each value is the literal formula (`AncientLocalization.freeEvolution`) a.e.

## Bounds

With `c` the compiled first-derivative kernel constant, `M = c/√(h/2)` and
`C = 1 + 3e + 9eM`:
* `X → X`: for `s ≤ 1` the components give `(1 + 3e) e^{-s/4}`; for `s ≥ 1`,
  `e^{s/2} e^{-s/4} c t^{-1/2} ≤ M e^{-s/4}` since `t ≥ (h/2) e^s`;
* `L² → X`, `X → Z` for `0 < s ≤ 1`: `t ≥ (h/2) s` gives `t^{-1/2} ≤ 1/(√(h/2) √s)`.

Main declaration: `freeEvolutionStep : Blueprint.FreeEvolutionStep`, with no hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.Loc.L02

open SobolevGraph Blueprint AncientLocalization

/-! ## Elementary real bounds -/

/-- `t^{-1/2} ≤ 1/√a` for `0 < a ≤ t`. -/
theorem rpow_neg_half_le {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    t ^ (-(1 : ℝ) / 2) ≤ 1 / Real.sqrt a := by
  have he : 1 / Real.sqrt a = a ^ (-(1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, neg_div, Real.rpow_neg ha.le]
    exact one_div _
  rw [he]
  exact Real.rpow_le_rpow_of_nonpos ha hat (by norm_num)

/-- For `s ≥ 1`, `h(e^s - 1) ≥ (h/2) e^s`. -/
theorem heatTime_ge_large {h s : ℝ} (hh : 0 < h) (hs : 1 ≤ s) :
    (h / 2) * Real.exp (s / 2) ^ 2 ≤ heatTime h s := by
  have he : Real.exp (s / 2) ^ 2 = Real.exp s := by
    rw [sq, ← Real.exp_add, add_halves]
  have h2 : 2 ≤ Real.exp s := by
    have h1 := Real.add_one_le_exp 1
    have h3 := Real.exp_le_exp.mpr hs
    linarith
  rw [he, heatTime]
  nlinarith

/-- For `s ≥ 0`, `h(e^s - 1) ≥ (h/2) s`. -/
theorem heatTime_ge_small {h s : ℝ} (hh : 0 < h) (hs : 0 ≤ s) :
    (h / 2) * s ≤ heatTime h s := by
  have h1 := Real.add_one_le_exp s
  rw [heatTime]
  nlinarith

/-! ## The three operators -/

/-- The inclusion `L²_div ⊂ L²`. -/
def Lincl : L2div →L[ℝ] L2Space := Leray.solenoidalSubspace.subtypeL

/-- `S₀(s) : X → X` (line 294). -/
def S0X (h s : ℝ) : X →L[ℝ] X :=
  (((dilH1 s).comp (heatH1 (heatTime h s))).comp Xincl).codRestrict Xsub
    (fun f => Submodule.mem_comap.mpr (dil_mem_solenoidal s
      (heat_mem_solenoidal _ (Submodule.mem_comap.mp (X.mem f)))))

/-- `S₀(s) : L²_div → X` at a positive heat time. -/
def S0Lpos {h s : ℝ} (ht : 0 < heatTime h s) : L2div →L[ℝ] X :=
  (((dilH1 s).comp (Heat.heatToH1 ht)).comp Lincl).codRestrict Xsub
    (fun F => by
      have hmem : Heat.heatOperator (heatTime h s) (Lclass F) ∈ Leray.solenoidalSubspace :=
        heat_mem_solenoidal _ (show ↥Leray.solenoidalSubspace from F).2
      rw [Heat.heatOperator_pos ht] at hmem
      exact Submodule.mem_comap.mpr (dil_mem_solenoidal s hmem))

/-- `S₀(s) : L²_div → X` (line 296), for `s > 0`; `0` otherwise. -/
def S0L (h s : ℝ) : L2div →L[ℝ] X :=
  if ht : 0 < heatTime h s then S0Lpos ht else 0

theorem S0L_of_pos {h s : ℝ} (ht : 0 < heatTime h s) : S0L h s = S0Lpos ht := dite_eq_left ht

/-- `S₀(s) : X → Z` at a positive heat time. -/
def S0Zpos {h s : ℝ} (ht : 0 < heatTime h s) : X →L[ℝ] Z :=
  (((dilH2 s).comp (heatH1toH2 ht)).comp Xincl).codRestrict Zsub
    (fun f => Submodule.mem_comap.mpr (dil_mem_solenoidal s
      (heat_mem_solenoidal _ (Submodule.mem_comap.mp (X.mem f)))))

/-- `S₀(s) : X → Z` (line 296), for `s > 0`; `0` otherwise. -/
def S0Z (h s : ℝ) : X →L[ℝ] Z :=
  if ht : 0 < heatTime h s then S0Zpos ht else 0

theorem S0Z_of_pos {h s : ℝ} (ht : 0 < heatTime h s) : S0Z h s = S0Zpos ht := dite_eq_left ht

/-- The free evolution of step L2. -/
def freeEvolutionOps (h : ℝ) : FreeEvolution := ⟨S0X h, S0L h, S0Z h⟩

theorem norm_X (f : X) : ‖f‖ = ‖f.toH1‖ := rfl

theorem norm_Z (g : Z) : ‖g‖ = ‖g.toH2‖ := rfl

theorem norm_L2div (F : L2div) : ‖F‖ = ‖Lclass F‖ := rfl

theorem norm_Xclass_le (f : X) : ‖Xclass f‖ ≤ ‖f‖ := h1_norm_value_le f.toH1

theorem norm_Xderivative_le (f : X) (i : Fin 3) : ‖f.toH1.derivative i‖ ≤ ‖f‖ :=
  h1_norm_derivative_le f.toH1 i

theorem Xclass_S0X (h s : ℝ) (f : X) : Xclass (S0X h s f) = freeL2 h s (Xclass f) :=
  dil_heatOperator h s (Xclass f)

theorem derivative_S0X (h s : ℝ) (f : X) (i : Fin 3) :
    (S0X h s f).toH1.derivative i = Real.exp (s / 2) • freeL2 h s (f.toH1.derivative i) := by
  rw [← dil_heatOperator]
  rfl

theorem toH1_S0L {h s : ℝ} (ht : 0 < heatTime h s) (F : L2div) :
    (S0L h s F).toH1 = dilH1 s (Heat.heatToH1 ht (Lclass F)) := by
  rw [S0L_of_pos ht]
  rfl

theorem Xclass_S0L {h s : ℝ} (ht : 0 < heatTime h s) (F : L2div) :
    Xclass (S0L h s F) = freeL2 h s (Lclass F) := by
  rw [Xclass, toH1_S0L ht, ← dil_heatOperator, Heat.heatOperator_pos ht]
  rfl

theorem toH2_S0Z {h s : ℝ} (ht : 0 < heatTime h s) (f : X) :
    (S0Z h s f).toH2 = dilH2 s (heatH1toH2 ht f.toH1) := by
  rw [S0Z_of_pos ht]
  rfl

theorem Zclass_S0Z {h s : ℝ} (ht : 0 < heatTime h s) (f : X) :
    Zclass (S0Z h s f) = freeL2 h s (Xclass f) := by
  rw [Zclass, toH2_S0Z ht, ← dil_heatOperator]
  rfl

/-! ## Representation by the literal formula -/

theorem S0X_rep (h s : ℝ) (f : X) :
    Xval (S0X h s f) =ᵐ[volume] freeEvolution h s (Xval f) := by
  unfold Xval
  rw [Xclass_S0X]
  exact coeFn_freeL2 h s _

theorem S0L_rep {h s : ℝ} (hh : 0 < h) (hs : 0 < s) (F : L2div) :
    Xval (S0L h s F) =ᵐ[volume] freeEvolution h s (Lval F) := by
  unfold Xval Lval
  rw [Xclass_S0L (heatTime_pos hh hs)]
  exact coeFn_freeL2 h s _

theorem S0Z_rep {h s : ℝ} (hh : 0 < h) (hs : 0 < s) (f : X) :
    Zval (S0Z h s f) =ᵐ[volume] freeEvolution h s (Xval f) := by
  unfold Zval Xval
  rw [Zclass_S0Z (heatTime_pos hh hs)]
  exact coeFn_freeL2 h s _

/-! ## Strong continuity on `X` -/

theorem isometry_Xincl : Isometry (Xincl : X → H1) :=
  AddMonoidHomClass.isometry_of_norm Xincl (fun _ => rfl)

theorem S0X_continuousOn {h : ℝ} (hh : 0 ≤ h) (f : X) :
    ContinuousOn (fun s => S0X h s f) (Ici 0) := by
  rw [isometry_Xincl.isEmbedding.isInducing.continuousOn_iff]
  apply (H1.continuousOn_iff_components _ _).mpr
  refine ⟨?_, fun i => ?_⟩
  · have hv : (fun s => ((Xincl ∘ fun s => S0X h s f) s).value) =
        fun s => freeL2 h s (Xclass f) := funext fun s => Xclass_S0X h s f
    rw [hv]
    exact continuousOn_freeL2 hh _
  · have hd : (fun s => ((Xincl ∘ fun s => S0X h s f) s).derivative i) =
        fun s => Real.exp (s / 2) • freeL2 h s (f.toH1.derivative i) :=
      funext fun s => derivative_S0X h s f i
    rw [hd]
    exact (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn.smul
      (continuousOn_freeL2 hh _)

/-! ## The bounds -/

/-- `M = c/√(h/2)`, with `c` the compiled first-derivative kernel constant. -/
def Mconst (h : ℝ) : ℝ := Heat.firstSmoothingConstant / Real.sqrt (h / 2)

/-- The constant `C_h = 1 + 3e + 9eM` of lines 296–298. -/
def Cconst (h : ℝ) : ℝ := 1 + 3 * Real.exp 1 + 9 * Real.exp 1 * Mconst h

theorem Mconst_nonneg (h : ℝ) : 0 ≤ Mconst h :=
  div_nonneg Heat.firstSmoothingConstant_pos.le (Real.sqrt_nonneg _)

theorem Cconst_pos (h : ℝ) : 0 < Cconst h := by
  have h1 : 0 ≤ 9 * Real.exp 1 * Mconst h :=
    mul_nonneg (by positivity) (Mconst_nonneg h)
  have h2 := Real.exp_pos 1
  rw [Cconst]
  linarith

/-- The value component of `S₀(s) f` decays like `e^{-s/4}`. -/
theorem norm_value_S0X_le (h s : ℝ) (f : X) :
    ‖(S0X h s f).toH1.value‖ ≤ Real.exp (-(s / 4)) * ‖f‖ := by
  calc ‖(S0X h s f).toH1.value‖ = ‖dil s (Heat.heatOperator (heatTime h s) (Xclass f))‖ := rfl
    _ ≤ Real.exp (-(s / 4)) * ‖Heat.heatOperator (heatTime h s) (Xclass f)‖ :=
      norm_dil_apply_le _ _
    _ ≤ Real.exp (-(s / 4)) * ‖f‖ :=
      mul_le_mul_of_nonneg_left
        ((Heat.heatOperator_apply_norm_le _ _).trans (norm_Xclass_le f)) (Real.exp_pos _).le

theorem norm_S0X_apply_le_small (h : ℝ) {s : ℝ} (hs1 : s ≤ 1) (f : X) :
    ‖S0X h s f‖ ≤ (1 + 3 * Real.exp 1) * (Real.exp (-(s / 4)) * ‖f‖) := by
  have hE : 0 ≤ Real.exp (-(s / 4)) * ‖f‖ := by positivity
  have hd : ∀ i, ‖(S0X h s f).toH1.derivative i‖ ≤
      Real.exp 1 * (Real.exp (-(s / 4)) * ‖f‖) := by
    intro i
    calc ‖(S0X h s f).toH1.derivative i‖ =
          ‖Real.exp (s / 2) • dil s (Heat.heatOperator (heatTime h s) (f.toH1.derivative i))‖ :=
          rfl
      _ = Real.exp (s / 2) *
          ‖dil s (Heat.heatOperator (heatTime h s) (f.toH1.derivative i))‖ :=
          norm_smul_of_nonneg (Real.exp_pos _).le _
      _ ≤ Real.exp 1 * (Real.exp (-(s / 4)) * ‖f‖) := by
        apply mul_le_mul (Real.exp_le_exp.mpr (by linarith)) _ (norm_nonneg _)
          (Real.exp_pos _).le
        refine (norm_dil_apply_le _ _).trans ?_
        exact mul_le_mul_of_nonneg_left
          ((Heat.heatOperator_apply_norm_le _ _).trans (norm_Xderivative_le f i))
          (Real.exp_pos _).le
  have hb := h1_norm_le_of hE (mul_nonneg (Real.exp_pos 1).le hE) (norm_value_S0X_le h s f) hd
  rw [norm_X]
  refine hb.trans_eq ?_
  ring

theorem norm_S0X_apply_le_large {h : ℝ} (hh : 0 < h) {s : ℝ} (hs1 : 1 ≤ s) (f : X) :
    ‖S0X h s f‖ ≤ (1 + 3 * Mconst h) * (Real.exp (-(s / 4)) * ‖f‖) := by
  have ht : 0 < heatTime h s := heatTime_pos hh (by linarith)
  have ha : 0 < (h / 2) * Real.exp (s / 2) ^ 2 := by positivity
  have hsq : 0 < Real.sqrt (h / 2) := Real.sqrt_pos.mpr (by positivity)
  have hT : heatTime h s ^ (-(1 : ℝ) / 2) ≤ 1 / (Real.sqrt (h / 2) * Real.exp (s / 2)) := by
    have h1 := rpow_neg_half_le ha (heatTime_ge_large hh hs1)
    rwa [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le] at h1
  have hE : 0 ≤ Real.exp (-(s / 4)) * ‖f‖ := by positivity
  have hd : ∀ i, ‖(S0X h s f).toH1.derivative i‖ ≤
      Mconst h * (Real.exp (-(s / 4)) * ‖f‖) := by
    intro i
    calc ‖(S0X h s f).toH1.derivative i‖ =
          ‖Real.exp (s / 2) • dil s (Heat.heatOperator (heatTime h s) (f.toH1.derivative i))‖ :=
          rfl
      _ = Real.exp (s / 2) *
          ‖dil s (Heat.heatOperator (heatTime h s) (f.toH1.derivative i))‖ :=
          norm_smul_of_nonneg (Real.exp_pos _).le _
      _ ≤ Real.exp (s / 2) * (Real.exp (-(s / 4)) *
          ‖Heat.firstDerivativeOperator ht i (Xclass f)‖) := by
        rw [heatOperator_derivative_eq ht (f.toH1.hasWeakDerivative i)]
        exact mul_le_mul_of_nonneg_left (norm_dil_apply_le _ _) (Real.exp_pos _).le
      _ ≤ Real.exp (s / 2) * (Real.exp (-(s / 4)) *
          ((Heat.firstSmoothingConstant * heatTime h s ^ (-(1 : ℝ) / 2)) * ‖f‖)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact (Heat.norm_firstDerivativeOperator_apply_le ht i _).trans
          (mul_le_mul_of_nonneg_left (norm_Xclass_le f)
            (mul_nonneg Heat.firstSmoothingConstant_pos.le (Real.rpow_nonneg ht.le _)))
      _ ≤ Real.exp (s / 2) * (Real.exp (-(s / 4)) *
          ((Heat.firstSmoothingConstant *
            (1 / (Real.sqrt (h / 2) * Real.exp (s / 2)))) * ‖f‖)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left hT Heat.firstSmoothingConstant_pos.le
      _ = Mconst h * (Real.exp (-(s / 4)) * ‖f‖) := by
        rw [Mconst]
        field_simp
  have hb := h1_norm_le_of hE (mul_nonneg (Mconst_nonneg h) hE) (norm_value_S0X_le h s f) hd
  rw [norm_X]
  refine hb.trans_eq ?_
  ring

theorem norm_S0X_le {h : ℝ} (hh : 0 < h) (s : ℝ) :
    ‖S0X h s‖ ≤ Cconst h * Real.exp (-(s / 4)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by have := Cconst_pos h; positivity)
  intro f
  have hE : 0 ≤ Real.exp (-(s / 4)) * ‖f‖ := by positivity
  have hM := Mconst_nonneg h
  have he := Real.exp_pos 1
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  rw [mul_assoc]
  rcases le_total s 1 with hs1 | hs1
  · refine (norm_S0X_apply_le_small h hs1 f).trans ?_
    apply mul_le_mul_of_nonneg_right _ hE
    rw [Cconst]
    nlinarith
  · refine (norm_S0X_apply_le_large hh hs1 f).trans ?_
    apply mul_le_mul_of_nonneg_right _ hE
    rw [Cconst]
    nlinarith

theorem norm_S0L_apply_le {h : ℝ} (hh : 0 < h) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (F : L2div) :
    ‖S0L h s F‖ ≤ (1 + 3 * (Real.exp 1 * Mconst h)) * (‖F‖ / Real.sqrt s) := by
  have ht := heatTime_pos hh hs0
  have hs : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have hs1' : Real.sqrt s ≤ 1 := Real.sqrt_le_one.mpr hs1
  have hF : ‖F‖ ≤ ‖F‖ / Real.sqrt s := le_div_self (norm_nonneg _) hs hs1'
  have hsq : 0 < Real.sqrt (h / 2) := Real.sqrt_pos.mpr (by positivity)
  have ha : 0 < (h / 2) * s := by positivity
  have hT : heatTime h s ^ (-(1 : ℝ) / 2) ≤ 1 / (Real.sqrt (h / 2) * Real.sqrt s) := by
    have h1 := rpow_neg_half_le ha (heatTime_ge_small hh hs0.le)
    rwa [Real.sqrt_mul' _ hs0.le] at h1
  have hexp : Real.exp (-(s / 4)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hE : 0 ≤ ‖F‖ / Real.sqrt s := by positivity
  have hv : ‖(S0L h s F).toH1.value‖ ≤ ‖F‖ / Real.sqrt s := by
    rw [toH1_S0L ht]
    calc ‖(dilH1 s (Heat.heatToH1 ht (Lclass F))).value‖ =
          ‖dil s (Heat.convolutionOperator (Heat.kernel (heatTime h s))
            (Heat.kernel_integrable ht) (Lclass F))‖ := rfl
      _ ≤ Real.exp (-(s / 4)) * ‖Heat.convolutionOperator (Heat.kernel (heatTime h s))
            (Heat.kernel_integrable ht) (Lclass F)‖ := norm_dil_apply_le _ _
      _ ≤ 1 * ‖F‖ :=
          mul_le_mul hexp (Heat.norm_heatConvolution_le ht _) (norm_nonneg _) zero_le_one
      _ ≤ ‖F‖ / Real.sqrt s := by rw [one_mul]; exact hF
  have hd : ∀ i, ‖(S0L h s F).toH1.derivative i‖ ≤
      Real.exp 1 * Mconst h * (‖F‖ / Real.sqrt s) := by
    intro i
    rw [toH1_S0L ht]
    calc ‖(dilH1 s (Heat.heatToH1 ht (Lclass F))).derivative i‖ =
          ‖Real.exp (s / 2) • dil s (Heat.firstDerivativeOperator ht i (Lclass F))‖ := rfl
      _ = Real.exp (s / 2) * ‖dil s (Heat.firstDerivativeOperator ht i (Lclass F))‖ :=
          norm_smul_of_nonneg (Real.exp_pos _).le _
      _ ≤ Real.exp 1 * (Real.exp (-(s / 4)) *
            ‖Heat.firstDerivativeOperator ht i (Lclass F)‖) :=
          mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (norm_dil_apply_le _ _)
            (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp 1 * (1 * ((Heat.firstSmoothingConstant *
            heatTime h s ^ (-(1 : ℝ) / 2)) * ‖F‖)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact mul_le_mul hexp (Heat.norm_firstDerivativeOperator_apply_le ht i _)
            (norm_nonneg _) zero_le_one
      _ ≤ Real.exp 1 * (1 * ((Heat.firstSmoothingConstant *
            (1 / (Real.sqrt (h / 2) * Real.sqrt s))) * ‖F‖)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          apply mul_le_mul_of_nonneg_left _ zero_le_one
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left hT Heat.firstSmoothingConstant_pos.le
      _ = Real.exp 1 * Mconst h * (‖F‖ / Real.sqrt s) := by
          rw [Mconst]
          field_simp
  have hb := h1_norm_le_of hE
    (mul_nonneg (mul_nonneg (Real.exp_pos 1).le (Mconst_nonneg h)) hE) hv hd
  rw [norm_X]
  refine hb.trans_eq ?_
  ring

theorem norm_S0Z_apply_le {h : ℝ} (hh : 0 < h) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (f : X) :
    ‖S0Z h s f‖ ≤ Cconst h * (‖f‖ / Real.sqrt s) := by
  have ht := heatTime_pos hh hs0
  have hs : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have hs1' : Real.sqrt s ≤ 1 := Real.sqrt_le_one.mpr hs1
  have hf : ‖f‖ ≤ ‖f‖ / Real.sqrt s := le_div_self (norm_nonneg _) hs hs1'
  have hsq : 0 < Real.sqrt (h / 2) := Real.sqrt_pos.mpr (by positivity)
  have ha : 0 < (h / 2) * s := by positivity
  have hT : heatTime h s ^ (-(1 : ℝ) / 2) ≤ 1 / (Real.sqrt (h / 2) * Real.sqrt s) := by
    have h1 := rpow_neg_half_le ha (heatTime_ge_small hh hs0.le)
    rwa [Real.sqrt_mul' _ hs0.le] at h1
  have hexp : Real.exp (-(s / 4)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hE : 0 ≤ ‖f‖ / Real.sqrt s := by positivity
  have hv : ‖(S0Z h s f).toH2.value‖ ≤ ‖f‖ / Real.sqrt s := by
    rw [toH2_S0Z ht]
    calc ‖(dilH2 s (heatH1toH2 ht f.toH1)).value‖ =
          ‖dil s (Heat.heatOperator (heatTime h s) (Xclass f))‖ := rfl
      _ ≤ Real.exp (-(s / 4)) * ‖Heat.heatOperator (heatTime h s) (Xclass f)‖ :=
          norm_dil_apply_le _ _
      _ ≤ 1 * ‖f‖ :=
          mul_le_mul hexp ((Heat.heatOperator_apply_norm_le _ _).trans (norm_Xclass_le f))
            (norm_nonneg _) zero_le_one
      _ ≤ ‖f‖ / Real.sqrt s := by rw [one_mul]; exact hf
  have h1 : ∀ i, ‖(S0Z h s f).toH2.first i‖ ≤ Real.exp 1 * (‖f‖ / Real.sqrt s) := by
    intro i
    rw [toH2_S0Z ht]
    calc ‖(dilH2 s (heatH1toH2 ht f.toH1)).first i‖ =
          ‖Real.exp (s / 2) • dil s (Heat.heatOperator (heatTime h s) (f.toH1.derivative i))‖ :=
          rfl
      _ = Real.exp (s / 2) *
          ‖dil s (Heat.heatOperator (heatTime h s) (f.toH1.derivative i))‖ :=
          norm_smul_of_nonneg (Real.exp_pos _).le _
      _ ≤ Real.exp 1 * (Real.exp (-(s / 4)) *
          ‖Heat.heatOperator (heatTime h s) (f.toH1.derivative i)‖) :=
          mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (norm_dil_apply_le _ _)
            (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp 1 * (1 * ‖f‖) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact mul_le_mul hexp
            ((Heat.heatOperator_apply_norm_le _ _).trans (norm_Xderivative_le f i))
            (norm_nonneg _) zero_le_one
      _ ≤ Real.exp 1 * (‖f‖ / Real.sqrt s) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left hf (Real.exp_pos _).le
  have h2 : ∀ i j, ‖(S0Z h s f).toH2.second i j‖ ≤
      Real.exp 1 * Mconst h * (‖f‖ / Real.sqrt s) := by
    intro i j
    rw [toH2_S0Z ht]
    calc ‖(dilH2 s (heatH1toH2 ht f.toH1)).second i j‖ =
          ‖Real.exp s • dil s (Heat.firstDerivativeOperator ht j (f.toH1.derivative i))‖ :=
          rfl
      _ = Real.exp s * ‖dil s (Heat.firstDerivativeOperator ht j (f.toH1.derivative i))‖ :=
          norm_smul_of_nonneg (Real.exp_pos _).le _
      _ ≤ Real.exp 1 * (Real.exp (-(s / 4)) *
            ‖Heat.firstDerivativeOperator ht j (f.toH1.derivative i)‖) :=
          mul_le_mul (Real.exp_le_exp.mpr hs1) (norm_dil_apply_le _ _)
            (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp 1 * (1 * ((Heat.firstSmoothingConstant *
            heatTime h s ^ (-(1 : ℝ) / 2)) * ‖f‖)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          refine mul_le_mul hexp ?_ (norm_nonneg _) zero_le_one
          exact (Heat.norm_firstDerivativeOperator_apply_le ht j _).trans
            (mul_le_mul_of_nonneg_left (norm_Xderivative_le f i)
              (mul_nonneg Heat.firstSmoothingConstant_pos.le (Real.rpow_nonneg ht.le _)))
      _ ≤ Real.exp 1 * (1 * ((Heat.firstSmoothingConstant *
            (1 / (Real.sqrt (h / 2) * Real.sqrt s))) * ‖f‖)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          apply mul_le_mul_of_nonneg_left _ zero_le_one
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left hT Heat.firstSmoothingConstant_pos.le
      _ = Real.exp 1 * Mconst h * (‖f‖ / Real.sqrt s) := by
          rw [Mconst]
          field_simp
  have hb := h2_norm_le_of hE (mul_nonneg (Real.exp_pos 1).le hE)
    (mul_nonneg (mul_nonneg (Real.exp_pos 1).le (Mconst_nonneg h)) hE) hv h1 h2
  rw [norm_Z]
  refine hb.trans_eq ?_
  rw [Cconst]
  ring

theorem norm_S0L_le {h : ℝ} (hh : 0 < h) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ‖S0L h s‖ ≤ Cconst h / Real.sqrt s := by
  have hs : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (Cconst_pos h).le hs.le)
  intro F
  refine (norm_S0L_apply_le hh hs0 hs1 F).trans ?_
  have hM := Mconst_nonneg h
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hc : 1 + 3 * (Real.exp 1 * Mconst h) ≤ Cconst h := by
    rw [Cconst]
    nlinarith
  calc (1 + 3 * (Real.exp 1 * Mconst h)) * (‖F‖ / Real.sqrt s) ≤
        Cconst h * (‖F‖ / Real.sqrt s) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = Cconst h / Real.sqrt s * ‖F‖ := by ring

theorem norm_S0Z_le {h : ℝ} (hh : 0 < h) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ‖S0Z h s‖ ≤ Cconst h / Real.sqrt s := by
  have hs : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (Cconst_pos h).le hs.le)
  intro f
  refine (norm_S0Z_apply_le hh hs0 hs1 f).trans_eq ?_
  ring

/-! ## Step L2 -/

/-- The free evolution of line 294 satisfies `IsFreeEvolution` for every `h > 0`. -/
theorem isFreeEvolution_freeEvolutionOps {h : ℝ} (hh : 0 < h) :
    IsFreeEvolution h (freeEvolutionOps h) where
  rep := fun s _ f => S0X_rep h s f
  repL := fun _ hs F => S0L_rep hh hs F
  repZ := fun _ hs f => S0Z_rep hh hs f
  strongly_continuous := fun f => S0X_continuousOn hh.le f
  bounds := ⟨Cconst h, Cconst_pos h, fun s _ => norm_S0X_le hh s,
    fun _ hs0 hs1 => ⟨norm_S0L_le hh hs0 hs1, norm_S0Z_le hh hs0 hs1⟩⟩

/-- **Step L2** `FreeEvolutionStep` (`paper/main.tex` lines 292–298,
`loc:eq:free-evolution`, blueprint unit B0712), proved with no hypothesis. -/
theorem freeEvolutionStep : FreeEvolutionStep :=
  fun h hh => ⟨freeEvolutionOps h, isFreeEvolution_freeEvolutionOps hh⟩

/-! Axiom audit: `[propext, Classical.choice, Quot.sound]`. -/
#print axioms freeEvolutionStep

end UnforcedLeray.Loc.L02
