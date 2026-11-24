import UnforcedLeray.Lib.ComplexODEC.Quadrupole

/-!
# Gaussian derivative bounds for the mode (INF18 O14)

Scoping note `scoping/INF10-INF12-INF18-Planar.md` §4 bypass B4 ("Bounds") and §5 target O14.
Manuscript `paper/main.tex` lines 1154--1179 (units B0052, B0054) and the derivative bound of
Proposition `prop:gaussian-existence` (lines 971--976).

The mode is `q = h(r) e^{2iϑ}` (`modeQ c F = ofProfile 2 h`). By the matching of
`Lib/ComplexODEC/Mode`, `q(y) = y² β(|y|²)` with `β = β₀ κ_c b` smooth on `ℝ`
(`modeQ_eq`), so `q` is `C^∞` on `ℝ²` (`contDiff_modeQ`, tex lines 1165--1167). The bounds:
* `κ_c` and all its derivatives are `≤ C (1+s)^N e^{-s/4}` on `s ≥ 0` (tex line 1176:
  `|Ω - c| ≥ Im c`), via `κ = (s/4 - 2) · e^{-s/4} · (e^{-s/4} - c)⁻¹` and Faà di Bruno;
* `b` and all its derivatives are polynomially bounded on `s ≥ 0`: on `[0, 1]` by
  compactness, `b, b'` bounded on `[1, ∞)` by the far field (`b(s) = F(½ log s)/(β₀ s)`),
  and the higher derivatives by induction from `s b^{(m+2)} = (κb)^{(m)}/4 - (m+3) b^{(m+1)}`;
* Leibniz (`DerivBoundUpTo.mul`) and the Cartesian chain rule for `y² β(|y|²)`
  (`Planar.norm_iteratedFDeriv_angularTwo_le`, P9).

Main result: `norm_iteratedFDeriv_modeQ_le` (O14 for `q`). The same bound for `U_G h_X` (the
adjoint eigenfunction) is not proved here.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory Finset
open scoped ContDiff Nat

namespace UnforcedLeray.ComplexODEC

open UnforcedLeray.GaussianVortex UnforcedLeray.Rayleigh UnforcedLeray.Sturm

/-! ### Derivative bounds with weights -/

/-- `‖f^{(m)}(s)‖ ≤ C (1 + |s|)^N w(s)` on `S` for every order `m ≤ k`. -/
def DerivBoundUpTo (w : ℝ → ℝ) (S : Set ℝ) (f : ℝ → ℂ) (k : ℕ) : Prop :=
  ∀ m ≤ k, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
    ∀ s ∈ S, ‖iteratedDeriv m f s‖ ≤ C * (1 + |s|) ^ N * w s

/-- `DerivBoundUpTo` at every order. -/
def DerivBound (w : ℝ → ℝ) (S : Set ℝ) (f : ℝ → ℂ) : Prop := ∀ k, DerivBoundUpTo w S f k

theorem one_le_one_add_abs (s : ℝ) : 1 ≤ 1 + |s| := le_add_of_nonneg_right (abs_nonneg s)

theorem natCast_le_infty (m : ℕ) : (m : ℕ∞ω) ≤ ∞ := by
  exact_mod_cast WithTop.coe_le_coe.mpr (le_top : (m : ℕ∞) ≤ ⊤)

theorem natCast_lt_infty (m : ℕ) : (m : ℕ∞ω) < ∞ := by
  exact_mod_cast WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m)

theorem contDiffAt_of_infty {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (m : ℕ) (x : ℝ) :
    ContDiffAt ℝ m f x :=
  (hf.of_le (natCast_le_infty m)).contDiffAt

namespace DerivBoundUpTo

variable {w w₁ w₂ : ℝ → ℝ} {S T : Set ℝ} {f g : ℝ → ℂ} {k : ℕ}

theorem mono (h : DerivBoundUpTo w S f k) {j : ℕ} (hj : j ≤ k) : DerivBoundUpTo w S f j :=
  fun m hm => h m (hm.trans hj)

theorem mono_set (h : DerivBoundUpTo w S f k) (hTS : T ⊆ S) : DerivBoundUpTo w T f k :=
  fun m hm => by
    obtain ⟨C, N, hC, hb⟩ := h m hm
    exact ⟨C, N, hC, fun s hs => hb s (hTS hs)⟩

theorem mono_weight (h : DerivBoundUpTo w₁ S f k) (hw : ∀ s ∈ S, w₁ s ≤ w₂ s) :
    DerivBoundUpTo w₂ S f k := fun m hm => by
  obtain ⟨C, N, hC, hb⟩ := h m hm
  refine ⟨C, N, hC, fun s hs => (hb s hs).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (hw s hs) (by positivity)

theorem union (h₁ : DerivBoundUpTo w S f k) (h₂ : DerivBoundUpTo w T f k)
    (hw : ∀ s ∈ S ∪ T, 0 ≤ w s) : DerivBoundUpTo w (S ∪ T) f k := fun m hm => by
  obtain ⟨C₁, N₁, hC₁, hb₁⟩ := h₁ m hm
  obtain ⟨C₂, N₂, hC₂, hb₂⟩ := h₂ m hm
  refine ⟨C₁ + C₂, N₁ + N₂, by positivity, fun s hs => ?_⟩
  have h1 := one_le_one_add_abs s
  have hws := hw s hs
  rcases hs with hs | hs
  · refine (hb₁ s hs).trans ?_
    have : (1 + |s|) ^ N₁ ≤ (1 + |s|) ^ (N₁ + N₂) := pow_le_pow_right₀ h1 (by omega)
    have h3 : C₁ ≤ C₁ + C₂ := by linarith
    gcongr
  · refine (hb₂ s hs).trans ?_
    have : (1 + |s|) ^ N₂ ≤ (1 + |s|) ^ (N₁ + N₂) := pow_le_pow_right₀ h1 (by omega)
    have h3 : C₂ ≤ C₁ + C₂ := by linarith
    gcongr

theorem const_mul (h : DerivBoundUpTo w S f k) (a : ℂ) :
    DerivBoundUpTo w S (fun s => a * f s) k := fun m hm => by
  obtain ⟨C, N, hC, hb⟩ := h m hm
  refine ⟨‖a‖ * C, N, by positivity, fun s hs => ?_⟩
  rw [iteratedDeriv_const_mul_field, norm_mul, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using hb s hs) (norm_nonneg a)

/-- **Leibniz**: weighted derivative bounds multiply. -/
theorem mul (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hw₁ : ∀ s ∈ S, 0 ≤ w₁ s)
    (hw₂ : ∀ s ∈ S, 0 ≤ w₂ s) (hbf : DerivBoundUpTo w₁ S f k)
    (hbg : DerivBoundUpTo w₂ S g k) :
    DerivBoundUpTo (fun s => w₁ s * w₂ s) S (fun s => f s * g s) k := by
  intro m hm
  have hf2 : ∀ i : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      (i ≤ k → ∀ s ∈ S, ‖iteratedDeriv i f s‖ ≤ C * (1 + |s|) ^ N * w₁ s) := fun i => by
    by_cases hi : i ≤ k
    · obtain ⟨C, N, hC, h⟩ := hbf i hi
      exact ⟨C, N, hC, fun _ => h⟩
    · exact ⟨0, 0, le_rfl, fun h => absurd h hi⟩
  have hg2 : ∀ i : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      (i ≤ k → ∀ s ∈ S, ‖iteratedDeriv i g s‖ ≤ C * (1 + |s|) ^ N * w₂ s) := fun i => by
    by_cases hi : i ≤ k
    · obtain ⟨C, N, hC, h⟩ := hbg i hi
      exact ⟨C, N, hC, fun _ => h⟩
    · exact ⟨0, 0, le_rfl, fun h => absurd h hi⟩
  choose Cf Nf hCf hbf' using hf2
  choose Cg Ng hCg hbg' using hg2
  set N : ℕ := ∑ i ∈ range (m + 1), (Nf i + Ng (m - i)) with hN
  refine ⟨∑ i ∈ range (m + 1), (m.choose i : ℝ) * Cf i * Cg (m - i), N,
    sum_nonneg fun i _ => by have := hCf i; have := hCg (m - i); positivity, fun s hs => ?_⟩
  have h1 := one_le_one_add_abs s
  have hw1 := hw₁ s hs
  have hw2 := hw₂ s hs
  rw [iteratedDeriv_fun_mul (contDiffAt_of_infty hf m s) (contDiffAt_of_infty hg m s)]
  refine (norm_sum_le _ _).trans ?_
  rw [sum_mul, sum_mul]
  refine sum_le_sum fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hfi := hbf' i (hi'.trans hm) s hs
  have hgi := hbg' (m - i) ((Nat.sub_le m i).trans hm) s hs
  have hexp : (1 + |s|) ^ Nf i * (1 + |s|) ^ Ng (m - i) ≤ (1 + |s|) ^ N := by
    rw [← pow_add]
    exact pow_le_pow_right₀ h1 (single_le_sum (f := fun j => Nf j + Ng (m - j))
      (fun j _ => Nat.zero_le _) hi)
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  have hCfi := hCf i
  have hCgi := hCg (m - i)
  calc (m.choose i : ℝ) * ‖iteratedDeriv i f s‖ * ‖iteratedDeriv (m - i) g s‖
      ≤ (m.choose i : ℝ) * (Cf i * (1 + |s|) ^ Nf i * w₁ s) *
          (Cg (m - i) * (1 + |s|) ^ Ng (m - i) * w₂ s) := by
        gcongr
    _ = (m.choose i : ℝ) * Cf i * Cg (m - i) *
          ((1 + |s|) ^ Nf i * (1 + |s|) ^ Ng (m - i)) * (w₁ s * w₂ s) := by ring
    _ ≤ (m.choose i : ℝ) * Cf i * Cg (m - i) * (1 + |s|) ^ N * (w₁ s * w₂ s) := by
        gcongr

end DerivBoundUpTo

theorem DerivBound.mul {w₁ w₂ : ℝ → ℝ} {S : Set ℝ} {f g : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hw₁ : ∀ s ∈ S, 0 ≤ w₁ s)
    (hw₂ : ∀ s ∈ S, 0 ≤ w₂ s) (hbf : DerivBound w₁ S f) (hbg : DerivBound w₂ S g) :
    DerivBound (fun s => w₁ s * w₂ s) S (fun s => f s * g s) := fun k =>
  (hbf k).mul hf hg hw₁ hw₂ (hbg k)

/-- For a real smooth function, the complexified derivatives have the same norm. -/
theorem norm_iteratedDeriv_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ) (s : ℝ) :
    ‖iteratedDeriv m (fun s => (f s : ℂ)) s‖ = |iteratedDeriv m f s| := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← Real.norm_eq_abs,
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left hf.contDiffAt
    (natCast_le_infty m)

/-! ### The three factors of `κ_c` -/

/-- The affine factor `s/4 - 2`. -/
def affP (s : ℝ) : ℂ := ((s / 4 - 2 : ℝ) : ℂ)

/-- The Gaussian factor `e^{-s/4}`. -/
def gaussE (s : ℝ) : ℂ := ((Real.exp ((-1 / 4) * s) : ℝ) : ℂ)

/-- The resolvent factor `(e^{-s/4} - c)⁻¹`. -/
def resI (c : ℂ) (s : ℝ) : ℂ := ((Real.exp ((-1 / 4) * s) : ℝ) - c)⁻¹

theorem kappa_eq_mul (c : ℂ) (s : ℝ) : kappa c s = affP s * gaussE s * resI c s := by
  have e : Real.exp (-(s / 4)) = Real.exp ((-1 / 4) * s) := by ring_nf
  rw [kappa, e]
  simp only [affP, gaussE, resI, div_eq_mul_inv, Complex.ofReal_mul]

theorem contDiff_affP : ContDiff ℝ ∞ affP :=
  Complex.ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ ∞ fun s : ℝ => s / 4 - 2)

theorem contDiff_gaussE : ContDiff ℝ ∞ gaussE :=
  Complex.ofRealCLM.contDiff.comp
    (by fun_prop : ContDiff ℝ ∞ fun s : ℝ => Real.exp ((-1 / 4) * s))

/-- `R(x) = (x - c)⁻¹`, smooth on `ℝ` for nonreal `c`. -/
def resR (c : ℂ) (x : ℝ) : ℂ := ((x : ℂ) - c)⁻¹

theorem contDiff_resR {c : ℂ} (hc : c.im ≠ 0) : ContDiff ℝ ∞ (resR c) := by
  have h : ContDiff ℝ ∞ fun x : ℝ => (x : ℂ) - c :=
    Complex.ofRealCLM.contDiff.sub contDiff_const
  exact h.inv fun x => ofReal_sub_ne_zero hc x

theorem resI_eq (c : ℂ) : resI c = resR c ∘ fun s => Real.exp ((-1 / 4) * s) := rfl

theorem contDiff_resI {c : ℂ} (hc : c.im ≠ 0) : ContDiff ℝ ∞ (resI c) := by
  rw [resI_eq]
  exact (contDiff_resR hc).comp (by fun_prop)

theorem derivBound_affP (k : ℕ) : DerivBoundUpTo (fun _ => 1) univ affP k := by
  intro m _
  refine ⟨2, 1, by norm_num, fun s _ => ?_⟩
  have hd : deriv affP = fun _ => ((1 / 4 : ℝ) : ℂ) := by
    funext x
    have : HasDerivAt (fun s : ℝ => s / 4 - 2) (1 / 4) x := by
      simpa using ((hasDerivAt_id x).div_const 4).sub_const 2
    exact this.ofReal_comp.deriv
  have h1 := one_le_one_add_abs s
  rcases m with _ | _ | m
  · simp only [iteratedDeriv_zero, affP, Complex.norm_real, Real.norm_eq_abs, pow_one,
      mul_one]
    have := abs_sub (s / 4) 2
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_two] at this
    linarith [abs_nonneg s]
  · rw [iteratedDeriv_one, hd]
    simp only [Complex.norm_real, Real.norm_eq_abs, pow_one, mul_one]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    linarith
  · rw [iteratedDeriv_succ', iteratedDeriv_succ', hd]
    have hdd : deriv (fun _ : ℝ => ((1 / 4 : ℝ) : ℂ)) = fun _ => 0 := by
      funext x; simp
    rw [hdd, iteratedDeriv_const]
    simp only [norm_zero, mul_one, pow_one, ite_self]
    positivity

theorem iteratedDeriv_gaussE (m : ℕ) (s : ℝ) :
    ‖iteratedDeriv m gaussE s‖ = (1 / 4) ^ m * Real.exp ((-1 / 4) * s) := by
  have e : gaussE = fun s => ((Real.exp ((-1 / 4) * s) : ℝ) : ℂ) := rfl
  rw [e, norm_iteratedDeriv_ofReal (by fun_prop) m s, iteratedDeriv_exp_const_mul,
    abs_mul, abs_of_pos (Real.exp_pos _), abs_pow, abs_div, abs_neg, abs_one,
    abs_of_pos (by norm_num : (0 : ℝ) < 4)]

theorem derivBound_gaussE (k : ℕ) :
    DerivBoundUpTo (fun s => Real.exp ((-1 / 4) * s)) univ gaussE k := by
  intro m _
  refine ⟨1, 0, zero_le_one, fun s _ => ?_⟩
  rw [iteratedDeriv_gaussE, pow_zero, mul_one, one_mul]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (pow_le_one₀ (by norm_num) (by norm_num))

/-- The resolvent factor has bounded derivatives on `s ≥ 0` (Faà di Bruno). -/
theorem derivBound_resI {c : ℂ} (hc : c.im ≠ 0) (k : ℕ) :
    DerivBoundUpTo (fun _ => 1) (Ici 0) (resI c) k := by
  intro m _
  have hR := contDiff_resR hc
  have hbd : ∀ i : ℕ, ∃ C : ℝ, ∀ y ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ i (resR c) y‖ ≤ C :=
    fun i => isCompact_Icc.exists_bound_of_continuousOn
      (hR.continuous_iteratedFDeriv
        (natCast_le_infty i)).continuousOn
  choose CR hCR using hbd
  set C : ℝ := ∑ j ∈ range (m + 1), |CR j|
  refine ⟨m ! * C, 0, by positivity, fun s hs => ?_⟩
  have hs0 : (0 : ℝ) ≤ s := hs
  have hfs : Real.exp ((-1 / 4) * s) ∈ Icc (0 : ℝ) 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, resI_eq]
  have h := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := resR c)
    (f := fun s : ℝ => Real.exp ((-1 / 4) * s)) (n := m) (N := ∞) hR (by fun_prop)
    (natCast_le_infty m) s (C := C) (D := 1)
    (fun i hi => (hCR i _ hfs).trans ((le_abs_self _).trans
      (single_le_sum (f := fun j => |CR j|) (fun j _ => abs_nonneg _)
        (mem_range.mpr (Nat.lt_succ_of_le hi)))))
    (fun i _ _ => by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul,
        Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), one_pow]
      refine mul_le_one₀ ?_ (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))
      rw [abs_pow, abs_div, abs_neg, abs_one, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      exact pow_le_one₀ (by norm_num) (by norm_num))
  simpa using h

/-- **`κ_c` is Gaussian with all derivatives** on `s ≥ 0` (tex line 1176). -/
theorem derivBound_kappa {c : ℂ} (hc : c.im ≠ 0) :
    DerivBound (fun s => Real.exp ((-1 / 4) * s)) (Ici 0) (kappa c) := by
  intro k
  have h1 := ((derivBound_affP k).mono_set (subset_univ (Ici 0))).mul contDiff_affP
    contDiff_gaussE (fun _ _ => zero_le_one) (fun _ _ => (Real.exp_pos _).le)
    ((derivBound_gaussE k).mono_set (subset_univ _))
  have h2 := h1.mul (contDiff_affP.mul contDiff_gaussE) (contDiff_resI hc)
    (fun _ _ => by positivity) (fun _ _ => zero_le_one) (derivBound_resI hc k)
  have e : kappa c = fun s => affP s * gaussE s * resI c s := funext (kappa_eq_mul c)
  rw [e]
  refine h2.mono_weight fun s _ => le_of_eq ?_
  ring

/-! ### Bounds for the regular solution `b` -/

/-- `iteratedDeriv (k+1) (σ ↦ σ g(σ)) = σ g^{(k+1)} + (k+1) g^{(k)}`. -/
theorem iteratedDeriv_ofReal_mul {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    iteratedDeriv (k + 1) (fun σ : ℝ => (σ : ℂ) * g σ) =
      fun σ : ℝ => (σ : ℂ) * iteratedDeriv (k + 1) g σ + ((k : ℂ) + 1) * iteratedDeriv k g σ := by
  have hdiff : ∀ j : ℕ, Differentiable ℝ (iteratedDeriv j g) := fun j =>
    hg.differentiable_iteratedDeriv j (natCast_lt_infty j)
  induction k with
  | zero =>
    funext σ
    rw [iteratedDeriv_one, zero_add, iteratedDeriv_one, iteratedDeriv_zero]
    have h1 : HasDerivAt (fun σ : ℝ => (σ : ℂ)) 1 σ := by
      simpa using (hasDerivAt_id σ).ofReal_comp
    have this : HasDerivAt (fun σ : ℝ => (σ : ℂ) * g σ) (1 * g σ + (σ : ℂ) * deriv g σ) σ :=
      h1.mul (hg.differentiable (by simp) σ).hasDerivAt
    rw [this.deriv]
    push_cast
    ring
  | succ k ih =>
    funext σ
    rw [iteratedDeriv_succ, ih]
    have h1 : HasDerivAt (fun σ : ℝ => (σ : ℂ)) 1 σ := by
      simpa using (hasDerivAt_id σ).ofReal_comp
    have hab : HasDerivAt (fun σ : ℝ => (σ : ℂ) * iteratedDeriv (k + 1) g σ +
        ((k : ℂ) + 1) * iteratedDeriv k g σ)
        ((1 * iteratedDeriv (k + 1) g σ + (σ : ℂ) * deriv (iteratedDeriv (k + 1) g) σ) +
          ((k : ℂ) + 1) * deriv (iteratedDeriv k g) σ) σ :=
      (h1.mul (hdiff (k + 1) σ).hasDerivAt).add
        ((hdiff k σ).hasDerivAt.const_mul ((k : ℂ) + 1))
    rw [hab.deriv, ← iteratedDeriv_succ, ← iteratedDeriv_succ]
    push_cast
    ring

/-- The differentiated regular equation: `s b^{(k+2)} = (κ b)^{(k)}/4 - (k+3) b^{(k+1)}`. -/
theorem regB_iteratedDeriv_add_two {c : ℂ} (hc : c.im ≠ 0) (k : ℕ) (s : ℝ) :
    (s : ℂ) * iteratedDeriv (k + 2) (regB c) s =
      iteratedDeriv k (fun σ => kappa c σ * regB c σ) s / 4 -
        ((k : ℂ) + 3) * iteratedDeriv (k + 1) (regB c) s := by
  have hb := contDiff_regB hc
  have hb1 : ContDiff ℝ ∞ (deriv (regB c)) := (contDiff_infty_iff_deriv.mp hb).2
  have hb2 : ContDiff ℝ ∞ (deriv (deriv (regB c))) := (contDiff_infty_iff_deriv.mp hb1).2
  have hfun : (fun σ : ℝ => (σ : ℂ) * deriv (deriv (regB c)) σ + 3 * deriv (regB c) σ) =
      fun σ => (kappa c σ * regB c σ) / 4 := by
    funext σ
    have := regB_ode hc σ
    linear_combination this / 4
  have hk := congrArg (fun f => iteratedDeriv k f s) hfun
  rw [iteratedDeriv_div_const] at hk
  have hsplit : iteratedDeriv k (fun σ : ℝ => (σ : ℂ) * deriv (deriv (regB c)) σ +
      3 * deriv (regB c) σ) s = iteratedDeriv k (fun σ : ℝ => (σ : ℂ) *
        deriv (deriv (regB c)) σ) s + 3 * iteratedDeriv (k + 1) (regB c) s := by
    have c1 : ContDiffAt ℝ k (fun σ : ℝ => (σ : ℂ) * deriv (deriv (regB c)) σ) s :=
      contDiffAt_of_infty ((Complex.ofRealCLM.contDiff.mul hb2 :
        ContDiff ℝ ∞ fun σ : ℝ => (σ : ℂ) * deriv (deriv (regB c)) σ)) k s
    have c2 : ContDiffAt ℝ k (fun σ : ℝ => (3 : ℂ) * deriv (regB c) σ) s :=
      contDiffAt_of_infty (contDiff_const.mul hb1) k s
    rw [iteratedDeriv_fun_add c1 c2, iteratedDeriv_const_mul_field, iteratedDeriv_succ']
  rw [hsplit] at hk
  have e2 : ∀ j : ℕ, iteratedDeriv j (deriv (deriv (regB c))) = iteratedDeriv (j + 2) (regB c) :=
    fun j => by rw [iteratedDeriv_succ', iteratedDeriv_succ']
  rcases k with _ | k
  · have e3 : deriv (deriv (regB c)) = iteratedDeriv 2 (regB c) := by
      rw [← e2 0, iteratedDeriv_zero]
    have hk' : (s : ℂ) * iteratedDeriv 2 (regB c) s + 3 * iteratedDeriv 1 (regB c) s =
        kappa c s * regB c s / 4 := by
      have h := hk
      simp only [iteratedDeriv_zero] at h
      rw [e3] at h
      exact h
    show (s : ℂ) * iteratedDeriv 2 (regB c) s = iteratedDeriv 0 (fun σ => kappa c σ * regB c σ)
      s / 4 - (((0 : ℕ) : ℂ) + 3) * iteratedDeriv 1 (regB c) s
    rw [iteratedDeriv_zero]
    push_cast
    linear_combination hk'
  · rw [iteratedDeriv_ofReal_mul hb2 k, e2, e2] at hk
    have hk' : (s : ℂ) * iteratedDeriv (k + 3) (regB c) s +
        ((k : ℂ) + 1) * iteratedDeriv (k + 2) (regB c) s +
          3 * iteratedDeriv (k + 2) (regB c) s =
        iteratedDeriv (k + 1) (fun σ => kappa c σ * regB c σ) s / 4 := hk
    show (s : ℂ) * iteratedDeriv (k + 3) (regB c) s =
      iteratedDeriv (k + 1) (fun σ => kappa c σ * regB c σ) s / 4 -
        (((k + 1 : ℕ) : ℂ) + 3) * iteratedDeriv (k + 2) (regB c) s
    push_cast
    linear_combination hk'

theorem kappa_norm_le_three {c : ℂ} (hc : c.im ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    ‖kappa c s‖ ≤ 3 / |c.im| := by
  have hpos : 0 < |c.im| := abs_pos.mpr hc
  refine (norm_kappa_le hc s).trans (div_le_div_of_nonneg_right ?_ hpos.le)
  have h1 : |s / 4 - 2| ≤ s / 4 + 2 := by
    rw [abs_le]; constructor <;> linarith
  have h2 : s / 4 * Real.exp (-(s / 4)) ≤ 1 := by
    have := Real.add_one_le_exp (s / 4)
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    linarith
  have h3 : Real.exp (-(s / 4)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  calc |s / 4 - 2| * Real.exp (-(s / 4)) ≤ (s / 4 + 2) * Real.exp (-(s / 4)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = s / 4 * Real.exp (-(s / 4)) + 2 * Real.exp (-(s / 4)) := by ring
    _ ≤ 1 + 2 * 1 := by gcongr
    _ = 3 := by norm_num

/-- `b(s) = F(½ log s)/(β₀ s)` for `s > 0`. -/
theorem regB_eq_of_pos {c : ℂ} {F : ℝ → ℂ} {β₀ : ℂ} (hβ : ∀ t, F t = β₀ * regLog c t)
    (hβ0 : β₀ ≠ 0) {s : ℝ} (hs : 0 < s) :
    regB c s = F (Real.log s / 2) / (β₀ * (s : ℂ)) := by
  have he : Real.exp (Real.log s / 2) ^ 2 = s := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (Real.log s / 2) = Real.log s by push_cast; ring,
      Real.exp_log hs]
  rw [hβ, regLog, he]
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp

theorem exists_bound_regB {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s, 0 ≤ s → ‖regB c s‖ ≤ B := by
  have hc := hF.im_ne_zero
  obtain ⟨β₀, hβ0, hβ⟩ := exists_mode_eq_regLog hF
  obtain ⟨M, hM0, hM⟩ := hF.exists_bound
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (contDiff_regB hc).continuous.continuousOn
  refine ⟨max |B₀| (M / ‖β₀‖), le_trans (abs_nonneg _) (le_max_left _ _), fun s hs => ?_⟩
  rcases le_total s 1 with h1 | h1
  · exact ((hB₀ s ⟨hs, h1⟩).trans (le_abs_self _)).trans (le_max_left _ _)
  · have hs0 : 0 < s := by linarith
    rw [regB_eq_of_pos (fun t => (hβ t).1) hβ0 hs0, norm_div, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs0]
    refine le_trans ?_ (le_max_right _ _)
    have hβpos : 0 < ‖β₀‖ := norm_pos_iff.mpr hβ0
    rw [div_le_div_iff₀ (by positivity) hβpos]
    calc ‖F (Real.log s / 2)‖ * ‖β₀‖ ≤ M * ‖β₀‖ := by gcongr; exact hM _
      _ ≤ M * (‖β₀‖ * s) := by
          refine mul_le_mul_of_nonneg_left ?_ hM0
          nlinarith
      _ = M * (‖β₀‖ * s) := rfl

theorem exists_bound_deriv_regB {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s, 0 ≤ s → ‖deriv (regB c) s‖ ≤ B := by
  have hc := hF.im_ne_zero
  obtain ⟨Bb, hBb0, hBb⟩ := exists_bound_regB hF
  refine ⟨3 / |c.im| * Bb / 4, by positivity, fun s hs => ?_⟩
  have hd : deriv (regB c) s = avgPow 2 (fun σ => kappa c σ * regB c σ) s / 4 := by
    unfold regB
    rw [deriv_regSol (contDiff_kappa hc).continuous]
  rw [hd, norm_div, Complex.norm_ofNat]
  refine div_le_div_of_nonneg_right (norm_avgPow_le fun u hu => ?_) (by norm_num)
  have hsu : 0 ≤ s * u := mul_nonneg hs hu.1
  rw [norm_mul]
  exact mul_le_mul (kappa_norm_le_three hc hsu) (hBb _ hsu) (norm_nonneg _) (by positivity)

/-- Polynomial bounds for all derivatives of `b` on `s ≥ 1` (induction on the order). -/
theorem derivBound_regB_Ici_one {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    ∀ k, DerivBoundUpTo (fun _ => 1) (Ici 1) (regB c) (k + 1) := by
  have hc := hF.im_ne_zero
  have hb := contDiff_regB hc
  intro k
  induction k with
  | zero =>
    intro m hm
    obtain ⟨Bb, hBb0, hBb⟩ := exists_bound_regB hF
    obtain ⟨Bd, hBd0, hBd⟩ := exists_bound_deriv_regB hF
    rcases m with _ | _ | m
    · refine ⟨Bb, 0, hBb0, fun s hs => ?_⟩
      simpa using hBb s (le_trans zero_le_one hs)
    · refine ⟨Bd, 0, hBd0, fun s hs => ?_⟩
      simpa using hBd s (le_trans zero_le_one hs)
    · omega
  | succ k ih =>
    intro m hm
    rcases Nat.lt_or_ge m (k + 2) with hlt | hge
    · exact ih m (by omega)
    have hmk : m = k + 2 := by omega
    subst hmk
    -- bounds for `(κ b)^{(k)}` and `b^{(k+1)}`
    have hκb := ((derivBound_kappa hc k).mono_set (Ici_subset_Ici.mpr zero_le_one)).mul
      (contDiff_kappa hc) hb (fun _ _ => (Real.exp_pos _).le) (fun _ _ => zero_le_one)
      (ih.mono (by omega))
    obtain ⟨C₁, N₁, hC₁, h₁⟩ := hκb k le_rfl
    obtain ⟨C₂, N₂, hC₂, h₂⟩ := ih (k + 1) le_rfl
    refine ⟨C₁ / 4 + (k + 3) * C₂, N₁ + N₂, by positivity, fun s hs => ?_⟩
    have hs1 : (1 : ℝ) ≤ s := hs
    have hs0 : 0 < s := by linarith
    have h1 := one_le_one_add_abs s
    have hid := regB_iteratedDeriv_add_two hc k s
    have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    have hx : iteratedDeriv (k + 2) (regB c) s =
        (iteratedDeriv k (fun σ => kappa c σ * regB c σ) s / 4 -
          ((k : ℂ) + 3) * iteratedDeriv (k + 1) (regB c) s) / (s : ℂ) := by
      rw [← hid]; field_simp
    have e1 := h₁ s hs
    have e2 := h₂ s hs
    have hexp : Real.exp ((-1 / 4) * s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have p1 : (1 + |s|) ^ N₁ ≤ (1 + |s|) ^ (N₁ + N₂) := pow_le_pow_right₀ h1 (by omega)
    have p2 : (1 + |s|) ^ N₂ ≤ (1 + |s|) ^ (N₁ + N₂) := pow_le_pow_right₀ h1 (by omega)
    have hsn : ‖(s : ℂ)‖ = s := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    rw [hx, norm_div, hsn, div_le_iff₀ hs0]
    have hk3 : ‖((k : ℂ) + 3)‖ = (k : ℝ) + 3 := by
      have : ((k : ℂ) + 3) = (((k : ℝ) + 3 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc ‖iteratedDeriv k (fun σ => kappa c σ * regB c σ) s / 4 -
          ((k : ℂ) + 3) * iteratedDeriv (k + 1) (regB c) s‖
        ≤ ‖iteratedDeriv k (fun σ => kappa c σ * regB c σ) s‖ / 4 +
            ((k : ℝ) + 3) * ‖iteratedDeriv (k + 1) (regB c) s‖ := by
          refine (norm_sub_le _ _).trans (le_of_eq ?_)
          rw [norm_div, Complex.norm_ofNat, norm_mul, hk3]
      _ ≤ C₁ * (1 + |s|) ^ N₁ * (Real.exp ((-1 / 4) * s) * 1) / 4 +
            ((k : ℝ) + 3) * (C₂ * (1 + |s|) ^ N₂ * 1) := by gcongr
      _ ≤ C₁ * (1 + |s|) ^ (N₁ + N₂) * (1 * 1) / 4 +
            ((k : ℝ) + 3) * (C₂ * (1 + |s|) ^ (N₁ + N₂) * 1) := by gcongr
      _ = (C₁ / 4 + (k + 3) * C₂) * (1 + |s|) ^ (N₁ + N₂) * 1 := by ring
      _ ≤ (C₁ / 4 + (k + 3) * C₂) * (1 + |s|) ^ (N₁ + N₂) * 1 * s := by
          have : 0 ≤ (C₁ / 4 + (k + 3) * C₂) * (1 + |s|) ^ (N₁ + N₂) * 1 := by positivity
          nlinarith

/-- **All derivatives of `b` are polynomially bounded on `s ≥ 0`.** -/
theorem derivBound_regB {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    DerivBound (fun _ => 1) (Ici 0) (regB c) := by
  have hc := hF.im_ne_zero
  have hb := contDiff_regB hc
  intro k
  have hcpt : DerivBoundUpTo (fun _ => 1) (Icc 0 1) (regB c) k := by
    intro m _
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (hb.continuous_iteratedDeriv m
        (natCast_le_infty m)).continuousOn
    exact ⟨|C|, 0, abs_nonneg _, fun s hs => by simpa using (hC s hs).trans (le_abs_self C)⟩
  have h := hcpt.union ((derivBound_regB_Ici_one hF k).mono (by omega))
    (fun _ _ => zero_le_one)
  rwa [Icc_union_Ici_eq_Ici zero_le_one] at h

/-! ### O14: the Gaussian bounds for `q` -/

/-- The angular-two profile `β = β₀ κ_c b` of `q = y² β(|y|²)`. -/
def modeBeta (c β₀ : ℂ) (s : ℝ) : ℂ := β₀ * (kappa c s * regB c s)

theorem contDiff_modeBeta {c : ℂ} (hc : c.im ≠ 0) (β₀ : ℂ) : ContDiff ℝ ∞ (modeBeta c β₀) :=
  contDiff_const.mul ((contDiff_kappa hc).mul (contDiff_regB hc))

theorem derivBound_modeBeta {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) (β₀ : ℂ) :
    DerivBound (fun s => Real.exp ((-1 / 4) * s)) (Ici 0) (modeBeta c β₀) := by
  have hc := hF.im_ne_zero
  intro k
  have h := ((derivBound_kappa hc).mul (contDiff_kappa hc) (contDiff_regB hc)
    (fun _ _ => (Real.exp_pos _).le) (fun _ _ => zero_le_one) (derivBound_regB hF) k).const_mul
    β₀
  have e : modeBeta c β₀ = fun s => β₀ * (kappa c s * regB c s) := rfl
  rw [e]
  exact h.mono_weight fun s _ => le_of_eq (mul_one (Real.exp ((-1 / 4) * s)))

/-- The mode `q = h(r) e^{2iϑ}` on `ℂ = ℝ²` (Proposition `prop:gaussian-existence`,
tex line 968). -/
def modeQ (c : ℂ) (F : ℝ → ℂ) : ℂ → ℂ := Planar.NUE.Ang.ofProfile 2 (modeVort c F)

/-- `q(y) = y² β(|y|²)` with `β = β₀ κ_c b` (tex lines 1163--1167). -/
theorem modeQ_eq {c : ℂ} {F : ℝ → ℂ} {β₀ : ℂ} (hβ : ∀ t, F t = β₀ * regLog c t) (y : ℂ) :
    modeQ c F y = y ^ 2 * modeBeta c β₀ (‖y‖ ^ 2) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [modeQ, Planar.NUE.Ang.ofProfile, Planar.NUE.Ang.angPhase]
  have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hr' : ((‖y‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [modeQ, Planar.NUE.Ang.ofProfile, Planar.NUE.Ang.angPhase, modeVort,
    modeRadial_eq hβ hr, modeBeta]
  rw [zpow_two, div_mul_div_comm]
  push_cast
  field_simp

theorem modeQ_eq_fun {c : ℂ} {F : ℝ → ℂ} {β₀ : ℂ} (hβ : ∀ t, F t = β₀ * regLog c t) :
    modeQ c F = fun y => y ^ 2 * modeBeta c β₀ (‖y‖ ^ 2) :=
  funext (modeQ_eq hβ)

/-- `q` is `C^∞` on `ℝ²` (tex lines 1165--1167). -/
theorem contDiff_modeQ {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    ContDiff ℝ ∞ (modeQ c F) := by
  obtain ⟨β₀, -, hβ⟩ := exists_mode_eq_regLog hF
  rw [modeQ_eq_fun (fun t => (hβ t).1)]
  exact Planar.contDiff_angularTwo (contDiff_modeBeta hF.im_ne_zero β₀)

/-- **O14** (Proposition `prop:gaussian-existence`, tex lines 971--976; units B0052, B0054):
every derivative of `q` is bounded by a polynomial times `e^{-|y|²/4}`. -/
theorem norm_iteratedFDeriv_modeQ_le {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) (k : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ y : ℂ,
      ‖iteratedFDeriv ℝ k (modeQ c F) y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-‖y‖ ^ 2 / 4) := by
  have hc := hF.im_ne_zero
  obtain ⟨β₀, -, hβ⟩ := exists_mode_eq_regLog hF
  rw [modeQ_eq_fun (fun t => (hβ t).1)]
  obtain ⟨C₀, N₀, hP9⟩ := Planar.norm_iteratedFDeriv_angularTwo_le k
  have hbeta := derivBound_modeBeta hF β₀ k
  have hb2 : ∀ m : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ (m ≤ k → ∀ s ∈ Ici (0 : ℝ),
      ‖iteratedDeriv m (modeBeta c β₀) s‖ ≤ C * (1 + |s|) ^ N * Real.exp ((-1 / 4) * s)) :=
    fun m => by
      by_cases hm : m ≤ k
      · obtain ⟨C, N, hC, h⟩ := hbeta m hm
        exact ⟨C, N, hC, fun _ => h⟩
      · exact ⟨0, 0, le_rfl, fun h => absurd h hm⟩
  choose Cm Nm hCm hm using hb2
  set Cs : ℝ := ∑ m ∈ range (k + 1), Cm m
  set Ns : ℕ := ∑ m ∈ range (k + 1), Nm m
  refine ⟨max C₀ 0 * Cs, N₀ + 2 * Ns, fun y => ?_⟩
  have hy0 : (0 : ℝ) ≤ ‖y‖ ^ 2 := by positivity
  have h1 : (1 : ℝ) ≤ 1 + |‖y‖ ^ 2| := one_le_one_add_abs _
  have hsq : 1 + |‖y‖ ^ 2| ≤ (1 + ‖y‖) ^ 2 := by
    rw [abs_of_nonneg hy0]; nlinarith [norm_nonneg y]
  have hexp : Real.exp ((-1 / 4) * ‖y‖ ^ 2) = Real.exp (-‖y‖ ^ 2 / 4) := by
    congr 1; ring
  have hsum : ∑ m ∈ range (k + 1), ‖iteratedDeriv m (modeBeta c β₀) (‖y‖ ^ 2)‖ ≤
      Cs * (1 + ‖y‖) ^ (2 * Ns) * Real.exp (-‖y‖ ^ 2 / 4) := by
    rw [mul_assoc, sum_mul]
    refine sum_le_sum fun m hmr => ?_
    have hmk : m ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hmr)
    refine (hm m hmk _ hy0).trans ?_
    rw [hexp, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hCm m)
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    calc (1 + |‖y‖ ^ 2|) ^ Nm m ≤ (1 + |‖y‖ ^ 2|) ^ Ns :=
          pow_le_pow_right₀ h1 (single_le_sum (f := Nm) (fun _ _ => Nat.zero_le _) hmr)
      _ ≤ ((1 + ‖y‖) ^ 2) ^ Ns := pow_le_pow_left₀ (by linarith) hsq Ns
      _ = (1 + ‖y‖) ^ (2 * Ns) := by rw [← pow_mul]
  refine (hP9 _ ((contDiff_modeBeta hc β₀).of_le (natCast_le_infty k)) y).trans ?_
  have hCs : 0 ≤ Cs := sum_nonneg fun m _ => hCm m
  calc C₀ * (1 + ‖y‖) ^ N₀ * ∑ m ∈ range (k + 1), ‖iteratedDeriv m (modeBeta c β₀) (‖y‖ ^ 2)‖
      ≤ max C₀ 0 * (1 + ‖y‖) ^ N₀ *
          ∑ m ∈ range (k + 1), ‖iteratedDeriv m (modeBeta c β₀) (‖y‖ ^ 2)‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (by positivity)) (sum_nonneg fun m _ => norm_nonneg _)
    _ ≤ max C₀ 0 * (1 + ‖y‖) ^ N₀ * (Cs * (1 + ‖y‖) ^ (2 * Ns) * Real.exp (-‖y‖ ^ 2 / 4)) := by
        gcongr
    _ = max C₀ 0 * Cs * (1 + ‖y‖) ^ (N₀ + 2 * Ns) * Real.exp (-‖y‖ ^ 2 / 4) := by
        rw [pow_add]; ring

end UnforcedLeray.ComplexODEC
