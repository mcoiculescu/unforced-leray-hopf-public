import UnforcedLeray.Units.B0147.Lattice

/-!
# B0147 helper: off-diagonal bilinear lattice sums (the rescaled cross stress)

Blueprint unit **B0147** (`eq:st18-t00145`, `paper/main.tex` lines 2217–2234), helper file;
infrastructure `INF29` ("the product bound `C a^{-3} e^{-b(i-j)²c²/a} e^{-b[(q-(i+j)c/2)²+η²]/a}`").

In rescaled variables (period `L = c/√a`) the cross stress `Q_c = ∑_{i≠j} V_i ⊗ V_j` of tex
line 2214 is `bil L f g (y) = ∑_{i≠j} f(y - iLe₁) g(y - jLe₁)` for unit-width profiles `f, g`.

* `bil_eq`: `bil L f g = (∑ f_i)(∑ g_j) - ∑ f_i g_i` (unit B0146's `offDiag_tsum`);
* `bil_abs_le`: the product of the `i`-th and `j`-th Gaussians, `i ≠ j`, is at most
  `e^{-βL²/4}` times a product of Gaussians of half the rate (tex lines 2230–2232), and summing
  over all pairs gives `|bil L f g y| ≤ C e^{-γL²} e^{-γy₂²}` uniformly for `L ≥ 1`;
* `BS`: finite sums of such bilinear sums of `GP` profiles; this class is closed under the
  classical partial derivatives (product rule, `BS.derivX`, `BS.derivY`), hence under every
  derivative word (`BS.derivWord`), and under the transverse weight (`BS.weight`).
-/

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace UnforcedLeray.B0147

open UnforcedLeray.GaussianVortex
open UnforcedLeray.B0146 (GF XDecay latticeSum shift radiusSq_nonneg summable_exp_shift
  offDiag_tsum)
open UnforcedLeray.B0151 (derivWord)

/-- The rescaled cross stress `∑_{i ≠ j} f(y - iLe₁) g(y - jLe₁)` over the off-diagonal pairs. -/
def bil (L : ℝ) (f g : Plane → ℝ) (y : Plane) : ℝ :=
  ∑' p : ({p : ℤ × ℤ | p.1 ≠ p.2} : Set (ℤ × ℤ)), f (shift L p.1.1 y) * g (shift L p.1.2 y)

theorem gbound_of_gf {h : Plane → ℝ} (hh : GF 1 1 (fun _ => h)) :
    ∃ K β : ℝ, 0 ≤ K ∧ 0 < β ∧ GBound K β h := by
  obtain ⟨K, β, hK, hβ, hb⟩ := hh
  exact ⟨K, β, hK, hβ, fun y => hb 1 ⟨le_rfl, le_rfl⟩ y⟩

theorem xdecay_of_gf {h : Plane → ℝ} (hh : GF 1 1 (fun _ => h)) : XDecay h :=
  B0146.xd (a := 1) hh

theorem gf_mul₁ {f g : Plane → ℝ} (hf : GF 1 1 (fun _ => f)) (hg : GF 1 1 (fun _ => g)) :
    GF 1 1 (fun _ y => f y * g y) :=
  B0146.gf_mul hf hg

theorem latticeSum_add {f g : Plane → ℝ} (hf : XDecay f) (hg : XDecay g) {L : ℝ} (hL : L ≠ 0)
    (y : Plane) :
    latticeSum L (fun x => f x + g x) y = latticeSum L f y + latticeSum L g y :=
  (hf.summable hL y).tsum_add (hg.summable hL y)

/-- `∑_{i≠j} f_i g_j = (∑ f_i)(∑ g_j) - ∑ f_i g_i`. -/
theorem bil_eq {f g : Plane → ℝ} (hf : XDecay f) (hg : XDecay g) {L : ℝ} (hL : L ≠ 0)
    (y : Plane) :
    bil L f g y = latticeSum L f y * latticeSum L g y - latticeSum L (fun x => f x * g x) y :=
  (offDiag_tsum (f := fun n => f (shift L n y)) (g := fun n => g (shift L n y))
    (hf.summable_norm hL y) (hg.summable_norm hL y)).2

/-- For `i ≠ j`, `(t-iL)² + (t-jL)² ≥ L²/4 + ((t-iL)² + (t-jL)²)/2`. -/
theorem pair_sq_ge {L t : ℝ} {i j : ℤ} (hij : i ≠ j) :
    L ^ 2 / 4 + ((t - i * L) ^ 2 + (t - j * L) ^ 2) / 2 ≤ (t - i * L) ^ 2 + (t - j * L) ^ 2 := by
  have hd : (1 : ℤ) ≤ |i - j| := Int.one_le_abs (sub_ne_zero.mpr hij)
  have hd' : (1 : ℝ) ≤ |(i : ℝ) - j| := by exact_mod_cast hd
  have h1 : (1 : ℝ) ≤ ((i : ℝ) - j) ^ 2 := by
    rw [← sq_abs]; nlinarith
  have h2 : L ^ 2 ≤ ((i : ℝ) - j) ^ 2 * L ^ 2 := by nlinarith [sq_nonneg L]
  have e : ((t - i * L) - (t - j * L)) ^ 2 = ((i : ℝ) - j) ^ 2 * L ^ 2 := by ring
  nlinarith [sq_nonneg ((t - i * L) + (t - j * L))]

/-- **The product bound for the cross stress** (tex lines 2228–2234): for Gaussian-bounded
profiles and every period `L ≥ 1`, `|∑_{i≠j} f_i g_j| ≤ C e^{-βL²/4} e^{-βy₂²/4}`. -/
theorem bil_abs_le {K β L : ℝ} {f g : Plane → ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hL : 1 ≤ L)
    (hf : GBound K β f) (hg : GBound K β g) (y : Plane) :
    |bil L f g y| ≤ K ^ 2 * (2 + theta (β / 2 / 8)) ^ 2 * Real.exp (-(β / 4 * L ^ 2)) *
      Real.exp (-(β / 4 * y.2 ^ 2)) := by
  have hL0 : L ≠ 0 := by positivity
  set a : ℤ → ℝ := fun n => Real.exp (-(β / 2 * (y.1 - n * L) ^ 2)) with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => (Real.exp_pos _).le
  have hsa : Summable a := summable_exp_shift (half_pos hβ) hL0 y.1
  have hsan : Summable fun n => ‖a n‖ := hsa.congr fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  have hP : Summable (fun p : ℤ × ℤ => a p.1 * a p.2) := summable_mul_of_summable_norm hsan hsan
  set S : Set (ℤ × ℤ) := {p : ℤ × ℤ | p.1 ≠ p.2}
  set C : ℝ := K ^ 2 * Real.exp (-(2 * β * y.2 ^ 2)) * Real.exp (-(β / 4 * L ^ 2)) with hC
  have hC0 : 0 ≤ C := by positivity
  have hterm : ∀ p : S, |f (shift L p.1.1 y) * g (shift L p.1.2 y)| ≤ C * (a p.1.1 * a p.1.2) := by
    intro p
    have hij : p.1.1 ≠ p.1.2 := p.2
    rw [abs_mul]
    have e1 := shift_bound (L := L) hf p.1.1 y
    have e2 := shift_bound (L := L) hg p.1.2 y
    have key := pair_sq_ge (L := L) (t := y.1) hij
    calc |f (shift L p.1.1 y)| * |g (shift L p.1.2 y)|
        ≤ (K * Real.exp (-(β * y.2 ^ 2)) * Real.exp (-(β * (y.1 - p.1.1 * L) ^ 2))) *
          (K * Real.exp (-(β * y.2 ^ 2)) * Real.exp (-(β * (y.1 - p.1.2 * L) ^ 2))) :=
          mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
      _ = K ^ 2 * Real.exp (-(2 * β * y.2 ^ 2)) *
            Real.exp (-(β * ((y.1 - p.1.1 * L) ^ 2 + (y.1 - p.1.2 * L) ^ 2))) := by
          have q1 : Real.exp (-(2 * β * y.2 ^ 2)) =
              Real.exp (-(β * y.2 ^ 2)) * Real.exp (-(β * y.2 ^ 2)) := by
            rw [← Real.exp_add]; congr 1; ring
          have q2 : Real.exp (-(β * ((y.1 - p.1.1 * L) ^ 2 + (y.1 - p.1.2 * L) ^ 2))) =
              Real.exp (-(β * (y.1 - p.1.1 * L) ^ 2)) *
                Real.exp (-(β * (y.1 - p.1.2 * L) ^ 2)) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [q1, q2]; ring
      _ ≤ K ^ 2 * Real.exp (-(2 * β * y.2 ^ 2)) *
            (Real.exp (-(β / 4 * L ^ 2)) * (a p.1.1 * a p.1.2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simp only [ha, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith [mul_le_mul_of_nonneg_left key hβ.le]
      _ = C * (a p.1.1 * a p.1.2) := by rw [hC]; ring
  have hsT : Summable (fun p : S => ‖f (shift L p.1.1 y) * g (shift L p.1.2 y)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => by rw [Real.norm_eq_abs]; exact hterm p)
      ((hP.subtype S).mul_left C)
  have hsub : ∑' p : S, a p.1.1 * a p.1.2 ≤ ∑' p : ℤ × ℤ, a p.1 * a p.2 :=
    hP.tsum_subtype_le (fun p : ℤ × ℤ => a p.1 * a p.2) S (fun p => mul_nonneg (ha0 _) (ha0 _))
  have hprod : ∑' p : ℤ × ℤ, a p.1 * a p.2 = (∑' n, a n) * (∑' n, a n) :=
    (tsum_mul_tsum_of_summable_norm hsan hsan).symm
  have hM := lattice1D_sup (half_pos hβ) hL y.1
  have hM0 : 0 ≤ ∑' n, a n := tsum_nonneg ha0
  have e2 : Real.exp (-(2 * β * y.2 ^ 2)) ≤ Real.exp (-(β / 4 * y.2 ^ 2)) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg y.2])
  calc |bil L f g y|
      ≤ ∑' p : S, ‖f (shift L p.1.1 y) * g (shift L p.1.2 y)‖ := norm_tsum_le_tsum_norm hsT
    _ ≤ ∑' p : S, C * (a p.1.1 * a p.1.2) :=
        hsT.tsum_le_tsum (fun p => by rw [Real.norm_eq_abs]; exact hterm p)
          ((hP.subtype S).mul_left C)
    _ = C * ∑' p : S, a p.1.1 * a p.1.2 := tsum_mul_left
    _ ≤ C * ((∑' n, a n) * (∑' n, a n)) := by
        rw [← hprod]; exact mul_le_mul_of_nonneg_left hsub hC0
    _ ≤ C * ((2 + theta (β / 2 / 8)) * (2 + theta (β / 2 / 8))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hM hM hM0 (hM0.trans hM)) hC0
    _ ≤ K ^ 2 * (2 + theta (β / 2 / 8)) ^ 2 * Real.exp (-(β / 4 * L ^ 2)) *
          Real.exp (-(β / 4 * y.2 ^ 2)) := by
        rw [hC]
        have h0 : 0 ≤ K ^ 2 * (2 + theta (β / 2 / 8)) ^ 2 * Real.exp (-(β / 4 * L ^ 2)) := by
          have := theta_nonneg (β / 2 / 8); positivity
        calc K ^ 2 * Real.exp (-(2 * β * y.2 ^ 2)) * Real.exp (-(β / 4 * L ^ 2)) *
              ((2 + theta (β / 2 / 8)) * (2 + theta (β / 2 / 8)))
            = (K ^ 2 * (2 + theta (β / 2 / 8)) ^ 2 * Real.exp (-(β / 4 * L ^ 2))) *
                Real.exp (-(2 * β * y.2 ^ 2)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left e2 h0

/-! ### Finite sums of bilinear lattice sums -/

/-- Finite sums of rescaled cross stresses `bil L f g` of `GP` profiles, as functions of the
period `L`. -/
inductive BS : (ℝ → Plane → ℝ) → Prop
  | pair {f g : Plane → ℝ} : GP f → GP g → BS (fun L => bil L f g)
  | add {H₁ H₂ : ℝ → Plane → ℝ} : BS H₁ → BS H₂ → BS (fun L y => H₁ L y + H₂ L y)

theorem BS.congr {H H' : ℝ → Plane → ℝ} (hH : BS H) (h : ∀ L y, H L y = H' L y) : BS H' := by
  have : H = H' := funext fun L => funext fun y => h L y
  subst this
  exact hH

/-- Common Gaussian bound for two `GP` profiles. -/
theorem GP.bound₂ {f g : Plane → ℝ} (hf : GP f) (hg : GP g) :
    ∃ K β : ℝ, 0 ≤ K ∧ 0 < β ∧ GBound K β f ∧ GBound K β g := by
  obtain ⟨K₁, β₁, hK₁, hβ₁, h₁⟩ := hf.bound
  obtain ⟨K₂, β₂, hK₂, hβ₂, h₂⟩ := hg.bound
  exact ⟨max K₁ K₂, min β₁ β₂, le_max_of_le_left hK₁, lt_min hβ₁ hβ₂,
    h₁.mono hK₁ (le_max_left _ _) (min_le_left _ _),
    h₂.mono hK₂ (le_max_right _ _) (min_le_right _ _)⟩

/-- **Uniform bound** for the class `BS`: `|H L y| ≤ C e^{-γL²} e^{-γy₂²}` for all `L ≥ 1`. -/
theorem BS.bound {H : ℝ → Plane → ℝ} (hH : BS H) :
    ∃ C γ : ℝ, 0 ≤ C ∧ 0 < γ ∧ ∀ L : ℝ, 1 ≤ L → ∀ y : Plane,
      |H L y| ≤ C * Real.exp (-(γ * L ^ 2)) * Real.exp (-(γ * y.2 ^ 2)) := by
  induction hH with
  | @pair f g hf hg =>
    obtain ⟨K, β, hK, hβ, h₁, h₂⟩ := hf.bound₂ hg
    refine ⟨K ^ 2 * (2 + theta (β / 2 / 8)) ^ 2, β / 4, ?_, by positivity, fun L hL y =>
      bil_abs_le hK hβ hL h₁ h₂ y⟩
    have := theta_nonneg (β / 2 / 8); positivity
  | @add H₁ H₂ _ _ ih₁ ih₂ =>
    obtain ⟨C₁, γ₁, hC₁, hγ₁, h₁⟩ := ih₁
    obtain ⟨C₂, γ₂, hC₂, hγ₂, h₂⟩ := ih₂
    refine ⟨C₁ + C₂, min γ₁ γ₂, by positivity, lt_min hγ₁ hγ₂, fun L hL y => ?_⟩
    have m : ∀ γ : ℝ, min γ₁ γ₂ ≤ γ → Real.exp (-(γ * L ^ 2)) * Real.exp (-(γ * y.2 ^ 2)) ≤
        Real.exp (-(min γ₁ γ₂ * L ^ 2)) * Real.exp (-(min γ₁ γ₂ * y.2 ^ 2)) := by
      intro γ hγ
      apply mul_le_mul (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg L]))
        (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg y.2])) (Real.exp_pos _).le
        (Real.exp_pos _).le
    have a1 := h₁ L hL y
    have a2 := h₂ L hL y
    have b1 := mul_le_mul_of_nonneg_left (m γ₁ (min_le_left _ _)) hC₁
    have b2 := mul_le_mul_of_nonneg_left (m γ₂ (min_le_right _ _)) hC₂
    calc |H₁ L y + H₂ L y| ≤ |H₁ L y| + |H₂ L y| := abs_add_le _ _
      _ ≤ C₁ * (Real.exp (-(min γ₁ γ₂ * L ^ 2)) * Real.exp (-(min γ₁ γ₂ * y.2 ^ 2))) +
          C₂ * (Real.exp (-(min γ₁ γ₂ * L ^ 2)) * Real.exp (-(min γ₁ γ₂ * y.2 ^ 2))) := by
          rw [mul_assoc] at a1 a2; linarith
      _ = (C₁ + C₂) * Real.exp (-(min γ₁ γ₂ * L ^ 2)) *
            Real.exp (-(min γ₁ γ₂ * y.2 ^ 2)) := by ring

theorem xdecay_mul {f g : Plane → ℝ} (hf : GP f) (hg : GP g) : XDecay (fun x => f x * g x) :=
  xdecay_of_gf (gf_mul₁ hf.gf hg.gf)

theorem xdecay_mul_add {f g f' g' : Plane → ℝ} (hf : GP f) (hg : GP g) (hf' : GP f')
    (hg' : GP g') : XDecay (fun x => f' x * g x + f x * g' x) :=
  xdecay_of_gf ((gf_mul₁ hf'.gf hg.gf).add (gf_mul₁ hf.gf hg'.gf))

/-- Product rule for the rescaled cross stress, with a genuine derivative in `q`. -/
theorem hasDerivAt_bil_x {f g f' g' : Plane → ℝ} (hf : GP f) (hg : GP g) (hf' : GP f')
    (hg' : GP g') (hdf : ∀ y : Plane, HasDerivAt (fun t => f (t, y.2)) (f' y) y.1)
    (hdg : ∀ y : Plane, HasDerivAt (fun t => g (t, y.2)) (g' y) y.1) {L : ℝ} (hL : L ≠ 0)
    (z : Plane) :
    HasDerivAt (fun t => bil L f g (t, z.2)) (bil L f' g z + bil L f g' z) z.1 := by
  have hd : ∀ y : Plane, HasDerivAt (fun t => f (t, y.2) * g (t, y.2))
      (f' y * g y + f y * g' y) y.1 := fun y => (hdf y).mul (hdg y)
  have hS := B0146.hasDerivAt_latticeSum_x (g := fun x => f x * g x)
    (g' := fun x => f' x * g x + f x * g' x) hL hd (xdecay_mul hf hg)
    (xdecay_mul_add hf hg hf' hg') z
  have hSf := hf.hasDerivAt_lattice_x hf' hdf hL z
  have hSg := hg.hasDerivAt_lattice_x hg' hdg hL z
  have hfun : (fun t => bil L f g (t, z.2)) = fun t => latticeSum L f (t, z.2) *
      latticeSum L g (t, z.2) - latticeSum L (fun x => f x * g x) (t, z.2) :=
    funext fun t => bil_eq hf.xdecay hg.xdecay hL _
  rw [hfun]
  refine ((hSf.mul hSg).sub hS).congr_deriv ?_
  rw [bil_eq hf'.xdecay hg.xdecay hL, bil_eq hf.xdecay hg'.xdecay hL,
    latticeSum_add (xdecay_mul hf' hg) (xdecay_mul hf hg') hL]
  ring

/-- Product rule for the rescaled cross stress, with a genuine derivative in `η`. -/
theorem hasDerivAt_bil_y {f g f' g' : Plane → ℝ} (hf : GP f) (hg : GP g) (hf' : GP f')
    (hg' : GP g') (hdf : ∀ y : Plane, HasDerivAt (fun t => f (y.1, t)) (f' y) y.2)
    (hdg : ∀ y : Plane, HasDerivAt (fun t => g (y.1, t)) (g' y) y.2) {L : ℝ} (hL : L ≠ 0)
    (z : Plane) :
    HasDerivAt (fun t => bil L f g (z.1, t)) (bil L f' g z + bil L f g' z) z.2 := by
  have hd : ∀ y : Plane, HasDerivAt (fun t => f (y.1, t) * g (y.1, t))
      (f' y * g y + f y * g' y) y.2 := fun y => (hdf y).mul (hdg y)
  have hS := B0146.hasDerivAt_latticeSum_y (g := fun x => f x * g x)
    (g' := fun x => f' x * g x + f x * g' x) hL hd (xdecay_mul hf hg)
    (xdecay_mul_add hf hg hf' hg') z
  have hSf := hf.hasDerivAt_lattice_y hf' hdf hL z
  have hSg := hg.hasDerivAt_lattice_y hg' hdg hL z
  have hfun : (fun t => bil L f g (z.1, t)) = fun t => latticeSum L f (z.1, t) *
      latticeSum L g (z.1, t) - latticeSum L (fun x => f x * g x) (z.1, t) :=
    funext fun t => bil_eq hf.xdecay hg.xdecay hL _
  rw [hfun]
  refine ((hSf.mul hSg).sub hS).congr_deriv ?_
  rw [bil_eq hf'.xdecay hg.xdecay hL, bil_eq hf.xdecay hg'.xdecay hL,
    latticeSum_add (xdecay_mul hf' hg) (xdecay_mul hf hg') hL]
  ring

theorem BS.derivX {H : ℝ → Plane → ℝ} (hH : BS H) :
    ∃ H' : ℝ → Plane → ℝ, BS H' ∧ ∀ L : ℝ, L ≠ 0 → ∀ z : Plane,
      HasDerivAt (fun t => H L (t, z.2)) (H' L z) z.1 := by
  induction hH with
  | @pair f g hf hg =>
    obtain ⟨f', hf', hdf⟩ := hf.derivX
    obtain ⟨g', hg', hdg⟩ := hg.derivX
    exact ⟨fun L y => bil L f' g y + bil L f g' y, (BS.pair hf' hg).add (BS.pair hf hg'),
      fun L hL z => hasDerivAt_bil_x hf hg hf' hg' hdf hdg hL z⟩
  | @add H₁ H₂ _ _ ih₁ ih₂ =>
    obtain ⟨H₁', h₁, d₁⟩ := ih₁
    obtain ⟨H₂', h₂, d₂⟩ := ih₂
    exact ⟨fun L y => H₁' L y + H₂' L y, h₁.add h₂, fun L hL z => (d₁ L hL z).add (d₂ L hL z)⟩

theorem BS.derivY {H : ℝ → Plane → ℝ} (hH : BS H) :
    ∃ H' : ℝ → Plane → ℝ, BS H' ∧ ∀ L : ℝ, L ≠ 0 → ∀ z : Plane,
      HasDerivAt (fun t => H L (z.1, t)) (H' L z) z.2 := by
  induction hH with
  | @pair f g hf hg =>
    obtain ⟨f', hf', hdf⟩ := hf.derivY
    obtain ⟨g', hg', hdg⟩ := hg.derivY
    exact ⟨fun L y => bil L f' g y + bil L f g' y, (BS.pair hf' hg).add (BS.pair hf hg'),
      fun L hL z => hasDerivAt_bil_y hf hg hf' hg' hdf hdg hL z⟩
  | @add H₁ H₂ _ _ ih₁ ih₂ =>
    obtain ⟨H₁', h₁, d₁⟩ := ih₁
    obtain ⟨H₂', h₂, d₂⟩ := ih₂
    exact ⟨fun L y => H₁' L y + H₂' L y, h₁.add h₂, fun L hL z => (d₁ L hL z).add (d₂ L hL z)⟩

/-- Every iterated classical partial derivative of a member of `BS` is again in `BS`. -/
theorem BS.deriv_word {H : ℝ → Plane → ℝ} (hH : BS H) (w : List Bool) :
    ∃ H' : ℝ → Plane → ℝ, BS H' ∧ ∀ L : ℝ, L ≠ 0 → derivWord w (H L) = H' L := by
  induction w with
  | nil => exact ⟨H, hH, fun _ _ => rfl⟩
  | cons b w ih =>
    obtain ⟨H₁, h₁, hw⟩ := ih
    cases b
    · obtain ⟨H₂, h₂, hd⟩ := h₁.derivY
      refine ⟨H₂, h₂, fun L hL => ?_⟩
      show partialY (derivWord w (H L)) = _
      rw [hw L hL]
      funext z
      exact (hd L hL z).deriv
    · obtain ⟨H₂, h₂, hd⟩ := h₁.derivX
      refine ⟨H₂, h₂, fun L hL => ?_⟩
      show partialX (derivWord w (H L)) = _
      rw [hw L hL]
      funext z
      exact (hd L hL z).deriv

/-- Members of `BS` have genuine partial derivatives everywhere. -/
theorem BS.hasPartial {H : ℝ → Plane → ℝ} (hH : BS H) {L : ℝ} (hL : L ≠ 0) (z : Plane) :
    B0146.HasPartialX (H L) z ∧ B0146.HasPartialY (H L) z := by
  obtain ⟨Hx, -, dx⟩ := hH.derivX
  obtain ⟨Hy, -, dy⟩ := hH.derivY
  exact ⟨B0146.hasPartialX_of (dx L hL z), B0146.hasPartialY_of (dy L hL z)⟩

theorem BS.continuous {H : ℝ → Plane → ℝ} (hH : BS H) {L : ℝ} (hL : L ≠ 0) :
    Continuous (H L) := by
  induction hH with
  | @pair f g hf hg =>
    have hfun : bil L f g = fun y => latticeSum L f y * latticeSum L g y -
        latticeSum L (fun x => f x * g x) y := funext fun y => bil_eq hf.xdecay hg.xdecay hL y
    show Continuous (bil L f g)
    rw [hfun]
    obtain ⟨K, β, hK, hβ, hb⟩ := gbound_of_gf (gf_mul₁ hf.gf hg.gf)
    exact ((hf.latticeSum_continuous hL).mul (hg.latticeSum_continuous hL)).sub
      (latticeSum_continuous (hf.continuous.mul hg.continuous) hK hβ hL hb)
  | add _ _ ih₁ ih₂ => exact ih₁.add ih₂

/-- The transverse weight `(1 + y₂²)^m` commutes with the lattice: closure of `BS`. -/
theorem BS.weight {H : ℝ → Plane → ℝ} (hH : BS H) (m : ℕ) :
    BS (fun L y => (1 + y.2 ^ 2) ^ m * H L y) := by
  induction hH with
  | @pair f g hf hg =>
    refine (BS.pair (hf.weight m) hg).congr fun L y => ?_
    simp only [bil]
    rw [← tsum_mul_left]
    congr 1
    funext p
    simp only [shift]
    ring
  | add _ _ ih₁ ih₂ => exact (ih₁.add ih₂).congr fun L y => by ring

end UnforcedLeray.B0147
