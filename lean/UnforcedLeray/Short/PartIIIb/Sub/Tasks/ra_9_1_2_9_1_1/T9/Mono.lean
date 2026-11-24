import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.Defs

/-!
# Gaussian monomial calculus (task `PartIII-b:C/asrc/ra/9/1/2/9/1/1/9`, helper)

A monomial `c · (a⁻¹)^n · u^α · v^β · exp(-(u²+v²)/(4a))` in the variables `(a,u,v)`, with
`a = 1 + νs`, `u = x₁ - jc`, `v = x₂`. The conormal operators act as
`∂_u`, `∂_v`, and `s∂_s = (a-1)∂_a` (since `a - 1 = νs`). Each derivative is a finite sum of
monomials of the same shape, with `α + β` increased by at most `2`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A Gaussian monomial data `(c, n, α, β)`. -/
structure GbMon where
  c : ℝ
  n : ℕ
  α : ℕ
  β : ℕ

/-- The monomial function in `(a,u,v)`. -/
def gbG (m : GbMon) (a u v : ℝ) : ℝ :=
  m.c * (a⁻¹) ^ m.n * u ^ m.α * v ^ m.β * Real.exp (-(u ^ 2 + v ^ 2) / (4 * a))

/-- A finite sum of monomials. -/
def gbL (L : List GbMon) (a u v : ℝ) : ℝ := (L.map fun mo => gbG mo a u v).sum

def gbDU (m : GbMon) : List GbMon :=
  [⟨m.c * m.α, m.n, m.α - 1, m.β⟩, ⟨-(m.c / 2), m.n + 1, m.α + 1, m.β⟩]

def gbDV (m : GbMon) : List GbMon :=
  [⟨m.c * m.β, m.n, m.α, m.β - 1⟩, ⟨-(m.c / 2), m.n + 1, m.α, m.β + 1⟩]

def gbDA (m : GbMon) : List GbMon :=
  [⟨-(m.c * m.n), m.n + 1, m.α, m.β⟩, ⟨m.c / 4, m.n + 2, m.α + 2, m.β⟩,
    ⟨m.c / 4, m.n + 2, m.α, m.β + 2⟩]

/-- `s∂_s = (a-1)∂_a` on monomials. -/
def gbDS (m : GbMon) : List GbMon :=
  [⟨-(m.c * m.n), m.n, m.α, m.β⟩, ⟨m.c * m.n, m.n + 1, m.α, m.β⟩,
    ⟨m.c / 4, m.n + 1, m.α + 2, m.β⟩, ⟨-(m.c / 4), m.n + 2, m.α + 2, m.β⟩,
    ⟨m.c / 4, m.n + 1, m.α, m.β + 2⟩, ⟨-(m.c / 4), m.n + 2, m.α, m.β + 2⟩]

/-- Apply a monomial operator to a list of monomials. -/
def gbOpL (f : GbMon → List GbMon) : List GbMon → List GbMon
  | [] => []
  | m :: L => f m ++ gbOpL f L

lemma gbL_nil (a u v : ℝ) : gbL [] a u v = 0 := by simp [gbL]

lemma gbL_cons (m : GbMon) (L : List GbMon) (a u v : ℝ) :
    gbL (m :: L) a u v = gbG m a u v + gbL L a u v := by
  simp [gbL]

lemma gbL_append (L₁ L₂ : List GbMon) (a u v : ℝ) :
    gbL (L₁ ++ L₂) a u v = gbL L₁ a u v + gbL L₂ a u v := by
  simp [gbL, List.map_append, List.sum_append]

/-- `∂_u` of one monomial. -/
lemma gbG_hasDerivAt_u (m : GbMon) (a u v : ℝ) (_ha : a ≠ 0) :
    HasDerivAt (fun u' => gbG m a u' v) (gbL (gbDU m) a u v) u := by
  obtain ⟨c, n, α, β⟩ := m
  have h1 : HasDerivAt (fun u' : ℝ => u' ^ α) (α * u ^ (α - 1)) u := hasDerivAt_pow α u
  have h2 : HasDerivAt (fun u' : ℝ => -(u' ^ 2 + v ^ 2) / (4 * a))
      (-(2 * u) / (4 * a)) u := by
    have h := (((hasDerivAt_pow 2 u).add_const (v ^ 2)).neg).div_const (4 * a)
    refine h.congr_deriv ?_
    norm_num
  have h3 := h2.exp
  have h4 := ((h1.const_mul (c * a⁻¹ ^ n)).mul_const (v ^ β)).fun_mul h3
  refine h4.congr_deriv ?_
  simp only [gbL, gbDU, gbG, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  ring

/-- `∂_v` of one monomial. -/
lemma gbG_hasDerivAt_v (m : GbMon) (a u v : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun v' => gbG m a u v') (gbL (gbDV m) a u v) v := by
  obtain ⟨c, n, α, β⟩ := m
  have h1 : HasDerivAt (fun v' : ℝ => v' ^ β) (β * v ^ (β - 1)) v := hasDerivAt_pow β v
  have h2 : HasDerivAt (fun v' : ℝ => -(u ^ 2 + v' ^ 2) / (4 * a))
      (-(2 * v) / (4 * a)) v := by
    have h := (((hasDerivAt_pow 2 v).const_add (u ^ 2)).neg).div_const (4 * a)
    refine h.congr_deriv ?_
    norm_num
  have h3 := h2.exp
  have h4 := (h1.const_mul (c * a⁻¹ ^ n * u ^ α)).fun_mul h3
  refine h4.congr_deriv ?_
  simp only [gbL, gbDV, gbG, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  ring

/-- `∂_a` of one monomial. -/
lemma gbG_hasDerivAt_a (m : GbMon) (a u v : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun a' => gbG m a' u v) (gbL (gbDA m) a u v) a := by
  obtain ⟨c, n, α, β⟩ := m
  have h1 : HasDerivAt (fun a' : ℝ => a'⁻¹) (-(a ^ 2)⁻¹) a := hasDerivAt_inv ha
  have h2 : HasDerivAt (fun a' : ℝ => a'⁻¹ ^ n) (n * a⁻¹ ^ (n - 1) * (-(a ^ 2)⁻¹)) a :=
    h1.pow n
  have hin : HasDerivAt (fun a' : ℝ => -(u ^ 2 + v ^ 2) / (4 * a'))
      ((u ^ 2 + v ^ 2) / (4 * a ^ 2)) a := by
    have h := (hasDerivAt_const a (-(u ^ 2 + v ^ 2))).fun_div
      ((hasDerivAt_id a).const_mul 4) (mul_ne_zero (by norm_num) ha)
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have h3 := hin.exp
  have h4 := (((h2.const_mul c).mul_const (u ^ α)).mul_const (v ^ β)).fun_mul h3
  refine h4.congr_deriv ?_
  cases n with
  | zero =>
    simp only [gbL, gbDA, gbG, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  | succ k =>
    simp only [gbL, gbDA, gbG, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Nat.add_sub_cancel]
    push_cast
    ring

/-- The `s∂_s` identity on one monomial, `s∂_s = (a-1)∂_a` (with `a a⁻¹ = 1`). -/
lemma gbDS_eq (m : GbMon) (a u v : ℝ) (hab : a * a⁻¹ = 1) :
    gbL (gbDS m) a u v = (a - 1) * gbL (gbDA m) a u v := by
  obtain ⟨c, n, α, β⟩ := m
  simp only [gbL, gbDS, gbDA, gbG, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  linear_combination
    (c * n * (u ^ α * v ^ β * Real.exp (-(u ^ 2 + v ^ 2) / (4 * a))) * a⁻¹ ^ n
      - c / 4 * (u ^ (α + 2) * v ^ β * Real.exp (-(u ^ 2 + v ^ 2) / (4 * a))) * a⁻¹ ^ (n + 1)
      - c / 4 * (u ^ α * v ^ (β + 2) * Real.exp (-(u ^ 2 + v ^ 2) / (4 * a))) * a⁻¹ ^ (n + 1))
    * hab

lemma gbL_hasDerivAt_u (L : List GbMon) (a u v : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun u' => gbL L a u' v) (gbL (gbOpL gbDU L) a u v) u := by
  induction L with
  | nil =>
    rw [show (fun u' => gbL [] a u' v) = fun _ => (0 : ℝ) from funext fun _ => gbL_nil _ _ _,
      show gbOpL gbDU [] = [] from rfl, gbL_nil]
    exact hasDerivAt_const u 0
  | cons m L ih =>
    have h := (gbG_hasDerivAt_u m a u v ha).add ih
    have e1 : (fun u' => gbL (m :: L) a u' v) = fun u' => gbG m a u' v + gbL L a u' v :=
      funext fun u' => gbL_cons m L a u' v
    rw [e1, show gbOpL gbDU (m :: L) = gbDU m ++ gbOpL gbDU L from rfl, gbL_append]
    exact h

lemma gbL_hasDerivAt_v (L : List GbMon) (a u v : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun v' => gbL L a u v') (gbL (gbOpL gbDV L) a u v) v := by
  induction L with
  | nil =>
    rw [show (fun v' => gbL [] a u v') = fun _ => (0 : ℝ) from funext fun _ => gbL_nil _ _ _,
      show gbOpL gbDV [] = [] from rfl, gbL_nil]
    exact hasDerivAt_const v 0
  | cons m L ih =>
    have h := (gbG_hasDerivAt_v m a u v ha).add ih
    have e1 : (fun v' => gbL (m :: L) a u v') = fun v' => gbG m a u v' + gbL L a u v' :=
      funext fun v' => gbL_cons m L a u v'
    rw [e1, show gbOpL gbDV (m :: L) = gbDV m ++ gbOpL gbDV L from rfl, gbL_append]
    exact h

lemma gbL_hasDerivAt_a (L : List GbMon) (a u v : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun a' => gbL L a' u v) (gbL (gbOpL gbDA L) a u v) a := by
  induction L with
  | nil =>
    rw [show (fun a' => gbL [] a' u v) = fun _ => (0 : ℝ) from funext fun _ => gbL_nil _ _ _,
      show gbOpL gbDA [] = [] from rfl, gbL_nil]
    exact hasDerivAt_const a 0
  | cons m L ih =>
    have h := (gbG_hasDerivAt_a m a u v ha).add ih
    have e1 : (fun a' => gbL (m :: L) a' u v) = fun a' => gbG m a' u v + gbL L a' u v :=
      funext fun a' => gbL_cons m L a' u v
    rw [e1, show gbOpL gbDA (m :: L) = gbDA m ++ gbOpL gbDA L from rfl, gbL_append]
    exact h

lemma gbL_DS_list (L : List GbMon) (a u v : ℝ) (hab : a * a⁻¹ = 1) :
    gbL (gbOpL gbDS L) a u v = (a - 1) * gbL (gbOpL gbDA L) a u v := by
  induction L with
  | nil => simp [gbOpL, gbL]
  | cons m L ih =>
    rw [show gbOpL gbDS (m :: L) = gbDS m ++ gbOpL gbDS L from rfl,
      show gbOpL gbDA (m :: L) = gbDA m ++ gbOpL gbDA L from rfl, gbL_append, gbL_append,
      gbDS_eq m a u v hab, ih]
    ring

end UnforcedLeray.Short.PartIIIb.Concrete
