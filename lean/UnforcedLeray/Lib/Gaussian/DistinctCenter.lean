import UnforcedLeray.Lib.Gaussian.PeriodizationCell

/-!
# Distinct-center Gaussian products (INF22 G8, BP11)


target G8 and bypass BP11 (the exact parallelogram identity, no "Gaussian product estimate").
Units B0146 (tex 2196–2216: `Q_c = ∑_{i≠j} V_i ⊗ V_j`), B0147 (tex 2217–2234), B0239
(tex 4133–4147), B0335 (tex 6348–6428), B0814/B0815 (tex 11888–11902), B0818.

Main results:
* `gauss_mul_gauss` (BP11): in a real inner product space,
  `e^{-‖x-p‖²/(4a)} e^{-‖x-q‖²/(4a)} = e^{-‖p-q‖²/(8a)} e^{-‖x-(p+q)/2‖²/(2a)}`;
* `lattice_gauss_mul_gauss`: its lattice form on `ℝ × ℝ` (tex 2224–2229),
  `e^{-((q-ic)²+η²)/(8a)} e^{-((q-jc)²+η²)/(8a)}
     = e^{-(i-j)²c²/(16a)} e^{-η²/(4a)} e^{-((q-(i-j)c/2) - jc)²/(4a)}`;
* `distinctPairsEquiv`: `{(i,j) : i ≠ j} ≃ {k ≠ 0} × ℤ`, `(i,j) ↦ (i-j, j)`;
* `tsum_distinct_center_le` (B0147, B0814): uniformly in `q`, `c` and `0 < a ≤ c²`,
  `∑_{i≠j} e^{-((q-ic)²+η²)/(8a)} e^{-((q-jc)²+η²)/(8a)} ≤ 340 e^{-c²/(16a)} e^{-η²/(4a)}`;
* `tsum_norm_mul_norm_distinct_le`: for functions with Gaussian translate bounds
  `‖g₁‖ ≤ A e^{-|z|²/(8a)}`, `‖g₂‖ ≤ B e^{-|z|²/(8a)}` (e.g. derivatives `D^αV`, `D^βV`, with the
  powers of `a` from G1/G2 inside `A`, `B`), the distinct-center sum
  `∑_{i≠j} ‖g₁(z - ic)‖ ‖g₂(z - jc)‖ ≤ 340 A B e^{-c²/(16a)} e^{-η²/(4a)}` (the `L^∞` bound);
* `lintegral_cell_sq_distinct_le`: its cell `L²` bound
  `∫_cell (∑_{i≠j} ‖g₁(z-ic)‖‖g₂(z-jc)‖)² ≤ 340² √(2π) A²B² · c √a · e^{-c²/(8a)}`, and
  `sqrt_mul_exp_le` turns `c e^{-c²/(16a)}` into `4√a`, which gives the manuscript's
  `C A² B² a e^{-c²/(16a)}` (tex 2229–2234).
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Gaussian

open MeasureTheory Set Real
open scoped ENNReal

/-! ### The parallelogram identity -/

section Inner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `‖x-p‖² + ‖x-q‖² = 2‖x - (p+q)/2‖² + ‖p-q‖²/2`. -/
theorem norm_sub_sq_add_norm_sub_sq (x p q : V) :
    ‖x - p‖ ^ 2 + ‖x - q‖ ^ 2 = 2 * ‖x - (1 / 2 : ℝ) • (p + q)‖ ^ 2 + ‖p - q‖ ^ 2 / 2 := by
  set u : V := x - (1 / 2 : ℝ) • (p + q)
  set d : V := (1 / 2 : ℝ) • (p - q)
  have h1 : x - p = u - d := by
    simp only [u, d, smul_add, smul_sub]; module
  have h2 : x - q = u + d := by
    simp only [u, d, smul_add, smul_sub]; module
  have hd : ‖d‖ = ‖p - q‖ / 2 := by
    simp only [d, norm_smul, Real.norm_eq_abs]; norm_num; ring
  have hpar := parallelogram_law_with_norm ℝ u d
  rw [hd, div_pow] at hpar
  rw [h1, h2]
  linarith

/-- **G8 (BP11).** `e^{-‖x-p‖²/(4a)} e^{-‖x-q‖²/(4a)} = e^{-‖p-q‖²/(8a)} e^{-‖x-(p+q)/2‖²/(2a)}`. -/
theorem gauss_mul_gauss (a : ℝ) (x p q : V) :
    Real.exp (-‖x - p‖ ^ 2 / (4 * a)) * Real.exp (-‖x - q‖ ^ 2 / (4 * a)) =
      Real.exp (-‖p - q‖ ^ 2 / (8 * a)) *
        Real.exp (-‖x - (1 / 2 : ℝ) • (p + q)‖ ^ 2 / (2 * a)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have h := norm_sub_sq_add_norm_sub_sq x p q
  rcases eq_or_ne a 0 with ha | ha
  · subst ha; simp
  · field_simp
    linear_combination (-16 : ℝ) * h

end Inner

/-! ### The lattice form and the distinct-pair reindexing -/

/-- **G8 (tex 2224–2229).** The lattice parallelogram identity with `8a`-Gaussians. -/
theorem lattice_gauss_mul_gauss (a c q η : ℝ) (i j : ℤ) :
    Real.exp (-((q - i * c) ^ 2 + η ^ 2) / (8 * a)) *
        Real.exp (-((q - j * c) ^ 2 + η ^ 2) / (8 * a)) =
      Real.exp (-((i - j : ℤ) : ℝ) ^ 2 * c ^ 2 / (16 * a)) * Real.exp (-η ^ 2 / (4 * a)) *
        Real.exp (-((q - ((i - j : ℤ) : ℝ) * c / 2) - j * c) ^ 2 / (4 * a)) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  push_cast
  rcases eq_or_ne a 0 with ha | ha
  · subst ha; simp
  · field_simp
    ring

/-- `{(i,j) : i ≠ j} ≃ {k ≠ 0} × ℤ`, `(i,j) ↦ (i - j, j)`. -/
def distinctPairsEquiv : ({k : ℤ // k ≠ 0} × ℤ) ≃ {p : ℤ × ℤ // p.1 ≠ p.2} where
  toFun x := ⟨(x.2 + x.1, x.2), by
    intro h; exact x.1.2 (by simpa using h)⟩
  invFun p := (⟨p.1.1 - p.1.2, sub_ne_zero.2 p.2⟩, p.1.2)
  left_inv x := by
    rcases x with ⟨⟨k, hk⟩, j⟩
    simp
  right_inv p := by
    rcases p with ⟨⟨i, j⟩, h⟩
    simp

/-- **G8 (B0147, B0814; tex 2224–2232).** Uniformly in `q`, `η`, the period `c` and
`0 < a ≤ c²`:
`∑_{i≠j} e^{-((q-ic)²+η²)/(8a)} e^{-((q-jc)²+η²)/(8a)} ≤ 340 e^{-c²/(16a)} e^{-η²/(4a)}`,
with summability. -/
theorem tsum_distinct_center_le {a c : ℝ} (ha : 0 < a) (hac : a ≤ c ^ 2) (q η : ℝ) :
    Summable (fun p : {p : ℤ × ℤ // p.1 ≠ p.2} =>
        Real.exp (-((q - p.1.1 * c) ^ 2 + η ^ 2) / (8 * a)) *
          Real.exp (-((q - p.1.2 * c) ^ 2 + η ^ 2) / (8 * a))) ∧
      ∑' p : {p : ℤ × ℤ // p.1 ≠ p.2},
          Real.exp (-((q - p.1.1 * c) ^ 2 + η ^ 2) / (8 * a)) *
            Real.exp (-((q - p.1.2 * c) ^ 2 + η ^ 2) / (8 * a)) ≤
        340 * Real.exp (-c ^ 2 / (16 * a)) * Real.exp (-η ^ 2 / (4 * a)) := by
  set β : ℝ := c ^ 2 / (16 * a) with hβdef
  have hβ16 : 1 / 16 ≤ β := by rw [hβdef, le_div_iff₀ (by positivity)]; linarith
  have hβ : 0 < β := by linarith
  set F : {p : ℤ × ℤ // p.1 ≠ p.2} → ℝ := fun p =>
    Real.exp (-((q - p.1.1 * c) ^ 2 + η ^ 2) / (8 * a)) *
      Real.exp (-((q - p.1.2 * c) ^ 2 + η ^ 2) / (8 * a)) with hF
  set H : {k : ℤ // k ≠ 0} × ℤ → ℝ := fun x =>
    Real.exp (-((x.1 : ℤ) : ℝ) ^ 2 * β) * Real.exp (-η ^ 2 / (4 * a)) *
      Real.exp (-((q - ((x.1 : ℤ) : ℝ) * c / 2) - x.2 * c) ^ 2 / (4 * a)) with hH
  have ha0 : a ≠ 0 := ha.ne'
  have hFH : ∀ x, F (distinctPairsEquiv x) = H x := by
    rintro ⟨⟨k, hk⟩, j⟩
    simp only [hF, hH, distinctPairsEquiv, Equiv.coe_fn_mk]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hβdef]
    push_cast
    field_simp
    ring
  have hH0 : 0 ≤ H := by
    intro x; simp only [hH, Pi.zero_apply]; positivity
  -- fibrewise sums
  have hfib : ∀ k : {k : ℤ // k ≠ 0}, Summable (fun j : ℤ => H (k, j)) ∧
      ∑' j : ℤ, H (k, j) ≤ 10 * (Real.exp (-((k : ℤ) : ℝ) ^ 2 * β) * Real.exp (-η ^ 2 / (4 * a))) := by
    intro k
    have hs := summable_gauss_shift ha hac (q - ((k : ℤ) : ℝ) * c / 2)
    have hb := tsum_gauss_shift_le ha hac (q - ((k : ℤ) : ℝ) * c / 2)
    simp only [hH]
    refine ⟨hs.mul_left _, ?_⟩
    rw [tsum_mul_left]
    have hp : 0 ≤ Real.exp (-((k : ℤ) : ℝ) ^ 2 * β) * Real.exp (-η ^ 2 / (4 * a)) := by positivity
    calc Real.exp (-((k : ℤ) : ℝ) ^ 2 * β) * Real.exp (-η ^ 2 / (4 * a)) *
          ∑' j : ℤ, Real.exp (-((q - ((k : ℤ) : ℝ) * c / 2) - j * c) ^ 2 / (4 * a))
        ≤ Real.exp (-((k : ℤ) : ℝ) ^ 2 * β) * Real.exp (-η ^ 2 / (4 * a)) * 10 :=
          mul_le_mul_of_nonneg_left hb hp
      _ = 10 * (Real.exp (-((k : ℤ) : ℝ) ^ 2 * β) * Real.exp (-η ^ 2 / (4 * a))) := by ring
  obtain ⟨hks, hkt⟩ := tsum_gauss_ne_zero_le_aux hβ
  have hmaj : Summable (fun k : {k : ℤ // k ≠ 0} =>
      10 * (Real.exp (-((k : ℤ) : ℝ) ^ 2 * β) * Real.exp (-η ^ 2 / (4 * a)))) :=
    (hks.mul_right _).mul_left _
  have hsumk : Summable (fun k : {k : ℤ // k ≠ 0} => ∑' j : ℤ, H (k, j)) :=
    Summable.of_nonneg_of_le (fun k => tsum_nonneg fun j => hH0 _) (fun k => (hfib k).2) hmaj
  have hHsum : Summable H := (summable_prod_of_nonneg hH0).2 ⟨fun k => (hfib k).1, hsumk⟩
  have hFsum : Summable F := by
    rw [← distinctPairsEquiv.summable_iff]
    exact hHsum.congr fun x => (hFH x).symm
  refine ⟨hFsum, ?_⟩
  have hFeq : ∑' p, F p = ∑' x, H x := by
    rw [← distinctPairsEquiv.tsum_eq F]; exact tsum_congr hFH
  show ∑' p, F p ≤ _
  rw [hFeq, hHsum.tsum_prod' fun k => (hfib k).1]
  refine (hsumk.tsum_le_tsum (fun k => (hfib k).2) hmaj).trans ?_
  rw [tsum_mul_left, tsum_mul_right]
  -- (1 - e^{-β})⁻¹ ≤ 17 from e^{1/16} ≥ 17/16
  have h1 : (1 : ℝ) / 16 + 1 ≤ Real.exp (1 / 16) := Real.add_one_le_exp _
  have hE : Real.exp (-(1 / 16)) * Real.exp (1 / 16) = 1 := by rw [← Real.exp_add]; simp
  have he16 : Real.exp (-(1 / 16)) ≤ 16 / 17 := by
    have hp := Real.exp_pos (-(1 / 16 : ℝ))
    nlinarith
  have heβ : Real.exp (-β) ≤ 16 / 17 := (Real.exp_le_exp.2 (by linarith)).trans he16
  have hpos : 0 < 1 - Real.exp (-β) := by linarith
  have hinv : (1 - Real.exp (-β))⁻¹ ≤ 17 := by
    rw [inv_le_iff_one_le_mul₀ hpos]; linarith
  have hk' : ∑' k : {k : ℤ // k ≠ 0}, Real.exp (-((k : ℤ) : ℝ) ^ 2 * β) ≤ 34 * Real.exp (-β) := by
    refine hkt.trans ?_
    have he : 0 ≤ Real.exp (-β) := (Real.exp_pos _).le
    calc 2 * (1 - Real.exp (-β))⁻¹ * Real.exp (-β) ≤ 2 * 17 * Real.exp (-β) := by gcongr
      _ = 34 * Real.exp (-β) := by ring
  have hrhs : Real.exp (-c ^ 2 / (16 * a)) = Real.exp (-β) := by
    congr 1; rw [hβdef, neg_div]
  rw [hrhs]
  have hη : 0 ≤ Real.exp (-η ^ 2 / (4 * a)) := (Real.exp_pos _).le
  calc 10 * ((∑' k : {k : ℤ // k ≠ 0}, Real.exp (-((k : ℤ) : ℝ) ^ 2 * β)) *
        Real.exp (-η ^ 2 / (4 * a)))
      ≤ 10 * (34 * Real.exp (-β) * Real.exp (-η ^ 2 / (4 * a))) := by gcongr
    _ = 340 * Real.exp (-β) * Real.exp (-η ^ 2 / (4 * a)) := by ring

/-! ### Functions with Gaussian translate bounds -/

section Bounds

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]

/-- **G8 (B0147, B0814, B0815; `L^∞` part).** If `‖g₁(z)‖ ≤ A e^{-(q²+η²)/(8a)}` and
`‖g₂(z)‖ ≤ B e^{-(q²+η²)/(8a)}` with `0 < a ≤ c²`, then
`∑_{i≠j} ‖g₁(q - ic, η)‖ ‖g₂(q - jc, η)‖ ≤ 340 A B e^{-c²/(16a)} e^{-η²/(4a)}`,
with summability, uniformly in `q`, `c` and `a`. -/
theorem tsum_norm_mul_norm_distinct_le {g₁ : ℝ × ℝ → E₁} {g₂ : ℝ × ℝ → E₂} {A B a c : ℝ}
    (ha : 0 < a) (hac : a ≤ c ^ 2)
    (h₁ : ∀ z : ℝ × ℝ, ‖g₁ z‖ ≤ A * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (8 * a)))
    (h₂ : ∀ z : ℝ × ℝ, ‖g₂ z‖ ≤ B * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (8 * a))) (z : ℝ × ℝ) :
    Summable (fun p : {p : ℤ × ℤ // p.1 ≠ p.2} =>
        ‖g₁ (z.1 - p.1.1 * c, z.2)‖ * ‖g₂ (z.1 - p.1.2 * c, z.2)‖) ∧
      ∑' p : {p : ℤ × ℤ // p.1 ≠ p.2}, ‖g₁ (z.1 - p.1.1 * c, z.2)‖ * ‖g₂ (z.1 - p.1.2 * c, z.2)‖ ≤
        340 * A * B * Real.exp (-c ^ 2 / (16 * a)) * Real.exp (-z.2 ^ 2 / (4 * a)) := by
  have hB : 0 ≤ B := by
    have h := h₂ 0
    simp only [Prod.fst_zero, Prod.snd_zero] at h
    norm_num at h
    exact (norm_nonneg _).trans h
  obtain ⟨hs, ht⟩ := tsum_distinct_center_le ha hac z.1 z.2
  have hpt : ∀ p : {p : ℤ × ℤ // p.1 ≠ p.2},
      ‖g₁ (z.1 - p.1.1 * c, z.2)‖ * ‖g₂ (z.1 - p.1.2 * c, z.2)‖ ≤
        A * B * (Real.exp (-((z.1 - p.1.1 * c) ^ 2 + z.2 ^ 2) / (8 * a)) *
          Real.exp (-((z.1 - p.1.2 * c) ^ 2 + z.2 ^ 2) / (8 * a))) := by
    intro p
    have e1 := h₁ (z.1 - p.1.1 * c, z.2)
    have e2 := h₂ (z.1 - p.1.2 * c, z.2)
    simp only at e1 e2
    calc ‖g₁ (z.1 - p.1.1 * c, z.2)‖ * ‖g₂ (z.1 - p.1.2 * c, z.2)‖
        ≤ (A * Real.exp (-((z.1 - p.1.1 * c) ^ 2 + z.2 ^ 2) / (8 * a))) *
          (B * Real.exp (-((z.1 - p.1.2 * c) ^ 2 + z.2 ^ 2) / (8 * a))) :=
          mul_le_mul e1 e2 (norm_nonneg _) ((norm_nonneg _).trans e1)
      _ = _ := by ring
  have hmaj := hs.mul_left (A * B)
  have hsum := Summable.of_nonneg_of_le (fun p => by positivity) hpt hmaj
  refine ⟨hsum, (hsum.tsum_le_tsum hpt hmaj).trans ?_⟩
  rw [tsum_mul_left]
  have hAB : 0 ≤ A * B := by
    have h := h₁ 0
    simp only [Prod.fst_zero, Prod.snd_zero] at h
    norm_num at h
    exact mul_nonneg ((norm_nonneg _).trans h) hB
  calc A * B * ∑' p : {p : ℤ × ℤ // p.1 ≠ p.2},
        Real.exp (-((z.1 - p.1.1 * c) ^ 2 + z.2 ^ 2) / (8 * a)) *
          Real.exp (-((z.1 - p.1.2 * c) ^ 2 + z.2 ^ 2) / (8 * a))
      ≤ A * B * (340 * Real.exp (-c ^ 2 / (16 * a)) * Real.exp (-z.2 ^ 2 / (4 * a))) :=
        mul_le_mul_of_nonneg_left ht hAB
    _ = _ := by ring

/-- `c e^{-c²/(16a)} ≤ 4√a` for `a > 0` (from `x e^{-x²} ≤ 1`). -/
theorem mul_exp_neg_sq_div_le {a : ℝ} (ha : 0 < a) (c : ℝ) :
    |c| * Real.exp (-c ^ 2 / (16 * a)) ≤ 4 * Real.sqrt a := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  set x : ℝ := |c| / (4 * Real.sqrt a) with hx
  have hx0 : 0 ≤ x := by positivity
  have hc : |c| = 4 * Real.sqrt a * x := by rw [hx]; field_simp
  have hsq : -c ^ 2 / (16 * a) = -x ^ 2 := by
    rw [← sq_abs c, hc, mul_pow, mul_pow, Real.sq_sqrt ha.le]; field_simp; ring
  rw [hc, hsq]
  -- x e^{-x²} ≤ 1 since e^{x²} ≥ 1 + x² ≥ x
  have h1 : x ^ 2 + 1 ≤ Real.exp (x ^ 2) := Real.add_one_le_exp _
  have hxe : x * Real.exp (-x ^ 2) ≤ 1 := by
    have hp := Real.exp_pos (-x ^ 2)
    have hxle : x ≤ Real.exp (x ^ 2) := by nlinarith [sq_nonneg (x - 1)]
    calc x * Real.exp (-x ^ 2) ≤ Real.exp (x ^ 2) * Real.exp (-x ^ 2) :=
          mul_le_mul_of_nonneg_right hxle hp.le
      _ = 1 := by rw [← Real.exp_add]; simp
  calc 4 * Real.sqrt a * x * Real.exp (-x ^ 2) = 4 * Real.sqrt a * (x * Real.exp (-x ^ 2)) := by
        ring
    _ ≤ 4 * Real.sqrt a * 1 := by gcongr
    _ = 4 * Real.sqrt a := by ring

/-- `∫_{[0,c)×ℝ} ofReal(e^{-η²/(2a)}) = c √(2πa)` (as a lower integral). -/
theorem lintegral_cell_exp_neg_sq {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∫⁻ z in cell c, ENNReal.ofReal (Real.exp (-z.2 ^ 2 / (2 * a))) =
      ENNReal.ofReal (c * Real.sqrt (2 * π * a)) := by
  have hb : 0 < 1 / (2 * a) := by positivity
  have hprod := lintegral_prod_mul (μ := (volume : Measure ℝ).restrict (Ico 0 c))
    (ν := (volume : Measure ℝ)) (f := fun _ : ℝ => (1 : ℝ≥0∞))
    (g := fun y : ℝ => ENNReal.ofReal (Real.exp (-(1 / (2 * a)) * y ^ 2)))
    aemeasurable_const (by fun_prop)
  have hG := ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq hb)
    (ae_of_all _ fun y => (Real.exp_pos _).le)
  rw [integral_gaussian] at hG
  calc ∫⁻ z in cell c, ENNReal.ofReal (Real.exp (-z.2 ^ 2 / (2 * a)))
      = ∫⁻ z, (fun _ : ℝ => (1 : ℝ≥0∞)) z.1 *
          (fun y : ℝ => ENNReal.ofReal (Real.exp (-(1 / (2 * a)) * y ^ 2))) z.2
            ∂((volume : Measure ℝ).restrict (Ico 0 c)).prod volume := by
        rw [cell, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
        congr 1; funext z; simp only [one_mul]; congr 2; ring
    _ = ENNReal.ofReal c * ENNReal.ofReal (Real.sqrt (π / (1 / (2 * a)))) := by
        rw [hprod, ← hG]; congr 1; simp [Real.volume_Ico]
    _ = ENNReal.ofReal (c * Real.sqrt (2 * π * a)) := by
        rw [← ENNReal.ofReal_mul hc.le]
        congr 2
        rw [div_div_eq_mul_div, div_one]; ring

/-- **G8 (B0147, B0815; cell `L²` part, tex 2229–2234).** Under the hypotheses of
`tsum_norm_mul_norm_distinct_le` and `c > 0`:
`∫_{[0,c)×ℝ} (∑_{i≠j} ‖g₁(z-ic)‖ ‖g₂(z-jc)‖)² ≤ 340² A²B² · c √(2πa) · e^{-c²/(8a)}`; with
`mul_exp_neg_sq_div_le` the right side is `≤ C A²B² a e^{-c²/(16a)}`. -/
theorem lintegral_cell_sq_distinct_le {g₁ : ℝ × ℝ → E₁} {g₂ : ℝ × ℝ → E₂} {A B a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hac : a ≤ c ^ 2)
    (h₁ : ∀ z : ℝ × ℝ, ‖g₁ z‖ ≤ A * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (8 * a)))
    (h₂ : ∀ z : ℝ × ℝ, ‖g₂ z‖ ≤ B * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (8 * a))) :
    ∫⁻ z in cell c, ENNReal.ofReal
        ((∑' p : {p : ℤ × ℤ // p.1 ≠ p.2},
          ‖g₁ (z.1 - p.1.1 * c, z.2)‖ * ‖g₂ (z.1 - p.1.2 * c, z.2)‖) ^ 2) ≤
      ENNReal.ofReal ((340 * A * B) ^ 2 * Real.exp (-c ^ 2 / (8 * a)) *
        (c * Real.sqrt (2 * π * a))) := by
  have hAB : 0 ≤ 340 * A * B := by
    have e1 := h₁ 0
    have e2 := h₂ 0
    simp only [Prod.fst_zero, Prod.snd_zero] at e1 e2
    norm_num at e1 e2
    have := (norm_nonneg _).trans e1
    have := (norm_nonneg _).trans e2
    positivity
  have hpt : ∀ z : ℝ × ℝ, ENNReal.ofReal
      ((∑' p : {p : ℤ × ℤ // p.1 ≠ p.2},
        ‖g₁ (z.1 - p.1.1 * c, z.2)‖ * ‖g₂ (z.1 - p.1.2 * c, z.2)‖) ^ 2) ≤
      ENNReal.ofReal ((340 * A * B) ^ 2 * Real.exp (-c ^ 2 / (8 * a))) *
        ENNReal.ofReal (Real.exp (-z.2 ^ 2 / (2 * a))) := by
    intro z
    obtain ⟨_, ht⟩ := tsum_norm_mul_norm_distinct_le ha hac h₁ h₂ z
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 : 0 ≤ ∑' p : {p : ℤ × ℤ // p.1 ≠ p.2},
        ‖g₁ (z.1 - p.1.1 * c, z.2)‖ * ‖g₂ (z.1 - p.1.2 * c, z.2)‖ :=
      tsum_nonneg fun p => by positivity
    have hsq := pow_le_pow_left₀ h0 ht 2
    refine hsq.trans (le_of_eq ?_)
    have e1 : Real.exp (-c ^ 2 / (16 * a)) ^ 2 = Real.exp (-c ^ 2 / (8 * a)) := by
      rw [← Real.exp_nat_mul]; congr 1; field_simp; ring
    have e2 : Real.exp (-z.2 ^ 2 / (4 * a)) ^ 2 = Real.exp (-z.2 ^ 2 / (2 * a)) := by
      rw [← Real.exp_nat_mul]; congr 1; field_simp; ring
    calc (340 * A * B * Real.exp (-c ^ 2 / (16 * a)) * Real.exp (-z.2 ^ 2 / (4 * a))) ^ 2
        = (340 * A * B) ^ 2 * Real.exp (-c ^ 2 / (16 * a)) ^ 2 *
            Real.exp (-z.2 ^ 2 / (4 * a)) ^ 2 := by ring
      _ = _ := by rw [e1, e2]
  calc ∫⁻ z in cell c, ENNReal.ofReal
        ((∑' p : {p : ℤ × ℤ // p.1 ≠ p.2},
          ‖g₁ (z.1 - p.1.1 * c, z.2)‖ * ‖g₂ (z.1 - p.1.2 * c, z.2)‖) ^ 2)
      ≤ ∫⁻ z in cell c, ENNReal.ofReal ((340 * A * B) ^ 2 * Real.exp (-c ^ 2 / (8 * a))) *
          ENNReal.ofReal (Real.exp (-z.2 ^ 2 / (2 * a))) := lintegral_mono hpt
    _ = ENNReal.ofReal ((340 * A * B) ^ 2 * Real.exp (-c ^ 2 / (8 * a))) *
          ENNReal.ofReal (c * Real.sqrt (2 * π * a)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_cell_exp_neg_sq ha hc]
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

end Bounds

end UnforcedLeray.Gaussian
