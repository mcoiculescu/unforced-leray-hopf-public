import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T9.Chart

/-!
# `gaussWordBound` (task `PartIII-b:C/asrc/ra/9/1/2/9/1/1/9`)

Source `the November 2 reference manuscript` lines 4963-4968 (Gaussian symbol
calculus), 5063-5071, 5076-5079. Every conormal word of length `≤ 4` on `hpGaussM` is a finite sum
of Gaussian monomials `c (a⁻¹)^n u^α v^β exp(-(u²+v²)/(4a))` with `α+β ≤ 11`, `a = 1+νs ∈ [1,2.1]`
(`Chart.lean`), and each monomial is bounded by `|c| (1+|x_j|)^{11} exp(-|x_j|²/(8a))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

lemma gb_len_of_budget {w : List (Fin 3)} (h : w ∈ budgetWords) : w.length ≤ 4 := by
  unfold budgetWords at h
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
    true_and] at h
  obtain ⟨n, hn, f, rfl⟩ := h
  simp only [List.length_ofFn]
  omega

lemma gbE0_eq : ‖gbE0‖ = 1 := by
  simp [gbE0, toMer, EuclideanSpace.norm_eq, Fin.sum_univ_two]

lemma gbE1_eq : ‖gbE1‖ = 1 := by
  simp [gbE1, toMer, EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- Sum of the absolute values of the monomial coefficients. -/
def gbK (L : List GbMon) : ℝ := (L.map fun mo => |mo.c|).sum

lemma gbK_nonneg (L : List GbMon) : 0 ≤ gbK L := by
  unfold gbK
  refine List.sum_nonneg fun x hx => ?_
  obtain ⟨mo, _, rfl⟩ := List.mem_map.mp hx
  exact abs_nonneg _

lemma gbG_bound (m : GbMon) (a u v r : ℝ) (ha : 1 ≤ a) (hr : 1 ≤ r) (hu : |u| ≤ r)
    (hv : |v| ≤ r) (hd : m.α + m.β ≤ 11) :
    |gbG m a u v| ≤ |m.c| * (r ^ 11 * Real.exp (-(u ^ 2 + v ^ 2) / (8 * a))) := by
  have ha0 : 0 < a := by linarith
  have hinv0 : 0 ≤ a⁻¹ := inv_nonneg.2 ha0.le
  have hinv1 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha
  have hP : |a⁻¹ ^ m.n| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hinv0 _)]
    exact pow_le_one₀ hinv0 hinv1
  have hU : |u| ^ m.α ≤ r ^ m.α := pow_le_pow_left₀ (abs_nonneg u) hu m.α
  have hV : |v| ^ m.β ≤ r ^ m.β := pow_le_pow_left₀ (abs_nonneg v) hv m.β
  have hr' : r ^ (m.α + m.β) ≤ r ^ 11 := pow_le_pow_right₀ hr (by omega)
  have hE : Real.exp (-(u ^ 2 + v ^ 2) / (4 * a)) ≤ Real.exp (-(u ^ 2 + v ^ 2) / (8 * a)) := by
    apply Real.exp_le_exp.mpr
    have hS : 0 ≤ u ^ 2 + v ^ 2 := by positivity
    have h8 : (u ^ 2 + v ^ 2) / (8 * a) ≤ (u ^ 2 + v ^ 2) / (4 * a) :=
      div_le_div_of_nonneg_left hS (by positivity) (by linarith)
    rw [neg_div, neg_div]
    linarith
  have habs : |gbG m a u v| = |m.c| * |a⁻¹ ^ m.n| * (|u| ^ m.α * |v| ^ m.β)
      * Real.exp (-(u ^ 2 + v ^ 2) / (4 * a)) := by
    unfold gbG
    simp only [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    ring
  have step1 : |m.c| * |a⁻¹ ^ m.n| * (|u| ^ m.α * |v| ^ m.β) ≤ |m.c| * 1 * (r ^ m.α * r ^ m.β) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hP (abs_nonneg _)) (mul_le_mul hU hV (by positivity)
      (by positivity)) (by positivity) (by positivity)
  rw [habs]
  calc |m.c| * |a⁻¹ ^ m.n| * (|u| ^ m.α * |v| ^ m.β) * Real.exp (-(u ^ 2 + v ^ 2) / (4 * a))
      ≤ (|m.c| * 1 * (r ^ m.α * r ^ m.β)) * Real.exp (-(u ^ 2 + v ^ 2) / (8 * a)) :=
        mul_le_mul step1 hE (Real.exp_pos _).le (by positivity)
    _ = |m.c| * (r ^ (m.α + m.β) * Real.exp (-(u ^ 2 + v ^ 2) / (8 * a))) := by
        rw [pow_add]; ring
    _ ≤ |m.c| * (r ^ 11 * Real.exp (-(u ^ 2 + v ^ 2) / (8 * a))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr' (Real.exp_pos _).le) (abs_nonneg _)

lemma gbL_bound (L : List GbMon) (a u v r : ℝ) (ha : 1 ≤ a) (hr : 1 ≤ r) (hu : |u| ≤ r)
    (hv : |v| ≤ r) (hd : ∀ mo ∈ L, mo.α + mo.β ≤ 11) :
    |gbL L a u v| ≤ gbK L * (r ^ 11 * Real.exp (-(u ^ 2 + v ^ 2) / (8 * a))) := by
  induction L with
  | nil => simp [gbL_nil, gbK]
  | cons m L ih =>
    have h1 := gbG_bound m a u v r ha hr hu hv (hd m (by simp))
    have h2 := ih (fun mo hmo => hd mo (by simp [hmo]))
    have hK : gbK (m :: L) = |m.c| + gbK L := by simp [gbK]
    rw [gbL_cons, hK]
    calc |gbG m a u v + gbL L a u v| ≤ |gbG m a u v| + |gbL L a u v| := abs_add_le _ _
      _ ≤ |m.c| * (r ^ 11 * Real.exp (-(u ^ 2 + v ^ 2) / (8 * a)))
          + gbK L * (r ^ 11 * Real.exp (-(u ^ 2 + v ^ 2) / (8 * a))) := add_le_add h1 h2
      _ = (|m.c| + gbK L) * (r ^ 11 * Real.exp (-(u ^ 2 + v ^ 2) / (8 * a))) := by ring

lemma gb_chart_bound (L : List GbMon) (ν : ℝ) (j : ℤ) (hν : 0 < ν) (q : Chart) (hq : 0 < q.1)
    (hd : ∀ mo ∈ L, mo.α + mo.β ≤ 11) : |gbC ν j L q| ≤ gbK L * envTerm 11 ν j q := by
  have ha : 1 ≤ ageA ν q.1 := by
    unfold ageA
    nlinarith [mul_pos hν hq]
  have hr : (1 : ℝ) ≤ 1 + ‖xj ν j q.2‖ := by linarith [norm_nonneg (xj ν j q.2)]
  have hu : |q.2.1 - (j : ℝ) * cOf ν| ≤ 1 + ‖xj ν j q.2‖ := by
    have h : ‖(xj ν j q.2).1‖ ≤ ‖xj ν j q.2‖ := norm_fst_le _
    rw [Real.norm_eq_abs] at h
    have e : (xj ν j q.2).1 = q.2.1 - (j : ℝ) * cOf ν := rfl
    rw [e] at h
    linarith
  have hv : |q.2.2| ≤ 1 + ‖xj ν j q.2‖ := by
    have h : ‖(xj ν j q.2).2‖ ≤ ‖xj ν j q.2‖ := norm_snd_le _
    rw [Real.norm_eq_abs] at h
    have e : (xj ν j q.2).2 = q.2.2 := rfl
    rw [e] at h
    linarith
  have hb := gbL_bound L (ageA ν q.1) (q.2.1 - (j : ℝ) * cOf ν) q.2.2 (1 + ‖xj ν j q.2‖) ha hr
    hu hv hd
  have henv : envTerm 11 ν j q = (1 + ‖xj ν j q.2‖) ^ 11
      * Real.exp (-((q.2.1 - (j : ℝ) * cOf ν) ^ 2 + q.2.2 ^ 2) / (8 * ageA ν q.1)) := rfl
  unfold gbC
  rw [henv]
  exact hb

/-- **Gaussian word bound** (source 4963-4968, 5063-5071, 5076-5079). -/
theorem gaussWordBound : ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 0 < s →
    ν * s ≤ 11 / 10 → ∀ w ∈ budgetWords, ∀ (a b : Fin 2) (x : ℝ × ℝ) (j : ℤ),
      ‖wordW w (hpGaussM ν j a b) (s, x)‖ ≤ C * envTerm m ν j (s, x) := by
  have hex : ∀ w ∈ budgetWords, ∀ a b : Fin 2, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (ν : ℝ), 0 < ν → ∀ (j : ℤ), ∀ q : Chart, 0 < q.1 →
        ‖wordW w (hpGaussM ν j a b) q‖ ≤ K * envTerm 11 ν j q := by
    intro w hw a b
    have hlen : w.length ≤ 4 := gb_len_of_budget hw
    obtain ⟨L0, L1, hdeg, hrep⟩ := gbRep_all a b w hlen
    refine ⟨gbK L0 + gbK L1, add_nonneg (gbK_nonneg _) (gbK_nonneg _), fun ν hν j q hq => ?_⟩
    have hqU : q ∈ UChart := ⟨hq, Set.mem_univ _⟩
    rw [hrep ν hν j q hqU]
    have hd0 : ∀ mo ∈ L0, mo.α + mo.β ≤ 11 := fun mo h => by
      have := hdeg mo (List.mem_append_left _ h)
      omega
    have hd1 : ∀ mo ∈ L1, mo.α + mo.β ≤ 11 := fun mo h => by
      have := hdeg mo (List.mem_append_right _ h)
      omega
    have h0 := gb_chart_bound L0 ν j hν q hq hd0
    have h1 := gb_chart_bound L1 ν j hν q hq hd1
    calc ‖gbC ν j L0 q • gbE0 + gbC ν j L1 q • gbE1‖
        ≤ ‖gbC ν j L0 q • gbE0‖ + ‖gbC ν j L1 q • gbE1‖ := norm_add_le _ _
      _ = |gbC ν j L0 q| + |gbC ν j L1 q| := by
          rw [norm_smul, norm_smul, gbE0_eq, gbE1_eq, Real.norm_eq_abs, Real.norm_eq_abs]
          ring
      _ ≤ gbK L0 * envTerm 11 ν j q + gbK L1 * envTerm 11 ν j q := add_le_add h0 h1
      _ = (gbK L0 + gbK L1) * envTerm 11 ν j q := by ring
  choose! K hK0 hK using hex
  refine ⟨∑ w ∈ budgetWords, ∑ a : Fin 2, ∑ b : Fin 2, K w a b, 11,
    Finset.sum_nonneg fun w hw => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      hK0 w hw a b, fun ν hν s hs _ w hw a b x j => ?_⟩
  have hKC : K w a b ≤ ∑ w ∈ budgetWords, ∑ a : Fin 2, ∑ b : Fin 2, K w a b := by
    have h1 : K w a b ≤ ∑ b : Fin 2, K w a b :=
      Finset.single_le_sum (f := fun b => K w a b) (fun b _ => hK0 w hw a b) (Finset.mem_univ b)
    have h2 : ∑ b : Fin 2, K w a b ≤ ∑ a : Fin 2, ∑ b : Fin 2, K w a b :=
      Finset.single_le_sum (f := fun a => ∑ b : Fin 2, K w a b)
        (fun a _ => Finset.sum_nonneg fun b _ => hK0 w hw a b) (Finset.mem_univ a)
    have h3 : ∑ a : Fin 2, ∑ b : Fin 2, K w a b
        ≤ ∑ w ∈ budgetWords, ∑ a : Fin 2, ∑ b : Fin 2, K w a b :=
      Finset.single_le_sum (f := fun w => ∑ a : Fin 2, ∑ b : Fin 2, K w a b)
        (fun w hw' => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hK0 w hw' a b) hw
    linarith
  have hq : (0 : ℝ) < (s, x).1 := hs
  have henv : 0 ≤ envTerm 11 ν j (s, x) :=
    mul_nonneg (pow_nonneg (add_nonneg zero_le_one (norm_nonneg _)) _) (Real.exp_pos _).le
  calc ‖wordW w (hpGaussM ν j a b) (s, x)‖ ≤ K w a b * envTerm 11 ν j (s, x) :=
        hK w hw a b ν hν j (s, x) hq
    _ ≤ (∑ w ∈ budgetWords, ∑ a : Fin 2, ∑ b : Fin 2, K w a b) * envTerm 11 ν j (s, x) :=
        mul_le_mul_of_nonneg_right hKC henv

end UnforcedLeray.Short.PartIIIb.Concrete
