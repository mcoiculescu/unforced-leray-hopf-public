import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAff
import UnforcedLeray.Short.PartIIIb.Concrete.Spaces
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.T54

/-- Gaussian derivative bound for the `j = 0` profiles, uniform for the age variable in a
compact interval `[s0, s1]`, `s0 > 0` (source lines 4963-4968, 4991: every derivative of
`a^{-k} e^{-|x|^2/(4a)} * polynomial(x)` is `polynomial(x, a^{-1}) e^{-|x|^2/(4a)}`, and
`|x|^2 ≥ ‖x‖^2` for the sup norm). -/
def GaussCore : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (s0 s1 : ℝ), 0 < s0 → ∀ n : ℕ, ∃ (C κ : ℝ) (P : ℕ), 0 < κ ∧
    ∀ z : Chart, s0 ≤ z.1 → z.1 ≤ s1 →
      ‖iteratedFDeriv ℝ n (fun q : Chart => Vj ν q.1 0 q.2) z‖
        ≤ C * (1 + ‖z.2‖) ^ P * Real.exp (-κ * ‖z.2‖ ^ 2) ∧
      ‖iteratedFDeriv ℝ n (fun q : Chart => psij ν q.1 0 q.2) z‖
        ≤ C * (1 + ‖z.2‖) ^ P * Real.exp (-κ * ‖z.2‖ ^ 2)

/-- Lattice absorption: a polynomially weighted Gaussian in the distance to a far lattice
point is a Gaussian in the index. -/
theorem lattice_real (κ X : ℝ) (hκ : 0 < κ) (hX : 0 ≤ X) (P : ℕ) (r a : ℝ) (hr : 0 ≤ r)
    (ha : 0 ≤ a) (har : a ≤ X + r) :
    (1 + r) ^ P * Real.exp (-κ * r ^ 2) ≤
      Real.exp ((P : ℝ) ^ 2 / (2 * κ)) * Real.exp (κ * X ^ 2 / 2) * Real.exp (-(κ / 4) * a ^ 2) := by
  have h1 : (1 + r) ^ P ≤ Real.exp ((P : ℝ) * r) := by
    calc (1 + r) ^ P ≤ (Real.exp r) ^ P := by
          apply pow_le_pow_left₀ (by linarith)
          linarith [Real.add_one_le_exp r]
      _ = Real.exp ((P : ℝ) * r) := by rw [← Real.exp_nat_mul]
  have hr2 : a ^ 2 / 2 - X ^ 2 ≤ r ^ 2 := by
    rcases le_or_gt a X with h | h
    · nlinarith [sq_nonneg r, sq_nonneg a, mul_nonneg ha ha]
    · have : a - X ≤ r := by linarith
      nlinarith [sq_nonneg (a - 2 * X), mul_self_le_mul_self (by linarith : 0 ≤ a - X) this]
  have h2 : (P : ℝ) * r - κ * r ^ 2 ≤
      (P : ℝ) ^ 2 / (2 * κ) + κ * X ^ 2 / 2 - (κ / 4) * a ^ 2 := by
    have h3 : (P : ℝ) * r - κ * r ^ 2 / 2 ≤ (P : ℝ) ^ 2 / (2 * κ) := by
      have : (P : ℝ) ^ 2 / (2 * κ) - ((P : ℝ) * r - κ * r ^ 2 / 2) = κ / 2 * (r - P / κ) ^ 2 := by
        field_simp
        ring
      nlinarith [mul_nonneg (div_nonneg hκ.le (show (0:ℝ) ≤ 2 by norm_num)) (sq_nonneg (r - P / κ))]
    nlinarith [mul_le_mul_of_nonneg_left hr2 hκ.le]
  calc (1 + r) ^ P * Real.exp (-κ * r ^ 2)
      ≤ Real.exp ((P : ℝ) * r) * Real.exp (-κ * r ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((P : ℝ) * r - κ * r ^ 2) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp ((P : ℝ) ^ 2 / (2 * κ) + κ * X ^ 2 / 2 - (κ / 4) * a ^ 2) :=
        Real.exp_le_exp.mpr h2
    _ = _ := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]
        congr 2
        ring_nf

/-- Translation of `V_j`, `ψ_j` to the `j = 0` profile. -/
theorem Vj_translate (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    Vj ν s j x = Vj ν s 0 (x.1 - j * cOf ν, x.2) := by
  simp [Vj, xj]

theorem psij_translate (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    psij ν s j x = psij ν s 0 (x.1 - j * cOf ν, x.2) := by
  simp [psij, xj]

/-- Bound for a compact `K ⊆ {s > 0}`: given the `j = 0` core, the shifted profiles satisfy a
Gaussian bound in `j`. -/
theorem vjPsijMajor_of (h1 : GaussCore) (ν : ℝ) (hν : 0 < ν) (K : Set Chart) (hK : IsCompact K)
    (hKs : K ⊆ Set.Ioi 0 ×ˢ Set.univ) (n : ℕ) :
    ∃ (C c : ℝ) (P : ℕ), 0 < c ∧ ∀ (j : ℤ), ∀ p ∈ K,
      ‖iteratedFDeriv ℝ n (fun q : Chart => Vj ν q.1 j q.2) p‖
        ≤ C * (1 + |(j : ℝ)|) ^ P * Real.exp (-c * (j : ℝ) ^ 2) ∧
      ‖iteratedFDeriv ℝ n (fun q : Chart => psij ν q.1 j q.2) p‖
        ≤ C * (1 + |(j : ℝ)|) ^ P * Real.exp (-c * (j : ℝ) ^ 2) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, 1, 0, one_pos, fun j p hp => absurd hp (Set.notMem_empty p)⟩
  have hcpos : 0 < cOf ν := by unfold cOf; positivity
  -- s-range and x-range of K
  obtain ⟨pmin, hpmin, hmin⟩ := hK.exists_isMinOn hne (continuous_fst.continuousOn)
  obtain ⟨pmax, hpmax, hmax⟩ := hK.exists_isMaxOn hne (continuous_fst.continuousOn)
  obtain ⟨pX, hpX, hX⟩ := hK.exists_isMaxOn hne (continuous_snd.norm.continuousOn)
  set s0 := pmin.1 with hs0def
  set s1 := pmax.1 with hs1def
  set X := ‖pX.2‖ with hXdef
  have hs0pos : 0 < s0 := (hKs hpmin).1
  have hs0le : ∀ p ∈ K, s0 ≤ p.1 := fun p hp => hmin hp
  have hs1ge : ∀ p ∈ K, p.1 ≤ s1 := fun p hp => hmax hp
  have hXge : ∀ p ∈ K, ‖p.2‖ ≤ X := fun p hp => hX hp
  obtain ⟨C, κ, P, hκ, hbd⟩ := h1 ν hν s0 s1 hs0pos n
  have hX0 : 0 ≤ X := norm_nonneg _
  set c := cOf ν
  refine ⟨|C| * (Real.exp ((P : ℝ) ^ 2 / (2 * κ)) * Real.exp (κ * X ^ 2 / 2)), κ / 4 * c ^ 2, P,
    by positivity, ?_⟩
  intro j p hp
  set a : Chart := (0, ((-(j * c) : ℝ), 0)) with ha
  have ha1 : ∀ q : Chart, (q + a).1 = q.1 := by intro q; simp [ha]
  have ha2 : ∀ q : Chart, (q + a).2 = (q.2.1 - j * c, q.2.2) := by
    intro q; ext <;> simp [ha, sub_eq_add_neg]
  have hz1 := ha1 p
  have hz2 := ha2 p
  have hfV : (fun q : Chart => Vj ν q.1 j q.2) =
      fun q : Chart => (fun w : Chart => Vj ν w.1 0 w.2) (q + a) := by
    funext q
    show Vj ν q.1 j q.2 = Vj ν (q + a).1 0 (q + a).2
    rw [ha1, ha2, Vj_translate]
  have hfP : (fun q : Chart => psij ν q.1 j q.2) =
      fun q : Chart => (fun w : Chart => psij ν w.1 0 w.2) (q + a) := by
    funext q
    show psij ν q.1 j q.2 = psij ν (q + a).1 0 (q + a).2
    rw [ha1, ha2, psij_translate]
  have e1 : iteratedFDeriv ℝ n (fun q : Chart => Vj ν q.1 j q.2) p =
      iteratedFDeriv ℝ n (fun w : Chart => Vj ν w.1 0 w.2) (p + a) :=
    (congrArg (fun F => iteratedFDeriv ℝ n F p) hfV).trans
      (iteratedFDeriv_comp_add_right (f := fun w : Chart => Vj ν w.1 0 w.2) n a p)
  have e2 : iteratedFDeriv ℝ n (fun q : Chart => psij ν q.1 j q.2) p =
      iteratedFDeriv ℝ n (fun w : Chart => psij ν w.1 0 w.2) (p + a) :=
    (congrArg (fun F => iteratedFDeriv ℝ n F p) hfP).trans
      (iteratedFDeriv_comp_add_right (f := fun w : Chart => psij ν w.1 0 w.2) n a p)
  rw [e1, e2]
  obtain ⟨hb1, hb2⟩ := hbd (p + a) (by rw [hz1]; exact hs0le p hp) (by rw [hz1]; exact hs1ge p hp)
  -- distance to the lattice point
  have hnorm : |(j : ℝ) * c| ≤ ‖p.2‖ + ‖(p + a).2‖ := by
    have h1' : ((j : ℝ) * c, (0 : ℝ)) = p.2 - (p + a).2 := by
      rw [hz2]; ext <;> simp
    have : ‖((j : ℝ) * c, (0 : ℝ))‖ ≤ ‖p.2‖ + ‖(p + a).2‖ := by
      rw [h1']; exact norm_sub_le _ _
    have h2' : ‖((j : ℝ) * c, (0 : ℝ))‖ = |(j : ℝ) * c| := by
      simp [Prod.norm_def]
      positivity
    rwa [h2'] at this
  have hab : |(j : ℝ)| * c = |(j : ℝ) * c| := by rw [abs_mul, abs_of_pos hcpos]
  have hlat := lattice_real κ X hκ hX0 P ‖(p + a).2‖ (|(j : ℝ)| * c) (norm_nonneg _)
    (by positivity) (by rw [hab]; linarith [hXge p hp])
  have hfin : C * (1 + ‖(p + a).2‖) ^ P * Real.exp (-κ * ‖(p + a).2‖ ^ 2) ≤
      |C| * (Real.exp ((P : ℝ) ^ 2 / (2 * κ)) * Real.exp (κ * X ^ 2 / 2)) *
        (1 + |(j : ℝ)|) ^ P * Real.exp (-(κ / 4 * c ^ 2) * (j : ℝ) ^ 2) := by
    have e1 : Real.exp (-(κ / 4) * (|(j : ℝ)| * c) ^ 2) =
        Real.exp (-(κ / 4 * c ^ 2) * (j : ℝ) ^ 2) := by
      congr 1
      rw [mul_pow, sq_abs]; ring
    rw [e1] at hlat
    have hone : (1 : ℝ) ≤ (1 + |(j : ℝ)|) ^ P := one_le_pow₀ (by linarith [abs_nonneg (j : ℝ)])
    calc C * (1 + ‖(p + a).2‖) ^ P * Real.exp (-κ * ‖(p + a).2‖ ^ 2)
        = C * ((1 + ‖(p + a).2‖) ^ P * Real.exp (-κ * ‖(p + a).2‖ ^ 2)) := by ring
      _ ≤ |C| * ((1 + ‖(p + a).2‖) ^ P * Real.exp (-κ * ‖(p + a).2‖ ^ 2)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * (Real.exp ((P : ℝ) ^ 2 / (2 * κ)) * Real.exp (κ * X ^ 2 / 2) *
            Real.exp (-(κ / 4 * c ^ 2) * (j : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hlat (abs_nonneg C)
      _ ≤ |C| * (Real.exp ((P : ℝ) ^ 2 / (2 * κ)) * Real.exp (κ * X ^ 2 / 2) *
            Real.exp (-(κ / 4 * c ^ 2) * (j : ℝ) ^ 2)) * (1 + |(j : ℝ)|) ^ P :=
          le_mul_of_one_le_right (by positivity) hone
      _ = _ := by ring
  exact ⟨hb1.trans hfin, hb2.trans hfin⟩

end UnforcedLeray.Short.PartIIIb.Concrete.T54
