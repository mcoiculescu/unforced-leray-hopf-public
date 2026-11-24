import UnforcedLeray.Short.PartIIb.Sub.TrainCloseCell
import UnforcedLeray.Lib.Train.PeriodizedVortex

/-!
# Uniform sup bound of the periodized heat vortex (every `c > 0`)

Source `the November 2 reference manuscript` lines 2085-2093 (bounded drift):
`|V_c| ≤ M` on `[0,Σ/ν] × ℝ²` for every `c > 0`.  Proof: Gaussian domination `K e^{-q²/β}` of
each image and a uniform lattice sum.
-/

set_option autoImplicit false

noncomputable section

open Real

namespace UnforcedLeray.Short.IIb

/-- Uniform bound of the lattice Gaussian sum. -/
theorem vs_lat_gauss (β c : ℝ) (hβ : 0 < β) (hc : 0 < c) :
    ∃ S : ℝ, ∀ x : ℝ, Summable (fun n : ℤ => exp (-(x - n * c) ^ 2 / β)) ∧
      ∑' n : ℤ, exp (-(x - n * c) ^ 2 / β) ≤ S := by
  set κ : ℝ := c ^ 2 / (4 * β) with hκ
  have hκ0 : 0 < κ := by positivity
  set D : ℤ → ℝ := fun m => exp (-κ * |(m : ℝ)|) with hD
  have hDs : Summable D := by
    have hg : Summable (fun n : ℕ => exp (-κ * (n : ℝ))) := by
      have := summable_geometric_of_lt_one (exp_pos (-κ)).le
        (by have := Real.exp_lt_exp.mpr (show -κ < 0 by linarith); simpa using this)
      refine this.congr fun n => ?_
      rw [← exp_nat_mul]; ring_nf
    refine Summable.of_nat_of_neg ?_ ?_
    · refine hg.congr fun n => ?_
      simp [hD]
    · refine hg.congr fun n => ?_
      simp [hD]
  refine ⟨∑' m, D m, fun x => ?_⟩
  set n0 : ℤ := round (x / c) with hn0
  have ht : |x - n0 * c| ≤ c / 2 := by
    have h := abs_sub_round (x / c)
    have : x - n0 * c = (x / c - n0) * c := by field_simp
    rw [this, abs_mul, abs_of_pos hc]
    nlinarith
  have hle : ∀ n : ℤ, exp (-(x - n * c) ^ 2 / β) ≤ D (n - n0) := by
    intro n
    simp only [hD]
    apply exp_le_exp.mpr
    set m : ℤ := n - n0 with hm
    have hmabs : (1 : ℝ) ≤ |(m : ℝ)| ∨ (m : ℝ) = 0 := by
      by_cases h0 : m = 0
      · right; simp [h0]
      · left
        have : (1 : ℤ) ≤ |m| := Int.one_le_abs h0
        have h2 : ((1 : ℤ) : ℝ) ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast this
        simpa using h2
    have key : (m * c) ^ 2 / 4 ≤ (x - n * c) ^ 2 := by
      rcases hmabs with h | h
      · have hu : c ≤ |(m : ℝ) * c| := by
          rw [abs_mul, abs_of_pos hc]; nlinarith
        have e : x - n * c = (x - n0 * c) - (m * c) := by
          rw [hm]; push_cast; ring
        have h3 : |(m : ℝ) * c| / 2 ≤ |x - n * c| := by
          rw [e]
          have h4 := abs_sub_abs_le_abs_sub ((m : ℝ) * c) (x - n0 * c)
          have h5 : |(m : ℝ) * c - (x - n0 * c)| = |(x - n0 * c) - m * c| := abs_sub_comm _ _
          linarith
        have h5 : (|(m : ℝ) * c| / 2) ^ 2 ≤ |x - n * c| ^ 2 :=
          pow_le_pow_left₀ (by positivity) h3 2
        rw [sq_abs] at h5
        have : (|(m : ℝ) * c| / 2) ^ 2 = ((m : ℝ) * c) ^ 2 / 4 := by
          rw [div_pow, sq_abs]; ring
        linarith
      · rw [h]; simp; positivity
    have hm1 : |(m : ℝ)| ≤ (m : ℝ) ^ 2 := by
      rcases hmabs with h | h
      · nlinarith [sq_abs (m : ℝ)]
      · rw [h]; simp
    have : -(x - n * c) ^ 2 / β ≤ -κ * (m : ℝ) ^ 2 := by
      rw [hκ, div_le_iff₀ hβ]
      have : -(c ^ 2 / (4 * β) * (m : ℝ) ^ 2) * β = -((m * c) ^ 2 / 4) := by
        field_simp
      nlinarith [this]
    have h6 : -κ * (m : ℝ) ^ 2 ≤ -κ * |(m : ℝ)| := by nlinarith
    linarith
  have hsh : Summable (fun n : ℤ => D (n - n0)) :=
    (Equiv.subRight n0).summable_iff.mpr hDs
  have hs : Summable (fun n : ℤ => exp (-(x - n * c) ^ 2 / β)) :=
    Summable.of_nonneg_of_le (fun n => (exp_pos _).le) hle hsh
  refine ⟨hs, ?_⟩
  calc ∑' n : ℤ, exp (-(x - n * c) ^ 2 / β) ≤ ∑' n : ℤ, D (n - n0) :=
        hs.tsum_le_tsum hle hsh
    _ = ∑' m, D m := (Equiv.subRight n0).tsum_eq D

/-- `|y| e^{-y²/(16A)} ≤ 1 + 8A`. -/
theorem vs_lin (A y : ℝ) (hA : 0 < A) : |y| * exp (-y ^ 2 / (16 * A)) ≤ 1 + 8 * A := by
  set z : ℝ := |y| * exp (-y ^ 2 / (16 * A)) with hz
  have h1 : y ^ 2 / (8 * A) ≤ exp (y ^ 2 / (8 * A)) := by
    have := add_one_le_exp (y ^ 2 / (8 * A)); linarith
  have h2 : z ^ 2 = y ^ 2 * exp (-y ^ 2 / (8 * A)) := by
    rw [hz, mul_pow, sq_abs, ← exp_nat_mul]
    congr 2
    field_simp; ring
  have h3 : y ^ 2 * exp (-y ^ 2 / (8 * A)) ≤ 8 * A := by
    have e : exp (-y ^ 2 / (8 * A)) * exp (y ^ 2 / (8 * A)) = 1 := by
      rw [← exp_add]; simp [neg_div]
    have hp := exp_pos (-y ^ 2 / (8 * A))
    have : y ^ 2 ≤ 8 * A * exp (y ^ 2 / (8 * A)) := by
      rwa [div_le_iff₀ (by positivity), mul_comm] at h1
    calc y ^ 2 * exp (-y ^ 2 / (8 * A)) ≤ 8 * A * exp (y ^ 2 / (8 * A)) *
          exp (-y ^ 2 / (8 * A)) := by gcongr
      _ = 8 * A := by rw [mul_assoc, mul_comm (exp (y ^ 2 / (8 * A))), e]; ring
  nlinarith [sq_nonneg (z - 1), h2, h3]

/-- Pointwise bound of the isolated vortex. -/
theorem vs_iso (A ν s : ℝ) (hA : 0 < A) (hs : 0 ≤ ν * s) (hsA : ν * s + 1 ≤ A) (w : ℝ × ℝ)
    (k : Fin 2) :
    |Train.isoV ν s w k| ≤ (1 + 8 * A) * exp (-w.1 ^ 2 / (16 * A)) := by
  set a : ℝ := 1 + ν * s with ha
  have ha1 : 1 ≤ a := by linarith
  have haA : a ≤ A := by linarith
  have h := Train.isoV_apply ν s w
  have hw : Train.isoV ν s w k = (a⁻¹ ^ 2 * exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * a))) *
      (Train.toVec (-w.2, w.1)) k := by
    rw [h]; rfl
  have hg : 0 ≤ a⁻¹ ^ 2 * exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * a)) := by positivity
  have hinv : a⁻¹ ^ 2 ≤ 1 := by
    have : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha1
    have h0 : 0 ≤ a⁻¹ := by positivity
    nlinarith
  have hex : exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * a)) ≤
      exp (-w.1 ^ 2 / (4 * A)) * exp (-w.2 ^ 2 / (4 * A)) := by
    rw [← exp_add]; apply exp_le_exp.mpr
    have : -(w.1 ^ 2 + w.2 ^ 2) / (4 * a) ≤ -(w.1 ^ 2 + w.2 ^ 2) / (4 * A) := by
      have h7 : (w.1 ^ 2 + w.2 ^ 2) / (4 * A) ≤ (w.1 ^ 2 + w.2 ^ 2) / (4 * a) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      rw [neg_div, neg_div]; linarith
    have e : -(w.1 ^ 2 + w.2 ^ 2) / (4 * A) = -w.1 ^ 2 / (4 * A) + -w.2 ^ 2 / (4 * A) := by
      ring
    linarith
  have hq : ∀ y : ℝ, exp (-y ^ 2 / (4 * A)) ≤ exp (-y ^ 2 / (16 * A)) := by
    intro y; apply exp_le_exp.mpr
    have : y ^ 2 / (16 * A) ≤ y ^ 2 / (4 * A) :=
      div_le_div_of_nonneg_left (sq_nonneg y) (by positivity) (by linarith)
    rw [neg_div, neg_div]; linarith
  have hq0 : ∀ y : ℝ, exp (-y ^ 2 / (4 * A)) ≤ 1 := fun y => by
    rw [exp_le_one_iff]; have : 0 ≤ y ^ 2 / (4 * A) := by positivity
    rw [neg_div]; linarith
  have hq2 : exp (-w.1 ^ 2 / (4 * A)) ≤
      exp (-w.1 ^ 2 / (16 * A)) * exp (-w.1 ^ 2 / (16 * A)) := by
    rw [← exp_add]; apply exp_le_exp.mpr
    have e : -w.1 ^ 2 / (16 * A) + -w.1 ^ 2 / (16 * A) =
        -w.1 ^ 2 / (4 * A) + w.1 ^ 2 / (8 * A) := by field_simp; ring
    have : 0 ≤ w.1 ^ 2 / (8 * A) := by positivity
    linarith
  have hE : a⁻¹ ^ 2 * exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * a)) ≤
      exp (-w.1 ^ 2 / (4 * A)) * exp (-w.2 ^ 2 / (4 * A)) :=
    (mul_le_of_le_one_left (exp_pos _).le hinv).trans hex
  have hcomp : |(Train.toVec (-w.2, w.1)) k| *
      (a⁻¹ ^ 2 * exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * a))) ≤
      (1 + 8 * A) * exp (-w.1 ^ 2 / (16 * A)) := by
    fin_cases k
    · simp only [Fin.zero_eta, Train.toVec_zero, abs_neg]
      calc |w.2| * (a⁻¹ ^ 2 * exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * a)))
          ≤ |w.2| * (exp (-w.1 ^ 2 / (16 * A)) * exp (-w.2 ^ 2 / (16 * A))) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact hE.trans (mul_le_mul (hq _) (hq _) (exp_pos _).le (exp_pos _).le)
        _ = (|w.2| * exp (-w.2 ^ 2 / (16 * A))) * exp (-w.1 ^ 2 / (16 * A)) := by ring
        _ ≤ (1 + 8 * A) * exp (-w.1 ^ 2 / (16 * A)) :=
            mul_le_mul_of_nonneg_right (vs_lin A w.2 hA) (exp_pos _).le
    · simp only [Fin.mk_one, Train.toVec_one]
      calc |w.1| * (a⁻¹ ^ 2 * exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * a)))
          ≤ |w.1| * (exp (-w.1 ^ 2 / (16 * A)) * exp (-w.1 ^ 2 / (16 * A))) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            calc _ ≤ exp (-w.1 ^ 2 / (4 * A)) * exp (-w.2 ^ 2 / (4 * A)) := hE
              _ ≤ exp (-w.1 ^ 2 / (4 * A)) * 1 :=
                  mul_le_mul_of_nonneg_left (hq0 _) (exp_pos _).le
              _ ≤ _ := by rw [mul_one]; exact hq2
        _ = (|w.1| * exp (-w.1 ^ 2 / (16 * A))) * exp (-w.1 ^ 2 / (16 * A)) := by ring
        _ ≤ (1 + 8 * A) * exp (-w.1 ^ 2 / (16 * A)) :=
            mul_le_mul_of_nonneg_right (vs_lin A w.1 hA) (exp_pos _).le
  rw [hw, abs_mul, abs_of_nonneg hg]
  linarith [hcomp, mul_comm |(Train.toVec (-w.2, w.1)) k| (a⁻¹ ^ 2 * exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * a)))]

/-- **Uniform sup bound of the periodized vortex for every `c > 0`.** -/
theorem Vc_sup_all_c : ∀ Sg ν c : ℝ, 0 < Sg → 0 < ν → 0 < c → ∃ M : ℝ, ∀ s : ℝ, 0 ≤ s →
    s ≤ Sg / ν → ∀ x : UnforcedLeray.Cyl.Plane, ∀ k : Fin 2,
      |UnforcedLeray.Train.Vc ν c s x k| ≤ M := by
  intro Sg ν c hSg hν hc
  set A : ℝ := 1 + Sg with hA
  have hA0 : 0 < A := by positivity
  obtain ⟨S, hS⟩ := vs_lat_gauss (16 * A) c (by positivity) hc
  refine ⟨(1 + 8 * A) * S, fun s hs0 hs1 x k => ?_⟩
  have hνs : ν * s ≤ Sg := by
    have := (le_div_iff₀ hν).mp hs1; linarith
  have hsum := Train.summable_isoV (ν := ν) (c := c) (s := s) hν hc.ne' hs0 x
  have hv : Train.Vc ν c s x = ∑' n : ℤ, Train.isoV ν s (x.1 - n * c, x.2) := rfl
  have hk : Train.Vc ν c s x k = ∑' n : ℤ, Train.isoV ν s (x.1 - n * c, x.2) k := by
    rw [hv]
    exact ((EuclideanSpace.proj k : Train.Vec →L[ℝ] ℝ).map_tsum hsum)
  rw [hk]
  have hb : ∀ n : ℤ, ‖Train.isoV ν s (x.1 - n * c, x.2) k‖ ≤
      (1 + 8 * A) * exp (-(x.1 - n * c) ^ 2 / (16 * A)) := by
    intro n
    rw [Real.norm_eq_abs]
    exact vs_iso A ν s hA0 (by positivity) (by linarith) _ k
  obtain ⟨hs2, hs3⟩ := hS x.1
  have hsm : Summable (fun n : ℤ => (1 + 8 * A) * exp (-(x.1 - n * c) ^ 2 / (16 * A))) :=
    hs2.mul_left _
  calc |∑' n : ℤ, Train.isoV ν s (x.1 - n * c, x.2) k|
      = ‖∑' n : ℤ, Train.isoV ν s (x.1 - n * c, x.2) k‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℤ, (1 + 8 * A) * exp (-(x.1 - n * c) ^ 2 / (16 * A)) :=
        tsum_of_norm_bounded hsm.hasSum hb
    _ = (1 + 8 * A) * ∑' n : ℤ, exp (-(x.1 - n * c) ^ 2 / (16 * A)) := tsum_mul_left
    _ ≤ (1 + 8 * A) * S := by gcongr

end UnforcedLeray.Short.IIb
