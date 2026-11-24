import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_1_1
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# `weightedTrainFluctAgeJetFixed` from the unweighted decay and a doubled-weight polynomial datum

Source `the November 2 reference manuscript`
516-526: "Interpolate a doubled polynomial weight with the unweighted exponential fluctuation
bounds in (sct:overlap); the resulting polynomial in `1+T` is absorbed in a smaller exponential."
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartI
open UnforcedLeray.Cyl (Plane)

/-- **Source leaf: doubled-weight polynomial datum of the stream fluctuation** (SP 439-445, proof
SP 516-526: "polynomial weighted bounds for all fields at every age", the weight `<eta>^{2m}` costs a
polynomial in `1+s`, from the Gaussian vorticity tails SP 494-499 and the mean tails SP 500-510):
for `rho > 1/2` one `nu0`, and for every BUC train with `nu <= nu0` and all `m, l, j` there are `C`,
`p` with `(1+|eta|)^(2m) ||partial_s^l D^j (psi - S)(s, z)|| <= C (1+s)^p` for all `s > 0`. -/
def FluctDoubledWeightPoly : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ m ℓ j : ℕ, ∃ C : ℝ, ∃ p : ℕ,
      ∀ s : ℝ, 0 < s → ∀ z : Plane,
        (1 + |z.2|) ^ (2 * m) *
            ‖ageJet ℓ j (fun r w => tr.ψ r w - hmean (trainPeriod ρ ν) (tr.ψ r) w.2) s z‖ ≤
          C * (1 + s) ^ p

private lemma poly_absorb (p : ℕ) (a : ℝ) (ha : 0 < a) (s : ℝ) (hs : 0 ≤ s) :
    (1 + s) ^ p ≤ (p.factorial : ℝ) * (a ^ p)⁻¹ * Real.exp a * Real.exp (a * s) := by
  have h := Real.pow_div_factorial_le_exp (a * (1 + s)) (by positivity) p
  have hf : (0 : ℝ) < p.factorial := by exact_mod_cast p.factorial_pos
  have hap : 0 < a ^ p := pow_pos ha p
  rw [div_le_iff₀ hf, mul_pow] at h
  have : Real.exp (a * (1 + s)) = Real.exp a * Real.exp (a * s) := by
    rw [mul_add, mul_one, Real.exp_add]
  rw [this] at h
  calc (1 + s) ^ p = (a ^ p)⁻¹ * (a ^ p * (1 + s) ^ p) := by field_simp
    _ ≤ (a ^ p)⁻¹ * (Real.exp a * Real.exp (a * s) * p.factorial) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.2 hap.le)
    _ = _ := by ring

theorem weightedTrainFluctAgeJetFixed_of (hA : TrainFluctAgeJetFixed)
    (hD : FluctDoubledWeightPoly) : WeightedTrainFluctAgeJetFixed := by
  intro ρ hρ
  obtain ⟨νA, hνA, hA'⟩ := hA ρ hρ
  obtain ⟨νD, hνD, hD'⟩ := hD ρ hρ
  refine ⟨min νA νD, lt_min hνA hνD, fun ν hν hle tr htr m ℓ j => ?_⟩
  obtain ⟨A, κ, hκ, hAb⟩ := hA' ν hν (hle.trans (min_le_left _ _)) tr htr ℓ j
  obtain ⟨B, p, hBb⟩ := hD' ν hν (hle.trans (min_le_right _ _)) tr htr m ℓ j
  set a := κ / 2 with ha
  have ha0 : 0 < a := by positivity
  set K : ℝ := (p.factorial : ℝ) * (a ^ p)⁻¹ * Real.exp a with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨Real.sqrt (|A| * |B| * K), κ / 4, by positivity, fun s hs z => ?_⟩
  set f := ‖ageJet ℓ j (fun r w => tr.ψ r w - hmean (trainPeriod ρ ν) (tr.ψ r) w.2) s z‖ with hf
  have hf0 : 0 ≤ f := norm_nonneg _
  set w := (1 + |z.2|) ^ m with hw
  have hw0 : 0 ≤ w := by positivity
  have h1 : f ≤ |A| * Real.exp (-(κ * s)) :=
    (hAb s hs z).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
  have h2 : w ^ 2 * f ≤ |B| * (1 + s) ^ p := by
    have := hBb s hs z
    have e : (1 + |z.2|) ^ (2 * m) = w ^ 2 := by rw [hw, ← pow_mul]; ring_nf
    rw [e] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have h3 : (1 + s) ^ p ≤ K * Real.exp (a * s) := by
    have := poly_absorb p a ha0 s hs.le
    simpa [hK, mul_assoc] using this
  have hsq : (w * f) ^ 2 ≤ |A| * |B| * K * Real.exp (-(κ * s / 2)) := by
    have e1 : (w * f) ^ 2 = (w ^ 2 * f) * f := by ring
    rw [e1]
    have h4 : (w ^ 2 * f) * f ≤ (|B| * (1 + s) ^ p) * (|A| * Real.exp (-(κ * s))) :=
      mul_le_mul h2 h1 hf0 (by positivity)
    have h5 : (|B| * (1 + s) ^ p) * (|A| * Real.exp (-(κ * s))) ≤
        (|B| * (K * Real.exp (a * s))) * (|A| * Real.exp (-(κ * s))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (abs_nonneg _)) (by positivity)
    have h6 : Real.exp (a * s) * Real.exp (-(κ * s)) = Real.exp (-(κ * s / 2)) := by
      rw [← Real.exp_add]; congr 1; rw [ha]; ring
    calc _ ≤ _ := h4.trans h5
      _ = |A| * |B| * K * (Real.exp (a * s) * Real.exp (-(κ * s))) := by ring
      _ = _ := by rw [h6]
  have e : (Real.sqrt (|A| * |B| * K) * Real.exp (-(κ / 4 * s))) ^ 2 =
      |A| * |B| * K * Real.exp (-(κ * s / 2)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  have hsq' : (w * f) ^ 2 ≤ (Real.sqrt (|A| * |B| * K) * Real.exp (-(κ / 4 * s))) ^ 2 := by
    rw [e]; exact hsq
  exact (abs_le_of_sq_le_sq' hsq' (by positivity)).2

end UnforcedLeray.Short.PartIIIb.Concrete
