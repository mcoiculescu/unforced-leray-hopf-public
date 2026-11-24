import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RADefs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EATermSummable.Mgrad

/-!
# `RALinear` helper: additivity of the global pressure `Ψ_A` in `A` (source 4974-4975, 5024)

`PsiA ν χ A s x = Σ_j (merApply (Ay A s) (x_j)) · ∇p_j(x)`.  The lattice terms are summable by the
Gaussian bound `mgradPjBound` and `gp_gauss_pow_summable`, so `tsum` is additive and homogeneous.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `(1+u)^4 ≤ 16(1+u^4)` for `u ≥ 0`. -/
lemma ra_one_add_pow4_le {u : ℝ} (hu : 0 ≤ u) : (1 + u) ^ 4 ≤ 16 * (1 + u ^ 4) := by
  rcases le_total u 1 with h | h
  · have h1 : (1 + u) ^ 4 ≤ (2:ℝ) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
    have h2 : (0:ℝ) ≤ u ^ 4 := by positivity
    norm_num at h1
    linarith
  · have h1 : (1 + u) ^ 4 ≤ (2 * u) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
    have h2 : (2 * u) ^ 4 = 16 * u ^ 4 := by ring
    have h3 : (0:ℝ) ≤ u ^ 4 := by positivity
    linarith

/-- The polynomial-weighted shifted Gaussian (weight `(1+|t - jc|)^4`) is summable over `j ∈ ℤ`. -/
lemma ra_poly4_summable (t α c : ℝ) (hα : 0 < α) (hc : 0 < c) :
    Summable (fun j : ℤ => (1 + |t - (j : ℝ) * c|) ^ 4 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by
  have hg := gp_gauss_summable t α c hα hc
  have hg4 := gp_gauss_pow_summable t α c hα hc 4
  set L : ℝ := |t| + c with hL
  have hL0 : 0 ≤ L := by positivity
  have hbound : ∀ j : ℤ, (1 + |t - (j : ℝ) * c|) ^ 4 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)
      ≤ (1 + L) ^ 4 * (16 * (Real.exp (-α * (t - (j : ℝ) * c) ^ 2) +
          |(j : ℝ)| ^ 4 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2))) := by
    intro j
    have hj : 0 ≤ |(j : ℝ)| := abs_nonneg _
    have hA : 1 + |t - (j : ℝ) * c| ≤ (1 + L) * (1 + |(j : ℝ)|) := by
      have h1 : |t - (j : ℝ) * c| ≤ |t| + c * |(j : ℝ)| := by
        calc |t - (j : ℝ) * c| ≤ |t| + |(j : ℝ) * c| := abs_sub _ _
          _ = |t| + c * |(j : ℝ)| := by rw [abs_mul, abs_of_pos hc]; ring
      nlinarith [mul_nonneg hL0 hj, abs_nonneg t, mul_nonneg hc.le hj]
    have hp : (1 + |t - (j : ℝ) * c|) ^ 4 ≤ (1 + L) ^ 4 * (1 + |(j : ℝ)|) ^ 4 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hA 4
    have hq := ra_one_add_pow4_le hj
    have he : 0 ≤ Real.exp (-α * (t - (j : ℝ) * c) ^ 2) := (Real.exp_pos _).le
    calc (1 + |t - (j : ℝ) * c|) ^ 4 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)
        ≤ ((1 + L) ^ 4 * (1 + |(j : ℝ)|) ^ 4) * Real.exp (-α * (t - (j : ℝ) * c) ^ 2) :=
          mul_le_mul_of_nonneg_right hp he
      _ ≤ ((1 + L) ^ 4 * (16 * (1 + |(j : ℝ)| ^ 4))) * Real.exp (-α * (t - (j : ℝ) * c) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ he
          exact mul_le_mul_of_nonneg_left hq (by positivity)
      _ = (1 + L) ^ 4 * (16 * (Real.exp (-α * (t - (j : ℝ) * c) ^ 2) +
          |(j : ℝ)| ^ 4 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2))) := by ring
  refine Summable.of_nonneg_of_le (fun j => by positivity) hbound ?_
  exact ((hg.add hg4).mul_left 16).mul_left ((1 + L) ^ 4)

/-- `Ay` is additive in `A`. -/
theorem ra_Ay_add (ν : ℝ) (χ : ℝ → ℝ) (A A' : ℝ → Mat3) (s : ℝ) :
    Ay ν χ (A + A') s = Ay ν χ A s + Ay ν χ A' s := by
  unfold Ay
  simp only [Pi.add_apply, smul_add]

/-- `Ay` is homogeneous in `A`. -/
theorem ra_Ay_smul (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (r s : ℝ) :
    Ay ν χ (r • A) s = r • Ay ν χ A s := by
  unfold Ay
  simp only [Pi.smul_apply]
  exact smul_comm _ _ _

/-- `merApply` is additive in the matrix. -/
theorem ra_merApply_add (M N : Mat3) (w : ℝ × ℝ) :
    merApply (M + N) w = merApply M w + merApply N w := by
  unfold merApply
  ext <;> simp <;> ring

/-- `merApply` is homogeneous in the matrix. -/
theorem ra_merApply_smul (r : ℝ) (M : Mat3) (w : ℝ × ℝ) :
    merApply (r • M) w = r • merApply M w := by
  unfold merApply
  ext <;> simp <;> ring

/-- The `j`-th lattice term of `Ψ_A` (source 5024): `(A^y_mer x_j)·∇p_j(x)`. -/
def psiATerm' (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) (j : ℤ) : ℝ :=
  (merApply (Ay ν χ A s) (xj ν j x)).1 * (mgrad (pj ν s j) x).1 +
    (merApply (Ay ν χ A s) (xj ν j x)).2 * (mgrad (pj ν s j) x).2

/-- `PsiA` is the `tsum` of the lattice terms (definitional). -/
theorem psiA_eq_tsum' (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    PsiA ν χ A s x = ∑' j : ℤ, psiATerm' ν χ A s x j := rfl

/-- The lattice terms of `Ψ_A` are summable for `ν, s > 0`. -/
theorem psiATerm'_summable (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ)
    (hν : 0 < ν) (hs : 0 < s) : Summable (psiATerm' ν χ A s x) := by
  have ha : 0 < ageA ν s := by
    unfold ageA
    nlinarith [mul_pos hν hs]
  have hc : 0 < cOf ν := by
    unfold cOf
    exact inv_pos.mpr (pow_pos hν 2)
  have hα : 0 < 1 / (4 * ageA ν s) := div_pos one_pos (by linarith)
  obtain ⟨K, hK⟩ := mgradPjBound ν s ha x
  have hS := ra_poly4_summable x.1 (1 / (4 * ageA ν s)) (cOf ν) hα hc
  have hS' := hS.mul_left (2 * (|Ay ν χ A s 0 0| + |Ay ν χ A s 0 2| + |Ay ν χ A s 2 0| +
    |Ay ν χ A s 2 2|) * (1 + |x.2|) * |K|)
  refine Summable.of_norm_bounded hS' (fun j => ?_)
  set M := Ay ν χ A s with hM
  set KM := |M 0 0| + |M 0 2| + |M 2 0| + |M 2 2| with hKM
  set t := x.1 - (j : ℝ) * cOf ν with ht
  set e := Real.exp (-(1 / (4 * ageA ν s)) * t ^ 2) with he
  set u := merApply M (xj ν j x) with hu
  set v := mgrad (pj ν s j) x with hv
  have hu1 : |u.1| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le u
  have hu2 : |u.2| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le u
  have hv1 : |v.1| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le v
  have hv2 : |v.2| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le v
  have hterm : |psiATerm' ν χ A s x j| ≤ 2 * ‖u‖ * ‖v‖ := by
    unfold psiATerm'
    calc |u.1 * v.1 + u.2 * v.2| ≤ |u.1 * v.1| + |u.2 * v.2| := abs_add_le _ _
      _ = |u.1| * |v.1| + |u.2| * |v.2| := by rw [abs_mul, abs_mul]
      _ ≤ ‖u‖ * ‖v‖ + ‖u‖ * ‖v‖ :=
          add_le_add (mul_le_mul hu1 hv1 (abs_nonneg _) (norm_nonneg _))
            (mul_le_mul hu2 hv2 (abs_nonneg _) (norm_nonneg _))
      _ = 2 * ‖u‖ * ‖v‖ := by ring
  have hxj : ‖xj ν j x‖ ≤ (1 + |x.2|) * (1 + |t|) := by
    have := gp_one_add_norm ν j x
    linarith
  have hun : ‖u‖ ≤ KM * ‖xj ν j x‖ := gp_merApply_norm_le M (xj ν j x)
  have hmg : ‖v‖ ≤ |K| * ((1 + |t|) ^ 3 * e) := by
    refine le_trans (hK j) ?_
    apply mul_le_mul_of_nonneg_right (le_abs_self K)
    positivity
  have hKM0 : 0 ≤ KM := by positivity
  have hxn : 0 ≤ ‖xj ν j x‖ := norm_nonneg _
  have hun0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hfin : 2 * ‖u‖ * ‖v‖ ≤ (2 * KM * (1 + |x.2|) * |K|) * ((1 + |t|) ^ 4 * e) := by
    have h1 : 2 * ‖u‖ * ‖v‖ ≤ 2 * (KM * ‖xj ν j x‖) * (|K| * ((1 + |t|) ^ 3 * e)) := by
      apply mul_le_mul (by linarith [hun]) hmg (norm_nonneg _) (by positivity)
    have h2 : 2 * (KM * ‖xj ν j x‖) * (|K| * ((1 + |t|) ^ 3 * e)) ≤
        2 * (KM * ((1 + |x.2|) * (1 + |t|))) * (|K| * ((1 + |t|) ^ 3 * e)) := by
      have h2' : KM * ‖xj ν j x‖ ≤ KM * ((1 + |x.2|) * (1 + |t|)) :=
        mul_le_mul_of_nonneg_left hxj hKM0
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2' (by norm_num)) (by positivity)
    have h3 : 2 * (KM * ((1 + |x.2|) * (1 + |t|))) * (|K| * ((1 + |t|) ^ 3 * e)) =
        (2 * KM * (1 + |x.2|) * |K|) * ((1 + |t|) ^ 4 * e) := by ring
    linarith
  rw [Real.norm_eq_abs]
  exact le_trans hterm hfin

/-- `Ψ_A` is additive in `A` at `s > 0` (source 4985, 5024). -/
theorem psiA_add_pt (ν : ℝ) (χ : ℝ → ℝ) (A A' : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ)
    (hν : 0 < ν) (hs : 0 < s) :
    PsiA ν χ (A + A') s x = PsiA ν χ A s x + PsiA ν χ A' s x := by
  have hT : ∀ j : ℤ, psiATerm' ν χ (A + A') s x j = psiATerm' ν χ A s x j + psiATerm' ν χ A' s x j := by
    intro j
    unfold psiATerm'
    rw [ra_Ay_add, ra_merApply_add]
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  rw [psiA_eq_tsum', psiA_eq_tsum', psiA_eq_tsum']
  simp only [hT]
  exact (psiATerm'_summable ν χ A s x hν hs).tsum_add (psiATerm'_summable ν χ A' s x hν hs)

/-- `Ψ_A` is homogeneous in `A` at every `s` (source 4985, 5024). -/
theorem psiA_smul_pt (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (r s : ℝ) (x : ℝ × ℝ) :
    PsiA ν χ (r • A) s x = r * PsiA ν χ A s x := by
  have hT : ∀ j : ℤ, psiATerm' ν χ (r • A) s x j = r * psiATerm' ν χ A s x j := by
    intro j
    unfold psiATerm'
    rw [ra_Ay_smul, ra_merApply_smul]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [psiA_eq_tsum', psiA_eq_tsum']
  simp only [hT]
  exact tsum_mul_left

end UnforcedLeray.Short.PartIIIb.Concrete
