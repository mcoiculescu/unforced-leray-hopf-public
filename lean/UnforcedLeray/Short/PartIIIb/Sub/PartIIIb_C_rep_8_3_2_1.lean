import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.Defs

/-!
# `PartIII-b:C/rep/8/3/2/1`: decomposition of `GaussSumEA` (source 4963-4985, 4978)

`gaussSumEA_of` proves `GaussSumEA` from four true lemmas on the lattice sums of the Gaussian
profiles `V_j`, `p_j` (Gaussian decay in `j`, source 4978: "sums and derivatives converge by
Gaussian decay"):

* `GaussSumSmooth`: `ContDiff ℝ 2 (gaussV ν s)` and `Differentiable ℝ (gaussP ν s)`;
* `GaussSumV`: `Σ_j V_j(x)` converges (summable);
* `GaussSumHess`: the second derivative of `gaussV` is the termwise sum (summable terms);
* `GaussSumGrad`: the gradient of `gaussP` is the termwise sum (summable terms).

Source of record `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Smoothness of the lattice sums (source 4963-4978). -/
def GaussSumSmooth : Prop :=
  ∀ ν s : ℝ, 0 < ν → 0 < s → ContDiff ℝ 2 (gaussV ν s) ∧ Differentiable ℝ (gaussP ν s)

/-- Convergence of `Σ_j V_j(x)` (source 4978). -/
def GaussSumV : Prop :=
  ∀ ν s : ℝ, 0 < ν → 0 < s → ∀ x : ℝ × ℝ, Summable (fun j : ℤ => Vj ν s j x)

/-- Termwise Hessian contraction of the summed velocity (source 4978). -/
def GaussSumHess : Prop :=
  ∀ ν s : ℝ, 0 < ν → 0 < s → ∀ (A : Mat3) (x : ℝ × ℝ),
    Summable (fun j : ℤ => hessContr A (Vj ν s j) x) ∧
      hessContr A (gaussV ν s) x = ∑' j : ℤ, hessContr A (Vj ν s j) x

/-- Termwise gradient of the summed pressure (source 4978). -/
def GaussSumGrad : Prop :=
  ∀ ν s : ℝ, 0 < ν → 0 < s → ∀ x : ℝ × ℝ,
    Summable (fun j : ℤ => mgrad (pj ν s j) x) ∧
      mgrad (gaussP ν s) x = ∑' j : ℤ, mgrad (pj ν s j) x

namespace SplitEmb8321

/-- `emb` as a continuous linear map. -/
def embL : ℝ × ℝ →L[ℝ] Vec3 :=
  (LinearMap.toContinuousLinearMap
    { toFun := fun v => emb v
      map_add' := fun a b => by funext i; fin_cases i <;> simp [emb]
      map_smul' := fun c a => by funext i; fin_cases i <;> simp [emb] })

end SplitEmb8321

theorem embL_apply (v : ℝ × ℝ) : SplitEmb8321.embL v = emb v := rfl

/-- `mv B` as a continuous linear map. -/
def mvL (B : Mat3) : Vec3 →L[ℝ] Vec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => mv B v
      map_add' := fun a b => by funext i; simp [mv, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        funext i; simp [mv, Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring) }

theorem mvL_apply (B : Mat3) (v : Vec3) : mvL B v = mv B v := rfl

theorem gaussSumEA_of (h1 : GaussSumSmooth) (h2 : GaussSumV) (h3 : GaussSumHess)
    (h4 : GaussSumGrad) : GaussSumEA := by
  intro ν s hν hs
  obtain ⟨hV, hP⟩ := h1 ν s hν hs
  refine ⟨hV, hP, fun μ χf A x => ?_⟩
  set B := Bmat ν μ χf A s
  set Ay' := Ay ν χf A s
  set C : Mat3 := fun a b => Ay' a b + Ay' b a
  have hsV := h2 ν s hν hs x
  obtain ⟨hsH, hH⟩ := h3 ν s hν hs Ay' x
  obtain ⟨hsG, hG⟩ := h4 ν s hν hs x
  have e1 : mv B (emb (gaussV ν s x)) = ∑' j : ℤ, mv B (emb (Vj ν s j x)) := by
    have : gaussV ν s x = ∑' j : ℤ, Vj ν s j x := rfl
    rw [this]
    have := ((mvL B).comp SplitEmb8321.embL).map_tsum hsV
    simpa [mvL_apply, embL_apply] using this
  have s1 : Summable (fun j : ℤ => mv B (emb (Vj ν s j x))) := by
    have := ((mvL B).comp SplitEmb8321.embL).summable hsV
    simpa [mvL_apply, embL_apply] using this
  have e3 : mv C (emb (mgrad (gaussP ν s) x)) = ∑' j : ℤ, mv C (emb (mgrad (pj ν s j) x)) := by
    rw [hG]
    have := ((mvL C).comp SplitEmb8321.embL).map_tsum hsG
    simpa [mvL_apply, embL_apply] using this
  have s3 : Summable (fun j : ℤ => mv C (emb (mgrad (pj ν s j) x))) := by
    have := ((mvL C).comp SplitEmb8321.embL).summable hsG
    simpa [mvL_apply, embL_apply] using this
  have s1' := s1.const_smul (2 : ℝ)
  have s2' := hsH.const_smul (2 * ν)
  show (∑' j : ℤ, ((2 : ℝ) • mv B (emb (Vj ν s j x))
      + (2 * ν) • hessContr Ay' (Vj ν s j) x - mv C (emb (mgrad (pj ν s j) x)))) =
    (2 : ℝ) • mv B (emb (gaussV ν s x)) + (2 * ν) • hessContr Ay' (gaussV ν s) x -
      mv C (emb (mgrad (gaussP ν s) x))
  rw [e1, hH, e3, Summable.tsum_sub (s1'.add s2') s3, Summable.tsum_add s1' s2',
    tsum_const_smul'' , tsum_const_smul'']
