import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.Cont.Age

/-!
# `PartIII-a:T21/2/2/3/2/1`: `MvPhiDiff` (leaf A of `movAdjEquation_of`)

Pointwise differentiability in the reverse moving time of `ζ ↦ mvPhi ν φ s ζ y = a⁻¹ φ(r, √a y)`,
`r = revAge ν s ζ`, `a = clockA ν r`, by the chain rule through the jointly smooth `φ`
(`IsAdjointFlow.jointSmooth`) at the interior age `r ∈ (t, s)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem movingZ_mul_lt_one_A {ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) :
    ν * movingZ ν s < 1 := by
  have hA : 0 < 1 + ν * s := by nlinarith [mul_nonneg hν.le hs]
  have e : ν * movingZ ν s = ν * s / (1 + ν * s) := by
    unfold movingZ clockA
    rw [mul_div_assoc]
  rw [e, div_lt_one hA]
  linarith

theorem revAge_mem_Ioo_A {ν t s ζ : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hts : t < s)
    (hζ : ζ ∈ Ioo 0 (deltaZ ν t s)) : revAge ν s ζ ∈ Ioo t s := by
  obtain ⟨hζ0, hζΔ⟩ := hζ
  have hs : 0 ≤ s := ht.trans hts.le
  have hAt : 0 < 1 + ν * t := by nlinarith [mul_nonneg hν.le ht]
  have hAs : 0 < 1 + ν * s := by nlinarith [mul_nonneg hν.le hs]
  have hzs : ν * movingZ ν s < 1 := movingZ_mul_lt_one_A hν hs
  have hΔ : ζ < movingZ ν s - movingZ ν t := hζΔ
  have hz1 : movingZ ν t < movingZ ν s - ζ := by linarith
  have hz2 : movingZ ν s - ζ < movingZ ν s := by linarith
  have hνz : ν * (movingZ ν s - ζ) < 1 := by nlinarith [mul_pos hν hζ0]
  have hlow : ageOfZ ν (movingZ ν t) < ageOfZ ν (movingZ ν s - ζ) :=
    IIIa.ageOfZ_strictMono_of ν _ _ hν hz1 hνz
  have hup : ageOfZ ν (movingZ ν s - ζ) < ageOfZ ν (movingZ ν s) :=
    IIIa.ageOfZ_strictMono_of ν _ _ hν hz2 hzs
  have htm : ageOfZ ν (movingZ ν t) = t := IIIa.ageOfZ_movingZ ν t hAt
  have hsm : ageOfZ ν (movingZ ν s) = s := IIIa.ageOfZ_movingZ ν s hAs
  rw [htm] at hlow
  rw [hsm] at hup
  exact ⟨hlow, hup⟩

theorem revAge_denom_pos_A {ν s ζ : ℝ} (hν : 0 < ν) (hζ0 : 0 < ζ) (hzs : ν * movingZ ν s < 1) :
    0 < 1 - ν * (movingZ ν s - ζ) := by
  nlinarith [mul_pos hν hζ0]

theorem differentiableAt_revAge_A (ν s ζ : ℝ) (hd : 0 < 1 - ν * (movingZ ν s - ζ)) :
    DifferentiableAt ℝ (fun ζ' => revAge ν s ζ') ζ := by
  have hc : DifferentiableAt ℝ (fun ζ' : ℝ => movingZ ν s - ζ') ζ := by
    fun_prop
  have hd' : DifferentiableAt ℝ (fun ζ' : ℝ => 1 - ν * (movingZ ν s - ζ')) ζ :=
    (hc.const_mul ν).const_sub 1
  have e : (fun ζ' => revAge ν s ζ') =
      fun ζ' => (movingZ ν s - ζ') / (1 - ν * (movingZ ν s - ζ')) := rfl
  rw [e]
  exact hc.div hd' hd.ne'

theorem joint_contDiffAt_A {t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hJ : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    {r : ℝ} (hr : r ∈ Ioo t s) (x : ℝ × ℝ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (r, x) := by
  have hmem : (r, x) ∈ Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hr, mem_univ x⟩
  have hopen : Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 (r, x) :=
    IsOpen.mem_nhds (isOpen_Ioo.prod isOpen_univ) hmem
  exact hJ.contDiffAt (Filter.mem_of_superset hopen (Set.prod_mono Set.Ioo_subset_Ico_self
    (Set.Subset.refl _)))

theorem mvPhiDiff (m : ℝ) : UnforcedLeray.Short.IIIa.AdjE1.MvPhiDiff m := by
  intro ν tr t s φ ζ hflow y
  obtain ⟨hν, ht0, hts, ⟨G, _, hF⟩, hζ⟩ := hflow
  have hr : revAge ν s ζ ∈ Ioo t s := revAge_mem_Ioo_A hν ht0 hts hζ
  have hζ0 : 0 < ζ := hζ.1
  have hzs : ν * movingZ ν s < 1 := movingZ_mul_lt_one_A hν (ht0.trans hts.le)
  have hd : 0 < 1 - ν * (movingZ ν s - ζ) := revAge_denom_pos_A hν hζ0 hzs
  have hR : DifferentiableAt ℝ (fun ζ' => revAge ν s ζ') ζ :=
    differentiableAt_revAge_A ν s ζ hd
  have hA : DifferentiableAt ℝ (fun ζ' => clockA ν (revAge ν s ζ')) ζ :=
    (hR.const_mul ν).const_add 1
  have hApos : 0 < clockA ν (revAge ν s ζ) := by
    have h0 : 0 ≤ ν * revAge ν s ζ := mul_nonneg hν.le (by linarith [hr.1, ht0])
    unfold clockA
    linarith
  have hsq : DifferentiableAt ℝ (fun ζ' => Real.sqrt (clockA ν (revAge ν s ζ'))) ζ :=
    hA.sqrt hApos.ne'
  have hQ : DifferentiableAt ℝ (fun ζ' => (revAge ν s ζ',
      (Real.sqrt (clockA ν (revAge ν s ζ')) * y.1, Real.sqrt (clockA ν (revAge ν s ζ')) * y.2)))
      ζ :=
    hR.prodMk ((hsq.mul_const y.1).prodMk (hsq.mul_const y.2))
  have hP : DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2)
      (revAge ν s ζ, (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
        Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) :=
    (joint_contDiffAt_A hF.jointSmooth hr _).differentiableAt (by simp)
  have hcomp := hP.comp ζ hQ
  have hinv : DifferentiableAt ℝ (fun ζ' => (clockA ν (revAge ν s ζ'))⁻¹) ζ :=
    hA.inv hApos.ne'
  have hinvC : DifferentiableAt ℝ (fun ζ' => (((clockA ν (revAge ν s ζ'))⁻¹ : ℝ) : ℂ)) ζ :=
    Complex.ofRealCLM.differentiableAt.comp ζ hinv
  exact hinvC.mul hcomp

end UnforcedLeray.Short.IIIa.AdjE1
