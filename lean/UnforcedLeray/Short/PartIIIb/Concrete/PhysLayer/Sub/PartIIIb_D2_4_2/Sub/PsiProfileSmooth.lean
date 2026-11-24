import Mathlib.Analysis.Calculus.ContDiff.Operations
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PartIIIb_IIIb_D2_4_2_1

/-!
# (L2) The profile `Ψ` is `C²` jointly on `s > 0` (task `PartIII-b:IIIb-D2/4/2/1/2`)

Source of record: `the November 2 reference manuscript` lines 4963-4991.
The profile is `psiPhi ν s (Ay ν χ A s) y = (-2 a⁻¹) e^{-|y|²/(4a)} (tr M - c₁(y, M y))`, with
`a = 1 + ν s`, `M = χ(ν s) A(s)`.  On `s > 0` we have `a > 0`, so every factor is `C²`:
`A` is `C⁶` on `(0,∞)` (`IsAffElem.smooth`), `χ` is `C^∞` (`IsSourceCutoffC`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psiProfileSmooth_proof (as : ℝ) (χf : ℝ → ℝ) : PsiProfileSmooth as χf := by
  unfold PsiProfileSmooth
  intro hχ ν hν A hA
  have hpos : ∀ p ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))), 0 < ageA ν p.1 := by
    intro p hp
    have h : (0 : ℝ) < p.1 := hp.1
    unfold ageA
    positivity
  have ha : ContDiffOn ℝ 2 (fun p : Chart => ageA ν p.1) (Ioi (0 : ℝ) ×ˢ univ) := by
    unfold ageA
    exact (contDiff_const.add (contDiff_const.mul contDiff_fst)).contDiffOn
  have hainv : ContDiffOn ℝ 2 (fun p : Chart => (ageA ν p.1)⁻¹) (Ioi (0 : ℝ) ×ˢ univ) :=
    ha.inv (fun p hp => (hpos p hp).ne')
  have hden : ContDiffOn ℝ 2 (fun p : Chart => 4 * ageA ν p.1) (Ioi (0 : ℝ) ×ˢ univ) :=
    contDiffOn_const.mul ha
  have hden0 : ∀ p ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))), 4 * ageA ν p.1 ≠ 0 :=
    fun p hp => by have := hpos p hp; positivity
  have hq : ContDiffOn ℝ 2 (fun p : Chart => -(sq2 p.2)) (Ioi (0 : ℝ) ×ˢ univ) := by
    unfold sq2
    fun_prop
  have hexp : ContDiffOn ℝ 2
      (fun p : Chart => Real.exp (-(sq2 p.2) / (4 * ageA ν p.1))) (Ioi (0 : ℝ) ×ˢ univ) :=
    (hq.div hden hden0).exp
  have hchi : ContDiffOn ℝ 2 (fun p : Chart => χf (ν * p.1)) (Ioi (0 : ℝ) ×ˢ univ) :=
    (hχ.smooth.comp (contDiff_const.mul contDiff_fst)).contDiffOn.of_le
      (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hA2 : ∀ i j : Fin 3, ContDiffOn ℝ 2 (fun s : ℝ => A s i j) (Ioi (0 : ℝ)) :=
    fun i j => ((contDiffOn_pi.1 (contDiffOn_pi.1 hA.smooth i)) j).of_le
      (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 6))
  have hAp : ∀ i j : Fin 3, ContDiffOn ℝ 2 (fun p : Chart => A p.1 i j)
      (Ioi (0 : ℝ) ×ˢ univ) :=
    fun i j => (hA2 i j).comp contDiff_fst.contDiffOn (fun p hp => hp.1)
  have hM : ∀ i j : Fin 3, ContDiffOn ℝ 2 (fun p : Chart => Ay ν χf A p.1 i j)
      (Ioi (0 : ℝ) ×ˢ univ) := by
    intro i j
    have heq : (fun p : Chart => Ay ν χf A p.1 i j) =
        fun p => χf (ν * p.1) * A p.1 i j := by
      funext p
      simp [Ay]
    rw [heq]
    exact hchi.mul (hAp i j)
  have hnum : ContDiffOn ℝ 2 (fun p : Chart =>
      -(2 * p.2.1 * (Ay ν χf A p.1 0 0 * p.2.1 + Ay ν χf A p.1 0 2 * p.2.2) +
        2 * p.2.2 * (Ay ν χf A p.1 2 0 * p.2.1 + Ay ν χf A p.1 2 2 * p.2.2)))
      (Ioi (0 : ℝ) ×ˢ univ) := by
    have h00 := hM 0 0
    have h02 := hM 0 2
    have h20 := hM 2 0
    have h22 := hM 2 2
    fun_prop
  have hT : ContDiffOn ℝ 2 (fun p : Chart =>
      (-2 * (ageA ν p.1)⁻¹) * Real.exp (-(sq2 p.2) / (4 * ageA ν p.1)) *
        ((Ay ν χf A p.1 0 0 + Ay ν χf A p.1 2 2) -
          (-(2 * p.2.1 * (Ay ν χf A p.1 0 0 * p.2.1 + Ay ν χf A p.1 0 2 * p.2.2) +
            2 * p.2.2 * (Ay ν χf A p.1 2 0 * p.2.1 + Ay ν χf A p.1 2 2 * p.2.2))) /
            (4 * ageA ν p.1)))
      (Ioi (0 : ℝ) ×ˢ univ) :=
    (((contDiffOn_const (c := (-2 : ℝ))).mul hainv).mul hexp).mul
      (((hM 0 0).add (hM 2 2)).sub (hnum.div hden hden0))
  refine hT.congr (fun p _ => ?_)
  simp only [psiProfile, psiPhi, merTrace, merApply, sq2]

end UnforcedLeray.Short.PartIIIb.Concrete
