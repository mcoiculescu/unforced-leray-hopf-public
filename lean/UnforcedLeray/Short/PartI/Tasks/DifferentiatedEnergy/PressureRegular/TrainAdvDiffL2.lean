import UnforcedLeray.Short.PartI.Sub.T08_3
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrBasic
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainAdvDiffL2.Leibniz

/-!
# Part I, task `PartI:T08/3/4` (`trainAdvDiffL2_proof`): the transport bracket

Source: `the November 2 reference manuscript` lines 326-329, 341.
Componentwise `A_k = ∑_j (V_j ∂_j e_k + e_j ∂_j V_k + e_j ∂_j e_k)` (`e = v - V_c^p`), each term a
product of a bounded-words factor (`V_j`, `∂_j V_k`, `e_j`; `Vc_word_bound`,
`trainErrBasic_proof`) and an `L²`-words factor (`e_j`, `∂_j e_k`; `trainErrJetL2_proof`), so
the Leibniz closure `AdvLeib.Gp` applies.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc width)
open AdvLeib

theorem trainAdvDiffL2_proof : UnforcedLeray.Short.PartI.TrainAdvDiffL2 := by
  intro ν c hν hc tr htr s hs hac
  have hc0 : 0 < c := by linarith
  have ha1 : 1 ≤ width ν s := by
    have : 0 ≤ ν * s := (mul_pos hν hs).le
    simp only [Train.width]; linarith
  obtain ⟨hes, -, -, hebd, hVs, -, -⟩ := trainErrBasic_proof ν c hν hc tr htr s hs hac
  have hejl := trainErrJetL2_proof ν c hν hc tr htr s hs hac
  have comp : ∀ {F : Plane → Vec}, ContDiff ℝ ∞ F → ∀ k : Fin 2,
      ContDiff ℝ ∞ (fun x => F x k) := fun hF k =>
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hF
  have hv : ContDiff ℝ ∞ (tr.v s) :=
    TrainErrorEquation.contDiff_slice tr.isTrain.smooth_v hs.le
  -- the four kinds of factors
  have Be : ∀ k : Fin 2, BW (fun x => trainErr tr s x k) := fun k =>
    ⟨comp hes k, fun w => hebd w k⟩
  have Le : ∀ k : Fin 2, LW c (fun x => trainErr tr s x k) := fun k =>
    ⟨comp hes k, fun w => hejl w k⟩
  have BV : ∀ k : Fin 2, BW (fun x => Vc ν c s x k) := by
    intro k
    refine ⟨comp hVs k, fun w => ?_⟩
    obtain ⟨C, -, hC⟩ := Vc_word_bound w.length
    exact ⟨C * width ν s ^ (-(3 + (w.length : ℝ)) / 2), fun z =>
      hC ν c s hc0 ha1 hac w rfl k z⟩
  have hd : ∀ (b : Bool) (j : Fin 2) (z : Plane),
      B0151.derivWord [b] (fun x => trainErr tr s x j) z =
        B0151.derivWord [b] (fun x => tr.v s x j) z - B0151.derivWord [b] (fun x => Vc ν c s x j) z :=
    fun b j z => derivWord_sub_smooth (comp hv j) (comp hVs j) [b] z
  have key : ∀ (k : Fin 2) (z : Plane), advDiff tr s z k =
      Vc ν c s z 0 * B0151.derivWord [true] (fun x => trainErr tr s x k) z +
      Vc ν c s z 1 * B0151.derivWord [false] (fun x => trainErr tr s x k) z +
      B0151.derivWord [true] (fun x => Vc ν c s x k) z * trainErr tr s z 0 +
      B0151.derivWord [false] (fun x => Vc ν c s x k) z * trainErr tr s z 1 +
      trainErr tr s z 0 * B0151.derivWord [true] (fun x => trainErr tr s x k) z +
      trainErr tr s z 1 * B0151.derivWord [false] (fun x => trainErr tr s x k) z := by
    intro k z
    rw [hd true k z, hd false k z]
    fin_cases k
    · simp [advDiff, Train.advection, trainErr, B0151.derivWord]
      change _ = _ 
      have e1 : ∀ f : Plane → ℝ, ∀ z, Cyl.partialQ f z = GaussianVortex.partialX f z := fun _ _ => rfl
      have e2 : ∀ f : Plane → ℝ, ∀ z, Cyl.partialEta f z = GaussianVortex.partialY f z := fun _ _ => rfl
      simp only [e1, e2]
      ring
    · simp [advDiff, Train.advection, trainErr, B0151.derivWord]
      change _ = _ 
      have e1 : ∀ f : Plane → ℝ, ∀ z, Cyl.partialQ f z = GaussianVortex.partialX f z := fun _ _ => rfl
      have e2 : ∀ f : Plane → ℝ, ∀ z, Cyl.partialEta f z = GaussianVortex.partialY f z := fun _ _ => rfl
      simp only [e1, e2]
      ring
  have hLW : ∀ k : Fin 2, LW c (fun x => advDiff tr s x k) := by
    intro k
    have hG : Gp c (fun z => advDiff tr s z k) := by
      have g := Gp.add (Gp.add (Gp.add (Gp.add (Gp.add
        (Gp.prod (BV 0) ((Le k).deriv true)) (Gp.prod (BV 1) ((Le k).deriv false)))
        (Gp.prod ((BV k).deriv true) (Le 0))) (Gp.prod ((BV k).deriv false) (Le 1)))
        (Gp.prod (Be 0) ((Le k).deriv true))) (Gp.prod (Be 1) ((Le k).deriv false))
      convert g using 1
      funext z
      exact key k z
    exact hG.lw
  refine ⟨contDiff_euclidean.2 fun k => (hLW k).1, fun w k => ?_⟩
  exact (hLW k).2 w

end UnforcedLeray.Short.PartI
