import UnforcedLeray.Short.PartIIa.Sub.F15
import UnforcedLeray.Short.PartIIa.Sub.F06
import UnforcedLeray.Short.PartIIa.Tasks.F01BodyResolvent
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation
import UnforcedLeray.Short.PartIIa.Tasks.F08cLerayYResolventComm
import UnforcedLeray.Short.PartIIa.Tasks.F12TensorDensity
import UnforcedLeray.Lib.LerayC.PhaseSol

/-!
# Part II-a, task `PartII-a:F15/1`: the weak stress is solenoidal

Source of record: `the November 2 reference manuscript`, lines 1537, 1548 and
1498-1500.

Smooth tensors: `w ∈ D_2` with `(μ+L)w = 𝐏 div G` and `R_μ` the Laplace resolvent (F01).
Both `w` and `R_μ (𝐏 div G)` solve the same body equation with data in `Y_2`, so they agree
(homogeneous uniqueness `bodyOp_uniqueness`, F05). `𝐏` commutes with `R_μ` (F08/3), so
`w = 𝐏 (R_μ div G)` is solenoidal (`lerayY_isPhaseSolenoidal`).
Rough tensors: density (`smoothTensorsDense`) and closedness of the solenoidal subspace.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- (F15/1) The weak stress `S_μ T` is solenoidal (`WSUSolenoidal`). -/
theorem wsuSolenoidal : WSUSolenoidal := by
  intro P _ ν hν μ hμ S hS
  have hg : gammaR 2 = 1 / 4 := by
    unfold gammaR
    norm_num
  have hμ' : 0 < μ.re + gammaR 2 := by
    rw [hg]
    exact hμ
  have h1 : (1 : ℝ≥0∞) < 2 := by norm_num
  have h3 : (2 : ℝ≥0∞) < 3 := by norm_num
  have hcl : IsClosed {T : symY2 P | IsPhaseSolenoidal (S T)} :=
    (isClosed_isPhaseSolenoidal (P := P) (q := 2)).preimage S.continuous
  have hd : Dense {T : symY2 P | ∃ G : Fin 3 → ℝ × Space → CVec3,
      (∀ i, IsPhaseTest P (G i)) ∧ IsSymRows G ∧ smoothTensor P G = (T : Y2Sym P)} :=
    smoothTensorsDense P
  have hsub : {T : symY2 P | ∃ G : Fin 3 → ℝ × Space → CVec3,
      (∀ i, IsPhaseTest P (G i)) ∧ IsSymRows G ∧ smoothTensor P G = (T : Y2Sym P)} ⊆
      {T : symY2 P | IsPhaseSolenoidal (S T)} := by
    rintro T ⟨G, hG, hsym, hT⟩
    obtain ⟨w, hwS, hw⟩ := hS T G hG hsym hT
    -- the body resolvent of the Leray-projected data
    obtain ⟨Rm, -, hRm⟩ := bodyResolvent_exists 2 h1 h3 P ν hν μ hμ'
    have hz := bodyResolvent_solves 2 h1 h3 P ν hν μ hμ' Rm hRm
      (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (testElem P 2 (tensorDiv G)))
    have hwL : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) (w : Yq P 2)
        (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (testElem P 2 (tensorDiv G))) := by
      have h := hasPhaseOp_body_of_D (μ := μ) w
      rwa [hw] at h
    have hx : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) ((w : Yq P 2) - Rm
        (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (testElem P 2 (tensorDiv G))))
        (0 : Yq P 2) := by
      have h2 := hwL.add (hz.smul (-1))
      have e1 : (w : Yq P 2) + (-1 : ℂ) • Rm
          (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (testElem P 2 (tensorDiv G))) =
          (w : Yq P 2) - Rm
          (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (testElem P 2 (tensorDiv G))) := by
        simp [sub_eq_add_neg]
      have e2 : lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (testElem P 2 (tensorDiv G)) +
          (-1 : ℂ) • lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top
            (testElem P 2 (tensorDiv G)) = (0 : Yq P 2) := by
        simp
      rw [e1, e2] at h2
      exact h2
    have hzero := bodyOp_uniqueness 2 h1 h3 P ν hν μ hμ' _ hx
    have hwz : (w : Yq P 2) = Rm
        (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (testElem P 2 (tensorDiv G))) :=
      sub_eq_zero.mp hzero
    have hcomm := lerayYResolventComm_proof 2 h1 h3 P ν hν μ hμ' Rm hRm
      (testElem P 2 (tensorDiv G))
    show IsPhaseSolenoidal (S T)
    rw [← hwS]
    rw [hwz, ← hcomm]
    exact lerayY_isPhaseSolenoidal (P := P) ENNReal.one_lt_two ENNReal.ofNat_ne_top _
  intro T
  have hT : T ∈ closure {T : symY2 P | ∃ G : Fin 3 → ℝ × Space → CVec3,
      (∀ i, IsPhaseTest P (G i)) ∧ IsSymRows G ∧ smoothTensor P G = (T : Y2Sym P)} := by
    rw [hd.closure_eq]
    trivial
  exact closure_minimal hsub hcl hT

end UnforcedLeray.Short.PartIIa
