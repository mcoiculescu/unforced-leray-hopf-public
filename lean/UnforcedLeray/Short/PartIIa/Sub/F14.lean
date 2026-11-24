import UnforcedLeray.Short.PartIIa.StatementsFree
import UnforcedLeray.Short.PartIIa.Sub.F12

/-!
# Part II-a, `PartII-a:F14`: `WeakStressExists` from the smooth-tensor stress map

Source of record: `the November 2 reference manuscript`, lines 1537-1544 and
1488-1500.  On the subspace `M` of smooth symmetric phase tensors the stress map `S₀ T = w`,
`(μ+L)w = 𝐏 div G`, is linear with the energy bounds `‖w‖ ≤ ‖T‖/(2√(aν))`,
`‖∇w‖ ≤ ν⁻¹‖T‖`.  `SmoothStressMap` packages exactly this (the analytic content: existence from
surjectivity of `μ+L` on `D_2`, energy identity, linearity).  The theorem
`weakStressExists_of` is the completion argument: extension by density to `symY2 P`
(`LinearMap.extendOfNorm`), the gradient extended in the same way, and closedness of
`HasPhaseOp` passing `HasGrad` to the limit.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **Smooth-tensor stress map** (lines 1537-1544): for a subspace `M ≤ symY2 P` consisting exactly
of the smooth symmetric phase tensors there are linear maps `S₀ : M → Y_2` and `Gr : M → Y_2³` with
`S₀ T = w ∈ D_2` solving `(μ+L)w = 𝐏 div G` whenever `T = smoothTensor G`, `Gr T = ∇ S₀ T`, and
`‖S₀ T‖ ≤ ‖T‖/(2√(aν))`, `‖Gr T‖ ≤ ν⁻¹‖T‖`. -/
def SmoothStressMap : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ M : Submodule ℂ (Y2Sym P), M ≤ symY2 P →
    (∀ X : Y2Sym P, X ∈ M ↔ ∃ G : Fin 3 → ℝ × Space → CVec3,
      (∀ i, IsPhaseTest P (G i)) ∧ IsSymRows G ∧ smoothTensor P G = X) →
    ∃ (S0 : M →ₗ[ℂ] Yq P 2) (Gr : M →ₗ[ℂ] PiLp 2 (fun _ : Fin 3 => Yq P 2)),
      (∀ (X : M) (G : Fin 3 → ℝ × Space → CVec3), (∀ i, IsPhaseTest P (G i)) → IsSymRows G →
        smoothTensor P G = (X : Y2Sym P) →
          ∃ w : D P ν 2, (w : Yq P 2) = S0 X ∧
            bodyOp P ν 2 μ w = lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top
              (testElem P 2 (tensorDiv G))) ∧
      ∀ X : M, ‖S0 X‖ ≤ ‖(X : Y2Sym P)‖ / (2 * Real.sqrt ((μ.re + 1 / 4) * ν)) ∧
        HasGrad (S0 X) (fun j => Gr X j) ∧ ‖Gr X‖ ≤ ν⁻¹ * ‖(X : Y2Sym P)‖

theorem weakStressExists_of (h : SmoothStressMap) (hM : SmoothSymSubmodule)
    (hd : SmoothTensorsDense) : WeakStressExists := by
  intro P _ hP ν hν μ hμ
  obtain ⟨M, hMS, hMmem⟩ := hM P
  obtain ⟨S0, Gr, hsol, hbd⟩ := h P hP ν hν μ hμ M hMS hMmem
  set e : M →ₗ[ℂ] symY2 P := LinearMap.codRestrict (symY2 P) M.subtype (fun x => hMS x.2) with he
  have hnorm : ∀ x : M, ‖e x‖ = ‖(x : Y2Sym P)‖ := fun x => rfl
  have hdense : DenseRange e := by
    have h1 := hd P
    refine h1.mono ?_
    intro T hT
    obtain ⟨G, hG, hs, hGT⟩ := hT
    refine ⟨⟨(T : Y2Sym P), (hMmem _).2 ⟨G, hG, hs, hGT⟩⟩, ?_⟩
    exact Subtype.ext rfl
  set c : ℝ := 1 / (2 * Real.sqrt ((μ.re + 1 / 4) * ν)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hnS : ∃ C : ℝ, ∀ x : M, ‖S0 x‖ ≤ C * ‖e x‖ := ⟨c, fun x => by
    rw [hnorm, hc, one_div, inv_mul_eq_div]; exact (hbd x).1⟩
  have hnG : ∃ C : ℝ, ∀ x : M, ‖Gr x‖ ≤ C * ‖e x‖ := ⟨ν⁻¹, fun x => by
    rw [hnorm]; exact (hbd x).2.2⟩
  set S := S0.extendOfNorm e with hS
  set Ĝ := Gr.extendOfNorm e with hĜ
  have hSe : ∀ x : M, S (e x) = S0 x := fun x => LinearMap.extendOfNorm_eq hdense hnS x
  have hĜe : ∀ x : M, Ĝ (e x) = Gr x := fun x => LinearMap.extendOfNorm_eq hdense hnG x
  refine ⟨S, ?_, ?_⟩
  · intro T G hG hs hGT
    have hTM : (T : Y2Sym P) ∈ M := (hMmem _).2 ⟨G, hG, hs, hGT⟩
    have hTe : e ⟨(T : Y2Sym P), hTM⟩ = T := Subtype.ext rfl
    obtain ⟨w, hw1, hw2⟩ := hsol ⟨(T : Y2Sym P), hTM⟩ G hG hs hGT
    refine ⟨w, ?_, hw2⟩
    rw [hw1]
    calc S0 ⟨(T : Y2Sym P), hTM⟩ = S (e ⟨(T : Y2Sym P), hTM⟩) := (hSe _).symm
      _ = S T := by rw [hTe]
  · intro T
    have hbS : ‖S T‖ ≤ c * ‖T‖ := by
      refine isClosed_property hdense (isClosed_le (S.continuous.norm)
        (continuous_const.mul continuous_norm)) (fun x => ?_) T
      show ‖S (e x)‖ ≤ c * ‖e x‖
      rw [hSe, hnorm, hc, one_div, inv_mul_eq_div]; exact (hbd x).1
    have hbG : ‖Ĝ T‖ ≤ ν⁻¹ * ‖T‖ := by
      refine isClosed_property hdense (isClosed_le (Ĝ.continuous.norm)
        (continuous_const.mul continuous_norm)) (fun x => ?_) T
      show ‖Ĝ (e x)‖ ≤ ν⁻¹ * ‖e x‖
      rw [hĜe, hnorm]; exact (hbd x).2.2
    have hgr : HasGrad (S T) (fun j => Ĝ T j) := by
      have hcl : IsClosed {T : symY2 P | HasGrad (S T) (fun j => Ĝ T j)} := by
        have : {T : symY2 P | HasGrad (S T) (fun j => Ĝ T j)} =
            ⋂ j : Fin 3, {T : symY2 P |
              ((S T, Ĝ T j) : Yq P 2 × Yq P 2) ∈
                {x : Yq P 2 × Yq P 2 | HasPhaseOp (fun Φ => -dy j Φ) x.1 x.2}} := by
          ext T; simp [HasGrad]
        rw [this]
        refine isClosed_iInter fun j => ?_
        exact (isClosed_hasPhaseOp (P := P) (q := 2) (fun Φ => -dy j Φ)).preimage
          (S.continuous.prodMk ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => Yq P 2) j).continuous.comp
            Ĝ.continuous))
      refine isClosed_property hdense hcl (fun x => ?_) T
      show HasGrad (S (e x)) (fun j => Ĝ (e x) j)
      rw [hSe, hĜe]; exact (hbd x).2.1
    refine ⟨?_, fun j => Ĝ T j, hgr, ?_⟩
    · have h3 : ‖(T : Y2Sym P)‖ = ‖T‖ := rfl
      rw [h3]
      calc ‖S T‖ ≤ c * ‖T‖ := hbS
        _ = ‖T‖ / (2 * Real.sqrt ((μ.re + 1 / 4) * ν)) := by rw [hc]; ring
    · have h2 : Real.sqrt (∑ j, ‖Ĝ T j‖ ^ 2) = ‖Ĝ T‖ := by
        rw [PiLp.norm_eq_of_L2]
      rw [h2]; exact hbG
end UnforcedLeray.Short.PartIIa
