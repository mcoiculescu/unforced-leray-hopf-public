import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub3
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDense
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.StressMapReal

/-!
# `RealTestApprox` (source 1675, 1678)

Route. Take a complex smooth tensor test `M` close to `F'` (`TensorTestDense`), and replace it by
its componentwise real part `realTL ∘ M` (still a test, `isTensorTest_realT`).  The real part is
the tensor `realTen (M p)` with entries `(Re M₀, 0, Re M₁; 0, Re M₃, 0; Re M₁, 0, Re M₂)`, whose
`tv4` is `realTL (M p)`.  Since `F'` is real a.e. and `realTL` is 1-Lipschitz, the `H_T` distance
does not increase.  The box tensor conditions come from the test conditions (continuity, periodicity
reduction to the cell `q ∈ [0, c]`, band support).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked
open UnforcedLeray.Short.PartIIa

namespace RealTestAux

/-- The real part of a complex tensor value, as a `3×3` tensor (`rr, rz, zz, φφ` placed as in
`tv4`). -/
def realTen (w : TensorVal) : Ten3 :=
  ten3Of !![(w 0).re, 0, (w 1).re; 0, (w 3).re, 0; (w 1).re, 0, (w 2).re]

theorem realTen_zero : realTen 0 = 0 := by
  ext ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> simp [realTen, ten3Of]

theorem tv4_realTen (w : TensorVal) : tv4 (realTen w) = realTL w := by
  ext i
  fin_cases i <;> simp [tv4, realTen, ten3Of, symRZ, realTL_apply]

theorem continuous_realTen : Continuous realTen := by
  unfold realTen ten3Of
  have hc : ∀ k : Fin 4, Continuous fun w : TensorVal => (w k).re := fun k =>
    Complex.continuous_re.comp ((continuous_apply k).comp (PiLp.continuous_ofLp 2 _))
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun ab => ?_)
  rcases ab with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> simp <;> first | exact hc _ | exact continuous_const

end RealTestAux

open RealTestAux in
/-- **`PartIII-b:C/near/masked/18/3/3`** (`realTestApprox`): real box tests approximate a real box
tensor in `H_T` (source 1675, 1678). -/
theorem realTestApprox : RealTestApprox := by
  intro c hc F' f hF' η hη
  obtain ⟨M, hMt, hM, hlt⟩ := tensorTestDense c hc F' η hη
  have hfun : (fun p => tv4 (realTen (M p))) = fun p => realTL (M p) :=
    funext fun p => tv4_realTen (M p)
  have hcoe : (realTL.compLpL 2 (UnforcedLeray.Short.PartIIa.measureHT c) (hM.toLp M) :
      UnforcedLeray.B0220.Profile → TensorVal) =ᵐ[UnforcedLeray.Short.PartIIa.measureHT c]
        fun p => realTL (M p) := by
    filter_upwards [realTL.coeFn_compLp (hM.toLp M), MemLp.coeFn_toLp hM] with p h1 h2
    exact h1.trans (by rw [h2])
  have hMemr : MemLp (fun p => realTL (M p)) 2 (UnforcedLeray.Short.PartIIa.measureHT c) :=
    MemLp.ae_eq hcoe (Lp.memLp _)
  have hM' : MemLp (fun p => tv4 (realTen (M p))) 2 (UnforcedLeray.Short.PartIIa.measureHT c) := by
    rw [hfun]; exact hMemr
  refine ⟨fun p => realTen (M p), ?_, ?_, hM', ?_⟩
  · show IsTensorTest c (fun p => tv4 (realTen (M p)))
    rw [hfun]
    exact isTensorTest_realT c M hMt
  · have hcont : Continuous fun p => realTen (M p) :=
      continuous_realTen.comp hMt.smooth.continuous
    obtain ⟨s0, s1, L, hs0, hb⟩ := hMt.band
    refine ⟨hcont.measurable, ?_, s0, s1, L, hs0, ?_⟩
    · have hKc : IsCompact (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)) :=
        isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
      obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
      refine ⟨max B 0, fun p => ?_⟩
      by_cases hp : M p = 0
      · simp [hp, realTen_zero]
      · obtain ⟨hp1, hp2⟩ := hb p hp
        have hper : Function.Periodic (fun q => M (p.1, q, p.2.2)) c :=
          fun q => hMt.periodic (p.1, q, p.2.2)
        obtain ⟨y, hy, hyeq⟩ := hper.exists_mem_Ico₀ hc p.2.1
        have hMeq : M p = M (p.1, y, p.2.2) := hyeq
        have hmem : (p.1, y, p.2.2) ∈ Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L) :=
          ⟨⟨hp1.1, hp1.2⟩, ⟨hy.1, hy.2.le⟩, abs_le.mp hp2⟩
        have hbd := hB (p.1, y, p.2.2) hmem
        calc ‖realTen (M p)‖ = ‖realTen (M (p.1, y, p.2.2))‖ := by rw [← hMeq]
          _ ≤ B := hbd
          _ ≤ max B 0 := le_max_left _ _
    · intro p hp
      have hp' : realTen (M p) ≠ 0 := hp
      have hMp : M p ≠ 0 := fun h => hp' (by rw [h, realTen_zero])
      exact ⟨(hb p hMp).1.1, (hb p hMp).1.2, (hb p hMp).2⟩
  · rw [Lp.norm_def] at hlt ⊢
    have hfin : eLpNorm (⇑(F' - hM.toLp M)) 2 (UnforcedLeray.Short.PartIIa.measureHT c) ≠ ⊤ :=
      (Lp.memLp (F' - hM.toLp M)).eLpNorm_lt_top.ne
    have hA : eLpNorm (⇑(F' - hM'.toLp _)) 2 (UnforcedLeray.Short.PartIIa.measureHT c) ≤
        eLpNorm (⇑(F' - hM.toLp M)) 2 (UnforcedLeray.Short.PartIIa.measureHT c) := by
      refine eLpNorm_mono_ae ?_
      filter_upwards [Lp.coeFn_sub F' (hM'.toLp _), Lp.coeFn_sub F' (hM.toLp M),
        MemLp.coeFn_toLp hM', MemLp.coeFn_toLp hM, hF'] with p e1 e2 e3 e4 e5
      have hrl : realTL ((F' : UnforcedLeray.B0220.Profile → TensorVal) p) =
          (F' : UnforcedLeray.B0220.Profile → TensorVal) p := by
        apply realTL_of_real
        intro i
        rw [e5]
        fin_cases i <;> simp [tv4]
      have key : ‖(F' : UnforcedLeray.B0220.Profile → TensorVal) p - tv4 (realTen (M p))‖ ≤
          ‖(F' : UnforcedLeray.B0220.Profile → TensorVal) p - M p‖ := by
        rw [tv4_realTen]
        calc ‖(F' : UnforcedLeray.B0220.Profile → TensorVal) p - realTL (M p)‖
            = ‖realTL ((F' : UnforcedLeray.B0220.Profile → TensorVal) p - M p)‖ := by
              rw [map_sub, hrl]
          _ ≤ ‖(F' : UnforcedLeray.B0220.Profile → TensorVal) p - M p‖ := realTL_norm_le _
      simp only [e1, e2, e3, e4, Pi.sub_apply]
      exact key
    exact lt_of_le_of_lt (ENNReal.toReal_mono hfin hA) hlt

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
