import UnforcedLeray.Short.PartIIIb.NearInst.Targets

/-!
# Sub-lemmas for `PartIII-b:C/near/5` (`NearOpsExistC`, source 3866-3914)

The assembly of the four pinned operators `S₀, S_N, M₀, M_U` from `FreeStressExists`,
`MaskedNearExists`, `CoeffMultExists`, `FlatTrainMultBound`, `SplitMultBound`.


size `ρ_b` *before* its smallness threshold `ν₀`, but `NearOpsExistC` needs it at
`ρ_b = rhoB p m₀ C₀ k₀`, which depends on the level `p` (and is only bounded by `C₀ ν^{-k₀}`).  The
source (1675-1690, 3905-3914) has the operators `S_ε`, `S_far` independent of `ρ_b`: `ρ_b` enters
only through the carrier `Z = Z₁ ⊕ ρ_b^{-1/2} H_T`, and the existing proof
`Masked.maskedNearExists_of` chooses `ν₀` (from `exists_period_le_one`) without using `ρ_b`.  Here
`MaskedNearExists` is the same statement with `∀ ρ_b` placed after `ν₀`; `nearOpsExistC_of_sub` is
the complete assembly from it.  The organizer task `PartIII-b:C/near/5/org` restates
`MaskedNearExists` in `Targets.lean` in this form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

theorem ten3Of_zero_symOuter (u : Merid) :
    ten3Of (UnforcedLeray.Short.IIIa.symOuter (0 : Merid) u) = 0 := by
  unfold ten3Of UnforcedLeray.Short.IIIa.symOuter UnforcedLeray.Short.IIIa.embedMerid
  ext ab
  obtain ⟨i, j⟩ := ab
  fin_cases i <;> fin_cases j <;> simp

/-- **`PartIII-b:C/near/5`, conditional on the uniform masked existence.** -/
theorem nearOpsExistC_of_sub (hF : FreeStressExists) (hN : MaskedNearExists)
    (hC : CoeffMultExists) (hT : FlatTrainMultBound) (hS : SplitMultBound) : NearOpsExistC := by
  intro P hP Kset hK hKsub mZ hmZ dm dp hdm b δ m0 hb hb1 hδ hm0 hm0le C0 k0 hC0 Sig hSig
  have hmZ0 : 0 ≤ mZ := by linarith
  obtain ⟨ν₁, hν₁, hFa⟩ := hF P hP Kset hK hKsub
  obtain ⟨ν₂, hν₂, hNa⟩ := hN Kset hK hKsub mZ hmZ0 b δ hb hb1 hδ dm dp hdm
  obtain ⟨CT, kT, ν₃, hν₃, hTa⟩ := hT mZ hmZ
  obtain ⟨CS, kS, ν₄, hν₄, hSa⟩ := hS dm dp hdm m0 C0 k0 hm0 hm0le hC0 mZ hmZ Sig P.eigenvalue
    P.mode hSig hP.eigenpair
  refine ⟨min ν₁ (min ν₂ (min ν₃ ν₄)), lt_min hν₁ (lt_min hν₂ (lt_min hν₃ hν₄)), ?_⟩
  intro p d hBG hν hSg hmode S_in V rb hsplit μ hμ
  have hν1 : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ ν₂ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν3 : p.ν ≤ ν₃ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν4 : p.ν ≤ ν₄ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hρ : 0 < UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 := by
    unfold UnforcedLeray.Short.IIb.rhoB
    have := p.ε_pos
    have := p.ν_pos
    positivity
  set ρb := UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 with hρdef
  have hcpos : 0 < p.c := p.c_pos
  -- the four operators
  obtain ⟨S0, hS0⟩ := hFa p.ν ⟨p.ν_pos, hν1⟩ p.c hBG.c_eq μ hμ mZ ρb hmZ0 hρ
  obtain ⟨SN, hSN⟩ := hNa p d hBG hν2 ρb hρ μ hμ
  obtain ⟨hTm, hTb⟩ := hTa p.ν ⟨p.ν_pos, hν3⟩ p.c hBG.c_eq p.trainData hBG.train_buc
  obtain ⟨M0, hM0⟩ := hC p.c mZ ρb (CT * p.ν⁻¹ ^ kT) 0 (trainMer p.trainData) (fun _ => 0)
    hcpos hρ hTm measurable_const hTb (Filter.Eventually.of_forall (fun _ => by simp))
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hSa p d hBG hν4 hSg hmode S_in V rb hsplit
  obtain ⟨MU, hMU⟩ := hC p.c mZ ρb (CS * p.ν⁻¹ ^ kS) ρb (UnforcedLeray.Short.IIIa.chartCoeff p.R V)
    (UnforcedLeray.Short.IIIa.chartCoeff p.R rb) hcpos hρ hc1 hc2 hc3 hc4
  refine ⟨⟨S0, SN, M0, MU⟩, ?_, ?_, hS0, hSN⟩
  · intro u
    obtain ⟨h1, h2⟩ := hM0 u
    refine ⟨h1, ?_⟩
    apply Lp.ext
    refine h2.trans ?_
    have : (fun p : Chart => ten3Of (UnforcedLeray.Short.IIIa.symOuter ((fun _ : Chart => (0 : Merid)) p)
        (u p))) = fun _ => 0 := by
      funext p; exact ten3Of_zero_symOuter _
    rw [this]
    exact (Lp.coeFn_zero _ _ _).symm
  · exact hMU

end UnforcedLeray.Short.PartIIIb.NearInst
