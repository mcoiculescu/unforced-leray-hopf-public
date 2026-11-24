import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G6.ActualSeq.SeedLink
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FrozenPairExists
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.GaussSourcesExist
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatForceCurl
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatForceLocal
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatForceDecay
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatXiRegular
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.KcPathEnergy
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatColumnVorticity
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.VorticityToVelocity
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu

/-!
# `PartIII-b:IIIb-D3/2/G6/5/org`: conditional assembly `actualSeqPinned_of`

Source of record: `the November 2 reference manuscript` (73 pages):
lines 4349-4356, 4557-4618, 4650-4654, 4761-4763.

Composes `ActualSeqAux.seedLink_exists`, `IIIa.perFrameFactsAll`,
`FlatSettingInst.frozenPairExists`, `FlatSettingInst.gaussSourcesExist`, and
`FlatSettingInst.isFlatDuhamelColumn_of_leaves` (with the proved force/vorticity/velocity leaves)
to obtain `ActualSeqPinned D` from `TrainEvolutionExists`, `BodyColumnFlat`, and `IIIa.PolyCausal`.
Composed by task `PartIII-b:IIIb-D3/2/G6/5` (`actualSeqPinned` in `G6/ActualSeq.lean`), which in
turn is consumed by `FlatUnif.G6.flatScalarChain_of` (`G6Org.lean`, task `PartIII-b:IIIb-D3/2/G6`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G6

/-- **Actual flat sequence and column pin from `TrainEvolutionExists`, `BodyColumnFlat`, and
`IIIa.PolyCausal`** (source 4349-4356, 4557-4618, 4650-4654, 4761-4763). Composed by task
`PartIII-b:IIIb-D3/2/G6/5` in `G6/ActualSeq.lean`. -/
theorem actualSeqPinned_of
    (hEvol : FlatSettingInst.TrainEvolutionExists)
    (hBody : FlatSettingInst.BodyColumnFlat)
    (hPC : IIIa.PolyCausal)
    (D : SeqData) : ActualSeqPinned D := by
  intro dm dp hst
  obtain ⟨κ, hSeed⟩ := ActualSeqAux.seedLink_exists D
  have hκ : IIIa.IsSeedKernels κ := hSeed.1
  have hFacts : IIIa.PerFrameFactsAll κ := IIIa.perFrameFactsAll κ hκ
  have hm1 : Fact (1 < (9 : ℝ)) := ⟨by norm_num⟩
  have hm8 : (8 : ℝ) < 9 := by norm_num
  obtain ⟨ν₁, hν₁, hE⟩ := hEvol 9 hm8
  obtain ⟨ν₂, hν₂, hFP⟩ := FlatSettingInst.frozenPairExists κ hκ hFacts 9 hm8
  have hFI : ∀ n : ℕ, retNu D.Pl D.σ₀ n ≤ min ν₁ ν₂ →
      Nonempty (FlatSettingInst.FlatInstData κ (retNu D.Pl D.σ₀ n) (cOf (retNu D.Pl D.σ₀ n)) 9
        (D.train n)) := by
    intro n hn
    have hνp : 0 < retNu D.Pl D.σ₀ n := retNu_pos D.Pl D.σ₀ n
    have h1 : retNu D.Pl D.σ₀ n ∈ Ioc 0 ν₁ := ⟨hνp, hn.trans (min_le_left _ _)⟩
    have h2 : retNu D.Pl D.σ₀ n ∈ Ioc 0 ν₂ := ⟨hνp, hn.trans (min_le_right _ _)⟩
    obtain ⟨ev⟩ := hE (retNu D.Pl D.σ₀ n) h1 (cOf (retNu D.Pl D.σ₀ n)) rfl hm1
      (D.train n) (D.train_buc n)
    obtain ⟨fp⟩ := hFP (retNu D.Pl D.σ₀ n) h2 (cOf (retNu D.Pl D.σ₀ n)) rfl hm1
    obtain ⟨gs⟩ := @FlatSettingInst.gaussSourcesExist (retNu D.Pl D.σ₀ n) 9 hm1 hνp
    exact ⟨⟨ev, fp, gs⟩⟩
  let S : ℕ → ConcreteYF.FlatSetting := fun n =>
    if hn : retNu D.Pl D.σ₀ n ≤ min ν₁ ν₂ then
      levelFlat (retNu_pos D.Pl D.σ₀ n) (Classical.choice (hFI n hn)) D.K.χo (retEps D.Pl D.σ₀ n)
    else D.flat n
  have hν_tend : Tendsto (retNu D.Pl D.σ₀) atTop (𝓝 0) := retNu_tendsto D.σ₀ hst.omega_ne
  have hev12 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ min ν₁ ν₂ := by
    filter_upwards [hν_tend.eventually (gt_mem_nhds (lt_min hν₁ hν₂))] with n hn
    exact hn.le
  have hAct : IsActualSeq D κ 9 S := by
    filter_upwards [hev12] with n hn
    exact ⟨Classical.choice (hFI n hn), dif_pos hn⟩
  set Kset : Set ℝ := Icc (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2)
  have hKs : Kset ⊆ Ioo 0 (1 / 4) := by
    intro μ hμ
    have h0 := hst.sigma_pos
    have h1 := hst.sigma_lt
    exact ⟨by linarith [hμ.1], by linarith [hμ.2]⟩
  obtain ⟨ν₃, hν₃, hCol⟩ := FlatSettingInst.isFlatDuhamelColumn_of_leaves
    FlatSettingInst.flatForceCurl FlatSettingInst.flatForceLocal FlatSettingInst.flatForceDecay
    FlatSettingInst.flatXiRegular FlatSettingInst.kcPathEnergy FlatSettingInst.flatColumnVorticity
    FlatSettingInst.vorticityToVelocity hBody hPC hst.planar isCompact_Icc hKs
  have hev3 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ ν₃ := by
    filter_upwards [hν_tend.eventually (gt_mem_nhds hν₃)] with n hn
    exact hn.le
  have hμ_mem := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  refine ⟨κ, 9, hm1, S, hSeed, hm8, hAct, ?_⟩
  filter_upwards [hev12, hev3, hμ_mem] with n hn12 hn3 hμ z hz
  have hSn : S n = levelFlat (retNu_pos D.Pl D.σ₀ n) (Classical.choice (hFI n hn12))
      D.K.χo (retEps D.Pl D.σ₀ n) := dif_pos hn12
  rw [hSn]
  haveI : Fact (0 < cOf (retNu D.Pl D.σ₀ n)) := ⟨cOf_pos (retNu_pos D.Pl D.σ₀ n)⟩
  exact hCol (retNu D.Pl D.σ₀ n) ⟨retNu_pos D.Pl D.σ₀ n, hn3⟩ 9 κ (D.train n) (D.train_buc n)
    (Classical.choice (hFI n hn12)) D.K.χo (retEps D.Pl D.σ₀ n)
    (cOf_pos (retNu_pos D.Pl D.σ₀ n)) (D.mu n z) (hμ z hz) D.K.as D.K.χf

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G6
