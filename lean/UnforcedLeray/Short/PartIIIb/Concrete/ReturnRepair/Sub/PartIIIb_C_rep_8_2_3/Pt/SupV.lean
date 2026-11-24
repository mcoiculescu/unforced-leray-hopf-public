import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VelBand
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.FixedBandJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcJetSup
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcSmooth

/-!
# `PartIII-b:C/rep/8/2/3/2/8`: the velocity sup jets `SupV`

Source of record: `the November 2 reference manuscript` 5484-5492 (young train as
the summed Gaussian train, `c = nu^{-2}`, `a = 1 + nu s <= 2.1`) and 468-478 (`sct:fixed-band`).
Split `v = (v - V_c^p) + V_c^p`: the fixed-band jets of `v - V_c^p` (`fixedBandJets_of`, `Sig = 1`,
transported to period `trainPeriod 2 nu = (nu^2)^{-1} = cOf nu`), and the Gaussian sup jets of
`V_c^p` (`vcJetSup_proof`). Template: `vb_single` / `rawVelBandJets_of`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- **Velocity sup jets on the young range** (source 5484-5492, 468-478). -/
theorem supV_of (hF : UnforcedLeray.Short.PartI.TrainFixedBand) : SupV := by
  intro ℓ m
  obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, H₁⟩ := UnforcedLeray.Short.IIb.fixedBandJets_of hF 1 one_pos ℓ m
  obtain ⟨C₂, N₂, ν₂, hC₂, hν₂, H₂⟩ := UnforcedLeray.Short.IIb.vcJetSup_proof 1 one_pos ℓ m
  refine ⟨C₁ + C₂, N₁ + N₂, min (min ν₁ ν₂) 1, lt_min (lt_min hν₁ hν₂) one_pos, ?_⟩
  intro ν hν hνa tr htr s hs hsS z
  have hν1 : ν ≤ 1 := hνa.trans (min_le_right _ _)
  have hνa1 : ν ≤ ν₁ := hνa.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνa2 : ν ≤ ν₂ := hνa.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hcdef : UnforcedLeray.Short.PartI.trainPeriod 2 ν = (ν ^ 2)⁻¹ := by
    unfold UnforcedLeray.Short.PartI.trainPeriod
    rw [Real.rpow_neg hν.le, Real.rpow_two]
  have hc : cOf ν = UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
    unfold cOf
    rw [hcdef]
  obtain ⟨tr', htr', hv⟩ := UnforcedLeray.Short.IIb.vb_transport hc tr htr
  rw [← hv]
  have hcpos : 0 < UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
    rw [hcdef]; positivity
  have hsm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr'.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr'.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self subset_rfl)
  have hsmG : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => UnforcedLeray.Train.Vc ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) x.1 x.2)
      (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.IIb.vcSmooth_proof ν _ hν hcpos
  have key : UnforcedLeray.Short.PartI.ageJet ℓ m tr'.v s z =
      UnforcedLeray.Short.PartI.ageJet ℓ m
        (fun r w => tr'.v r w - UnforcedLeray.Train.Vc ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) r w) s z +
      UnforcedLeray.Short.PartI.ageJet ℓ m
        (fun r w => UnforcedLeray.Train.Vc ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) r w) s z := by
    have h := UnforcedLeray.Short.IIb.vb_ageJet_sub tr'.v
      (fun r w => UnforcedLeray.Train.Vc ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) r w)
      hsm hsmG hs ℓ m z
    rw [h]
    abel
  rw [key]
  have hA := H₁ ν hν hνa1 tr' htr' s hs hsS z
  have hB := H₂ ν hν hνa2 s hs hsS z
  rw [← hcdef] at hB
  rw [← inv_pow] at hA hB
  have ht : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hm1 : ν⁻¹ ^ N₁ ≤ ν⁻¹ ^ (N₁ + N₂) := pow_le_pow_right₀ ht (by omega)
  have hm2 : ν⁻¹ ^ N₂ ≤ ν⁻¹ ^ (N₁ + N₂) := pow_le_pow_right₀ ht (by omega)
  have e1 := mul_le_mul_of_nonneg_left hm1 hC₁.le
  have e2 := mul_le_mul_of_nonneg_left hm2 hC₂.le
  refine (norm_add_le _ _).trans ?_
  rw [add_mul]
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
